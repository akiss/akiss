(****************************************************************************)
(* Akiss                                                                    *)
(* Copyright (C) 2011-2014 Baelde, Ciobaca, Delaune, Kremer                 *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

(** We use Tamarin (branch feature-ac-rewrite-rules) to compute
  * variants modulo AC because the feature is broken in Maude. *)

open Term

let debug = false
let pdebug = false (* show parsing info *)
let sdebug = pdebug || false (* show script *)

let input_line chan =
  let line = input_line chan in
    if pdebug then
      Format.printf "input line > %S\n%!" line ;
    line

(** Printing *)
let rec print chan = function
  | Fun ("plus",[a;b]) ->
      Format.fprintf chan "(%a+%a)" print a print b

  | Fun ("!tuple!",l) ->
      assert (List.length l > 1) ;
      Format.fprintf chan "<%a>" (Util.pp_list print ", ") l

  | Fun ("!test!",[]) ->
      Format.fprintf chan "akisstest()"
  | Fun ("!out!",[Fun(c,[])]) ->
      Format.fprintf chan "akissout('%s')" c
  | Fun ("!in!",[Fun(c,[]);t]) ->
      Format.fprintf chan "akissin('%s',%a)" c print t

  | Fun (s,[]) when List.mem s !private_names ->
      Format.fprintf chan "'%s'" s

  | Fun (s,[]) ->
      begin try
        Scanf.sscanf s "w%d"
          (fun d -> Format.fprintf chan "'%s'" s)
      with Scanf.Scan_failure _ ->
        begin try
          Scanf.sscanf s "!n!%d"
            (fun n -> Format.fprintf chan "'akissn%d'" n)
        with Scanf.Scan_failure _ ->
          Format.fprintf chan "%s()" s
        end
      end

  | Fun (s,args) ->
      Format.fprintf chan "%s(%a)" s (Util.pp_list print ", ") args

  | Var s ->
      Format.fprintf chan "%s" s

(** Parse variants *)

(** Running and interacting with tamarin-prover *)
let process print_query parse_result =
  let chan_out,chan_in =
    Unix.open_process (Lazy.force Config.tamarin_binary ^ " variants")
  in
  let fin = Format.formatter_of_out_channel chan_in in
    if sdebug then print_query Format.std_formatter ;
    Format.print_flush () ;
    print_query fin ;
    Format.pp_print_flush fin () ;
    let result = parse_result chan_out in
    let ret = Unix.close_process (chan_out,chan_in) in
      assert (ret = Unix.WEXITED 0) ;
      result

let print_sig chan rules =
  (* Akiss constructors *)
  let op f a =
    Format.fprintf chan "functions: %s/%d\n" f a
  in
  op "akissout" 1 ; op "akissin" 2 ; op "akisstest" 0 ;
  op "world" 2 ; op "empty" 0 ;
  op "knows" 3 ; op "reach" 1 ; op "identical" 3 ; op "ridentical" 3 ;
  (* Term signature *)
  List.iter
    (fun (f,n) -> if f <> "plus" then op f n)
    !fsymbols ;
  (* Rewrite rules *)
  List.iter
    (fun (left,right) ->
       Format.fprintf chan "equations: %a = %a\n" print left print right)
    rules ;
  Format.fprintf chan ".\n"

let variants normalize t rules =
  if debug then
    Format.printf "<< tamarin variants: %s\n" (show_term t) ;
  let query chan =
    print_sig chan rules ;
    Format.fprintf chan "variants %a\n" print t ;
    Format.fprintf chan ".\n"
  in
  let parse_variants ch =
    match Parsetam.main Lextam.token (Lexing.from_channel ch) with
      | [`Variants substs] ->
          if debug then
            List.iter
              (fun s -> Printf.printf "result> %s\n" (show_subst s))
              substs ;
          let norm x = normalize x rules in
          let result =
            List.map (fun s -> norm (apply_subst t s), s) substs
          in
            if debug then
              List.iter
                (fun (t,s) ->
                   Printf.printf
                     "Result> %s,%s\n" (show_term t) (show_subst s))
                result ;
            result
      | _ -> assert false
  in
  let parse_variants ch =
    try parse_variants ch with
      | Parsing.Parse_error as e ->
          Format.printf
            "Error while parsing tamarin-prover output.\n" ;
          query Format.std_formatter ;
          raise e
  in
    process query parse_variants

(** Unification modulo AC. Maude could also be used. *)
let unifiers s t =
  if debug then
    Format.printf "<< tamarin unifiers: %s =? %s\n" (show_term s) (show_term t) ;
  let query chan =
    print_sig chan [] ;
    Format.fprintf chan "unify %a = %a\n" print s print t ;
    Format.fprintf chan ".\n"
  in
  let parse_unifiers ch =
    match Parsetam.main Lextam.token (Lexing.from_channel ch) with
      | [`Unify substs] ->
          if debug then
            List.iter
              (fun s -> Printf.printf "Result> %s\n" (show_subst s))
              substs ;
          substs
      | _ -> assert false
  in
  let parse_unifiers ch =
    try parse_unifiers ch with
      | Parsing.Parse_error as e ->
          Format.printf
            "Error while parsing tamarin-prover output.\n" ;
          query Format.std_formatter ;
          raise e
  in
    process query parse_unifiers

(** Unification modulo AC + theory, using variants. *)
let unifiers normalize s t rules : subst list =
  let v = variants normalize (Fun("pair",[s;t])) rules in
    List.concat
      (List.map
         (function
            | (Fun("pair",[ss;ts]),sigma) ->
                begin match unifiers ss ts with
                  | [theta] -> [compose sigma theta]
                  | [] -> []
                  | _ -> assert false
                end
            | _ -> assert false)
         v)

(** Final unification wrapper, eliminating tuples of size less than 2. *)
let unifiers normalize s t rules =
  match s,t with
    | Fun("!tuple!",[]), Fun("!tuple!",[]) -> [[]]
    | Fun("!tuple!",[s]), Fun("!tuple!",[t]) -> unifiers normalize s t rules
    | s,t -> unifiers normalize s t rules
