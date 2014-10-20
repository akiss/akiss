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

(** Process command line and preamble of the input,
  * which defines the theory in which we should work. *)

open Lexer
open Parser
open Term
open Util

(** Flags set from the script using #set ac/xor.
  * - [ac] triggers special treatment of "plus" as AC connective.
  * - [xor] triggers normalization of identical statements in the form
  *   id(X,0). *)
let ac = ref false
let xor = ref false

let ac_toolbox = ref false

(** See in [Horn] for documentation. *)
let check_generalizations = ref false

let usage = Printf.sprintf
  "Usage: %s [-verbose] [-debug] < specification-file.api"
  (Filename.basename Sys.argv.(0))

let command_line_options_list = [
  ("--verbose", Arg.Unit (fun () -> verbose_output := true),
   "Enable verbose output");
  ("-verbose", Arg.Unit (fun () -> verbose_output := true),
   "Enable verbose output");
  ("-debug", Arg.Unit (fun () -> debug_output := true),
   "Enable debug output");
  ("--debug", Arg.Unit (fun () -> debug_output := true),
   "Enable debug output");
  ("--ac-compatible", Arg.Set ac_toolbox,
   "Use the AC-compatible toolbox even on non-AC theories.");
  ("--check-generalizations", Arg.Set check_generalizations,
   "Check that generalizations of kept statements are never dropped.")
]

let cmdlist =
  let collect arg = Printf.printf "%s\n" usage ; exit 1 in
  let _ = Arg.parse command_line_options_list collect usage in
  let lexbuf = Lexing.from_channel stdin in
  try
    Parser.main Lexer.token lexbuf
  with Parsing.Parse_error ->
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      Printf.printf "Syntax error at line %d, column %d!\n" line cnum ;
      exit 1

let evchannels = ref []

let rewrite_rules = ref []

let evrewrite_rules = ref []

let appendto lref l = lref := List.append !lref l

let addto lref e = appendto lref [e];;

let rec declare_symbols symbolList =
  appendto fsymbols symbolList

let rec declare_names nameList = 
  appendto private_names nameList

let rec declare_channels nameList =
  appendto channels nameList

let rec declare_evchannels nameList =
  appendto channels nameList;
  appendto evchannels nameList

let rec declare_vars varList = 
  appendto vars varList

let rec declare_rewrite t1 t2 = 
  addto rewrite_rules ((parse_term t1), (parse_term t2))

let rec declare_evrewrite t1 t2 = 
  addto evrewrite_rules ((parse_term t1), (parse_term t2))

type atom_type =  
  | Channel
  | Name
  | Symbol of int
  | Variable

exception No_duplicate

let rec find_dup l = 
  match l with
    | [] -> raise No_duplicate
    | _ :: [] -> raise No_duplicate
    | (x, _) :: ((y, _) as hd) :: tl ->
	if y = x then
	  x
	else
	  find_dup (hd :: tl)

exception Parse_error_semantic of string;;

let check_atoms () =
  let atoms = 
    List.concat [
      List.map (fun (x, y) -> (x, Symbol(y))) !fsymbols;
      List.map (fun x -> (x, Channel)) !channels;
      List.map (fun x -> (x, Variable)) !vars;
      List.map (fun x -> (x, Name)) !private_names;
    ] in
  let sorted_atoms =
    List.sort (fun (x, _) (xp, _) -> compare x xp) atoms
  in
  try
    let duplicate = find_dup sorted_atoms in
    raise
      (Parse_error_semantic
         (Printf.sprintf
            "Identifier \"%s\" declared more than once."
            duplicate))
  with
    | No_duplicate -> ()
    | Parse_error_semantic(e) -> raise (Parse_error_semantic(e))

open Ast

let process_decl = function

  | SetAC ->
      ac := true
  | SetXOR ->
      ac := true ;
      xor := true ;
      if !rewrite_rules <> [] then begin
        Printf.printf
          "#set xor: only allowed at the beginning of the script!\n" ;
        exit 1
      end ;
      let x = Var "X" and y = Var "Y" in
      let (+) a b = Fun("plus",[a;b]) in
      let zero = Fun("zero",[]) in
      let (==) left right = left,right in
        rewrite_rules := [
          x+zero  == x ;
          x+x     == zero ;
          x+(x+y) == y
        ]

  | DeclSymbols symbolList ->
    Printf.printf "Declaring symbols\n%!";
    declare_symbols symbolList;
    check_atoms ()
  | DeclChannels channelList ->
    Printf.printf "Declaring symbols\n%!";
    declare_channels channelList;
    check_atoms ()
  | DeclEvChannels evchannelList ->
    Printf.printf "Declaring symbols\n%!";
    declare_evchannels evchannelList;
    check_atoms ()
  | DeclPrivate nameList ->
    Printf.printf "Declaring private names\n%!";
    declare_names nameList;
    check_atoms ()
  | DeclVar varList ->
    Printf.printf "Declaring variables\n%!";
    declare_vars varList;
    check_atoms ()

  | DeclRewrite(t1, t2) ->
    Printf.printf "Declaring rewrite rule\n%!";
    declare_rewrite t1 t2
  | DeclEvRewrite(t1, t2) ->
    Printf.printf "Declaring rewrite rule\n%!";
    declare_evrewrite t1 t2
  | _ -> failwith "not preamble"

let cmdlist =
  let rec parse = function
    | d::l ->
        if
          (try process_decl d ; true with
             | Failure "not preamble" -> false)
        then
          parse l
        else
          d::l
    | [] -> []
  in
    parse cmdlist

(** Final versions of the theory parameters *)

let () =
  (* we use pairing in tamarin, and indirectly in maude:
   * make sure it is properly defined. *)
  fsymbols :=
    try
      let a = List.assoc "pair" !fsymbols in
        if a <> 2 then begin
          Format.printf
            "The \"pair\" symbol cannot be defined \
             with another arity than 2!\n" ;
          exit 1
        end ;
        !fsymbols
    with Not_found -> ("pair",2) :: !fsymbols

let xor = !xor
let ac = !ac
let fsymbols = !fsymbols
let channels = !channels
let private_names = !private_names
let evchannels = !evchannels
let rewrite_rules = !rewrite_rules
let evrewrite_rules = !evrewrite_rules
let check_generalizations = !check_generalizations

(** Rewriting toolbox *)

module type REWRITING = sig
  val unifiers : term -> term -> rules -> subst list
  val normalize : term -> rules -> term
  val variants : term -> rules -> (term*subst) list
  val equals : term -> term -> rules -> bool
  val matchers : term -> term -> rules -> subst list
end

module AC : REWRITING = struct
  let normalize = Maude.normalize
  let equals = Maude.equals
  let unifiers s t r =
    if r = [] then Maude.unifiers s t [] else
      let u1 = Tamarin.unifiers s t r in
        assert (ac ||
                let u2 = Rewriting.unifiers s t r in
                  List.length u1 = List.length u2) ;
        u1
  let matchers = Maude.matchers
  let variants = Tamarin.variants
end

module NonAC : REWRITING = struct

  let normalize = Rewriting.normalize

  let equals s t rules =
    if rules = [] then s = t else
      normalize s rules = normalize t rules

  let unifiers s t rules =
    if rules = [] then
      try [Rewriting.mgu s t] with
        | Rewriting.Not_unifiable -> []
    else
      Rewriting.unifiers s t rules

  let matchers s t rules =
    assert (rules = []) ;
    try [Rewriting.mgm s t] with
      | Rewriting.Not_matchable -> []

  let variants = Rewriting.variants

end

module R = (val if ac || !ac_toolbox then begin
              if not ac && List.mem ("plus",2) fsymbols then begin
                Printf.printf
                  "Cannot use non-AC \"plus\" symbol \
                   with AC-compatible toolbox!\n" ;
                exit 1
              end ;
              Printf.printf "Using AC-compatible toolbox...\n" ;
              (module AC : REWRITING)
            end else begin
              Printf.printf "Using non-AC toolbox...\n" ;
              (module NonAC : REWRITING)
            end : REWRITING)
