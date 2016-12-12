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

open Term

let debug= (! Util.extra_output land Util.about_theory != 0)
let pdebug = (! Util.extra_output land Util.debug_theory != 0) (* show parsing info *)
let sdebug = false (* show maude script *)

let terms_of_rules rules =
  List.fold_left
    (fun tms (l,r) -> l::r::tms)
    []
    rules

let input_line chan =
  let line = input_line chan in
    if(! Util.extra_output land Util.debug_theory != 0)then
      Format.printf "input line > %S\n%!" line ;
    line

(** Printing Maude terms and modules *)

let rec print chan = function

  | Fun ("!tuple!",l) ->
      let n = List.length l in
      let f = Format.sprintf "akiss%duple" n in
        print chan (Fun (f,l))
  | Fun ("!test!",[]) ->
      print chan (Fun ("akisstest",[]))
  | Fun ("!out!",[Fun(c,[])]) ->
      print chan (Fun ("akissout",[Fun ("akissch"^c,[])]))
  | Fun ("!in!",[Fun(c,[]);t]) ->
      print chan (Fun ("akissin",[Fun("akissch"^c,[]);t]))

  | Fun (s,[]) | Var s ->
      begin try
        Scanf.sscanf s "w%d"
          (fun _ -> Format.fprintf chan "akiss%s" s)
      with Scanf.Scan_failure _ ->
        begin try
          Scanf.sscanf s "!n!%d"
            (fun n -> Format.fprintf chan "akissn%d" n)
        with Scanf.Scan_failure _ ->
          Util.output_string chan s
        end
      end
  | Fun (s,args) ->
      Format.fprintf chan "%s(%a)" s (Util.pp_list print ", ") args

let sprint t =
  print Format.str_formatter t ;
  Format.flush_str_formatter ()

let rec times n f =
  if n = 0 then () else begin f () ; times (n-1) f end

let cursig = ref []

  
let print_module rules extrasig chan () =
  cursig := [] ;
  let op name arity =
    cursig := (name,arity) :: !cursig ;
    Format.fprintf chan "op %s : %a-> Term .\n" name
      (fun chan () -> times arity (fun () -> Format.fprintf chan "Term "))
      ()
  in
    Format.fprintf chan "mod AKISS is\nsorts Term .\n" ;

    (* Constructors for tuples, actions, worlds and predicates *)
    op "akissout" 1 ; op "akissin" 2 ; op "akisstest" 0 ;
    op "world" 2 ; op "empty" 0 ;
    op "knows" 3 ; op "reach" 1 ; op "identical" 3 ; op "ridentical" 3 ;
    op "akisschthen" 0;op "xx" 0;
    List.iter (fun c -> op ("akissch"^c) 0) !Term.channels ;

    (* Declarations from the input file: theory symbols and private names *)
    List.iter
      (fun (f,n) ->
         if f = "plus" then
           Format.fprintf chan "op plus : Term Term -> Term [assoc comm] .\n"
         else
           op f n)
      !fsymbols ;
    List.iter (fun v -> op v 0) !private_names ;

    (* Tuples, parameters, names and variables not declared in input file
     * but present in the term, given as extrasig. *)
    List.iter
      (fun n ->
         op (Printf.sprintf "akiss%duple" n) n)
      extrasig.tuples ;
    List.iter
      (fun n -> op ("akissw" ^ string_of_int n) 0)
      extrasig.params ;
    List.iter
      (fun n -> op ("akissn" ^ string_of_int n) 0)
      extrasig.names ;
    if !vars <> [] || extrasig.vars <> [] then
      Format.fprintf chan "var %a : Term .\n"
        (Util.pp_list Util.output_string " ")
        (Util.unique (List.rev_append !vars extrasig.vars)) ;

    (* Rewrite rules *)
    let c = ref 0 in
    List.iter
      (fun (left,right) ->
         incr c ;
         Format.fprintf chan
           "eq [rule%d] : %a = %a [variant] .\n"
           !c print left print right)
      rules ;

    Format.fprintf chan "endm\n\n"

(** Interacting with a maude process *)

let get_chans =
  let dummy = stdin,stdout in
  let chans = ref dummy in
  let countdown = ref 0 in
  let close () =
    if !chans <> dummy then begin
      (* Maude doesn't seem to return 0 on clean termination. *)
      ignore (Unix.close_process !chans) ;
      (* Reset chans to dummy to avoid closing twice. *)
      chans := dummy
    end
  in
  at_exit close ;
  fun () ->
    if !countdown > 0 then begin
      decr countdown ;
      !chans
    end else begin
      close () ;
      let pair = Unix.open_process (Lazy.force Config.maude_command) in
      chans := pair ;
      countdown := 10000 ;
      pair
    end

      
let run_maude print_query parse_result =
  if(! Util.extra_output land Util.debug_theory != 0)then
    Format.printf "<< maude command: %s\n"  (Lazy.force Config.maude_command);
  let chan_out,chan_in = get_chans () in
      (* let chan_out,chan_in = *)
      (* 	Unix.open_process (Lazy.force Config.maude_command) in *)
  let fin = Format.formatter_of_out_channel chan_in in
  if sdebug then print_query Format.std_formatter ;
  Format.print_flush () ;
  print_query fin ;
  Format.pp_print_flush fin () ;
  let result = parse_result chan_out in
      (* Unix.close_process (chan_out,chan_in); *)
  result


(** Unification mod AC + R*)

let unifiers s t rules =
  if(! Util.extra_output land Util.about_theory != 0)then
    Format.printf "<< maude unifiers: %s =? %s\n" (show_term s) (show_term t) ;
  let esig = sig_of_term_list [s;t] in
  let query chan =
    Format.fprintf chan "%a\n" (print_module rules esig) () ;
    Format.fprintf chan "variant unify %a =? %a .\n" print s print t ; 
    (* Format.fprintf chan "quit \n" *)
  in 
  let parse_unifiers ch lexbuf =
    match Parsemaude.main Lexmaude.token lexbuf with
    | `Unify substs ->
      if(! Util.extra_output land Util.about_theory != 0)then
        List.iter
          (fun s -> Printf.printf "Result> %s\n" (show_subst s))
          substs ;
      substs
    | _ -> assert false
  in
  let parse_unifiers ch =
    let lexbuf = (Lexing.from_channel ch) in
    try parse_unifiers ch lexbuf with
    | Parsing.Parse_error as e ->
      Format.printf
        "Error while parsing maude output.\n" ;
      query Format.std_formatter ;
      raise e
  in
  run_maude
    (fun chan -> query chan)
    (fun chan -> parse_unifiers chan)
      
let unifiers s t rules =
  let v = unifiers s t rules in
  (* let v = rename_in_subst v in *)
    if(! Util.extra_output land Util.about_theory != 0)then begin
      Format.printf "unifiers %s %s (%d solutions):\n%!"
        (show_term s) (show_term t) (List.length v) ;
      List.iter (fun s -> Format.printf " %s\n" (show_subst s)) v
    end ;
    v



let acunifiers s t =
  if(! Util.extra_output land Util.about_theory != 0)then
    Format.printf "<< maude unifiers: %s =? %s\n" (show_term s) (show_term t) ;
  let esig = sig_of_term_list [s;t] in
  let query chan =
    Format.fprintf chan "%a\n" (print_module [] esig) () ;
    Format.fprintf chan "unify %a =? %a .\n" print s print t ; 
    (* Format.fprintf chan "quit \n" *)
  in 
  let parse_unifiers ch lexbuf =
    match Parsemaude.main Lexmaude.token lexbuf with
    | `Unify substs ->
      if(! Util.extra_output land Util.about_theory != 0)then
        List.iter
          (fun s -> Printf.printf "Result> %s\n" (show_subst s))
          substs ;
      substs
    | _ -> assert false
  in
  let parse_unifiers ch =
    let lexbuf = (Lexing.from_channel ch) in
    try parse_unifiers ch lexbuf with
    | Parsing.Parse_error as e ->
      Format.printf
        "Error while parsing maude output.\n" ;
      query Format.std_formatter ;
      raise e
  in
  run_maude
    (fun chan -> query chan)
    (fun chan -> parse_unifiers chan)
      
let acunifiers s t  =
  let v = acunifiers s t  in
  (* let v = rename_in_subst v in *)
  if(! Util.extra_output land Util.about_theory != 0)then begin
    Format.printf "unifiers %s %s (%d solutions):\n%!"
        (show_term s) (show_term t) (List.length v) ;
    List.iter (fun s -> Format.printf " %s\n" (show_subst s)) v
  end ;
  v


      
(** variants of a term *)

let variants t rules =
  if(! Util.extra_output land Util.about_theory != 0)then
    Format.printf "<< maude variants: %s \n" (show_term t) ;
  let esig = sig_of_term_list [t] in
  let query chan =
    Format.fprintf chan "%a\n" (print_module rules esig) () ;
    Format.fprintf chan "get variants %a .\n" print t ;
    (* Format.fprintf chan "quit \n" *)
  in 
  let parse_variants ch =
    match Parsemaude.main Lexmaude.token (Lexing.from_channel ch) with
    | `Variants v ->
      if(! Util.extra_output land Util.about_theory != 0)then
	(
      	  let (_, sl) = List.split v in
          List.iter
      	    (fun s -> Printf.printf "Result> %s\n"(show_subst s))
      	    sl ;
	);
      v
    | _ -> assert false
  in
  let parse_variants ch =
    try parse_variants ch with
    | Parsing.Parse_error as e ->
      Format.printf
        "Error while parsing maude output.\n" ;
      query Format.std_formatter ;
      raise e
  in
  run_maude
    (fun chan -> query chan)
    (fun chan -> parse_variants chan)
      
let variants t rules =
  let v = variants t rules in
  (* let v = rename_in_subst v in *)
  if(! Util.extra_output land Util.about_theory != 0)then begin
    Format.printf "variants %s (%d solutions):\n%!"
      (show_term t) (List.length v) ;
    (*      List.iter (fun s -> Format.printf " %s\n" (show_subst s)) v *)
    end ;
  v

(** Matching *)

let acmatchers s t =
  let esig = sig_of_term_list [s;t] in

  let query chan =
    Format.fprintf chan "%a\n" (print_module [] esig) () ;
    Format.fprintf chan "match %a <=? %a .\n" print s print t;
  in

  let parse_matchers ch =
    match Parsemaude.main Lexmaude.token (Lexing.from_channel ch) with
    | `Match substs ->
      if(! Util.extra_output land Util.about_theory != 0)then
        List.iter
          (fun s -> Printf.printf "Result> %s\n" (show_subst s))
          substs ;
      substs
    | _ -> assert false
  in
  let parse_matchers ch =
    try parse_matchers ch with
    | Parsing.Parse_error as e ->
      Format.printf
        "Error while parsing maude output.\n" ;
      query Format.std_formatter ;
      raise e
  in
  run_maude
    (fun chan -> query chan)
    (fun chan -> parse_matchers chan)

let acmatchers s t =
  let v = acmatchers s t in
  (* let v = rename_in_subst v in *)
    if(! Util.extra_output land Util.about_theory != 0)then begin
      Format.printf "matchers %s %s (%d solutions):\n%!"
        (show_term s) (show_term t) (List.length v) ;
      List.iter (fun s -> Format.printf " %s\n" (show_subst s)) v
    end ;
    v

(** Check equality modulo AC+R *)

let equals s t rules =
  if s = t then true
  else(
    if(! Util.extra_output land Util.about_theory != 0)then
      Format.printf "<< maude equals: %s = %s\n" (show_term s) (show_term t) ;
    let esig = sig_of_term_list (s :: t :: terms_of_rules rules) in
    
    let query chan =
      Format.fprintf chan "%a\n" (print_module rules esig) () ;
      Format.fprintf chan "reduce %a == %a .\n" print s print t ;
    in
    let parse_equals ch =
      match Parsemaude.main Lexmaude.token (Lexing.from_channel ch) with
      | `Equal b ->
	if(! Util.extra_output land Util.about_theory != 0)then
          Printf.printf "Result> %B\n" b;
	b
      | _ -> assert false
    in
    let parse_equals ch =
      try parse_equals ch with
      | Parsing.Parse_error as e ->
	Format.printf
          "Error while parsing Equals maude output.\n" ;
	query Format.std_formatter ;
	raise e
    in
    run_maude
      (fun chan -> query chan)
      (fun chan -> parse_equals chan)
  )
    
(* let equals s t rules = *)
(*   let b = equals s t rules in *)
  
(*     if(! Util.extra_output land Util.about_theory != 0)then *)
(*       Format.printf "equals %s %s: %B\n" *)
(*         (show_term s) (show_term t) b ; *)
(*     b *)

(** Normalize a term *)
let normalize t rules =
  if(! Util.extra_output land Util.about_theory != 0)then
    Format.printf "<< maude reduce: %s\n" (show_term t) ;
  let esig = sig_of_term_list (t :: terms_of_rules rules) in
  let query chan =
    Format.fprintf chan "%a\n" (print_module rules esig) () ;
    Format.fprintf chan "reduce %a .\n" print t ;
    (* Format.fprintf chan "quit \n" *)
  in
  let parse_normalize ch =
    match Parsemaude.main Lexmaude.token (Lexing.from_channel ch) with
    | `Norm term ->
      if(! Util.extra_output land Util.about_theory != 0)then
        Printf.printf "Result> %s\n" (show_term term);
      term
    | _ -> assert false
  in
  let parse_normalize ch =
    try parse_normalize ch with
    | Parsing.Parse_error as e ->
      Format.printf
        "Error while parsing maude output.\n" ;
      query Format.std_formatter ;
      raise e
  in
  run_maude
    (fun chan -> query chan)
    (fun chan -> parse_normalize chan)
      
let normalize t rules =
  let nt = normalize t rules in
    if(! Util.extra_output land Util.about_theory != 0)then begin
      Format.printf "normalize %s:\n%!"
        (show_term t) ;
    end ;
    nt

