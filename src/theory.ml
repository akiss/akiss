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

(*open Lexer
open Parser*)
(*open Term *)
open Util

(*let dotfile = ref None
let jobs = ref 1*)

(** Flags set from the script using #set ac/xor.
  * - [ac] triggers special treatment of "plus" as AC connective.
  * - [xor] triggers normalization of identical statements in the form
  *   id(X,0). *)


(*
let ac_toolbox = ref false
let tamarin_variants = ref false

(** Experimental POR optimization *)
let por = ref false
let disable_por = ref false
*)

let usage = Printf.sprintf
  "Usage: %s [options] specification-file list"
  (Filename.basename Sys.argv.(0))

let  set_debug = function
  | "progress" -> about_progress := true
  | "else" -> about_completion := true
  | "canon" ->  about_canonization := true
  | "seed" -> about_seed := true
  | "sat" -> about_saturation := true
  | "saturation" -> about_saturation := true ; debug_saturation := true
  | "maude" -> about_maude := true
  | "bij" -> about_bijection := true
  | _ -> raise (Arg.Bad("Undefined semantics"))


    
let command_line_options_list = [
  ("-d",
   Arg.Symbol(["progress";"completion";"canon";"seed";"sat";"saturation";"maude";"exec"],set_debug),
   " Enable additional debug information");
   ("-comp", Arg.Set(about_completion), 
    "Enable debug output about completions"); 
   ("-canonization", Arg.Set(about_canonization),
    "Enable debug output about canonization rules");
   ("-seed", Arg.Set(about_seed), 
    "Enable debug output about seed"); 
   ("-sat", Arg.Set(about_saturation), 
    "Enable verbose output about saturation"); 
   ("-saturation", Arg.Set(debug_saturation), 
    "Enable debug output about saturation"); 
   ("-bij", Arg.Set(about_bijection), 
    "Show tests correspondance");
   ("-loc", Arg.Set(about_location), 
    "Show location information");
   ("-execution", Arg.Set(debug_execution), 
    "Show tests executions debugging"); 
   ("-tests", Arg.Set(about_tests), 
    "Show information about tests");
   ("-tests-info", Arg.Set(debug_tests), 
    "Show information about tests");
   ("-merge", Arg.Set(debug_merge), 
    "Show information about merging tests");
   ("-progress", Arg.Set(about_progress),
    "Print info in about progression of Akiss");
   ("-bench", Arg.Set(about_bench),
    "Bench compatible output");
   ("-xml", Arg.Set(use_xml),
    "Print info in xml format");
  (*"--extra", Arg.Int (fun i -> extra_output := i),
   "<n>  Display information <n>"*)
  (*("--output-dot", Arg.String (fun s -> dotfile := Some s),
   "<file>  Output statement graph to <file>");*)
 (* ("-j", Arg.Int (fun i -> jobs := i),
   "<n>  Use <n> parallel jobs (if supported)");*)
  (*("--ac-compatible", Arg.Set ac_toolbox,
   "Use the AC-compatible toolbox even on non-AC theories (experimental)");
  ("--disable-por", Arg.Set(disable_por),
   "Disable partial order reduction (por) optimisations")*)
]

(******* Parsing *****)

let process_file f =

  let ch_in = open_in f in

  
  let lexbuf = Lexing.from_channel ch_in in
  
  let _ =
    try
      while true do
        Parser_queries.parse_one_declaration (Grammar.main Lexer.token lexbuf)
      done
    with
      | Failure msg -> Printf.printf "%s\n" msg; exit 0
      | End_of_file -> () in
  
  close_in ch_in;
  Parser_functions.reset_parser ()
  
let () =
  (*Printf.printf "Akiss starts\n%!" ;*)
  Arg.parse command_line_options_list process_file usage;
  exit 0

(*let cmdlist =
  let collect arg = Printf.printf "%s\n" usage ; exit 1 in
  let _ = Arg.parse command_line_options_list collect usage in
  let lexbuf = Lexing.from_channel stdin in
  try
    Parser_functions.parse_one_declaration (Grammar.main Lexer.token lexbuf)
  with Parsing.Parse_error ->
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      Printf.printf "Syntax error at line %d, column %d!\n" line cnum ;
      exit 1
*)
(*
let evchannels = ref []

let privchannels = ref []

let rewrite_rules = ref []

let evrewrite_rules = ref []

let appendto lref l = lref := List.append !lref l

let addto lref e = appendto lref [e];;

let declare_symbols symbolList =
  appendto fsymbols symbolList

let declare_names nameList =
  appendto private_names nameList

let declare_channels nameList =
  appendto channels nameList

let declare_evchannels nameList =
  appendto channels nameList;
  appendto evchannels nameList

let declare_privchannels nameList =
  appendto privchannels nameList

let declare_vars varList =
  appendto vars varList

let declare_rewrite t1 t2 =
  addto rewrite_rules ((parse_term t1), (parse_term t2))

let declare_evrewrite t1 t2 =
  addto evrewrite_rules ((parse_term t1), (parse_term t2))

type atom_type =  
  | Channel
  | PrivChannel
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
      List.map (fun x -> (x, PrivChannel)) !privchannels;
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
      let x = Var "#X" and y = Var "#Y" in
      let (+) a b = Fun("plus",[a;b]) in
      let zero = Fun("zero",[]) in
      let (==) left right = left,right in
        rewrite_rules := [
          x+zero  == x ;
          x+x     == zero ;
          x+(x+y) == y
        ];  
      declare_symbols ["plus",2;"zero",0];
      declare_vars ["#X";"#Y"];
      check_atoms ()
  | DeclSymbols symbolList ->
    if !verbose_output then Format.printf  "Declaring symbols\n%!";
    declare_symbols symbolList;
    check_atoms ()
  | DeclChannels channelList ->
    if !verbose_output then Format.printf "Declaring channels\n%!";
    declare_channels channelList;
    check_atoms ()
  | DeclEvChannels evchannelList ->
    if !verbose_output then Format.printf "Declaring channels\n%!";
    declare_evchannels evchannelList;
    check_atoms ()
  | DeclPrivChannels privchannelList ->
    if !verbose_output then Format.printf "Declaring private channels\n%!";
    declare_privchannels privchannelList;
    check_atoms ()
  | DeclPrivate nameList ->
    if !verbose_output then Format.printf "Declaring private names\n%!";
    declare_names nameList;
    check_atoms ()
  | DeclVar varList ->
    if !verbose_output then Format.printf "Declaring variables\n%!";
    declare_vars varList;
    check_atoms ()

  | DeclRewrite(t1, t2) ->
    if !verbose_output then Format.printf "Declaring rewrite rule\n%!";
    declare_rewrite t1 t2
  | DeclEvRewrite(t1, t2) ->
    if !verbose_output then Format.printf "Declaring rewrite rule\n%!";
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

let dotfile = !dotfile
let jobs = !jobs
let xor = !xor
let ac = !ac
let set_por b = por:= b
let disable_por = !disable_por
let fsymbols = !fsymbols
let channels = !channels
let private_names = !private_names
let evchannels = !evchannels
let privchannels = !privchannels
let rewrite_rules = !rewrite_rules
let evrewrite_rules = !evrewrite_rules

(** Rewriting toolbox *)

module type REWRITING = sig
  val unifiers : term -> term -> rules -> subst list
  val normalize : term -> rules -> term
  val variants : term -> rules -> (term*subst) list
  val equals : term -> term -> rules -> bool
  val matchers : term -> term -> rules -> subst list
end

module AC : REWRITING = struct
  let normalize t rules =
	try Rewriting.normalize t rules with
	| Rewriting.No_easy_match -> 
		if !about_maude then Format.printf "     Maude normalize %s" (show_term t);
		Maude.normalize t rules 

  let equals s t rules = 
    if rules <> [] 
    then 
       try 
	   let s' =  Rewriting.normalize s rules in
	   let t' =  Rewriting.normalize t rules in
	   Rewriting.equals_ac s' t' 
       with
	  | Rewriting.No_easy_match -> 
		if !about_maude then Format.printf "     Maude equal %s == %s" (show_term s)(show_term t);
		Maude.equals s t rules
    else Rewriting.equals_ac s t 
 
  let unifiers s t r =
    if r = [] then begin 
	try [Rewriting.mgu s t] with
		| Rewriting.Not_unifiable -> [] 
		| Rewriting.No_easy_unifier ->
		  begin
		    if !about_maude then Format.printf "     Maude unif %s =?= %s \n" (show_term s)(show_term t);
		    Maude.unifiers s t []
		  end
	end
	else
      let u1 = Maude.unifiers s t r in
      assert (ac ||
                let u2 = Rewriting.unifiers s t r in
                  List.length u1 = List.length u2) ;
        u1 

  let matchers s t rules = 
  assert (rules = []) ;
    try [Rewriting.mgmac s t] with
    | Rewriting.Not_matchable -> []
    | Rewriting.No_easy_match ->
      begin
	    if !about_maude then Format.printf "     Maude match %s <=? %s \n" (show_term s)(show_term t);
	let m= Maude.acmatchers s t in
        (*debugOutput "Matchers: %s\n" (show_subst_list  m ) ;*)
	m
      end 

  let variants t rules = 
	if not (contains_plus t) then Rewriting.variants t rules 
	else Maude.variants t rules
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

let () = flush stdout; flush stderr
*)

