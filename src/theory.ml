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

let dotfile = ref None
let jobs = ref 1

(** Flags set from the script using #set ac/xor.
  * - [ac] triggers special treatment of "plus" as AC connective.
  * - [xor] triggers normalization of identical statements in the form
  *   id(X,0). *)
let ac = ref false
let xor = ref false

let ac_toolbox = ref false
let tamarin_variants = ref false

(** Experimental POR optimization *)
let por = ref false

(** See in [Horn] for documentation. *)
let check_generalizations = ref false

let usage = Printf.sprintf
  "Usage: %s [options] < specification-file.api"
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
  ("--output-dot", Arg.String (fun s -> dotfile := Some s),
   "<file>  Output statement graph to <file>");
  ("-j", Arg.Int (fun i -> jobs := i),
   "<n>  Use <n> parallel jobs (if supported)");
  ("--ac-compatible", Arg.Set ac_toolbox,
   "Use the AC-compatible toolbox even on non-AC theories (experimental, needs maude and tamarin)");
  ("--tamarin-variants", Arg.Set tamarin_variants,
   "Use tamarin-prover to compute variants in seed statements");
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
  | SetPOR ->
      por := true
  | DeclSymbols symbolList ->
    verboseOutput "Declaring symbols\n%!";
    declare_symbols symbolList;
    check_atoms ()
  | DeclChannels channelList ->
    verboseOutput "Declaring channels\n%!";
    declare_channels channelList;
    check_atoms ()
  | DeclEvChannels evchannelList ->
    verboseOutput "Declaring channels\n%!";
    declare_evchannels evchannelList;
    check_atoms ()
  | DeclPrivChannels privchannelList ->
    verboseOutput "Declaring private channels\n%!";
    declare_privchannels privchannelList;
    check_atoms ()
  | DeclPrivate nameList ->
    verboseOutput "Declaring private names\n%!";
    declare_names nameList;
    check_atoms ()
  | DeclVar varList ->
    verboseOutput "Declaring variables\n%!";
    declare_vars varList;
    check_atoms ()

  | DeclRewrite(t1, t2) ->
    verboseOutput "Declaring rewrite rule\n%!";
    declare_rewrite t1 t2
  | DeclEvRewrite(t1, t2) ->
    verboseOutput "Declaring rewrite rule\n%!";
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
let por = !por
let fsymbols = !fsymbols
let channels = !channels
let private_names = !private_names
let evchannels = !evchannels
let privchannels = !privchannels
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
  let normalize t rules =
	try Rewriting.normalize t rules with
	| Rewriting.No_easy_match -> Maude.normalize t rules 

  let equals s t rules = if rules <> [] 
    then Maude.equals s t rules
    else Rewriting.equals_ac s t 
 
  let unifiers s t r =
    if r = [] then begin 
	try [Rewriting.mgu s t] with
		| Rewriting.Not_unifiable -> [] 
		| Rewriting.No_easy_unifier -> begin
			debugOutput "Maude is called: %s =?= %s \n" (show_term s)(show_term t);
		        Maude.unifiers s t [] end
	end
	else
      (* let u1 = Tamarin.unifiers Fullmaude.normalize s t r in *)
      let u1 = Maude.unifiers s t r in
      assert (ac ||
                let u2 = Rewriting.unifiers s t r in
                  List.length u1 = List.length u2) ;
        u1
  let matchers s t rules =
    assert (rules = []) ;
    try [Rewriting.mgmac s t] with
    | Rewriting.Not_matchable -> []
    (* | Rewriting.No_easy_match -> Fullmaude.matchers s t rules *)
    | Rewriting.No_easy_match ->
      begin
	debugOutput "Maude is called: %s <=? %s \n" (show_term s)(show_term t);
	let m= Maude.acmatchers s t in
	(* let m= Fullmaude.matchers s t rules in *)
        debugOutput "Matchers: %s\n" (show_subst_list  m ) ;
	m
      end 
  (* let variants = Tamarin.variants Fullmaude.normalize *)
  let variants = Maude.variants
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

module NonACTamarin : REWRITING = struct
  let normalize = NonAC.normalize
  let equals = NonAC.equals

  let unifiers s t r =
    if r = [] then
      try [Rewriting.mgu s t] with
      | Rewriting.Not_unifiable -> []
    else
      Tamarin.unifiers Rewriting.normalize s t r

  let matchers = NonAC.matchers
  let variants = Tamarin.variants Rewriting.normalize
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
            end else if !tamarin_variants then begin
              Printf.printf "Using tamarin-prover to compute variants in seed statements\n";
              (module NonACTamarin : REWRITING)
            end else begin
              Printf.printf "Using non-AC toolbox...\n" ;
              (module NonAC : REWRITING)
            end : REWRITING)

let () = flush stdout; flush stderr
