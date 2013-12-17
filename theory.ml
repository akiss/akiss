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

let usage = Printf.sprintf
  "Usage: %s [-verbose] [-debug] < specification-file.api"
  (Filename.basename Sys.argv.(0))

let command_line_options_list = [
  ("-xor", Arg.Set xor,
   "Enable EXPERIMENTAL xor-specific optimizations.") ;
  ("-verbose", Arg.Unit (fun () -> verbose_output := true),
   "Enable verbose output");
  ("-debug", Arg.Unit (fun () -> debug_output := true),
   "Enable debug output")  
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

let process_decl (c : cmd) =
  match c with
  | SetAC -> ac := true
  | SetXOR -> xor := true ; ac := true
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

let xor = !xor
let ac = !ac
let fsymbols = !fsymbols
let channels = !channels
let private_names = !private_names
let evchannels = !evchannels
let rewrite_rules = !rewrite_rules
let evrewrite_rules = !evrewrite_rules
