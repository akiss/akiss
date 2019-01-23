open Term
open Util
open Types
open Parser_functions

let memoize_maude_unify :  (string * bool, subst_maker list) Hashtbl.t=  Hashtbl.create 10

let show_binder_maude = function 
  Master -> "x"
 | Slave | Rule -> "y"
 | Extra(0) -> "z"
 | New -> "_"
 | _ -> "?"
 
 
let rec print_maude_term t sigma =
 match t with
 | Fun({id=Regular(f)},args) -> "w" ^ f.name ^(if args = [] then " " else  "(" ^ (print_maude_term_list args sigma) ^ ")")
 | Fun({id=Tuple(n)},args) -> "tuple"^(string_of_int n)^"(" ^ (print_maude_term_list args sigma ) ^ ")"
 | Fun({id=Projection(m,n)},args) -> "proj"^(string_of_int m)^"o"^(string_of_int n)^"(" ^ (print_maude_term_list args sigma) ^ ")"
 | Fun({id=Plus},[l;r]) ->  (print_maude_term l sigma) ^ " + " ^ (print_maude_term r sigma) 
 | Fun({id=Plus},args) ->   "+?" ^ (string_of_int (List.length args)) 
 | Fun({id=Zero},[]) ->   " zero " 
 | Fun({id=Nonce(n)},[]) -> 
    if not (List.mem_assoc n.n !Parser_functions.nonces) 
    then 
      Parser_functions.nonces := (n.n, n) :: !Parser_functions.nonces;   
    Format.sprintf "nonce%d " n.n  
 | Fun({id=InputVar(l)},[]) -> Format.sprintf "i[%d]" l.p  
 | Fun({id=Frame(l)},[]) -> Format.sprintf "w[%d]" l.p
 | Var(id) -> (
    match sigma with 
    None -> (show_binder_maude !(id.status)) ^ (string_of_int id.n) ^ ":Term "
    | Some sigm -> 
    begin
    match (find_sub id sigm).(id.n) with
    | None -> (show_binder_maude !(id.status)) ^ (string_of_int id.n) ^ ":Term "
    | Some t -> print_maude_term t sigma end )
 | _ -> invalid_arg ("Todo")
and print_maude_term_list args sigma = 
  match args with
  | [x] -> print_maude_term x sigma
  | x :: l -> ( (print_maude_term x sigma) ^ "," ^ (print_maude_term_list l sigma) )
  | [] -> ""
  
let print_maude_pairlst with_rules pairlst sigma=
  Parser_functions.nonces := [] ;
  let terms = List.fold_left (fun str (s,t) -> 
    ( if str = "" then (if with_rules then "variant " else "")^"unify in Current : " else  str ^ " /\\ ") 
     ^ (print_maude_term s (Some sigma)) ^ " =? " ^ (print_maude_term t (Some sigma))) "" pairlst in
  "mod Current is\nincluding "^(if with_rules then "Theory" else "AKISS")^" .\n" ^
  (List.fold_left (fun str (n,_) -> 
     str ^ "op nonce"^(string_of_int n) ^" : -> Term .\n") "" !Parser_functions.nonces) 
  ^ "endm\n\n" ^ terms ^ ".\n"
  
let print_maude_variants term =
  Parser_functions.nonces := [] ;
  let term = print_maude_term term None in
  "mod Current is\nincluding Theory .\n" ^
  (List.fold_left (fun str (n,_) -> 
     str ^ "op nonce"^(string_of_int n) ^" : -> Term .\n") "" !Parser_functions.nonces) 
  ^ "endm\n\nget variants " ^ term ^ ".\n"
  
let print_maude_matchers p t =
  Parser_functions.nonces := [] ;
  let term = print_maude_term t None in
  let pattern = print_maude_term p None in
  "mod Current is\nincluding AKISS .\n" ^
  (List.fold_left (fun str (n,_) -> 
     str ^ "op nonce"^(string_of_int n) ^" : -> Term .\n") "" !Parser_functions.nonces) 
  ^ "endm\n\nmatch "^ pattern ^" <=? "^( term )^" .\n"
  
let print_maude_rules () =
  "mod Theory is\nincluding AKISS .\n" ^
  (List.fold_left
    (fun str rule -> str ^ "eq "^(print_maude_term rule.lhs None )^" = "^(print_maude_term rule.rhs None)^" [variant] .\n")
    ""
    !Parser_functions.rewrite_rules)
  ^ "endm\n\n"

let input_line chan =
  let line = input_line chan in
    if false then
      Format.printf "input line > %S\n%!" line ;
    line

let rec times n str =
  if n = 0 then "" else begin str ^ times (n-1) str end

let print_maude_signature () =
  let op name arity = Format.sprintf "op %s : %s-> Term .\n" name (times arity "Term ") in
  let print_env_elt _ env str =
    match env with
    | Func (f) -> str ^ (op ("w" ^f.name) f.arity)
    | _ -> str
  in
  let str = ref "" in
  List.iter (fun i -> 
    str := !str ^ op ("tuple" ^ (string_of_int i)) i ; 
    for j = 0 to i - 1 do
      str := !str ^ op ("proj" ^ (string_of_int j) ^ "o" ^ (string_of_int i)) 1 
    done
  ) !Parser_functions.tuple_arity;
  "mod AKISS is\nsorts Term .\n op _ + _ : Term Term -> Term [assoc comm] .\n op zero : -> Term .\n"
  ^ !str
  ^ (Env.fold print_env_elt !environment "")
  ^ "endm\n\n"

(** Interacting with a maude process *)
let find_in_path x =
  let path = Str.split (Str.regexp ":") (Sys.getenv "PATH") in
  List.find
    Sys.file_exists
    (List.map (fun d -> Filename.concat d x) path)

let maude_binary = lazy (
  try
    find_in_path "maude"
  with
    | Not_found ->
        Printf.eprintf "Cound not find maude in PATH!\n" ;
        exit 1
)

let maude_command = lazy (
  let lazy maude_binary = maude_binary in
  maude_binary ^ " -batch -no-banner -no-ansi-color -no-advise"
)

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
      let pair = Unix.open_process (Lazy.force maude_command) in
      chans := pair ;
      countdown := 10000 ;
      pair
    end

      
let run_maude print_query parse_result =
  if false then
    Format.printf "<< maude command: %s\n"  (Lazy.force maude_command);
  let chan_out,chan_in = get_chans () in
      (* let chan_out,chan_in = *)
      (* 	Unix.open_process (Lazy.force Config.maude_command) in *)
  let fin = Format.formatter_of_out_channel chan_in in
  if false then print_query Format.std_formatter ;
  Format.print_flush () ;
  print_query fin ;
  Format.pp_print_flush fin () ;
  let result = parse_result chan_out in
      (* Unix.close_process (chan_out,chan_in); *)
  if false then
    Format.printf ">> ok\n" ;
  result


(** Unification mod AC + R*)



let acunifiers with_rules pairlst sigma =
  if !about_maude then
    List.iter (fun (s,t) -> Format.printf " %s =? %s /\\\n" (show_term s) (show_term t)) pairlst ;
  let query_string = print_maude_pairlst with_rules pairlst sigma in
(*  try 
  List.map (fun subst -> 
    let sigma = Rewriting.identity_subst subst.nbvars in
    Rewriting.compose subst sigma
  )
  (Hashtbl.find memoize_maude_unify (query_string,with_rules))
  with
  | Not_found -> *)
  if !about_maude then 
    Printf.printf "%s%s%s%!"
      (print_maude_signature ())
      (if with_rules then print_maude_rules () else "") 
      query_string;
    (*Format.fprintf chan "unify in AKISS %a =? %a .\n" print s print t ; *)
    (* Format.fprintf chan "quit \n" *)
  
  let query chan =
    Format.fprintf chan "%s%s%s"
      (print_maude_signature ())
      (if with_rules then print_maude_rules () else "") 
      query_string
  in 
  (*query Format.std_formatter*)
  let parse_unifiers ch lexbuf =
    match Parsemaude.main Lexmaude.token lexbuf with
    | `Unify substs ->
      if !about_maude then
        List.iter
          (fun s -> Printf.printf "Result> %s\n" (show_subst_maker s))
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
  let result_subst =
  run_maude
    (fun chan -> query chan)
    (fun chan -> parse_unifiers chan) in
(*  Hashtbl.add memoize_maude_unify (query_string,with_rules) result_subst;*)
  result_subst
      
let acunifiers with_rules pairlst sigma =
  maude_current_sigma := sigma;
  let v = acunifiers with_rules pairlst sigma in
  (* let v = rename_in_subst v in *)
  if !about_maude then begin
    List.iter (fun s -> Format.printf " %s\n" (show_subst_maker s)) v
  end ;
  v


      
(** variants of a term *)

let variants t =
  if !about_maude then
    Format.printf "<< maude variants: %s \n" (show_term t) ;
  if !about_maude then 
    Printf.printf  "%s%s%s%!" (print_maude_signature ()) (print_maude_rules ())(print_maude_variants t);
  let query chan =
    Format.fprintf chan "%s%s%s" (print_maude_signature ()) (print_maude_rules ())(print_maude_variants t)
    (* Format.fprintf chan "%a\n" (print_module rules esig) () ;
    Format.fprintf chan "get variants %a .\n" print t ;*)
    (* Format.fprintf chan "quit \n" *)
  in 
  let parse_variants ch =
    match Parsemaude.main Lexmaude.token (Lexing.from_channel ch) with
    | `Variants v ->
      if !about_maude then
      (
        let (_, sl) = List.split v in
         List.iter
          (fun s -> Printf.printf "Result> %s\n"(show_substitution s))
          sl 
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
      
let variants t  =
  let v = variants t in
  (* let v = rename_in_subst v in *)
  if !about_maude then begin
    Format.printf "variants %s (%d solutions):\n%!"
      (show_term t) (List.length v) ;
    (*      List.iter (fun s -> Format.printf " %s\n" (show_subst s)) v *)
    end ;
  v


(** Matching *)

let rec acmatchers pairlst sigma =
  match pairlst with
  | [] -> [ sigma ]
  | (s,t) :: sigmas -> 
    let s = apply_subst s sigma in
    let t = apply_subst t sigma in
  if !about_maude then 
    Format.printf "<< maude matcher: %s <= %s ; %s\n"(show_term s) (show_term t) (show_subst_lst sigma); 
  if !about_maude then 
    Printf.printf  "%s%s%!" (print_maude_signature ()) (print_maude_matchers s t);
  let query chan =
    Format.fprintf chan "%s%s" (print_maude_signature ()) (print_maude_matchers s t)
  in
  let parse_matchers ch =
    match Parsemaude.main Lexmaude.token (Lexing.from_channel ch) with
    | `Match substs ->
      if !about_maude then
        List.iter
          (fun s -> Printf.printf "Result> %s\n" (show_subst_lst s))
          substs ;
      List.concat (List.map (fun subst -> 
      try 
      let subst = List.fold_left (fun sigm (x,t) -> new_or_same x t sigm ) sigma subst in
      acmatchers sigmas subst
      with Term.Not_matchable -> []) substs)
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

let acmatchers binder pairlst sigma =
  maude_current_binder := binder;
  let v = acmatchers pairlst sigma in
  (* let v = rename_in_subst v in *)
    if !about_maude then begin
      Format.printf "matchers (%d solutions):\n%!"
        (List.length v) ;
      List.iter (fun s -> Format.printf " %s\n" "?") v
    end ;
    v

(** Check equality modulo AC+R *)
(*
let equals s t rules =
  if s = t then true
  else(
    if !about_maude then
      Format.printf "<< maude equals: %s = %s\n" (show_term s) (show_term t) ;
    let esig = sig_of_term_list (s :: t :: terms_of_rules rules) in
    
    let query chan =
      Format.fprintf chan "%a\n" (print_module rules esig) () ;
      Format.fprintf chan "reduce %a == %a .\n" print s print t ;
    in
    let parse_equals ch =
      match Parsemaude.main Lexmaude.token (Lexing.from_channel ch) with
      | `Equal b ->
	if !about_maude then
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
  if !about_maude then
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
      if !about_maude then
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
    if !about_maude then begin
      Format.printf "normalize %s:\n%!"
        (show_term t) ;
    end ;
    nt

*)
