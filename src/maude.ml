(** Interface between Akiss and Maude *)

open Term
open Util
open Types
open Parser_functions


type maude_mode = E | AC | XOR

let memoize_maude_unify :  (string * maude_mode ,statement_role ref *statement_role ref *(statement_role ref * int * (varId * term) list) list) Hashtbl.t=  Hashtbl.create 10

let maude_calls = ref 0
let maude_memoize = ref 0

let show_binder_maude = function 
  Master -> "x"
 | Slave | Rule -> "y"
 | Extra(i) -> "z" ^ (string_of_int i)
 | New -> "_"
 
let get_binders pairlst =
  let exception E in
  let mnull = (ref Types.Master) in
  let snull = (ref Types.Slave) in
  let mbinder = ref mnull in 
  let sbinder = ref snull in 
  let rec get_b_term  = function
  | Fun(f,args) -> List.iter get_b_term args
  | Var(x) -> (
      match !(x.status) with
      | Master -> (mbinder := x.status ; if !sbinder != snull then raise E)
      | Slave -> (sbinder := x.status ; if !mbinder != mnull then raise E) 
      | _ -> () ) in
  try List.iter (fun (s,t) -> get_b_term t;get_b_term s) pairlst;
  (!mbinder,!sbinder)
  with E -> (!mbinder,!sbinder)
  
let temporary_terms = ref []
 
let rec print_maude_term freeze t sigma =
 match t with
 | Fun({id=Regular(f)},args) -> "w" ^ f.name ^(if args = [] then " " else  "(" ^ (print_maude_term_list freeze args sigma) ^ ")")
 | Fun({id=Tuple(n)},args) -> "tuple"^(string_of_int n)^"(" ^ (print_maude_term_list freeze args sigma ) ^ ")"
 | Fun({id=Projection(m,n)},args) -> "proj"^(string_of_int m)^"o"^(string_of_int n)^"(" ^ (print_maude_term_list freeze args sigma) ^ ")"
 | Fun({id=Plus},[l;r]) ->  (print_maude_term freeze l sigma) ^ " + " ^ (print_maude_term freeze r sigma) 
 | Fun({id=Plus},args) ->   "+?" ^ (string_of_int (List.length args)) 
 | Fun({id=Zero},[]) ->   " zero " 
 | Fun({id=Nonce(n)},[]) -> 
    if not (List.mem_assoc n.n !Parser_functions.nonces) 
    then 
      Parser_functions.nonces := (n.n, n) :: !Parser_functions.nonces;   
    Format.sprintf "nonce%d " n.n  
(* | Fun({id=InputVar(l)},[]) -> Format.sprintf "i[%d]" l.p  *)
 | Fun({id=Frame(l)},[]) -> 
    if not (List.mem_assoc l.p !Parser_functions.frames) 
    then 
      Parser_functions.frames := (l.p, l) :: !Parser_functions.frames;   
    Format.sprintf "frame%d " l.p
 | Var(id) -> (
    if freeze then (
      (show_binder_maude !(id.status)) ^ (string_of_int id.n))
    else
      match sigma with 
      | None -> (show_binder_maude !(id.status)) ^ (string_of_int id.n) ^ ":Term "
      | Some sigm -> 
        begin
        match (find_sub id sigm).(id.n) with
        | None -> (show_binder_maude !(id.status)) ^ (string_of_int id.n) ^ ":Term "
        | Some t -> print_maude_term freeze t sigma end )
 | _ -> invalid_arg ("Invalid term for maude")
and print_maude_term_list freeze args sigma = 
  match args with
  | [x] -> print_maude_term freeze x sigma
  | x :: l -> ( (print_maude_term freeze x sigma) ^ "," ^ (print_maude_term_list freeze l sigma) )
  | [] -> ""
  
let print_maude_pairlst with_rules pairlst sigma=
  Parser_functions.nonces := [] ;
  Parser_functions.frames := [] ;
  let terms = List.fold_left (fun str (s,t) -> 
    ( if str = "" then (match with_rules with E | XOR -> "variant " | AC -> "")^"unify in Current : " else  str ^ " /\\ ") 
     ^ (print_maude_term false s (Some sigma)) ^ " =? " ^ (print_maude_term false t (Some sigma))) "" pairlst in
  "mod Current is\nincluding "^(match with_rules with E -> "Theory" | XOR -> "Xor" | AC -> "AKISS")^" .\n" ^
  (List.fold_left (fun str (n,_) -> 
     str ^ "op nonce"^(string_of_int n) ^" : -> Term .\n") "" !Parser_functions.nonces) ^
  (List.fold_left (fun str (n,_) -> 
     str ^ "op frame"^(string_of_int n) ^" : -> Term .\n") "" !Parser_functions.frames) 
  ^ "endm\n\n" ^ terms ^ ".\n"
  
let print_maude_variants term =
  Parser_functions.nonces := [] ;
  Parser_functions.frames := [] ;
  let term = print_maude_term false term None in
  "mod Current is\nincluding Theory .\n" ^
  (List.fold_left (fun str (n,_) -> 
     str ^ "op nonce"^(string_of_int n) ^" : -> Term .\n") "" !Parser_functions.nonces) ^
  (List.fold_left (fun str (n,_) -> 
     str ^ "op frame"^(string_of_int n) ^" : -> Term .\n") "" !Parser_functions.frames) 
  ^ "endm\n\nget variants " ^ term ^ ".\n"
  
let rec times n str =
  if n = 0 then "" else begin str ^ times (n-1) str end
  
let op name arity = Format.sprintf "op %s : %s-> Term .\n" name (times arity "Term ")
  
let print_maude_matchers xor p t =
  Parser_functions.nonces := [] ;
  Parser_functions.frames := [] ;
  let term = "tuple"^(string_of_int (List.length t))^"(" ^ (print_maude_term_list false t None ) ^ ")" in
  let pattern = "tuple"^(string_of_int (List.length p))^"(" ^ (print_maude_term_list false p None ) ^ ")" in 
  "mod Current is\nincluding "^(if xor then "Xor" else "AKISS")^" .\n" ^
  (op ("tuple"^(string_of_int (List.length t))) (List.length t)) ^
  (List.fold_left (fun str (n,_) -> 
     str ^ "op nonce"^(string_of_int n) ^" : -> Term .\n") "" !Parser_functions.nonces) ^
  (List.fold_left (fun str (n,_) -> 
     str ^ "op frame"^(string_of_int n) ^" : -> Term .\n") "" !Parser_functions.frames) 
  ^ "endm\n\nxmatch "^ pattern ^" <=? "^( term )^" .\n"
  
let print_maude_rules () =
  "mod Theory is\nincluding AKISS .\n" ^
  (List.fold_left
    (fun str rule -> str ^ "eq "^(print_maude_term false rule.lhs None )^" = "^(print_maude_term false rule.rhs None)^" [variant] .\n")
    ""
    !Parser_functions.rewrite_rules)
  ^ "endm\n\n"
  
let print_maude_xor () =
  "mod Xor is\nincluding AKISS .\n" ^
  (List.fold_left
    (fun str rule -> str ^ "eq "^(print_maude_term false rule.lhs None )^" = "^(print_maude_term false rule.rhs None)^" [variant] .\n")
    "" [Parser_functions.rewrite_rule_xor_1 ; Parser_functions.rewrite_rule_xor_2 ; Parser_functions.rewrite_rule_xor_3 ]
  )
  ^ "endm\n\n"
  

let print_maude_signature () =
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

let countdown = ref 0 

let rec get_chans =
  let dummy = stdin,stdout in
  let chans = ref dummy in
  let close () =
    if !chans <> dummy then begin
      (* Maude doesn't seem to return 0 on clean termination. *)
      ignore (Unix.close_process !chans) ;
      if !about_maude then Printf.printf "maude :%d mem %d\n%!" !maude_calls !maude_memoize;
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
      let print_query chan = Format.fprintf chan "%s%s%s" (print_maude_signature ()) (print_maude_rules ())(print_maude_xor ()) in
      ignore (run_maude print_query (fun _ -> []));
      pair
    end

      
and run_maude print_query parse_result =
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
let rec repl_binder_term e e' term =
  match term with
  | Fun(f,args) -> Fun(f, List.map (repl_binder_term e e') args)
  | Var(x) -> assert (x.status = e); Var({x with status = e'})

let complete_subst_maker e' (binder,nbv,pairlst) sigma =
  let subst = copy_subst_add_extra sigma nbv binder in
  List.iter (fun (x,t) -> 
    let sigm = find_sub x subst in 
    try
    sigm.(x.n) <- Some (if binder = e' then t else repl_binder_term binder e' t )
    with Invalid_argument a -> Printf.printf "%s index %s %d\n" (show_subst_maker subst)(show_binder !(x.status)) x.n; raise (Invalid_argument a)) pairlst;
  subst


(*  
let replace_binder m s subst_maker = 
  let repl m s e = Array.map (function None -> None | Some t ->  Some (repl_binder_term m s e t)) in 
  let size = List.length subst_maker.e in
  let ebinder = Array.init size (fun i -> ref(Types.Extra i)) in
{
  m = repl m s ebinder subst_maker.m ;
  s = repl m s ebinder subst_maker.s ;
  e = List.mapi (fun i se -> 
    { binder_extra = ebinder.(i);
      nb_extra = se.nb_extra; 
      subst_extra = repl m s ebinder se.subst_extra}) subst_maker.e
}*)

let acunifiers with_rules pairlst sigma =
  (*if !about_maude then (
    List.iter (fun (s,t) -> Format.printf " %s =? %s /\\\n" (show_term s) (show_term t)) pairlst ;
    Printf.printf "sig: %s \n%!" (show_subst_maker sigma));*)
  let query_string = print_maude_pairlst with_rules pairlst sigma in
  let mbinder,sbinder = get_binders pairlst in
  try 
  let oldm,olds,sublst = Hashtbl.find memoize_maude_unify (query_string,with_rules) in
  let oldms = !oldm in
  let oldss = !olds in
  oldm := Master;
  olds := Slave;
  incr maude_memoize;
  (*Printf.printf "- %s\n%!" query_string;
  List.iter (fun (s,t) -> Format.printf "| %s =? %s /\\\n" (show_term s) (show_term t)) oldpl ;*)
  let i = List.length sigma.e in
  let substs = List.map (fun sub -> complete_subst_maker (ref (Extra i)) sub sigma) sublst in
  (*List.map (fun subst -> 
    (*Printf.printf "* %s\n" (show_subst_maker subst);*)
    let subs = replace_binder mbinder sbinder subst in
    (*Printf.printf "> %s\n" (show_subst_maker subs);*)
    subs
  ) mem in*)
  oldm := oldms;
  olds := oldss;
  substs
  with
  | Not_found -> 
  incr maude_calls;
  if !about_maude then 
    Printf.printf "%s\n%!"
      query_string;
    (*Format.fprintf chan "unify in AKISS %a =? %a .\n" print s print t ; *)
    (* Format.fprintf chan "quit \n" *)
  
  let query chan =
    Format.fprintf chan "%s"
     (* (print_maude_signature ())
      (match with_rules with E -> print_maude_rules () | XOR -> print_maude_xor () | AC -> "") *)
      query_string
  in 
  (*query Format.std_formatter*)
  let parse_unifiers ch lexbuf =
    match Parsemaude.main Lexmaude.token lexbuf with
    | `Unify substs ->
      if !about_maude then
          Printf.printf "%d substitutions\n"(List.length substs);
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
  Hashtbl.add memoize_maude_unify (query_string,with_rules) (mbinder,sbinder,result_subst);
  List.map (fun (b,n,sub) -> complete_subst_maker b (b,n,sub) sigma)
  result_subst
      
let acunifiers with_rules pairlst sigma =
  maude_current_sigma := sigma;
  let v = acunifiers with_rules pairlst sigma in
  (* let v = rename_in_subst v in *)
  (*if !about_maude then begin
    List.iter (fun s -> Format.printf "- %s\n%!" (show_subst_maker s)) v
  end ;*)
  v


      
(** variants of a term *)

let variants t =
  if !about_maude then
    Format.printf "<< maude variants: %s \n" (show_term t) ;
  if !about_maude then 
    Printf.printf  "%s%s%s%!" (print_maude_signature ()) (print_maude_rules ())(print_maude_variants t);
  let query chan =
    Format.fprintf chan "%s" (*(print_maude_signature ()) (print_maude_rules ())*)(print_maude_variants t)
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

let matchers xor pairlst sigma =
  let pattern,matching = List.split pairlst in
  let pattern = List.map (fun p -> let t = apply_subst p sigma in (*Printf.printf ":%s>%s," (show_term p)(show_term t);*) t) pattern in
  let matching = List.map (fun p -> let t= apply_subst p sigma in (*Printf.printf ";%s>%s," (show_term p)(show_term t);*) t) matching in
  if !about_maude then 
    Printf.printf  "%s%s%s%!" (print_maude_signature ())(print_maude_xor ())(print_maude_matchers xor pattern matching);
  let query chan =
    Format.fprintf chan "%s" (*(print_maude_signature ())(print_maude_xor ())*)(print_maude_matchers xor pattern matching)
  in
  let parse_matchers ch =
    match Parsemaude.main Lexmaude.token (Lexing.from_channel ch) with
    | `Match substs ->
      if !about_maude then
        List.iter
          (fun s -> Printf.printf "Result> %s\n" (show_subst_lst s))
          substs ;
      List.map (fun subst -> 
      try 
      List.fold_left (fun sigm (x,t) -> new_or_same x t sigm ) sigma subst 
      with Term.Not_matchable -> []) substs
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
  let status = !binder in
  maude_current_binder := binder;
  binder := New; (*Trick to get good binder in terms *)
  let v = matchers false pairlst sigma in
  (* let v = rename_in_subst v in *)
    if !about_maude then begin
      Format.printf "matchers (%d solutions):\n%!"
        (List.length v) ;
      List.iter (fun s -> Format.printf " %s\n" (show_subst_list v)) v
    end ;
    binder := status;
    v

let xormatchers binder pairlst sigma =
  let status = !binder in
  maude_current_binder := binder;
  binder := New; (*Trick to get good binder in terms *)
  let v = matchers true pairlst sigma in
  (* let v = rename_in_subst v in *)
    if !about_maude then begin
      Format.printf "xor matchers (%d solutions):\n%!" 
        (List.length v);
      List.iter (fun s -> Format.printf " %s\n"  (show_subst_list v)) v
    end ;
    binder := status;
    v


let clean_maude () =
  Hashtbl.reset memoize_maude_unify;
  countdown := 0
