open Util;;
open Parser;;

exception Parse_error_semantic of string;;

exception Invalid_term;;

exception Not_unifiable;;

exception Not_matchable;;

let vars : (string list) ref = ref [];;

let fsymbols : ((string * int) list) ref = ref [];;

let private_names : (string list) ref = ref [];;

type id = string;;

type varName = id;;

type funName = id;;

type term =
  | Fun of funName * term list
  | Var of varName
;;

type subst =
    (varName * term) list
;;

let is_var term = match term with
  | Var(_) -> true
  | _ -> false
;;

let unbox_var = function
  | Var(x) -> x
  | _ -> invalid_arg "unbox_var"
;;

let rec vars_of_term_list term_list =
  unique (trconcat (trmap vars_of_term term_list))
and vars_of_term = function
  | Fun(_, term_list) -> vars_of_term_list term_list
  | Var(x) -> [x]
;;

(** Signature extension: symbols that may be used in terms
  * in addition to the declared public symbols. *)
type extrasig = {
  vars : string list ;
  names : int list ;
  params : int list
}

let rec sig_of_term_list cur = function
  | [] -> cur
  | Var x :: l ->
      sig_of_term_list { cur with vars = x :: cur.vars } l
  | Fun (s,[]) :: l ->
      begin try
        Scanf.sscanf s "w%d"
          (fun n ->
             let cur = { cur with params = n::cur.params } in
               sig_of_term_list cur l)
      with Scanf.Scan_failure _ ->
        begin try
          Scanf.sscanf s "!n!%d"
            (fun n ->
               let cur = { cur with names = n::cur.names } in
                 sig_of_term_list cur l)
            with Scanf.Scan_failure _ ->
              sig_of_term_list cur l
        end
      end
  | Fun (_,l) :: l' ->
      sig_of_term_list cur (List.rev_append l l')

let sig_of_term_list l =
  let { vars ; names ; params } =
    sig_of_term_list { vars = [] ; names = [] ; params = [] } l
  in
    { vars = Util.unique vars ; names = Util.unique names ;
      params = Util.unique params }

let is_ground t =
  (List.length (vars_of_term t)) = 0
;;

let occurs var term =
  List.mem var (vars_of_term term)
;;

let rec show_term = function
  | Fun("!out!", term_list) ->
      show_term (Fun("out", term_list))
  | Fun("!in!", term_list) ->
      show_term (Fun("in", term_list))
  | Fun("!test!", term_list) ->
      show_term (Fun("test", term_list))
  | Fun("world", term_list) -> "["^(show_term_list term_list)^"]"
  | Fun(f, l) ->
      (f ^
	 (if List.length l != 0 then "(" else "") ^
	 (show_term_list l) ^ 
	 (if List.length l != 0 then ")" else "") )
  | Var(v) -> v
and show_term_list = function
  | [x] -> show_term x
  | x :: l -> ( (show_term x) ^ "," ^ (show_term_list l) )
  | [] -> "";
;;

let rec apply_subst term (sigma : subst) =
  match term with
    | Var(x) ->
	if List.mem_assoc x sigma then
	  List.assoc x sigma
	else
	  term
    | Fun(symbol, list) ->
	Fun(symbol, trmap (function x -> apply_subst x sigma) list)
;;

let bound variable sigma = 
  let (f, _) = List.split sigma in
  List.mem variable f
;;

let apply_subst_term_list tl sigma =
  trmap (fun x -> apply_subst x sigma) tl
;;

let show_subst sigma = 
    "{ " ^ 
      (String.concat ", "
	 (trmap
	    (fun (x, t) -> x ^ " |-> " ^ (show_term t))
	    sigma)) ^
      " }"
;;

let compose (sigma : subst) (tau : subst) =
  trmap (function x -> (x, apply_subst (apply_subst (Var(x)) sigma) tau))
    (List.append (fst (List.split sigma)) (fst (List.split tau)))
;;

let restrict (sigma : subst) (domain : varName list) =
  List.filter (fun (x, _) -> List.mem x domain) sigma
;;

let rec subst_one x small = function
  | Var(y) -> if x = y then small else Var(y)
  | Fun(f, list) ->
      Fun(f, trmap (function y -> subst_one x small y) list)
;;

let subst_one_in_list x small list =
  trmap (function y -> subst_one x small y) list
;;

let subst_one_in_subst x small sigma = 
  trmap (function (v, t) -> (v, (subst_one x small t))) sigma
;;

let rec parse_term (t : tempTerm) =
  match t with
  | TempTermCons(x, l) ->
    if List.mem x !vars then
      if List.length l = 0 then
	Var(x)
      else
	raise (Parse_error_semantic 
		 (Printf.sprintf "variable %s used as function symbol" x))
      else
      if List.mem x !private_names then
	if List.length l = 0 then
	  Fun(x, [])
	else
	  raise (Parse_error_semantic
		   (Printf.sprintf "private name %s used as function symbol" x))
      else
	try
	  let arity = List.assoc x !fsymbols in
	  if List.length l = arity then
	    Fun(x, trmap parse_term l)
	  else
	    raise (Parse_error_semantic
		     (Printf.sprintf "function symbol %s has arity %d but is used here with arity %d" x arity (List.length l)))
	with 
	| Not_found -> 
	  raise (Parse_error_semantic (Printf.sprintf "undeclared function symbol %s" x))
;;

let rec unify_once s t sl tl sigma =
  match (s, t) with
    | (Var(x), Var(y)) when x = y -> unify_list sl tl sigma
    | (Var(x), _) ->
	(if occurs x t then
	   raise Not_unifiable
	 else
	   let update = function list -> subst_one_in_list x t list in
	   unify_list (update sl) (update tl) ((x, t) :: (subst_one_in_subst x t sigma)))
    | (_, Var(y)) ->
	unify_once t s sl tl sigma
    | (Fun(f, sa), Fun(g, ta)) when ((f = g) && (List.length sa = List.length ta)) ->
	unify_list (List.append sa sl) (List.append ta tl) sigma
    | _ -> raise Not_unifiable
and unify_list sl tl sigma = 
  match (sl, tl) with
    | ([], []) -> sigma
    | (s :: sr, t :: tr) -> unify_once s t sr tr sigma
    | _ -> raise Not_unifiable
;;

let rec mgu s t = unify_once s t [] [] [];;

let rec new_or_same x t sigma =
  try
    if (List.assoc x sigma) = t then
      sigma
    else
      raise Not_matchable
  with Not_found -> (x, t) :: sigma
;;

let rec match_once pattern model pl ml sigma =
  match (pattern, model) with
    | (Var(x), t) -> match_list pl ml (new_or_same x t sigma)
    | (Fun(f, pa), Fun(g, ma)) when ((f = g) && (List.length pa = List.length ma)) ->
	match_list (List.append pa pl) (List.append ma ml) sigma
    | (_, _) -> raise Not_matchable
and match_list pl ml sigma =
  match (pl, ml) with
    | ([], []) -> sigma
    | (p :: pr, m :: mr) -> match_once p m pr mr sigma
    | _ -> raise Not_matchable
;;

(* most general matcher *)
let rec mgm p m = match_once p m [] [] [];;

let rec top_rewrite t (l, r) =
  try
    let sigma = mgm l t in
    [apply_subst r sigma]
  with Not_matchable -> []

(* top normlize assumes that all strict subterms are in normal form *)
let rec top_normalize t rules =
  match  trconcat (trmap (fun x -> top_rewrite t x) rules) with
    | [] -> t
    | s :: _ -> normalize s rules
(* call this function to find the normal form of any term *)
and normalize t rules =
  match t with
    | Fun(f, ta) ->
	top_normalize (Fun(f, trmap (fun x -> normalize x rules) ta)) rules
    | Var(x) -> t
;;
