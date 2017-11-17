open Util
open Types
(*
exception Parse_error_semantic of string

exception Invalid_term

let vars : (string list) ref = ref []

let fsymbols : ((string * int) list) ref = ref []

let channels : (string list) ref = ref []

let private_names : (string list) ref = ref []
*)

open Dag

module VarAux =      struct
         type t = varId
         let compare =
           compare 
       end  

module VariableSet = Set.Make(VarAux)
module VarMap = Map.Make(VarAux)

let rec var_set_of_term_list vs term_list =
  List.fold_left (fun vset term -> (var_set_of_term vset term)) vs term_list
and var_set_of_term vs = function
  | Fun(_, term_list) -> var_set_of_term_list vs term_list
  | Var(x) -> VariableSet.add x vs
  
type dag = {
  rel : LocationSet.t Dag.t ;
}


let is_var term = match term with
  | Var(x) -> true
  | _ -> false

let unbox_var = function
  | Var(x) -> x
  | _ -> invalid_arg "unbox_var"



let rec vars_of_term_list term_list =
  unique (List.concat (List.map vars_of_term term_list))
and vars_of_term = function
  | Fun(_, term_list) -> vars_of_term_list term_list
  | Var(x) -> [x]
  
let rec apply_var_set_subst term sigma  =
  match term with
  | Var(x) -> begin try VarMap.find x sigma with Not_found -> term end
  | Fun(symbol, list) ->
    Fun(symbol, trmap (function x -> apply_var_set_subst x sigma) list)



(** Signature extension: symbols that may be used in terms
  * in addition to the declared public symbols. *)
(*
type extrasig = {
  vars : string list ;
  names : int list ;
  params : int list ;
  tuples : int list ;
  hiddenchan : int list ;
}

let rec sig_of_term_list cur = function
  | [] -> cur
  | Var x :: l ->
      sig_of_term_list { cur with vars = x :: cur.vars } l
  | Fun ("!tuple!",l) :: l' ->
      let cur = { cur with tuples = List.length l :: cur.tuples } in
        sig_of_term_list cur (l@l')
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
          begin try
            Scanf.sscanf s "!hidden!Z%d"
              (fun n ->
                 let cur = { cur with hiddenchan = n::cur.hiddenchan } in
                   sig_of_term_list cur l)
              with Scanf.Scan_failure _ ->
                sig_of_term_list cur l
          end
        end
      end
  | Fun (_,l) :: l' ->
      sig_of_term_list cur (List.rev_append l l')

let sig_of_term_list l =
  let { vars=vars ; names=names ; params=params ; tuples=tuples ; hiddenchan=hiddenchan} =
    sig_of_term_list { vars = [] ; names = [] ; params = [] ; tuples = [] ; hiddenchan = [] } l
  in
    { vars = Util.unique vars ; names = Util.unique names ;
      params = Util.unique params ; tuples = Util.unique tuples ;
      hiddenchan = Util.unique hiddenchan}*)

let is_ground t = vars_of_term t = []

let occurs var term =
  List.mem var (vars_of_term term)



let rec apply_subst term (sigma : subst_lst) =
  match term with
    | Var(x) ->
	if List.mem_assoc x sigma then
	  List.assoc x sigma
	else
	  term
    | Fun(symbol, list) ->
	Fun(symbol, trmap (function x -> apply_subst x sigma) list)

let bound variable sigma =
  List.mem_assoc variable sigma

let apply_subst_term_list tl sigma =
  trmap (fun x -> apply_subst x sigma) tl

let show_subst sigma =
    "{ " ^
      (String.concat ", "
	 (trmap
	    (fun ((x, t): varId * term) -> (string_of_int x.n) ^ " |-> " ^ (show_term t))
	    sigma)) ^
      " }"

let rec show_subst_list sl =
  match sl with
  | [x] -> show_subst x
  | x :: l -> ( (show_subst x) ^ "," ^ (show_subst_list l) )
  | [] -> ""

let show_variant (t,s) =
  (show_term t)^": "^(show_subst s)
  
    
let rec show_variant_list vl =
  match vl with
  | [v] -> show_variant v
  | v :: l -> ( (show_variant v) ^ ", " ^ (show_variant_list l) )
  | [] -> ""
    
let compose (sigma : subst_lst) (tau : subst_lst) =
  trmap (function x -> (x, apply_subst (apply_subst (Var(x)) sigma) tau))
    (List.append (fst (List.split sigma)) (fst (List.split tau)))

let restrict (sigma : subst_lst) (domain : varId list) =
  List.filter (fun (x, _) -> List.mem x domain) sigma

(*let rec parse_term (Ast.TempTermCons(x,l)) =
  if List.mem x !vars then
    if l = [] then
      Var x
    else
      raise (Parse_error_semantic
               (Printf.sprintf "variable %s used as function symbol" x))
  else if List.mem x !private_names then
      if l = [] then
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
            raise
              (Parse_error_semantic
                 (Printf.sprintf
                    "function symbol %s has arity %d \
                                but is used here with arity %d"
                    x arity (List.length l)))
      with
        | Not_found ->
            raise
              (Parse_error_semantic
                 (Printf.sprintf "undeclared function symbol %s" x))

let rec contains_plus t =
	match t with 
	| Var(x) -> false
	| Fun({id = Plus},_) -> true
	| Fun(_,l) -> List.fold_left (fun r a -> r || contains_plus a) false l

*)
