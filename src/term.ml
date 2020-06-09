(** auxilary functions for terms *)
open Util
open Types
open Dag

module VarAux =      struct
         type t = varId
         let compare =
           compare 
       end  

module VariableSet = Set.Make(VarAux)
module VarMap = Map.Make(VarAux)


  


exception Not_matchable

let rec var_set_of_term_list vs term_list =
  List.fold_left (fun vset term -> (var_set_of_term vset term)) vs term_list
and var_set_of_term vs = function
  | Fun(_, term_list) -> var_set_of_term_list vs term_list
  | Var(x) -> VariableSet.add x vs



let is_var term = match term with
  | Var(x) -> true
  | _ -> false

let unbox_var = function
  | Var(x) -> x
  | _ -> invalid_arg "unbox_var"

let rec is_sum_term term = 
  match term with
  | Var(x) -> true
  | Fun({id = Plus}, args) -> List.for_all is_sum_term args
  | _ -> false

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


(*let is_ground t = vars_of_term t = []*)

(*let occurs var term =
  List.mem var (vars_of_term term)*)

let rec equals s t =
  match (s,t) with
  | (Fun(f,args),Fun(g,args')) when f.id = g.id -> List.fold_left2 (fun r f g -> r && (equals f g)) true args args' 
  | (x,y) -> x = y

let rec new_or_same x t sigma =
  try
    if equals (List.assoc x sigma) t then
      sigma
    else
      raise Not_matchable
  with Not_found -> (x, t) :: sigma


let rec apply_subst term (sigma : subst_lst) =
  match term with
  | Var(x) ->
    if List.mem_assoc x sigma 
    then
      List.assoc x sigma
    else
      term
  | Fun(symbol, list) ->
      Fun(symbol, trmap (function x -> apply_subst x sigma) list)

(*let bound variable sigma =
  List.mem_assoc variable sigma *)

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

(*
let rec contains_plus t =
	match t with 
	| Var(x) -> false
	| Fun({id = Plus},_) -> true
	| Fun(_,l) -> List.fold_left (fun r a -> r || contains_plus a) false l

*)


(** Rewrite functions use by maude.ml *)
let sigma_maker_init i j = {m=Array.make i None; s=Array.make j None; e=[]}

let copy_subst sigma =
  { m = Array.copy sigma.m ; s = Array.copy sigma.s ; e = List.map (fun e -> {e with subst_extra = Array.copy e.subst_extra}) sigma.e}
  
let copy_subst_add_extra sigma n bind =
  { m = Array.copy sigma.m ; s = Array.copy sigma.s ; e = (List.map (fun e -> {e with subst_extra = Array.copy e.subst_extra}) sigma.e) 
    @ [{binder_extra = bind; nb_extra = n ; subst_extra= Array.make n None}]}
  
  
let find_sub x sigma =
  match !(x.status) with
  | Master -> sigma.m
  | Slave -> sigma.s
  | Extra(n) -> (List.nth (sigma.e) n).subst_extra
  | Rule -> sigma.s
  | _ -> assert false

(** {2 Global function used in maude's parser an lexer} *)  
let maude_current_sigma = ref (sigma_maker_init 0 0)  (**binder to use when creating new variables *)
let maude_current_binder = ref (ref New) (** for matchers only *)
let maude_current_nbv = ref 0 (**number of new variables generated as far *)
