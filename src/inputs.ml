open Types
open Dag
open Term
open Util

exception Incompatible_choices
type inputs = { i : term Dag.t ;
}
type choices = { c : int Dag.t}

let show_inputs inputs =
  if Dag.is_empty inputs.i then "" 
  else if !use_xml then 
  (Dag.fold (fun l ls str -> (if str = "" then "<inputs>" else str ^ " , ") ^ Format.sprintf "<input><loc>%d:</loc><term>%s</term></input>" l.p (show_term ls)) inputs.i "" ) ^ "</inputs>"
  else
  (Dag.fold (fun l ls str -> (if str = "" then "[" else str ^ " | ") ^ Format.sprintf "[%d]_%s: %s" l.p  l.name (show_term ls)) inputs.i "" ) ^ "]"

let show_choices choices =
  if Dag.is_empty choices.c then "" 
  else if !use_xml then 
  (Dag.fold (fun l i str -> (if str = "" then "<choices>" else str ^ " , ") ^ Format.sprintf "<input><loc>%d:</loc><term>%d</term></input>" l.p i) choices.c "" ) ^ "</choices>"
  else
  (Dag.fold (fun l i str -> (if str = "" then "[" else str ^ " | ") ^ Format.sprintf "<%d>: %d" l.p  i) choices.c "" ) ^ "]"

let new_inputs = { i = Dag.empty } 
let new_choices = { c = Dag.empty }

(*hashing...*)
let canonize_inputs inputs = 
 { i = List.fold_left (fun i' (l,t) -> Dag.add l t i') Dag.empty (Dag.bindings inputs.i)}
 
let canonize_choices choices =
 { c = List.fold_left (fun c' (l,i) -> Dag.add l i c') Dag.empty (Dag.bindings choices.c)}
 
(* when considering a new input *)
let add_input loc var inputs =
  { i = Dag.add loc (Var(var)) inputs.i }(*(Dag.map (fun t -> new_term binder t) inputs)}*)
let add_choice loc i choices =
  { c = Dag.add loc i choices.c}

let add_to_frame loc term outputs = 
  { i = Dag.add loc term outputs.i }
(*let concretize inputs term = 
*)
(**
  Choice stuff
**)
let merge_choices c1 c2 =
  try Some
  { c =
  Dag.merge (fun loc i1 i2 -> 
    match (i1,i2) with
    | (Some i1, Some i2) -> if i1 = i2 then Some(i1) else raise Incompatible_choices
    | (Some i , None)  
    | (None , Some i) -> Some(i) 
    | (None,None) -> None) c1.c c2.c 
  }
  with Incompatible_choices -> None

(**
  Inputs stuff
**)
let get l input =
  try Dag.find l input.i with 
  Not_found -> begin Printf.printf "Error: no %d on %s \n%!" (l.p)(show_inputs input); raise Not_found end

let map f input = 
  { i = Dag.map f input.i}

let csu sigma inputs1 inputs2 =
  let to_list = Dag.merge (fun loc i1 i2 -> 
    match (i1,i2) with
    | (Some i1, Some i2) -> Some(i1,i2)
    | _ -> None) inputs1.i inputs2.i in
  try 
  let hard = Dag.fold (fun l pl hard -> Rewriting.unify hard [pl] sigma) to_list [] in
  if hard = [] 
  then [sigma]
  else [] (* Call Maude *)
  with
  | Rewriting.Not_unifiable -> []
  
let csu_recipes sigma recipe1 recipe2 =
  let to_list = Dag.merge (fun loc i1 i2 -> 
    match (i1,i2) with
    | (Some i1, Some i2) -> Some(i1,i2)
    | _ -> None) recipe1.i recipe2.i in
  let hard = Dag.fold (fun _ pl hard -> try Rewriting.unify hard [pl] sigma with Rewriting.Not_unifiable -> hard) to_list [] in
  if hard = [] 
  then [sigma]
  else [] (* Call Maude *)

let csm inputs1 inputs2 = 
  let to_list = Dag.merge (fun loc i1 i2 -> 
    match (i1,i2) with
    | (Some i1, Some i2) -> Some(i1,i2)
    | _ -> None) inputs1.i inputs2.i in
  try 
  let (hard,sigma) = Dag.fold (fun l pl (hard,sigma) -> Rewriting.match_ac hard [pl] sigma) to_list ([],[]) in
  if hard = [] 
  then [sigma]
  else [] (* Call Maude *)
  with
  | Rewriting.Not_matchable -> []

let merge sigma inputs1 inputs2 =
  { i =
  Dag.merge (fun loc i1 i2 -> 
    match (i1,i2) with
    | (Some i1, Some i2) -> Some(Rewriting.apply_subst_term i1 sigma)
    | (Some i , None)  
    | (None , Some i) -> Some(Rewriting.apply_subst_term i sigma) 
    | (None,None) -> None) inputs1.i inputs2.i 
  }
  
let merge_recipes sigma inputs1 inputs2 =
  { i =
  Dag.merge (fun loc i1 i2 -> 
    match (i1,i2) with
    | (Some i1, Some i2) -> 
      if Rewriting.csm i1 i2 <> [] then Some(Rewriting.apply_subst_term i2 sigma) else 
      if Rewriting.csm i2 i1 <> [] then Some(Rewriting.apply_subst_term i1 sigma) else 
      if Term.vars_of_term i1 = [] 
      then Some(Rewriting.apply_subst_term i1 sigma)
      else if Term.vars_of_term i2 = [] 
      then Some(Rewriting.apply_subst_term i2 sigma) else
      failwith (Printf.sprintf "Merge recipe not implemented yet: %s and %s\n%!" (show_term i1)(show_term i2))
    | (Some i , None)  
    | (None , Some i) -> Some(Rewriting.apply_subst_term i sigma) 
    | (None,None) -> None) inputs1.i inputs2.i 
  }  
  
let apply_subst_recipes sigma inputs =
  {i = Dag.map (fun  r -> Rewriting.apply_subst_term r sigma) inputs.i}
 
let are_normal inputs =
  Dag.for_all (fun l t -> let t' = Rewriting.normalize t (!Parser_functions.rewrite_rules) in Rewriting.equals_ac t t') inputs.i

  (* To avoid merging too much tests *)
let contains input1 input2 =
 let r = Dag.merge (fun loc i1 i2 -> 
    match (i1,i2) with
    | (Some i1, Some i2) -> if i1 = i2 then None else Some false
    | (Some i , None)  -> None
    | (None , Some i) -> Some false
    | (None,None) -> None) input1.i input2.i in
  Dag.is_empty r

let debug input1 input2 =
 let r = Dag.merge (fun loc i1 i2 -> 
    match (i1,i2) with
    | (Some i1, Some i2) -> if i1 = i2 then None else Some loc
    | (Some i , None)  -> Some loc
    | (None , Some i) -> Some loc
    | (None,None) -> None) input1.i input2.i in
    try
  let (a,b) = Dag.choose r in a.p  
  with Not_found -> 0
