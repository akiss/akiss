open Types
open Dag
open Term 

type inputs = { i : term Dag.t ;
}

let show_inputs inputs =
  if Dag.is_empty inputs.i then "" else
  (Dag.fold (fun l ls str -> (if str = "" then "[" else str ^ " | ") ^ Format.sprintf "[%d]_%s: %s" l.p  l.name (show_term ls)) inputs.i "" ) ^ "]"

let new_inputs = { i = Dag.empty } 

(* when considering a new input *)
let add_input loc var inputs =
  { i = Dag.add loc (Var(var)) inputs.i }(*(Dag.map (fun t -> new_term binder t) inputs)}*)

let add_to_frame loc term outputs = 
  { i = Dag.add loc term outputs.i }
(*let concretize inputs term = 
*)
(**
  Inputs stuff
**)
let get l input =
  try Dag.find l input.i with 
  Not_found -> begin Printf.printf "Error: no %d on %s \n" (l.p)(show_inputs input); raise Not_found end

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
    | (Some i1, Some i2) -> Some(Rewriting.apply_subst_term i1 sigma)
    (*Printf.printf "eeer" ;
      if Term.vars_of_term i1 = [] 
      then Some(Rewriting.apply_subst_term i1 sigma)
      else if Term.vars_of_term i2 = [] 
      then Some(Rewriting.apply_subst_term i2 sigma)
      else failwith "Not implemented yet"*)
    | (Some i , None)  
    | (None , Some i) -> Some(Rewriting.apply_subst_term i sigma) 
    | (None,None) -> None) inputs1.i inputs2.i 
  }  
  
let apply_subst_recipes sigma inputs =
  {i = Dag.map (fun  r -> Rewriting.apply_subst_term r sigma) inputs.i}
 
let are_normal inputs =
  Dag.for_all (fun l t -> let t' = Rewriting.normalize t (!Parser_functions.rewrite_rules) in Rewriting.equals_ac t t') inputs.i