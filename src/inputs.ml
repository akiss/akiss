open Types
open Dag
open Term 

type inputs = { i : term Dag.t ;
}

let show_inputs inputs =
  (Dag.fold (fun l ls str -> (if str = "" then "[" else str ^ " | ") ^ Format.sprintf "%s(%s)_%d: %s" l.chan.name l.name l.p (show_term ls)) inputs.i "" ) ^ "]"

let new_inputs = { i = Dag.empty } 

(* when considering a new input *)
let add_input binder loc var inputs =
  { i = Dag.add loc (Var(var)) inputs.i }(*(Dag.map (fun t -> new_term binder t) inputs)}*)


(*let concretize inputs term = 
*)
(**
  Inputs stuff
**)
let get l input =
  Dag.find l input.i

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
  
