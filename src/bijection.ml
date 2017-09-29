open Types
open Dag
open Base

type which_process = P | Q

type correspondance = { a : location Dag.t}

let show_correspondance c =
  (Dag.fold (fun lp lq str -> str ^(Format.sprintf " %d => %d ;" lp.p lq.p)) c.a "{|")^"|}"

type partial_run = {
  process :  which_process ;
  statement : raw_statement ; (* the solved statement seen as the test to check *)
  corresp : correspondance ; (* a mapping from the actions of P to the actions of Q *)
  corresp_back : correspondance ; (* the reverse mapping from the actions of Q to the actions of P *)
  remaining_actions : LocationSet.t; 
  frame : Inputs.inputs ; (* the frame for outputs *)
  dag : dag; (* The run dag: may be more constrained than the Initial one *)
  qthreads : (LocationSet.t * Process.process) list ; (* The available action of Q, the constrainsts *)
  mutable children : partial_run list ; (* once processed, the list of possible continuation of the execution *)
}

let show_run pr =
  Format.sprintf "{ \n statement= %s frame= %s\n corresp= %s\n"
    (show_raw_statement pr.statement)
    (Inputs.show_inputs pr.frame)
    (show_correspondance pr.corresp)
    
    
let show_partial_run pr =
  (List.fold_left (fun str (lset, p) -> str ^ (show_loc_set lset) ^" : "^(Process.show_process_start 2 p)^"\n   ")
  ((show_run pr) ^ " remaining_actions= " ^ (show_loc_set pr.remaining_actions) ^ "\nqthreads= \n   ") 
  pr.qthreads) ^ "}\n"

type test = {
  nb_actions : int;
  test : statement;
}


(* records which are the partial executions of a test *) 
type solutions = {
  mutable partial_runs : partial_run list;
  mutable partial_runs_todo : partial_run list;
  mutable partial_runs_priority_todo : partial_run list;
  mutable possible_runs : partial_run list; (* Run which are not compatible for the current bijection *)
  mutable possible_runs_todo : partial_run list;
  mutable partitions : partial_run list; (* Current solution under testing *)
}


module Test =
       struct
         type t = test
         let compare x y =
           let r = compare x.nb_actions y.nb_actions in
           if r = 0 then - (compare x.test.id y.test.id) else - r
       end

module Tests = Map.Make(Test)


type tests = {
  tests : solutions Tests.t ;
}



type record = {
  locP : location; (* loc of P whatever is a test of P or Q *)
  locQ : location;
  partial_run : partial_run;
}

type bijection = {
  mutable records : record list;
}

let base = {
  records = [];
}

let show_base () =
  Printf.printf "Bijection:\n";
  List.iter (fun r -> Printf.printf "%d => %d (%s)\n" r.locP.p r.locQ.p (show_run r.partial_run)) base.records

let loc_p_to_q p corr =
  Dag.find p corr.a

let add_partial_run partial_run =
   base.records <- Dag.fold (fun lp lq lst -> {locP = lp; locQ = lq; partial_run = partial_run;}::lst) 
    (if partial_run.process = P then partial_run.corresp.a else partial_run.corresp_back.a) base.records
  
let remove_partition partial_run =
  base.records <- List.filter (fun r -> r.partial_run != partial_run) base.records

let records_for_P locP = 
  List.filter (fun r -> r.locP = locP) base.records
  

let straight locP locQ = 
  not( List.exists (fun r -> r.locP = locP && r.locQ != locQ) base.records) 
  || ( List.exists (fun r -> r.locP = locP && r.locQ = locQ) base.records)

let compatible partial_run = 
  let (corresp,corresp_back) = 
    if partial_run.process = P 
    then (partial_run.corresp,partial_run.corresp_back)
    else (partial_run.corresp_back,partial_run.corresp)
  in
  List.fold_left (fun lst record -> 
    let p = try loc_p_to_q record.locQ corresp_back with Not_found -> record.locP in
    let q = try loc_p_to_q record.locP corresp with Not_found -> record.locQ in
    if not (p = record.locP && q = record.locQ) 
    then
      record.partial_run :: lst
    else
      lst
    ) [] base.records
