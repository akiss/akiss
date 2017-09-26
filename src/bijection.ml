open Types
open Dag
open Base

type correspondance = { a : location Dag.t}

let show_correspondance c =
  (Dag.fold (fun lp lq str -> str ^(Format.sprintf " %d => %d ;" lp.p lq.p)) c.a "{|")^"|}"

type partial_run = {
  statement : raw_statement ; (* the solved statement seen as the test to check *)
  corresp : correspondance ; (* a mapping from the actions of P to the actions of Q *)
  remaining_actions : LocationSet.t; 
  frame : Inputs.inputs ; (* the frame for outputs *)
  dag : dag; (* The run dag: may be more constrained than the Initial one *)
  qthreads : (LocationSet.t * Process.process) list ; (* The available action of Q, the constrainsts *)
  mutable children : partial_run list ; (* once processed, the list of possible continuation of the execution *)
}

let show_partial_run pr =
  (List.fold_left (fun str (lset, p) -> str ^ (show_loc_set lset) ^" : "^(Process.show_process p)^"\n   ")
  (Format.sprintf "{ \n statement= %s frame= %s\n corresp= %s\n remaining_actions= %s\n qthreads= \n   "
    (show_raw_statement pr.statement)
    (Inputs.show_inputs pr.frame)
    (show_correspondance pr.corresp)
    (show_loc_set pr.remaining_actions)) 
  pr.qthreads) ^ "}\n"

type test = {
  nb_actions : int;
  test : statement;
}

type partition = {
  run : partial_run;
  dag : dag;
  equalities : Inputs.inputs;
  disequalities : (term * term) list;
}

(* records which are the partial executions of a test *) 
type solutions = {
  mutable partial_runs : partial_run list;
  mutable partial_runs_todo : partial_run list;
  mutable partial_runs_priority_todo : partial_run list;
  mutable possible_runs : partial_run list; (* Run which are not compatible for the current bijection *)
  mutable possible_runs_todo : partial_run list;
  mutable partitions : partition list; (* Current solution under testing *)
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
  locP : location;
  locQ : location;
  partition : partition;
}

type bijection = {
  mutable records : record list;
}

let base = {
  records = [];
}

let loc_p_to_q p corr =
  Dag.find p corr.a
  
let whole_partition partial_run =
  {
    run = partial_run ;
    dag = partial_run.dag ;
    equalities = partial_run.frame ; 
    disequalities = [] ;
  }

let add_partition partition =
   base.records <- Dag.fold (fun lp lq lst -> {locP = lp; locQ = lq; partition = partition;}::lst) 
    partition.run.corresp.a base.records
  
let remove_partition partition =
  base.records <- List.filter (fun r -> r.partition != partition) base.records

let records_for_P locP = 
  List.filter (fun r -> r.locP = locP) base.records
  

let straight locP locQ = 
  not( List.exists (fun r -> r.locP = locP && r.locQ != locQ) base.records) 
  || ( List.exists (fun r -> r.locP = locP && r.locQ = locQ) base.records)

let compatible partition = 
  List.for_all (fun record -> 
    let q = try loc_p_to_q record.locP partition.run.corresp with Not_found -> record.locQ in
    if q = record.locQ then true
    else
      if is_cyclic (merge partition.dag record.partition.dag) then true
      else
        false (* TODO: check inputs compatibility *)
    ) base.records
