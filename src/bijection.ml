open Types
open Dag
open Base

type which_process = P | Q

let show_which_process p =
match p with P -> "P" | Q -> "Q"

type correspondance = { a : location Dag.t}

let show_correspondance c =
  (Dag.fold (fun lp lq str -> str ^(Format.sprintf " %d => %d ;" lp.p lq.p)) c.a "{|")^"|}"




module IntegerSet = Set.Make(struct type t = int let compare = compare end)  

let show_int_set s =
  (IntegerSet.fold (fun e str -> (if str = "" then "((" else (str^",")) ^(string_of_int e)) s "" ) ^"))"

type partial_run = {
  (*process :  which_process ; *)
  test : test; (* The test from which the prun come from *)
  corresp : correspondance ; (* a mapping from the actions of P to the actions of Q *)
  corresp_back : correspondance ; (* the reverse mapping from the actions of Q to the actions of P *)
  remaining_actions : LocationSet.t; 
  frame : Inputs.inputs ; (* the frame for outputs *)
  choices : Inputs.choices ;
  dag : dag; (* The run dag: may be more constrained than the Initial one *)
  qthreads : (Inputs.choices * LocationSet.t * Process.process) list ; (* The available action of Q, the constrainsts *)
  failed_qthreads : (Inputs.choices * LocationSet.t * Process.process) list ; (* The action that might be availble for a specific substitution *)
  (*mutable children : partial_run list ; (* once processed, the list of possible continuation of the execution *)*)
}

and origin = Initial of statement | Composed of test * test
  
and test = {
  process_name : which_process; (* Is it a test of P or of Q?*)
  statement : raw_statement ; (* the solved statement seen as the test to check *)
  origin : origin;
  id : int;
  from : IntegerSet.t;
  nb_actions : int; (* used to order the tests *)
  mutable new_actions : int; (* compared to the base actions, used to order the tests *)
}


let show_run pr =
  Format.sprintf "{ \n frame= %s\n corresp= %s\n dag = %s\n"
    (Inputs.show_inputs pr.frame)
    (show_correspondance pr.corresp)
    (show_dag pr.dag)
    
    
let show_partial_run pr =
  (List.fold_left (fun str (choices,lset, p) -> str ^ "   " ^(show_loc_set lset) ^" : "^(Process.show_process_start 2 p)^"\n")
  ((List.fold_left (fun str (choices,lset, p) -> str ^ "   " ^ (show_loc_set lset) ^" : "^(Process.show_process_start 2 p)^"\n")
  ((show_run pr) ^ " remaining_actions= " ^ (show_loc_set pr.remaining_actions) ^ "\n qthreads= \n") 
  pr.qthreads) ^ " fthreads=\n") pr.failed_qthreads) ^ "}\n"


  
let rec show_origin o =
  match o with 
  |Initial(st) -> Format.sprintf "%d" (st.id)
  |Composed(t1,t2) -> Format.sprintf "[ %d:%s | %d:%s]"  t1.id (show_origin t1.origin)  t2.id (show_origin t2.origin) 
  
and show_test t =
  Format.sprintf "Test[%d]: %s %s {%d,%d} %s\n%s\n" t.id (show_origin t.origin) (show_int_set t.from) t.new_actions t.nb_actions (show_which_process t.process_name) (show_raw_statement t.statement)



 
module PartialRun =
       struct
         type t = partial_run
         let compare x y =
           compare x y
       end


module RunSet = Set.Make(PartialRun)

type possible_runs = {
  execution : partial_run;
  conflicts : RunSet.t ;
  score : int;
}

module PossibleRuns =
  struct
    type t = possible_runs
    let compare x y =
      let r = compare x.score y.score in
      if r = 0 then compare x.execution y.execution else r
  end
  
module Solutions = Set.Make(PossibleRuns) 

(* records which are the partial executions of a test *) 
type solutions = {
  mutable partial_runs : partial_run list;
  mutable partial_runs_todo : partial_run list;
  mutable partial_runs_priority_todo : partial_run list; (* Partial execution compatible with the bijection *)
  mutable possible_runs_todo : partial_run list; (* Queue here before processing *)
  mutable possible_runs : Solutions.t; (* Run which are not compatible for the current bijection, to test if no other option *)
  mutable possible_restricted_runs : partial_run list; 
  mutable failed_partial_run : partial_run list;
  mutable failed_run : partial_run list; (* execution but on of the identity fails *)
  mutable partitions : partial_run list; (* Current solution under testing *)
}


module Test =
  struct
    type t = test
      let compare x y =
           
        match (x.origin , y.origin) with
          | (Initial st1, Initial st2) ->
            let r = compare (x.new_actions, x.nb_actions) (y.new_actions, y.nb_actions) in
            if r = 0 then 
              let r = - (compare st1.id st2.id) in
              if r = 0 then compare x.process_name y.process_name else - r else - r
           | (Initial _, Composed _) -> 1
           | (Composed _ , Initial _) -> -1
           | (Composed(_), Composed(_)) ->
              let r = compare (IntegerSet.cardinal x.from)(IntegerSet.cardinal y.from) in
              if r = 0 then 
              compare x.id y.id 
              else -r
   end

module Tests = Map.Make(Test)




type record = {
  locP : location; (* loc of P whatever is a test of P or Q *)
  locQ : location;
  partial_run : partial_run;
}

  
type index = ((RunSet.t) Dag.t) Dag.t

type bijection = {
  (*mutable records : record list;*)
  mutable p : Process.process ; (* The process P *)
  mutable q : Process.process ;
  mutable indexP : index ;
  mutable indexQ : index ;
  mutable next_id : int;
  mutable tests : solutions Tests.t; (* The remaining tests to test on the other process *)
  mutable locs : LocationSet.t; (* the locations already in the tests of the base *)
  htable : (int list , origin) Hashtbl.t;
}

let base = {
  (*records = [];*)
  p = Process.EmptyP ; 
  q = Process.EmptyP ;
  indexP = Dag.empty ;
  indexQ = Dag.empty ;
  next_id = 0 ;
  tests = Tests.empty;
  locs = LocationSet.empty;
  htable = Hashtbl.create 1000 ;
}

let show_base () =
  Printf.printf "Bijection:\n";
  Dag.iter (fun kp ind2 -> 
    Dag.iter (fun kq recordlist ->
      Printf.printf "%d => %d (%d)\n" kp.p kq.p (RunSet.cardinal recordlist);
      RunSet.iter (fun pr -> Printf.printf "         %s   %s\n"  (show_correspondance pr.corresp)(show_origin pr.test.origin)) recordlist ) ind2 )  base.indexP

let proc name =
  match name with
  | P -> base.p
  | Q -> base.q
  
let other name =
  match name with 
  | P -> Q
  | Q -> P
  
let reorder_int_set s =
  IntegerSet.fold (fun e set -> IntegerSet.add e s) s IntegerSet.empty

let push (statement : raw_statement) process_name origin init =
  let int_set = match origin with 
      Initial _ -> IntegerSet.singleton base.next_id 
      | Composed(t1,t2) ->  (IntegerSet.union t1.from t2.from) in
  let int_lst = IntegerSet.elements int_set in
  statement.binder := New;
  if Hashtbl.mem base.htable int_lst then ()  else begin
  Hashtbl.add base.htable int_lst origin;
  
  base.next_id <- base.next_id + 1 ;

  let nb = Dag.cardinal statement.dag.rel in
  let test = {
    nb_actions = nb;
    new_actions = 0;
    process_name = process_name;
    statement = statement;
    origin = origin;
    id = base.next_id;
    from = int_set;
  } in
  let solution =
  { 
       partial_runs = [init test] ;
       partial_runs_todo = [] ;
       partial_runs_priority_todo = [init test] ;
       possible_restricted_runs = [];
       possible_runs = Solutions.empty;
       possible_runs_todo = [];
       failed_partial_run = [];
       failed_run = [];
       partitions = [] ;
     } in
  Printf.printf "Adding new test: %s\n" (show_test test);
  (*if base.next_id mod 10000 = 0 then (*Hashtbl.iter (fun k v -> Printf.printf "%s" (show_raw_statement k)) base.htable;*)show_base ();*)
  base.tests <- Tests.add test solution base.tests 
  end
  
let reorder_tests () = 
  base.tests <- Tests.fold (fun test sol map -> 
    test.new_actions <-  
      Dag.fold (fun l _ nb -> 
        if LocationSet.mem l base.locs 
        then nb 
        else begin base.locs<-LocationSet.add l base.locs; nb + 1 end)
      test.statement.dag.rel 0;
    Tests.add test sol map) base.tests Tests.empty
  
let pop () = 
  let (test, sol) = Tests.min_binding base.tests in
  base.tests <- Tests.remove test base.tests ; 
  (test,sol)

let loc_p_to_q p corr =
  try Dag.find p corr.a
  with Not_found -> failwith (Printf.sprintf "locptoq %d" p.p)

let add_partial_run partial_run =
    Dag.iter (fun lp lq -> 
    (*let r = {locP = lp; locQ = lq; partial_run = partial_run;} in*)
    let recintP = try Dag.find lp base.indexP with Not_found -> Dag.empty in 
    let reclstP = try Dag.find lq recintP with Not_found -> RunSet.empty in
    base.indexP <- Dag.add lp (Dag.add lq (RunSet.add partial_run reclstP) recintP) base.indexP;
    let recintQ = try Dag.find lq base.indexQ with Not_found -> Dag.empty in 
    let reclstQ = try Dag.find lp recintQ with Not_found -> RunSet.empty in
    base.indexQ <- Dag.add lq (Dag.add lp (RunSet.add partial_run reclstQ) recintQ) base.indexQ;
    ) 
    (if partial_run.test.process_name = P then partial_run.corresp.a else partial_run.corresp_back.a) 
  
let remove_partition partial_run = ()
  (*base.records <- List.filter (fun r -> r.partial_run != partial_run) base.records*)

let straight locP locQ = 
  try
  let p = (Dag.find locP base.indexP) in 
  try ignore (Dag.find locQ p); true
  with Not_found -> false
  with Not_found -> 
    try ignore (Dag.find locQ base.indexQ); false
    with Not_found -> true

let compatible partial_run = 
  let (corresp,corresp_back) = 
    if partial_run.test.process_name = P 
    then (partial_run.corresp,partial_run.corresp_back)
    else (partial_run.corresp_back,partial_run.corresp)
  in
  let conflicts = ref RunSet.empty in
  let score = ref 0 in
  (Dag.iter (fun locP locQ -> 
    try
      let p = (Dag.find locP base.indexP) in 
      Dag.iter (fun lq runset ->
        if lq <> locQ 
        then begin conflicts := RunSet.union runset !conflicts; score := !score + (RunSet.cardinal runset) end) p  
    with Not_found -> ()) corresp.a);
   (Dag.iter (fun locP locQ-> 
    try
      let q = (Dag.find locQ base.indexQ) in 
      Dag.iter (fun lp runset ->
        if lp <> locP 
        then begin conflicts := RunSet.union runset !conflicts; score := !score + (RunSet.cardinal runset) end) q 
    with Not_found -> ()) corresp.a);
    {
      execution = partial_run;
      conflicts = !conflicts;
      score = !score;
    }
         
