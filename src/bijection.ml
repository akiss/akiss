open Types
open Dag
open Base

type which_process = P | Q

let show_which_process p =
match p with P -> "P" | Q -> "Q"

type correspondance = { a : location Dag.t}

let empty_correspondance = {a = Dag.empty}

let is_empty_correspondance corr = Dag.is_empty corr.a

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
  choices : Inputs.choices ; (* the choices on Q that have been made in this trace *)
  dag : dag; (* The run dag: may be more constrained than the Initial one *)
  disequalities : (term * term) list; (*All the disequalities that have been encountred during the trace *)
  qthreads : (Inputs.choices * LocationSet.t * (term * term) list * Process.process) list ; (* The available action of Q, the constraints *)
  failed_qthreads : (Inputs.choices * LocationSet.t * (term * term) list * Process.process) list ; (* The action that might be availble for a specific substitution *)
  (*mutable children : partial_run list ; (* once processed, the list of possible continuation of the execution *)*)
}

and origin = 
  | Initial of statement 
  | Composed of partial_run * partial_run 
  | Refined of partial_run * statement 
  | Else
  
and test = {
  process_name : which_process; (* Is it a test of P or of Q?*)
  statement : raw_statement ; (* the solved statement seen as the test to check *)
  origin : origin;
  id : int;
  from : IntegerSet.t;
  nb_actions : int; (* used to order the tests *)
  mutable new_actions : int; (* compared to the base actions, used to order the tests *)
  mutable constraints : correspondance; (* Try to pass the test prioritary satisfying the constraints *)
  mutable constraints_back : correspondance; (* Inverse mapping *)
}


let show_run pr =
  (List.fold_left (fun str (t,t') -> str ^ (show_term t)  ^ " != " ^ (show_term t') ^ ", " )
    (Format.sprintf "{ \n frame= %s\n corresp= %s\n dag = %s\n diseq = "
    (Inputs.show_inputs pr.frame)
    (show_correspondance pr.corresp)
    (show_dag pr.dag))
    pr.disequalities) ^"\n"
    
    
let show_partial_run pr =
  (List.fold_left (fun str (choices,lset,diseq, p) -> str ^ "   " ^(show_loc_set lset) ^" : "^(Process.show_process_start 2 p)^"\n")
  ((List.fold_left (fun str (choices,lset,diseq, p) -> str ^ "   " ^ (show_loc_set lset) ^" : "^(Process.show_process_start 2 p)^"\n")
  ((show_run pr) ^ " remaining_actions= " ^ (show_loc_set pr.remaining_actions) ^ "\n qthreads= \n") 
  pr.qthreads) ^ " fthreads=\n") pr.failed_qthreads) ^ "}\n"


  
let rec show_origin o =
  match o with 
  | Initial(st) -> Format.sprintf "%d" (st.id)
  | Composed(run1,run2) -> Format.sprintf "[ %d:%s | %d:%s]"  run1.test.id (show_origin run1.test.origin)  run2.test.id (show_origin run2.test.origin) 
  | Refined(run,st) -> Format.sprintf "{ %d:%s < #%d}"  run.test.id (show_origin run.test.origin)  st.id 
  | Else -> "else"
  
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
  conflicts_loc : LocationSet.t
}

module PossibleRuns =
  struct
    type t = possible_runs
    let compare x y =
      let r = compare x.score y.score in
      if r = 0 then compare x.execution y.execution else r
  end
  
module Solutions = Set.Make(PossibleRuns) 

let show_solution_set sol =
  Solutions.iter (fun prun -> Printf.printf "possible run: %s"  (show_run prun.execution)) sol

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
          | (Refined _, Refined _) -> compare x.id y.id
          | (Refined _, _) -> -1
          | (_, Refined _) ->  1
          | (_,_) -> assert false 
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
  mutable satP : Base.base ;
  mutable satQ : Base.base ;
  mutable indexP : index ;
  mutable indexQ : index ;
  mutable next_id : int;
  mutable tests : solutions Tests.t; (* The remaining tests to test on the other process *)
  mutable registered_tests : solutions Tests.t; (* The tests that are set in *)
  mutable locs : LocationSet.t; (* the locations already in the tests of the base *)
  htable : (int list , origin) Hashtbl.t;
}

let bijection = 
  let nb = Base.new_base () in
{
  (*records = [];*)
  p = Process.EmptyP ; 
  q = Process.EmptyP ;
  satP = nb ;
  satQ = nb ;
  indexP = Dag.empty ;
  indexQ = Dag.empty ;
  next_id = 0 ;
  tests = Tests.empty;
  registered_tests = Tests.empty;
  locs = LocationSet.empty;
  htable = Hashtbl.create 1000 ;
}

let show_bijection () =
  Printf.printf "Bijection of %d tests:\n" (Tests.cardinal bijection.registered_tests);
  Dag.iter (fun kp ind2 -> Printf.printf "\n- %d =>" kp.p;
    Dag.iter (fun kq recordlist ->
      Printf.printf " %d (%d),"  kq.p (RunSet.cardinal recordlist)
      (*RunSet.iter (fun pr -> Printf.printf "         %s   %s\n"  (show_correspondance pr.corresp)(show_origin pr.test.origin)) recordlist *)) ind2 )  bijection.indexP ;
  Printf.printf "\n"

let proc name =
  match name with
  | P -> bijection.p
  | Q -> bijection.q
  
let other name =
  match name with 
  | P -> Q
  | Q -> P
  
let reorder_int_set s =
  IntegerSet.fold (fun e set -> IntegerSet.add e s) s IntegerSet.empty

(* Add a test to test in the queue *)
let push (statement : raw_statement) process_name origin init =
  let int_set = match origin with 
      | Initial _ -> IntegerSet.singleton bijection.next_id 
      | Refined(run,st) -> IntegerSet.singleton bijection.next_id
      | Composed(run1,run2) ->  (IntegerSet.union run1.test.from run2.test.from)
      | Else -> assert false in
  let int_lst = IntegerSet.elements int_set in
  statement.binder := New;
  if Hashtbl.mem bijection.htable int_lst then ()  else begin
  Hashtbl.add bijection.htable int_lst origin;
  bijection.next_id <- bijection.next_id + 1 ;
  let nb = Dag.cardinal statement.dag.rel in
  let test = {
    nb_actions = nb;
    new_actions = 0;
    process_name = process_name;
    statement = statement;
    origin = origin;
    id = bijection.next_id;
    from = int_set;
    constraints = empty_correspondance;
    constraints_back = empty_correspondance;
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
  if !Util.debug_tests then Printf.printf "Adding new test: %s\n" (show_test test);
  (*if bijection.next_id mod 10000 = 0 then (*Hashtbl.iter (fun k v -> Printf.printf "%s" (show_raw_statement k)) bijection.htable;*)show_bijection ();*)
  bijection.tests <- Tests.add test solution bijection.tests 
  end
  
let reorder_tests () = 
  bijection.tests <- Tests.fold (fun test sol map -> 
    test.new_actions <-  
      Dag.fold (fun l _ nb -> 
        if LocationSet.mem l bijection.locs 
        then nb 
        else begin bijection.locs<-LocationSet.add l bijection.locs; nb + 1 end)
      test.statement.dag.rel 0;
    Tests.add test sol map) bijection.tests Tests.empty

(* Pop the queue of the test to check *)
let pop () = 
  let (test, sol) = Tests.min_binding bijection.tests in
  bijection.tests <- Tests.remove test bijection.tests ; 
  (test,sol)

exception LocPtoQ of int

let loc_p_to_q p corr =
  try Dag.find p corr.a
  with Not_found -> raise (LocPtoQ p.p)

(* Register a solution to a test *)
let add_run solution partial_run =
    bijection.registered_tests <- Tests.add partial_run.test solution bijection.registered_tests;
    Dag.iter (fun lp lq -> 
    (*let r = {locP = lp; locQ = lq; partial_run = partial_run;} in*)
    let recintP = try Dag.find lp bijection.indexP with Not_found -> Dag.empty in 
    let reclstP = try Dag.find lq recintP with Not_found -> RunSet.empty in
    bijection.indexP <- Dag.add lp (Dag.add lq (RunSet.add partial_run reclstP) recintP) bijection.indexP;
    let recintQ = try Dag.find lq bijection.indexQ with Not_found -> Dag.empty in 
    let reclstQ = try Dag.find lp recintQ with Not_found -> RunSet.empty in
    bijection.indexQ <- Dag.add lq (Dag.add lp (RunSet.add partial_run reclstQ) recintQ) bijection.indexQ;
    ) 
    (if partial_run.test.process_name = P then partial_run.corresp.a else partial_run.corresp_back.a) 
  
let remove_run partial_run = 
  bijection.registered_tests <- Tests.remove partial_run.test bijection.registered_tests;
  Dag.iter (fun lp lq -> 
    (*let r = {locP = lp; locQ = lq; partial_run = partial_run;} in*)
    let recintP = try Dag.find lp bijection.indexP with Not_found -> Dag.empty in 
    let reclstP = try Dag.find lq recintP with Not_found -> RunSet.empty in
    bijection.indexP <- Dag.add lp (Dag.add lq (RunSet.remove partial_run reclstP) recintP) bijection.indexP;
    let recintQ = try Dag.find lq bijection.indexQ with Not_found -> Dag.empty in 
    let reclstQ = try Dag.find lp recintQ with Not_found -> RunSet.empty in
    bijection.indexQ <- Dag.add lq (Dag.add lp (RunSet.remove partial_run reclstQ) recintQ) bijection.indexQ;
    ) 
    (if partial_run.test.process_name = P then partial_run.corresp.a else partial_run.corresp_back.a) 
  

let straight locP locQ = 
  try
  let p = (Dag.find locP bijection.indexP) in 
  try ignore (Dag.find locQ p); true
  with Not_found -> false
  with Not_found -> 
    try ignore (Dag.find locQ bijection.indexQ); false
    with Not_found -> true

let compatible partial_run = 
  let (corresp,corresp_back) = 
    if partial_run.test.process_name = P 
    then (partial_run.corresp,partial_run.corresp_back)
    else (partial_run.corresp_back,partial_run.corresp)
  in
  let conflicts = ref RunSet.empty in
  let score = ref 0 in
  let conflicts_loc = ref LocationSet.empty in
  (Dag.iter (fun locP locQ -> 
    try
      let p = (Dag.find locP bijection.indexP) in 
      Dag.iter (fun lq runset ->
        if lq <> locQ 
        then begin conflicts := RunSet.union runset !conflicts; score := !score + (RunSet.cardinal runset) ; conflicts_loc :=LocationSet.add locP !conflicts_loc end) p  
    with Not_found -> ()) corresp.a);
   (Dag.iter (fun locP locQ-> 
    try
      let q = (Dag.find locQ bijection.indexQ) in 
      Dag.iter (fun lp runset ->
        if lp <> locP 
        then begin conflicts := RunSet.union runset !conflicts; score := !score + (RunSet.cardinal runset) ; conflicts_loc :=LocationSet.add locQ !conflicts_loc end) q 
    with Not_found -> ()) corresp.a);
    {
      execution = partial_run;
      conflicts = !conflicts;
      score = !score;
      conflicts_loc = ! conflicts_loc
    }
         
