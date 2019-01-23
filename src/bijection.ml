open Types
open Dag
open Base
open Util

let recipes_of_head head = 
  match head with
  | Tests({equalities=equal; disequalities=diseq}) -> equal , diseq
  | Identical(r,r') -> EqualitiesSet.singleton (r,r'),EqualitiesSet.empty
  | Knows(_)
  | Reach -> EqualitiesSet.empty,EqualitiesSet.empty
  | Unreachable | ReachTest(_) -> assert false
  
let head_predicate_to_test binder pred =
  match pred with
  | Identical(s,t) -> Tests({
    head_binder = binder;
    equalities = EqualitiesSet.singleton (s,t); 
    disequalities = EqualitiesSet.empty})
  | Reach -> Tests({
    head_binder = binder ;
    equalities = EqualitiesSet.empty ; 
    disequalities = EqualitiesSet.empty})
  | _ -> assert false


type which_process = P | Q

let show_which_process p =
match p with P -> "P" | Q -> "Q"

type correspondance = { a : location Dag.t}

let empty_correspondance = {a = Dag.empty}

let is_empty_correspondance corr = Dag.is_empty corr.a

let show_correspondance c =
  if !use_xml then
  (Dag.fold (fun lp lq str -> str ^(Format.sprintf  "<src>%d</src> =&gt; <dst>%d</dst> ;"  lp.p lq.p)) c.a "<corresp>")^"</corresp>"
  else
  (Dag.fold (fun lp lq str -> str ^(Format.sprintf " %d => %d ;" lp.p lq.p)) c.a "{|")^"|}"

(*let canonize_correspondance corr =
  { a = List.fold_left (fun c' (l,l') -> Dag.add l l' c') Dag.empty (Dag.bindings corr.a)}
*)

module IntegerSet = Set.Make(struct type t = int let compare = compare end)  
module IntegerMap = Map.Make(struct type t = int let compare = compare end)  

let show_int_set s =
  (IntegerSet.fold (fun e str -> (if str = "" then "((" else (str^",")) ^(string_of_int e)) s "" ) ^"))"

(* For execution of processes *)  
type extra_thread = {
  before_locs : LocationSet.t; (* the set of indexes that shoul have been reduced to unlock this thread *)
  made_choices : Inputs.choices; (* the choices that are made if this thread is selected *)
  (*disequalities : (term * term) list;*)
  thread : Process.process; (* the thread itself *)
  }
  
let show_extra_thread th =
  Printf.sprintf "%s <| %s ==> %s " (show_loc_set th.before_locs) (Inputs.show_choices th.made_choices) (Process.show_process_start 2 th.thread)
  
let show_extra_thread_list lst =
  List.fold_left (fun str e -> (if str = "" then "  " else str ^ "\n  " ) ^ (show_extra_thread e)) "" lst
  
module rec Run : sig 
  type completion = {
    id_c : int; (* primary key *)
    st_c : raw_statement ; (* the current completion g u U_i f_i *)
    corresp_c : correspondance ; (* the correspondance of the union of f_i *)
    corresp_back_c : correspondance ; (* the inverse mapping *)
    missing_actions :  LocationSet.t; (* all the locations which are present on the initial statement but not on the runs *)
    selected_action : location; (*Among all missing locations the one to complete first *)
    root : complement_root; (* data about the test that origin this completion *)
    mutable further_completions : completion list;
    mutable generated_test : Test.test option;
  }
  and complement_root = {
    from_base : which_process; (* the saturated base from which the completion come from *)
    from_statement : statement; (* the unreach or identity test from which the completion is issued*)
    initial_statement : raw_statement ; (* from_statement.st *) 
    hash_initial_statement : hash_test ; (* the hash of the initial_statement *) 
    mutable directory : (((hash_completion * completion) list) ref) Dag.t ; (* For each selected missing action, the list of completions so far, to avoid duplicates *)
  } 
  and hash_completion = {
    is_opti : bool;
    hash_st_c : hash_test ; 
    hash_corresp_c : (location * location) list ;
  }
  and  partial_run = {
  test : Test.test; (* The test from which the prun come from *)
  sol : solution;
  corresp : correspondance ; (* a mapping from the actions of P to the actions of Q *)
  corresp_back : correspondance ; (* the reverse mapping from the actions of Q to the actions of P *)
  remaining_actions : LocationSet.t; 
  frame : Inputs.inputs ; (* the frame for outputs *)
  choices : Inputs.choices ; (* the choices on Q that have been made in this trace *)
  phase : int; 
  (*disequalities : (term * term) list;*) (*All the disequalities that have been encountred during the trace *)
  qthreads : extra_thread list ; (* The available action of Q, the constraints *)
  failed_qthreads : extra_thread list ; (* The action that might be availble for a specific substitution, used for debugging *)
  pending_qthreads : ((location * term option * extra_thread) list) Base.ChanMap.t ; (* The threads which is locked by a hidden chan *)
  (*mutable children : partial_run list ; (* once processed, the list of possible continuation of the execution *)*)
  restrictions : LocationSet.t;
  (*performed_restrictions : LocationSet.t;*)
  parent : partial_run option;
  (* for scoring *)
  last_exe : location ; (* the action whose run lead to this pr *)
  weird_assoc : int ; (* when the parent of an action is not associated to the parent of the associated action *)
  score : int ;
  (* for complete runs *)
  mutable consequences : (statement_role * substitution * Test.test) list; (* the merged tests from this run, empty if this run is not part of the solution  *)
  mutable completions :  completion list; (* the completion from this run, empty if this run is not part of the solution  *)
}
and origin = 
  | Initial of statement 
  | Composed of partial_run * partial_run 
  | Completion 
  | Temporary
  

(* records which are the partial executions of a test *) 
and solution = {
  init_run : partial_run;
  mutable partial_runs : partial_run list;
  mutable partial_runs_todo : Solutions.t; (*partial_run list;*)
  mutable possible_runs_todo : Solutions.t; (* Queue here before processing *)
  mutable possible_runs : Solutions.t; (* Run which are not compatible for the current bijection, to test if no other option *)
  mutable movable : int; (*Number of Test.tests which are merged require to consider changing the partition *) 
  mutable restricted_dag : dag;
  mutable selected_run : partial_run option;
  sol_test : Test.test;
}
type t = partial_run
val compare : t -> t -> int 
end
= 
struct
  type completion = {
    id_c : int;
    st_c : raw_statement ; (* the current completion g u U_i f_i *)
    corresp_c : correspondance ; (* the correspondance of the union of f_i *)
    corresp_back_c : correspondance ;
    (*core_corresp : (location * location) list ;*)
    missing_actions :  LocationSet.t; (* all the locations which are present on the initial statement but not on the runs *)
    selected_action : location; (*Among all missing locations the one to complete first *)
    root : complement_root;
    mutable further_completions : completion list;
    mutable generated_test : Test.test option;
  }
  and complement_root = {
    from_base : which_process; (* the saturated base from which the completion come from *)
    from_statement : statement; (* for debugging to have its id*)
    initial_statement : raw_statement ; (* the unreach or identity from which the completion is issued: g *) 
    hash_initial_statement : hash_test ;
    mutable directory : (((hash_completion * completion) list) ref) Dag.t ; (* For each selected missing action, the list of completions so far, to avoid duplicates and not optimal completions *)
  }  
  and hash_completion = {
    is_opti : bool ;
    hash_st_c : hash_test ; 
    hash_corresp_c : (location * location) list ;
  }
  and partial_run = {
  test : Test.test; (* The test from which the prun come from *)
  sol : solution;
  corresp : correspondance ; (* a mapping from the actions of P to the actions of Q *)
  corresp_back : correspondance ; (* the reverse mapping from the actions of Q to the actions of P *)
  remaining_actions : LocationSet.t; 
  frame : Inputs.inputs ; (* the frame for outputs *)
  choices : Inputs.choices ; (* the choices on Q that have been made in this trace *)
  phase : int ; (* the current phase *)
  qthreads : extra_thread list ; (* The available action of Q, the constraints *)
  failed_qthreads : extra_thread list ; (* The action that might be availble for a specific substitution, used for debugging *)
  pending_qthreads : ((location * term option * extra_thread) list) Base.ChanMap.t ; (* The threads which is locked by a hidden chan *)
  (*mutable children : partial_run list ; (* once processed, the list of possible continuation of the execution *)*)
  restrictions : LocationSet.t;
  parent : partial_run option;
  (* for scoring *)
  last_exe : location ; (* the action whose run lead to this pr *)
  weird_assoc : int ; (* when the parent of an action is not associated to the parent of the associated action *)
  score : int ;
  (* for selected runs only: the list of merged tests from this run (consequences) and completions from this run (completions) *)
  mutable consequences : (statement_role * substitution * Test.test) list;
  mutable completions : completion list;
}
  

and origin = 
  | Initial of statement 
  | Composed of partial_run * partial_run 
  | Completion 
  | Temporary

(* records which are the partial executions of a test *) 
and solution = {
  init_run : partial_run;
  mutable partial_runs : partial_run list;
  mutable partial_runs_todo : Solutions.t; (*partial_run list;*)
  mutable possible_runs_todo : Solutions.t; (* Queue here before processing *)
  mutable possible_runs : Solutions.t; (* Run which are not compatible for the current bijection, to test if no other option *)
  mutable movable : int; (*Number of tests which are merged require to consider changing the partition *) 
  mutable restricted_dag : dag;
  mutable selected_run : partial_run option;
  sol_test : Test.test;
}
type t = partial_run
let compare (x : t) (y : t)= 
      compare (LocationSet.cardinal x.restrictions,x.weird_assoc,-x.score,x)
              (LocationSet.cardinal y.restrictions,y.weird_assoc,-y.score,y)


end
and Test : sig 
type test = {
  process_name : which_process; (* Is it a test of P or of Q?*)
  reflexive : bool ; (* the target process is process_name *)
  statement : raw_statement ; (* the solved statement seen as the test to check *)
  origin : Run.origin;
  id : int;
  from : IntegerSet.t;
  nb_actions : int; (* used to order the tests *)
  mutable new_actions : int; (* compared to the base actions, used to order the tests in the database *)
  mutable constraints : correspondance; (* Try to pass the test with these constraints *)
  mutable constraints_back : correspondance; (* Inverse mapping *)
  mutable solutions_todo : Run.solution list;
  mutable solutions_done : Run.solution list;
}
type t = test
val compare : t -> t -> int
end
= struct
type test = {
  process_name : which_process; (* Is it a test of P or of Q?*)
  reflexive : bool ; (* the target process is process_name *)
  statement : raw_statement ; (* the solved statement seen as the test to check *)
  origin : Run.origin;
  id : int;
  from : IntegerSet.t;
  nb_actions : int; (* used to order the tests *)
  mutable new_actions : int; (* compared to the base actions, used to order the tests *)
  mutable constraints : correspondance; (* Try to pass the test prioritary satisfying the constraints *)
  mutable constraints_back : correspondance; (* Inverse mapping *)
  mutable solutions_todo : Run.solution list;
  mutable solutions_done : Run.solution list;
}
type t = test
let compare (x : Test.test) (y : Test.test)=
           
        match (x.origin , y.origin) with
          | (Initial st1, Initial st2) ->
            let r = compare (x.new_actions, x.nb_actions) (y.new_actions, y.nb_actions) in
            if r = 0 then begin
              match x.statement.head,y.statement.head with
              | Identical(_) ,Reach -> -1
              | Reach,Identical(_) -> 1
              | _ -> 
              let r = - (compare st1.id st2.id) in
              if r = 0 then compare x.process_name y.process_name else - r end else - r
           | (Initial _, Composed _) -> 1
           | (Composed _ , Initial _) -> -1
           | (Composed(_), Composed(_)) ->
              let r = compare (IntegerSet.cardinal x.from)(IntegerSet.cardinal y.from) in
              if r = 0 then 
              compare x.id y.id 
              else -r
          | (Completion , Completion ) -> compare x.id y.id
          | (Completion , _) -> -1
          | (_, Completion ) ->  1
          | (Temporary,_) 
          | (_,Temporary) -> assert false
end
and Solutions : Set.S with type elt = Run.t 
  = Set.Make(Run) 
and Tests : Set.S with type elt = Test.t
  = Set.Make(Test)

module PartialRun =
       struct
         type t = Run.partial_run
         let compare (x : Run.partial_run) (y : Run.partial_run) =
            let z = compare x.test.id y.test.id in
            if z = 0 then
              compare x y
            else z
       end

module RunSet = Set.Make(PartialRun)
  
open Run 
open Test

let show_ext_extra_thread_lst lst =
  List.fold_left (fun str (loc,t,extra_thread) -> 
    (if str = "" then "    " else str ^ "\n    ") 
    ^ (string_of_int loc.p) ^ "::" ^ (show_extra_thread extra_thread)) "" lst
    
let show_pending_threads pthr =
  ChanMap.fold (fun chkey lst str -> 
    (if str = "" then "\n  " else str ^ "\n  ")
    ^ (show_chan_key chkey) ^" : \n" ^(show_ext_extra_thread_lst lst)) pthr ""
    
let show_run pr  =
  if !use_xml 
  then 
    show_correspondance pr.corresp
  else
  (*(List.fold_left (fun str (t,t') -> str ^ (show_term t)  ^ " != " ^ (show_term t') ^ ", " )*)
    (Format.sprintf "{ %s: \n corresp= %s\n choices= %s\n"
    (show_which_process pr.test.process_name)
    (show_correspondance pr.corresp)
    (Inputs.show_choices pr.choices))
   (* pr.disequalities) ^"\n" *)
        
let show_partial_run pr =
    Format.sprintf 
    "%s frame= %s\n remaining_actions=%s\n action=%d; weird = %d ; score = %d ; restricted = %s;\n qthreads=\n%s\n pending_qthreads=%s\n fthreads=%s\n}\n"
    (show_run pr)
    (Inputs.show_inputs pr.frame)
    (show_loc_set pr.remaining_actions)
    pr.last_exe.p pr.weird_assoc pr.score (show_loc_set pr.restrictions)
    (show_extra_thread_list pr.qthreads)
    (show_pending_threads pr.pending_qthreads)
    (show_extra_thread_list pr.failed_qthreads)

  
(*let show_executions sol =*)

  
let rec show_origin o =
  if !use_xml then 
  match o with 
  | Initial(st) -> Format.sprintf "<initial>%d</initial>" (st.id)
  | Composed(run1,run2) -> Format.sprintf "<composed><idtest>%d</idtest>:%s | <idtest>%d</idtest>:%s</composed>"  run1.test.id (show_origin run1.test.origin)  run2.test.id (show_origin run2.test.origin) 
  | Completion -> "comp"
  | Temporary -> "T"
  else    
  match o with 
  | Initial(st) -> Format.sprintf "#%d" (st.id)
  | Composed(run1,run2) -> Format.sprintf "[ %d | %d ]"  run1.test.id  run2.test.id  
  | Completion -> "comp"
  | Temporary -> "T"
  
and show_test (t : test) =
  Format.sprintf 
  (if !use_xml then "<test>{<idtest>%d</idtest>}<origin>%s</origin><infos>%s %d,%d</infos><prname>%s</prname>%s</test>"
  else "Test[%d]: %s %s {%d,%d} %s\n%s\n") t.id (show_origin t.origin) (show_int_set t.from) t.new_actions t.nb_actions (show_which_process t.process_name) (show_raw_statement t.statement)

  
let show_completion completion = 
  Format.sprintf (
    if !use_xml then 
      "<completion>§<idcomp>%d</idcomp><wp>%s</wp>%s\n%s\n<miss>%s</miss>\n<loc>%d</loc></completion>"
    else
      "completion %d[%s] from statement\n %s -corresp: %s \n -missing: %s (%d)\n" )
    completion.id_c
    (show_which_process completion.root.from_base)
    (show_raw_statement completion.st_c) 
    (show_correspondance completion.corresp_c) 
    (show_loc_set completion.missing_actions)
    (completion.selected_action.p)
 
let show_all_completions daglst = 
   Dag.iter (fun loc listcomp -> 
    Printf.printf "loc %d\n" (loc.p);
    List.iter ( fun c -> Printf.printf "%s\n" (show_completion c)) listcomp) ( daglst)  

let show_solution_set sol =
  Solutions.iter (fun prun -> Printf.printf "possible run: %s"  (show_run prun)) sol


let completion_to_hash_completion completion =
  let hash_test = raw_to_hash_test completion.st_c in
  { 
    is_opti = (hash_test = completion.root.hash_initial_statement);
    hash_st_c = hash_test;
    hash_corresp_c = Dag.bindings completion.corresp_c.a;
  }



exception Attack of test * solution


let null_test = {
  process_name = P ;
  reflexive = false;
  statement = null_raw_statement;
  origin = Temporary;
  id = -100;
  from = IntegerSet.empty;
  nb_actions = 0;
  new_actions= 0;
  constraints = empty_correspondance;
  constraints_back= empty_correspondance;
  solutions_todo = [];
  solutions_done = [];
}

let rec null_sol = {
  init_run = empty_run;
  partial_runs = [];
  partial_runs_todo = Solutions.empty;
  possible_runs_todo = Solutions.empty;
  possible_runs = Solutions.empty;
  movable = 0; (*Number of tests which are merged require to consider changing the partition *) 
  restricted_dag = empty;
  selected_run = None;
  sol_test = null_test;
}

and empty_run =
   {
     test = null_test ;
     sol = null_sol ;
     corresp = empty_correspondance ;
     corresp_back = empty_correspondance ;
     remaining_actions = LocationSet.empty ;
     frame = Inputs.new_inputs; (* inputs maps to received terms and outputs maps to sent terms *)
     choices = Inputs.new_choices;
     phase = 0 ;
    (* disequalities = [] ;*)
     qthreads = [] ;
     failed_qthreads = [];
     pending_qthreads = Base.ChanMap.empty ;
     restrictions = LocationSet.empty;
     (*performed_restrictions = LocationSet.empty;*)
     parent = None;
     last_exe = null_location ;
     weird_assoc = 0;
     score = 0 ;
     consequences = [];
     completions = [];
   } 











type record = {
  locP : location; (* loc of P whatever is a test of P or Q *)
  locQ : location;
  partial_run : partial_run;
}

  
type index = ((RunSet.t) Dag.t) Dag.t

type choices_index = ((RunSet.t) IntegerMap.t) Dag.t

type bijection = {
  mutable p : Process.process ; (* The process P *)
  mutable q : Process.process ;
  mutable satP : Base.base ;
  mutable satQ : Base.base ;
  mutable indexP : index ;
  mutable indexQ : index ;
  mutable choices_indexP : choices_index;
  mutable choices_indexQ : choices_index ;
  mutable next_comp_id : int;
  mutable next_id : int; (* the index for tests id *)
  mutable tests : Tests.t; (* The remaining tests to test on the other process *)
  (*mutable registered_tests : Tests.t; (* The tests that are set in *)*)
  mutable runs_for_completions_P : partial_run list; (* the pending runs of P, for completion treatement in Q *)
  mutable runs_for_completions_Q : partial_run list; (* of Q *)
  mutable partial_completions_P : (completion list) Dag.t; (* The partial completions from base P *)
  mutable partial_completions_Q : (completion list) Dag.t; (* The partial completions *)
  mutable todo_completion_P : completion list; (* new partial completion from base P which should be tested on all runs *)
  mutable todo_completion_Q : completion list; (* new partial completion which should be tested on all runs *)
  mutable locs : LocationSet.t; (* the locations already in the tests of the base, for optimization only *)
  (*htable : (int list , origin) Hashtbl.t;*)
  htable_st : (hash_test, test) Hashtbl.t;
  (*Only to print infos *)
  mutable initial_tests : test list;
  mutable initial_completions : completion list;
  mutable attacks : (test * solution) list;
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
  choices_indexP = Dag.empty ;
  choices_indexQ = Dag.empty ;
  next_comp_id = 0 ;
  next_id = 0 ;
  tests = Tests.empty;
  (*registered_tests = Tests.empty;*)
  runs_for_completions_P = [];
  runs_for_completions_Q = [];
  partial_completions_P = Dag.empty;
  partial_completions_Q = Dag.empty;
  todo_completion_P = [];
  todo_completion_Q = [];
  locs = LocationSet.empty;
  (*htable = Hashtbl.create 5000 ;*)
  htable_st = Hashtbl.create 5000 ;
  initial_tests = [];
  initial_completions = [];
  attacks = [];
}

let show_bijection () =
  Printf.printf "Bijection of %d tests:\n" (Hashtbl.length bijection.htable_st);
  Dag.iter (fun kp ind2 -> Printf.printf "\n- %d =>" kp.p;
    Dag.iter (fun kq recordlist ->
      let nb = RunSet.cardinal recordlist in
      Printf.printf " %d (%d%s),"  kq.p nb
      (if nb < 6 then RunSet.fold (fun pr str -> str ^ " [" ^ (string_of_int  pr.test.id) ^ "]") recordlist ":" else "")) ind2 )  bijection.indexP ;
  Printf.printf "\n"
  
open Run 

let show_hashtbl () =
  Hashtbl.iter (fun h s -> Printf.printf "-- %s  \n\n" (show_test s)) bijection.htable_st

let hash_view : (test, unit) Hashtbl.t = Hashtbl.create 2000
let hash_comp_view : (completion,unit) Hashtbl.t = Hashtbl.create 5000

let rec show_all_tests test =
  if Hashtbl.mem hash_view test then Printf.printf (if !use_xml then ".<idtest>%d</idtest>.\n" else "--> [%d]\n") test.id
  else (
  Hashtbl.add hash_view test ();
  Printf.printf (if !use_xml then "<testnode>%s\n" else "-- %s\n") (show_test test);
  List.iter (fun  sol -> 
    if !use_xml then Printf.printf "<solution>";
    if false && sol.restricted_dag != test.statement.dag then Printf.printf (if !use_xml then "%s\n" else "dag %s\n")  (show_dag sol.restricted_dag);
    (match sol.selected_run with 
    | None -> Printf.printf "attack\n" 
    | Some run -> 
      Printf.printf (if !use_xml then "%s\n" else "run:%s\n") (show_run run);
      List.iter (function 
          (Master,sigma,test) -> show_all_tests test
        | (Slave,sigma,test) -> Printf.printf (if !use_xml then "<slv><idtest>%d</idtest></slv>," else "*[%d]") test.id
        | _ -> assert false)  run.consequences;
      List.iter (fun c -> Printf.printf (if !use_xml then "[+<idcomp>%d</idcomp>+]," else "+[%d]") c.id_c)  run.completions);      
    if !use_xml then Printf.printf "</solution>"
  ) test.solutions_done ;
    if !use_xml then Printf.printf "</testnode>\n" else Printf.printf "end of (%d)\n" test.id;
  )
  
let rec show_completion_tree completion =
  if Hashtbl.mem hash_comp_view completion then Printf.printf (if !use_xml then "[-<idcomp>%d</idcomp>-].\n" else "--> [%d]\n") completion.id_c
  else (
  Hashtbl.add hash_comp_view completion ();
  Printf.printf (if !use_xml then "<comptree>%s\n" else "%s\n") (show_completion completion);
  if completion.selected_action = null_location 
  then
    match  completion.generated_test with
    | None -> () (*Printf.printf "X"*)
    | Some (t) -> Printf.printf (if !use_xml then "[*<idtest>%d</idtest>*] " else "%d ") t.id
  else
    List.iter (fun c -> show_completion_tree c) completion.further_completions;
  Printf.printf (if !use_xml then "</comptree>" else "\n")
  )
  
let show_all_tests () = 
  List.iter show_all_tests (List.rev bijection.initial_tests)
  
let show_final_completions () =
  List.iter (fun c -> 
    Printf.printf (if !use_xml then "<comproot>(%d)" else "(%d)\n") c.root.from_statement.id;
    show_completion_tree c;
    Printf.printf (if !use_xml then "</comproot>\n" else "\n")) bijection.initial_completions

let proc name =
  match name with
  | P -> bijection.p
  | Q -> bijection.q
  
let other name =
  match name with 
  | P -> Q
  | Q -> P
  
let base_of_name name =
  match name with 
  | P -> bijection.satP
  | Q -> bijection.satQ
  
let reorder_int_set s =
  IntegerSet.fold (fun e set -> IntegerSet.add e s) s IntegerSet.empty
  

(* Add a test to the tests in the queue *)
let push (statement : raw_statement) process_name origin init =
  bijection.next_id <- bijection.next_id + 1 ;
  let (int_set,initial) = match origin with 
      | Initial _ -> IntegerSet.singleton (bijection.next_id),true
      | Completion -> IntegerSet.singleton (bijection.next_id),true;
      | Composed(run1,run2) ->  (IntegerSet.union run1.test.from run2.test.from),false
      | Temporary -> assert false
  in
  (*let int_lst = IntegerSet.elements int_set in*)
  (*if origin != Completion && Hashtbl.mem bijection.htable int_lst then ()  else begin
  Hashtbl.add bijection.htable int_lst origin;*)
  (*if bijection.next_id = 2000 then show_hashtbl ();*)
  let nb = Dag.cardinal statement.dag.rel in
  let test = { null_test with
    nb_actions = nb;
    (* new_actions = 0; *)
    process_name = process_name;
    statement = statement;
    origin = origin;
    id = bijection.next_id;
    from = int_set;
    (*constraints = empty_correspondance;
    constraints_back = empty_correspondance;
    consequences = [];*)
  } in
  let solution = init test in
  test.solutions_todo <- [solution];
  (*Hashtbl.add bijection.htable_st hash_statement test;*)
  if !Util.debug_tests || (!about_progress && bijection.next_id mod 250 = 0) then Printf.printf "\nAdding new test: %s\n%!" (show_test test);
  (*if bijection.next_id mod 10000 = 0 then (*Hashtbl.iter (fun k v -> Printf.printf "%s" (show_raw_statement k)) bijection.htable;*)show_bijection ();*)
  bijection.tests <- Tests.add test bijection.tests;
  if initial then bijection.initial_tests <- test :: bijection.initial_tests;
  test

  
let reorder_tests () = 
  bijection.tests <- Tests.fold (fun test map -> 
    test.new_actions <-  
      Dag.fold (fun l _ nb -> 
        if LocationSet.mem l bijection.locs 
        then nb 
        else begin bijection.locs<-LocationSet.add l bijection.locs; nb + 1 end)
      test.statement.dag.rel 0;
    Tests.add test map) bijection.tests Tests.empty

(* Pop the queue of the test to check *)
let pop () = 
  let test = Tests.min_elt bijection.tests in
  bijection.tests <- Tests.remove test bijection.tests ; 
  test

(* add a partial completion to the todo list *) 
(* return true if a test should be extracted from completion, false otherwise with the actual completion *)
let register_completion completion =
  if !debug_completion then Printf.printf "Registering completion: %s\n" (show_completion completion);
  completion.st_c.binder := New ;
  let hash_compl = completion_to_hash_completion completion in
  if !debug_completion && hash_compl.is_opti then Printf.printf "optimal statement\n";
  let core_corresp = List.filter (fun (l,l') -> try ignore (Dag.find l' completion.root.initial_statement.dag.rel); true with Not_found -> false) (Dag.bindings completion.corresp_c.a) in
  let eq, diseq = recipes_of_head completion.st_c.head in
  let is_consistent = EqualitiesSet.is_empty (EqualitiesSet.inter eq diseq) in
  if is_consistent || hash_compl.is_opti then (* The optimal completions are kept because they can be used to discard further ones *)
  (
    let to_be_completed = if completion.root.from_base = P then bijection.partial_completions_P else bijection.partial_completions_Q in
    let loc = completion.selected_action in
    if not (Dag.mem loc completion.root.directory) then completion.root.directory <- Dag.add loc (ref []) completion.root.directory;
    let hash_table_loc = Dag.find loc completion.root.directory in
    (
   match List.find_opt (fun (hash_c,compl) -> hash_c.is_opti && core_corresp = hash_c.hash_corresp_c) !hash_table_loc with
    | None -> (
    match List.assoc_opt hash_compl !hash_table_loc with
    | None -> 
      if !debug_completion then Printf.printf "New completion: %s\n" (show_completion completion);
      hash_table_loc :=  (hash_compl,completion) :: !hash_table_loc;
      let new_list = Dag.add loc (completion:: (try Dag.find loc to_be_completed with Not_found -> [])) to_be_completed in
      if completion.root.from_base = P  then bijection.partial_completions_P <- new_list else bijection.partial_completions_Q <- new_list;
      if is_consistent && not (LocationSet.is_empty completion.missing_actions) then
      begin
          if !debug_completion then Printf.printf "Adding partial completion %s\n" (show_raw_statement completion.st_c);
          if completion.root.from_base = P then 
            bijection.todo_completion_P <- completion :: bijection.todo_completion_P
          else
            bijection.todo_completion_Q <- completion :: bijection.todo_completion_Q;
          false,Some completion
      end
      else
        is_consistent,Some completion
    | Some compl -> 
      if !debug_completion then Printf.printf "(((%s ----> %d )))\n" (show_completion completion)(compl.id_c) ;
      false,Some compl (* Todo: add test identities *)
    )
  | Some (_,compl) -> 
      if !debug_completion then Printf.printf "  %d is opti\n" (compl.id_c) ;
      false,None)
  )
  else begin
    if !debug_completion then Printf.printf "Inconsistant completion\n";
    false,None
  end

exception LocPtoQ of int

let loc_p_to_q p corr =
  try Dag.find p corr.a
  with Not_found -> raise (LocPtoQ p.p)

(* Register a solution to a test *)
let add_run partial_run =
    (*bijection.registered_tests <- Tests.add partial_run.test bijection.registered_tests;*)
    if partial_run.test.process_name = P 
    then 
      bijection.runs_for_completions_P <- partial_run :: bijection.runs_for_completions_P
    else 
      bijection.runs_for_completions_Q <- partial_run :: bijection.runs_for_completions_Q;
    Dag.iter (fun lp lq -> 
    (*let r = {locP = lp; locQ = lq; partial_run = partial_run;} in*)
    let recintP = try Dag.find lp bijection.indexP with Not_found -> Dag.empty in 
    let reclstP = try Dag.find lq recintP with Not_found -> RunSet.empty in
    bijection.indexP <- Dag.add lp (Dag.add lq (RunSet.add partial_run reclstP) recintP) bijection.indexP;
    let recintQ = try Dag.find lq bijection.indexQ with Not_found -> Dag.empty in 
    let reclstQ = try Dag.find lp recintQ with Not_found -> RunSet.empty in
    bijection.indexQ <- Dag.add lq (Dag.add lp (RunSet.add partial_run reclstQ) recintQ) bijection.indexQ;
    ) 
    (if partial_run.test.process_name = P then partial_run.corresp.a else partial_run.corresp_back.a) ;
    Dag.iter (fun loc i ->
      let choices_ind = if partial_run.test.process_name = P then bijection.choices_indexQ else bijection.choices_indexP in
      let recQ = try Dag.find loc choices_ind with Not_found -> IntegerMap.empty in
      let recQi = try IntegerMap.find i recQ with Not_found -> RunSet.empty in
      let ch = Dag.add loc (IntegerMap.add i (RunSet.add partial_run recQi) recQ) choices_ind in
      if partial_run.test.process_name = P then bijection.choices_indexQ <- ch else bijection.choices_indexP <- ch
    )
    partial_run.choices.c
  
let remove_run partial_run = 
  (*bijection.registered_tests <- Tests.remove partial_run.test bijection.registered_tests;*)
  if partial_run.test.process_name = P 
  then 
    bijection.runs_for_completions_P <- List.filter (fun pr -> pr != partial_run) bijection.runs_for_completions_P
  else 
    bijection.runs_for_completions_Q <- List.filter (fun pr -> pr != partial_run) bijection.runs_for_completions_Q ;
  Dag.iter (fun lp lq -> 
    (*let r = {locP = lp; locQ = lq; partial_run = partial_run;} in*)
    let recintP = try Dag.find lp bijection.indexP with Not_found -> Dag.empty in 
    let reclstP = try Dag.find lq recintP with Not_found -> RunSet.empty in
    bijection.indexP <- Dag.add lp (Dag.add lq (RunSet.remove partial_run reclstP) recintP) bijection.indexP;
    let recintQ = try Dag.find lq bijection.indexQ with Not_found -> Dag.empty in 
    let reclstQ = try Dag.find lp recintQ with Not_found -> RunSet.empty in
    bijection.indexQ <- Dag.add lq (Dag.add lp (RunSet.remove partial_run reclstQ) recintQ) bijection.indexQ;
    ) 
    (if partial_run.test.process_name = P then partial_run.corresp.a else partial_run.corresp_back.a) ;
    Dag.iter (fun loc i ->
      let choices_ind = if partial_run.test.process_name = P then  bijection.choices_indexQ else  bijection.choices_indexP in
      let recQ = try Dag.find loc choices_ind with Not_found -> IntegerMap.empty in
      let recQi = try IntegerMap.find i recQ with Not_found -> RunSet.empty in
      let ch = Dag.add loc (IntegerMap.add i (RunSet.remove partial_run recQi) recQ) choices_ind in
      if partial_run.test.process_name = P then bijection.choices_indexQ <- ch else bijection.choices_indexP <- ch
    )
    partial_run.choices.c

let mappings_of process loc = 
  try Dag.find loc
    (match process with P -> bijection.indexP | Q -> bijection.indexQ)
  with Not_found -> Dag.empty

let mapping_exists process loc1 loc2 =
  try not (RunSet.is_empty (Dag.find loc1 (Dag.find loc2 
    (match process with P -> bijection.indexQ | Q -> bijection.indexP)))) with Not_found -> false
  
let straight locP locQ = 
  try
  let p = (Dag.find locP bijection.indexP) in 
  try not (RunSet.is_empty (Dag.find locQ p))
  with Not_found -> false
  with Not_found -> 
    try ignore (Dag.find locQ bijection.indexQ); false
    with Not_found -> true
    
let straight pr locP locQ =
  if pr = P then straight locP locQ else straight locQ locP 


 let compatible partial_run = 
  let (corresp,corresp_back) = 
    if partial_run.test.process_name = P 
    then (partial_run.corresp,partial_run.corresp_back)
    else (partial_run.corresp_back,partial_run.corresp)
  in
  let choices_index = 
    if partial_run.test.process_name = P 
    then bijection.choices_indexQ
    else bijection.choices_indexP
  in
  let conflicts = ref RunSet.empty in
(*  let score = ref 0 in
  let conflicts_loc = ref LocationSet.empty in *)
  (Dag.iter (fun locP locQ -> 
    try
      let p = (Dag.find locP bijection.indexP) in 
      Dag.iter (fun lq runset ->
        if lq <> locQ 
        then begin conflicts := RunSet.union runset !conflicts end) p  
    with Not_found -> ()) corresp.a);
   (Dag.iter (fun locP locQ-> 
    try
      let q = (Dag.find locQ bijection.indexQ) in 
      Dag.iter (fun lp runset ->
        if lp <> locP 
        then begin conflicts := RunSet.union runset !conflicts end) q 
    with Not_found -> ()) corresp.a);
  (Dag.iter (fun loc i -> 
    try
      let set_i = (Dag.find loc choices_index) in 
      IntegerMap.iter (fun j runset ->
        if i <> j 
        then begin conflicts := RunSet.union runset !conflicts end) set_i 
    with Not_found -> ()) partial_run.choices.c);
  !conflicts;

