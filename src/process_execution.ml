open Util
open Types
open Dag
open Base
open Process
open Bijection
open Term
open Bijection.Run

let rec apply_subst_inputs term frame =
  match term with
    | Fun({ id=Input(l)}, []) -> Inputs.get l frame
    | Fun(f, args) -> Fun(f, List.map (fun x -> apply_subst_inputs x frame) args)
    | Var(x) -> Var(x)


(* return a tuple : the updated threads, the threads which have failed due to a test *)
let rec run_until_io process first frame =
  (*Printf.printf "run until io %s \n" (show_process_start 3 process);*)
  match process with
  | EmptyP -> ([],[])
  | ParallelP(proclst) -> List.fold_left (fun (lst1,lst2) (x,y) -> (x @ lst1 , y @ lst2)) ([],[]) (List.map (fun p -> run_until_io p first frame ) proclst)
  | ChoiceP(l,proclst) -> 
    List.fold_left (fun (lst1,lst2) (x,y) -> (x @ lst1 , y @ lst2)) ([],[])
    (List.map (fun (i,p) -> 
      let (lst1,lst2) = run_until_io p first frame in
      (List.map (fun (c,ls,diseq,p) -> (Inputs.add_choice l i c, ls,diseq, p)) lst1, lst2)
      ) proclst)
  | SeqP(Input(l),p) 
  | SeqP(Output(l,_),p) -> ([(Inputs.new_choices,first,[],process)],[])
  | SeqP(Test(t,t'),p) -> 
    let t = apply_subst_inputs t frame in
    let t' = apply_subst_inputs t' frame in
    (**) 
    if Rewriting.equals_r t t' (! Parser_functions.rewrite_rules) 
    then run_until_io p first frame 
    else begin 
    (*let t'' = Rewriting.normalize t (! Parser_functions.rewrite_rules) in
    let t''' = Rewriting.normalize t' (! Parser_functions.rewrite_rules) in
    Printf.printf "Test fail %s = %s \n" (show_term t'')(show_term t''');*)
      ([],[(Inputs.new_choices,first,[],process)]) end
  | SeqP(TestInequal(t,t'),p) ->
    let t = apply_subst_inputs t frame in
    let t' = apply_subst_inputs t' frame in
    if not (Rewriting.equals_r t t' (! Parser_functions.rewrite_rules)) 
    then let (lst1,lst2) = run_until_io p first frame in
      (List.map (fun (c,ls,diseq,p) -> (c,ls, (t,t')::diseq,p)) lst1, lst2)  
    else ([],[(Inputs.new_choices,first,[],process)])
  | CallP(l,n,p,terms,chans) ->
    List.fold_left (fun (lst1,lst2) (x,y) -> (x @ lst1 , y @ lst2)) ([],[]) 
      (List.init n (fun i -> 
        let pr = expand_call l (i+1) p terms chans in
        run_until_io pr first frame ))
  | SeqP(OutputA(_,_),_) -> assert false
  
let init_sol process_name (statement : raw_statement) processQ test : solution =
  let (qt,fqt) = run_until_io processQ LocationSet.empty Inputs.new_inputs in
  let rec sol = { null_sol with 
    init_run = run;
    partial_runs = [run];
    partial_runs_todo = Solutions.empty (*singleton run*);
    restricted_dag = test.statement.dag ;
    sol_test = test;
  }
  and run =
   { empty_run with 
     test = test ;
     sol = sol ; 
     remaining_actions = LocationSet.of_list(List.map (fun (x,y) -> x) (Dag.bindings statement.dag.rel)) ;
     qthreads = qt ;
     failed_qthreads = fqt;
   } in
   sol.partial_runs_todo <- Solutions.singleton run;
   sol

(* Technical function called twice in try_run *)
(* Produce a new partial_run object from already computed elements except the remaining threads *)
let next_partial_run run action full_p proc l frame locs choices diseq =
  (*Printf.printf "next_partial_run %s \n dag = %s\n" (show_process_start 3 full_p)(show_dag run.sol.restricted_dag);*)
  let (qt,fqt) = List.fold_left 
    (fun (lst,flst) (chs,ls,diseq,p) -> 
      if p != full_p 
      then ((chs,ls,diseq,p) :: lst,flst)
      else begin
        (*Printf.printf "start run until io %s \n" (show_process_start 3 proc);*)
        let (lqt,flqt)= (run_until_io proc (LocationSet.add action ls) frame) in 
        (lqt @ lst , flqt @ flst) end
    )
    ([],[]) run.qthreads in
    let restrictions = (*match run.next_action with
    | None ->*) LocationSet.filter (fun loc -> 
      not (LocationSet.mem action (try Dag.find loc run.sol.restricted_dag.rel with Not_found -> assert false))) locs
    (*| Some _ -> LocationSet.empty *) in
    let corresp = { a = Dag.add action l run.corresp.a } in 
    (* if not (LocationSet.is_empty restrictions) && run.next_actions <> [] then (Printf.eprintf "error %s\n" (show_partial_run run);exit 5);*)
    try
    {
      test = run.test ;
      sol = run.sol;
      corresp = corresp ;
      corresp_back = { a = Dag.add l action run.corresp_back.a } ;
      remaining_actions = LocationSet.remove action run.remaining_actions ;
      frame = frame;
      choices = choices;
      phase = l.phase;
      disequalities = diseq @ run.disequalities;
      qthreads = qt ;
      failed_qthreads = fqt @ run.failed_qthreads ;
      restrictions = restrictions;
      (*performed_restrictions = run.performed_restrictions;*)
      parent = Some run;
      last_exe = action;
      weird_assoc = run.weird_assoc + (
        match l.parent,action.parent with 
        | Some l1,Some l2 -> if loc_p_to_q l2 run.corresp = l1 then 0 else 1 
        | None,None -> 0 | _ -> 1 );
      score = run.score + (if Bijection.straight (run.test.process_name) action (loc_p_to_q action corresp) then 1 else -25);
      consequences = [];
      completions = [];
    }
    with
    LocPtoQ i -> (Printf.eprintf "next_partial_run error \n"; raise (LocPtoQ i))
    

  
let rec apply_frame recipe (prun : partial_run) =
       try(
  match recipe with
    | Fun({ id=Frame(l)}, []) -> Inputs.get (Bijection.loc_p_to_q l prun.corresp) prun.frame
    | Fun({ id=Input(l)}, []) -> Inputs.get l prun.frame
    | Fun(f, args) -> Fun(f, List.map (fun x -> apply_frame x prun) args)
    | Var(x) -> try 
        let ba = List.find (fun ba -> ba.recipe = Var(x) ) prun.test.statement.body in 
        ba.term 
      with Not_found -> Printf.eprintf "unbound recipe variable %s in %s" (show_term recipe)(show_raw_statement prun.test.statement); exit 2(* Var(x) *)
     ) with
      LocPtoQ i -> (Printf.eprintf "apply_frame error %s \n" (show_term recipe); raise (LocPtoQ i))

(* Given a partial_run run, try to execute action on one of the available threads of Q *)        
let try_run run action  (choices,locs,diseq,process)  =
  (*Printf.printf "constraints %s \n" (show_correspondance run.test.constraints );*)
  let condition = if is_empty_correspondance run.test.constraints 
    then 
      fun (action : location) (l : location) -> action.io = l.io && action.phase >= l.phase
    else 
      fun action l -> try loc_p_to_q action run.test.constraints = l with LocPtoQ i -> (Printf.eprintf "try run error\n"; raise (LocPtoQ i)) in
   (*Printf.printf "Testing %s against %s\n" action.chan.name (show_process_start 1 process);*)
  match Inputs.merge_choices run.choices choices with
  | None -> None
  | Some choices -> 
   match process with
   | SeqP(Input(l),p) -> 
     if condition action l (* make sure channel still work *)
     then 
       begin 
         let new_frame = Inputs.add_to_frame l 
            (Rewriting.normalize (apply_frame (Inputs.get action run.test.statement.recipes) run)(! Parser_functions.rewrite_rules)) run.frame in
         let npr = next_partial_run run action process p l new_frame locs choices diseq in
         (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
        Some (npr,l) 
       end
       else None
   | SeqP(Output(l,t),p) -> 
     if condition action l 
     then begin
       let new_frame = Inputs.add_to_frame l (Rewriting.normalize (apply_subst_inputs t run.frame)(! Parser_functions.rewrite_rules)) run.frame in
       let npr = next_partial_run run action process p l new_frame locs choices diseq in
       (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
       Some (npr,l)
     end
     else None
   | _ -> assert false
   
let next_run_with_action current_loc partial_run=
   if ! debug_execution then Printf.printf "___________________\nNext execution step on %s" (show_partial_run partial_run); 
  let (new_runs,locs) = List.fold_left (
    fun (new_runs,locs) lp -> 
      match try_run partial_run current_loc lp with
      | None -> (new_runs,locs)
      | Some (npr,l) -> (npr ::  new_runs, LocationSet.add l locs)
    ) ([],LocationSet.empty) partial_run.qthreads in
  (new_runs, current_loc)

(* Given a partial_run select an action to execute and test this action on available threads of Q *)
let next_run partial_run : (partial_run list * location)= 
  let first_actions = first_actions_among partial_run.test.statement.dag partial_run.remaining_actions in
  let current_loc = 
    try LocationSet.choose first_actions 
    with
    Not_found -> 
      begin Printf.printf "No run on %s [%s] \n" (show_dag partial_run.test.statement.dag) (show_loc_set partial_run.remaining_actions); 
      assert false end
  in
  next_run_with_action current_loc partial_run
(*  let (new_runs,locs) = List.fold_left (fun (new_runs,locs) lp -> 
    match try_run partial_run current_loc lp with
    | None -> (new_runs,locs)
    | Some (npr,l) -> (npr ::  new_runs, LocationSet.add l locs)
    ) ([],LocationSet.empty) partial_run.qthreads in
  (new_runs, current_loc)*)



 

let compatible constraints constraints_back locP locQ = 
  try locQ = Dag.find locP constraints.a
  with Not_found -> begin 
    try Dag.find locQ constraints_back.a  =  locP 
    with Not_found -> true end
          
let compatible_prun constraints constraints_back (prun : partial_run)=
  Dag.for_all (compatible constraints constraints_back) prun.corresp.a
  
let rec get_all_new_roots before after run = 
  if LocationSet.is_empty before then []
  else 
  match run.parent with
  | None -> assert false
  | Some r -> 
    if LocationSet.mem run.last_exe before
    then 
      let before = LocationSet.remove run.last_exe before in
      let after = LocationSet.add run.last_exe after in
    (before,after,r) :: get_all_new_roots before after r
    else get_all_new_roots before after r
  
let check_recipes partial_run (r,r')=
  let r = apply_frame r partial_run in
  let r' = apply_frame r' partial_run in
  (*let r'' = Rewriting.normalize r (! Parser_functions.rewrite_rules) in
  let r''' = Rewriting.normalize r' (! Parser_functions.rewrite_rules) in
  Printf.printf "recipes %s and %s\n %s\n>> %s \n=? %s\n" 
    (show_term r)(show_term r')(Inputs.show_inputs partial_run.frame)(show_term r'')(show_term r''');*)
  Rewriting.equals_r r r' (! Parser_functions.rewrite_rules) 
  
let check_identities run head = 
  (EqualitiesSet.for_all (check_recipes run) head.equalities) 
  && (EqualitiesSet.for_all ( fun dis -> not (check_recipes run dis)) head.disequalities)


let rec next_solution solution =
  let pr = Solutions.min_elt solution.partial_runs_todo in
  solution.partial_runs_todo <- Solutions.remove pr solution.partial_runs_todo;
  solution.partial_runs <- pr :: solution.partial_runs;
  if LocationSet.is_empty pr.restrictions then begin
    let first_actions = first_actions_among pr.sol.restricted_dag pr.remaining_actions in
    let current_loc = try LocationSet.choose first_actions with Not_found -> assert false in
    try
    let (new_runs,new_loc) = next_run_with_action current_loc pr in 
    if !debug_execution && new_runs = [] then Printf.printf "No possible run from this trace \n"  ;
    List.iter (fun partial_run -> 
      (* if !debug_execution then Printf.printf "New p. run %s \n\n" (show_partial_run partial_run); *)
      if LocationSet.is_empty partial_run.remaining_actions 
      then begin
        if check_identities partial_run (get_test_head partial_run.test.statement.head)
        then 
          begin if !debug_execution then Printf.printf "\nSolution succeeds the tests \n %s " (show_run partial_run) ;
          solution.possible_runs_todo <- Solutions.add partial_run solution.possible_runs_todo end
        else
          begin if !debug_execution then Printf.printf "\nSolution fails the tests: \n %s \n" (show_run partial_run) (*;
          solution.failed_run <- partial_run :: solution.failed_run *) end
      end
      else begin
        solution.partial_runs_todo <- Solutions.add partial_run solution.partial_runs_todo 
      end
    ) new_runs 
  with
  | LocPtoQ i -> Printf.eprintf "error loc_p_to_q %d while executing on %d %s \n %s \n constraints %s\n" 
    i current_loc.p (show_partial_run pr) (show_test pr.test)(show_correspondance pr.test.constraints); exit(5)
  end
  else
    if is_empty_correspondance pr.test.constraints (* When the mapping is set there is no way to have a restricted dag *)
    then (
    if !debug_execution 
    then Printf.printf "A restricted run is being tested from %s \n which test is \n %s \n" (show_partial_run pr)(show_test pr.test) ;
    let par = match pr.parent with Some par -> par | _ -> assert false in
    let roots = get_all_new_roots pr.restrictions LocationSet.empty par in
    let new_dag = dag_with_one_action_at_end pr.restrictions pr.last_exe in
    let restr_dag = canonize_dag (merge pr.sol.restricted_dag new_dag) in
    pr.sol.restricted_dag <- restr_dag;  
    List.iter (fun (before,after,prun) -> 
      if !debug_execution 
      then Printf.printf "\n**** Starting the restriction for %s  < %d < %s ****\n%s\n" 
        (show_loc_set before) pr.last_exe.p (show_loc_set after)(show_dag pr.sol.restricted_dag);
      let new_dag = { rel = LocationSet.fold (fun l dag -> Dag.add l (LocationSet.singleton pr.last_exe) dag) after (dag_with_one_action_at_end before pr.last_exe).rel } in
      let restr_dag = canonize_dag (merge pr.sol.restricted_dag new_dag) in
      if not (List.exists (fun s -> s.restricted_dag == restr_dag) (pr.test.solutions_done @ pr.test.solutions_todo )) 
      then
      let new_solution =
      { null_sol with 
        init_run = prun.sol.init_run;
        partial_runs_todo = Solutions.singleton prun.sol.init_run;
        restricted_dag = restr_dag; 
        sol_test = prun.sol.sol_test;
      } in
      pr.test.solutions_todo <- new_solution :: pr.test.solutions_todo
    )  roots 
    )
  
let rec find_possible_run solution =
  if Solutions.is_empty solution.possible_runs_todo 
  then begin
      if (Solutions.is_empty solution.partial_runs_todo) 
      then None
      else begin 
        next_solution solution; 
        find_possible_run solution 
      end
  end
  else begin
    let pr =  Solutions.min_elt solution.possible_runs_todo in
    solution.possible_runs_todo <- Solutions.remove pr solution.possible_runs_todo ;
    if !debug_execution then Printf.printf "Selected execution:\n %s\n"(show_run pr) ;
    solution.selected_run <- Some pr;
    Some pr
  end
  
    
