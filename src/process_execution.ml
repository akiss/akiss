open Util
open Types
open Dag
open Base
open Process
open Bijection
open Term


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
  | CallP(l,p,terms,chans) -> run_until_io (expand_call l p terms chans) first frame
  | SeqP(OutputA(_,_),_) -> assert false
  
let init_run process_name (statement : raw_statement) processQ test : partial_run=
  let (qt,fqt) = run_until_io processQ LocationSet.empty Inputs.new_inputs in
   { empty_run with 
     test = test ;
     remaining_actions = LocationSet.of_list(List.map (fun (x,y) -> x) (Dag.bindings statement.dag.rel)) ;
     qthreads = qt ;
     failed_qthreads = fqt;
     dag = test.statement.dag ;
   } 

(* Technical function called twice in try_run *)
(* Produce a new partial_run object from already computed elements except the remaining threads *)
let next_partial_run run action full_p proc l frame locs choices diseq =
  (*Printf.printf "next_partial_run %s \n" (show_process_start 3 full_p);*)
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
      not (LocationSet.mem action (try Dag.find loc run.dag.rel with Not_found -> assert false))) locs
    (*| Some _ -> LocationSet.empty *) in
    let corresp = { a = Dag.add action l run.corresp.a } in 
    (* if not (LocationSet.is_empty restrictions) && run.next_actions <> [] then (Printf.eprintf "error %s\n" (show_partial_run run);exit 5);*)
    try
    {
      test = run.test ;
      corresp = corresp ;
      corresp_back = { a = Dag.add l action run.corresp_back.a } ;
      remaining_actions = LocationSet.remove action run.remaining_actions ;
      frame = frame;
      choices = choices;
      dag = run.dag (*merge(dag_with_one_action_at_end locs action)*);
      added_dag = run.added_dag ;
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
let try_run run action (choices,locs,diseq,process)  =
  (*Printf.printf "constraints %s \n" (show_correspondance run.test.constraints );*)
  let condition = if is_empty_correspondance run.test.constraints 
    then 
      fun action l -> action.io = l.io 
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

let rec next_solution solution =
  let pr = Solutions.min_elt solution.partial_runs_todo in
  solution.partial_runs_todo <- Solutions.remove pr solution.partial_runs_todo;
  solution.partial_runs <- pr :: solution.partial_runs;
  if LocationSet.is_empty pr.restrictions then begin
    let first_actions = first_actions_among pr.dag pr.remaining_actions in
    let current_loc = try LocationSet.choose first_actions with Not_found -> assert false in
    try
    let (new_runs,new_loc) = next_run_with_action current_loc pr in 
    if !debug_execution && new_runs = [] then Printf.printf "No possible run from this trace \n"  ;
    List.iter (fun partial_run -> 
      (* if !debug_execution then Printf.printf "New p. run %s \n\n" (show_partial_run partial_run); *)
      if LocationSet.is_empty partial_run.remaining_actions 
      then begin
        if 
          match partial_run.test.statement.head with 
          | Knows(_)
          | Reach -> true
          | Identical(t,t') -> check_recipes partial_run (t,t') 
          | Tests(equal,diseq) -> 
            (EqualitiesSet.for_all (check_recipes partial_run) equal) 
            && (EqualitiesSet.for_all ( fun dis -> not (check_recipes partial_run dis)) diseq)
          | Unreachable -> assert false
        then 
          begin if !debug_execution then Printf.printf "Solution succeeds the tests \n"  ;
          solution.possible_runs_todo <- Solutions.add partial_run solution.possible_runs_todo end
        else
          begin if !debug_execution then Printf.printf "Solution fails the tests: \n %s \n" (show_run partial_run) (*;
          solution.failed_run <- partial_run :: solution.failed_run *) end
      end
      else begin
        solution.partial_runs_todo <- Solutions.add partial_run solution.partial_runs_todo 
      end
    ) new_runs ;
    None
  with
  | LocPtoQ i -> Printf.eprintf "error loc_p_to_q %d while executing on %d %s \n %s \n constraints %s\n" 
    i current_loc.p (show_partial_run pr) (show_test pr.test)(show_correspondance pr.test.constraints); exit(5)
  end
  else
    if is_empty_correspondance pr.test.constraints then
    begin
    let lvl = sol_level solution in
    if !debug_execution || lvl = 15
    then Printf.printf "A restricted run is being tested from %s \n which test is \n %s \n" (show_partial_run pr)(show_test pr.test) ;
    let par = match pr.parent with Some par -> par | _ -> assert false in
    let roots = get_all_new_roots pr.restrictions LocationSet.empty par in
    let exception Fail in
    try 
    Some (
    List.fold_left (fun prlst (before,after,prun) -> 
      if !debug_execution 
      then Printf.printf "\n**** Starting the restriction (level %d) for %s  < %d < %s ****\n%s\n" 
      lvl (show_loc_set before) pr.last_exe.p (show_loc_set after)(show_dag pr.dag);
      let new_dag = { rel = LocationSet.fold (fun l dag -> Dag.add l (LocationSet.singleton pr.last_exe) dag) after (dag_with_one_action_at_end before pr.last_exe).rel } in 
      let new_solution =
      { empty_solution with 
       (* partial_runs = [] ; *)
       partial_runs_todo = Solutions.singleton {prun with 
        dag = merge prun.dag new_dag;
        added_dag = merge prun.added_dag new_dag;
        restrictions = LocationSet.empty ; };
       (* possible_restricted_runs = [];
       possible_runs = Solutions.empty;
       possible_runs_todo = Solutions.empty;
       failed_partial_run = [];
       failed_run = [];
       partitions = [] ;
       movable = 0 ; *)
       due_to = Some solution;
      } in
      match find_possible_run new_solution with
      | None -> raise Fail
      | Some sol -> sol @ prlst
    ) [] ((pr.restrictions,LocationSet.empty, par) :: roots ) )
    with Fail -> 
      if !debug_execution then Printf.printf "The restricted partial run with %d : %s has failed\n" pr.last_exe.p (show_loc_set pr.restrictions); 
      None
  end
  else None
  
and find_possible_run solution : (partial_run list) option  =
  if Solutions.is_empty solution.possible_runs_todo 
  then begin
      if Solutions.is_empty solution.partial_runs_todo 
      then None (*
        if Solutions.is_empty solution.possible_runs 
        then begin
          if solution.possible_restricted_runs = [] then
            None
          else begin Printf.eprintf "Further investigation are required (%d partial dags not considered).\n" (List.length solution.possible_restricted_runs); 
            None end 
          end
        else begin (* All possible run have been tested, we take the better one and add the tests of its conflicts *)
          let pr = Solutions.min_elt solution.possible_runs in
          Some [pr] end *)
      else begin 
        match next_solution solution with 
        | None -> find_possible_run solution (* if the next solution is just a next step*)
        | Some sol -> Some sol (* the next solution returned a list of restricted dag *) 
      end
  end
  else begin
    let pr =  Solutions.min_elt solution.possible_runs_todo in
    solution.possible_runs_todo <- Solutions.remove pr solution.possible_runs_todo ;
    if !debug_execution then Printf.printf "complete run: %s\n"(show_run pr) ;
    Some [pr] (*
    if subset pr.dag pr.test.statement.dag 
    then begin
      (*let conflicts = Bijection.compatible pr in
        solution.possible_runs <- Solutions.add conflicts solution.possible_runs;*)
        Some [pr] (* conflicts *)
      end
    else begin
      if !debug_execution then Printf.printf "Partial dag\n";
      solution.possible_restricted_runs <- pr :: solution.possible_restricted_runs;
      find_possible_run solution
      end *)
  end
(*let rec find_compatible_run solution =
  if Solutions.is_empty solution.possible_runs_todo 
  then begin
    if Solutions.is_empty solution.partial_runs_todo 
    then 
        if Solutions.is_empty solution.possible_runs 
        then begin
          if solution.possible_restricted_runs = [] then
            None
          else begin Printf.printf "Further investigation are required (%d partial dags not considered).\n" (List.length solution.possible_restricted_runs); 
            None end 
          end
        else begin (* All possible run have been tested, we take the better one and add the tests of its conflicts *)
          try Some [(Solutions.min_elt (Solutions.filter (fun sol -> 
              compatible_prun sol.test.constraints sol.test.constraints_back sol)
            solution.possible_runs)) ]
          with Not_found -> None end
    else begin next_solution solution; 
      find_compatible_run solution 
    end end
  else begin
    let pr =  Solutions.min_elt solution.possible_runs_todo in
    solution.possible_runs_todo <- Solutions.remove pr solution.possible_runs_todo ;
    if !debug_execution then Printf.printf "complete run: %s\n"(show_run pr) ;
    if subset pr.dag pr.test.statement.dag 
    then begin
      (* let conflicts = Bijection.compatible pr in *)
      if compatible_prun pr.test.constraints pr.test.constraints_back pr then
        begin
        Some [pr] (* conflicts *)
        end
      else begin 
        if !debug_execution then Printf.printf "Solution does not fit correspondance \n";
        solution.possible_runs <- Solutions.add pr solution.possible_runs;
        find_compatible_run solution
        end
      end
    else begin
      if !debug_execution then Printf.printf "Partial dag\n";
      solution.possible_restricted_runs <- pr :: solution.possible_restricted_runs;
      find_compatible_run solution
      end
  end
 *)     

      
