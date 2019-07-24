(** Execution of traces, computation of complete set of solutions *)
open Util
open Types
open Dag
open Base
open Process
open Bijection
open Bijection.Run
open Bijection.Test

(** set to true to describe attacks in english *)
let verbose_execution = ref false

let rec apply_subst_inputs term frame =
  match term with
    | Fun({ id=InputVar(l)}, []) -> Inputs.get l frame
    | Fun(f, args) -> Fun(f, List.map (fun x -> apply_subst_inputs x frame) args)
    | Var(x) -> Var(x)

(*let dispatch tuple = List.fold_left (fun (lst1,lst2,lst3) (x,y,z) -> 
  (List.rev_append x lst1 ,List.rev_append y lst2,List.rev_append z lst3)) ([],[],[]) tuple*)

(** update the tuple (pending,final,failure) : 
  - the (chan,threads) waiting for a silent action, 
  - the updated threads, 
  - the threads which have failed due to a test (* for debug outputs *)*)
let rec run_until_io test pending final failure (choices_constraints : Inputs.choices) process first frame =
  (*Printf.printf "run until io %s \n%!" (show_process_start 1 process);*)
  match process with
  | EmptyP -> ()
  | ParallelP(proclst) -> List.iter (fun p -> run_until_io test pending final failure choices_constraints p first frame ) proclst
  | ChoiceP(l,proclst) -> begin
      (*Printf.printf "Choice is done: %d\n %s\n%s\n%!" l.p (Inputs.show_choices test.choice_constraints)(show_process_start 1 process) ;*)
      match Inputs.get_choice_opt l choices_constraints with
      | None -> (*
        if (test.choice_constraints <> Inputs.new_choices)
        then (Printf.printf "Choice constraints are not enough: %d\n %s\n%s\n%!" l.p (show_test test)(show_process_start 1 process) )
        ;
        if not test.reflexive then *)
        if (test.choice_constraints = Inputs.new_choices)
        then
          List.iter (fun (i,p) -> run_until_io test pending final failure (Inputs.add_choice l i choices_constraints) p first frame) proclst
      | Some i -> try 
          run_until_io test pending final failure choices_constraints (List.assoc i proclst) first frame 
        with Not_found -> assert false
      end
  | SeqP(Input({io = Input(chanId); observable= Public}) ,p) 
  | SeqP(Output({io = Output(chanId,_); observable= Public},_) ,p) -> 
      final := { made_choices = choices_constraints; before_locs = first; thread = process} :: !final
  | SeqP(Input({io = Input(chanId); observable= Hidden; phase = ph} as l),p) -> 
      pending := (l,None,   {c = chanId; io = In;  ph = ph},{ made_choices = choices_constraints; before_locs = first; thread = p}) :: !pending
  | SeqP(Output({io = Output(chanId,_); observable= Hidden; phase = ph} as l,t),p) -> 
      pending := (l,Some t, {c = chanId; io = Out; ph = ph},{ made_choices = choices_constraints; before_locs = first; thread = p}) :: !pending
  | SeqP(Test(t,t'),p) -> 
      let t = apply_subst_inputs t frame in
      let t' = apply_subst_inputs t' frame in
      if Rewriting.equals_r t t' (! Parser_functions.rewrite_rules) 
      then run_until_io test pending final failure choices_constraints p first frame 
      else begin 
      (*let t'' = Rewriting.normalize t (! Parser_functions.rewrite_rules) in
      let t''' = Rewriting.normalize t' (! Parser_functions.rewrite_rules) in
      Printf.printf "Test fail %s \n    =     %s \n%!" (show_term t'')(show_term t''');*)
      failure := { made_choices =choices_constraints; before_locs = first; thread = process} :: !failure end
  | SeqP(TestInequal(t,t'),p) ->
    let t = apply_subst_inputs t frame in
    let t' = apply_subst_inputs t' frame in
    if not (Rewriting.equals_r t t' (! Parser_functions.rewrite_rules)) 
    then run_until_io test pending final failure choices_constraints p first frame 
    else failure := { made_choices = choices_constraints; before_locs = first; thread = process} :: !failure
  | CallP(l,n,p,terms,chans) -> 
      for i = 1 to n do
        let pr = expand_call l i p terms chans in
        run_until_io test pending final failure choices_constraints pr first frame 
      done
  | _ -> assert false
  
(** Given a secret channel communication from a loc_input to a loc_output of a term_output, 
computes the threads which appears after this reduction *)  
let reduc_and_run test choices_constraints pending final failure (loc_input : location) (loc_output : location) term_output thread_input thread_output frame =
  (*Printf.printf "  reduc_and_run %d -> %d\n" loc_output.p loc_input.p;*)
  let process_input = Process.apply_subst_process loc_input term_output thread_input.thread in
  if test.choice_constraints = Inputs.new_choices 
  then (
    let first = LocationSet.union thread_input.before_locs thread_output.before_locs  in
    match Inputs.merge_choices_with_link thread_input.made_choices thread_output.made_choices loc_input loc_output with 
    Some choices_constraints ->
      run_until_io test pending final failure choices_constraints process_input first frame; 
      run_until_io test pending final failure choices_constraints thread_output.thread first frame
    | None -> ()
  )
  else (
    if Inputs.get_choice_opt loc_input test.choice_constraints = Some loc_output.p 
    then (
      if ! verbose_execution then
      Printf.printf "    out(%s) -%s[%d]-> in(%s)\n" loc_output.name 
        (match loc_output.io with Input(c) | Output(c,_) -> c.name | _ -> assert false) 
        loc_output.phase loc_input.name;
      let first = LocationSet.union thread_input.before_locs thread_output.before_locs  in
      let choices_constraints = test.choice_constraints in
      run_until_io test pending final failure choices_constraints process_input first frame; 
      run_until_io test pending final failure choices_constraints thread_output.thread first frame
    )
  )
  

  
let run_silent_actions old_threads test (choices_constraints : Inputs.choices ) process first frame  =
  let new_threads = ref [] in
  let final = ref [] in
  let failure = ref [] in
  run_until_io test new_threads final failure choices_constraints process first frame ;
  while !new_threads != [] 
  do
    match !new_threads with
    | [] -> assert false
    | (new_loc,new_term,chan_kind,new_ext_thread) :: q -> 
      new_threads := q ;
      let conj_chan = { chan_kind with io = Base.switch_io chan_kind.io} in 
      (
        match ChanMap.find_opt conj_chan !old_threads with
        | None -> ()
        | Some old_chan_lst -> List.iter (fun (old_loc,old_term,old_ext_thread) ->
          match new_term,old_term with
          | None, Some t -> reduc_and_run test choices_constraints new_threads final failure new_loc old_loc t new_ext_thread old_ext_thread frame
          | Some t, None -> reduc_and_run test choices_constraints new_threads final failure old_loc new_loc t old_ext_thread new_ext_thread frame
          | _ -> assert false
          ) old_chan_lst 
      );
      old_threads := ChanMap.add chan_kind ((new_loc,new_term,new_ext_thread)::(try ChanMap.find chan_kind !old_threads with Not_found -> [])) !old_threads 
  done ;
  (!final,!failure)
      

      
(*let run_silent_actions choices_constraints process old_pending first frame =
  (*Printf.printf "run silent actions of %s \n%!" (show_process_start 3 process);*)
  let pending,final,failure = run_until_io pending final failure choices_constraints process (Inputs.new_choices) first frame in
  (* Printf.printf "run_silent_actions: %s\n %!" (show_ext_extra_thread_lst (List.map (fun (l,t,c,et) -> (l,t,et)) pending)); *)
  let res = test_all_internal_communications choices_constraints (merge_pending_lst old_pending pending) pending frame in
  dispatch [(pending,final,failure);res]*)
  
let choices_constraints test choice =
  if test.reflexive
  then test.statement.choices
  else choice

let rec dag_to_sequence dag set =
  if LocationSet.is_empty set then []
  else 
    try let loc = LocationSet.choose (first_actions_among dag set) in 
    loc :: (dag_to_sequence dag (LocationSet.remove loc set))
    with
    Not_found -> Printf.printf "cyclic dag unexpected: %s (%s) \n%!" (show_dag dag) (show_loc_set set); assert false 
    
let dag_to_sequence dag = 
  dag_to_sequence dag (Dag.fold (fun l _ remain ->  LocationSet.add l remain) dag.rel LocationSet.empty )
  
let init_sol process_name (statement : raw_statement) processQ sequence test : solution =
  let old_threads = ref ChanMap.empty in
  let (final,failure) = run_silent_actions old_threads test (choices_constraints test test.choice_constraints) processQ LocationSet.empty Inputs.new_inputs in
  (*let sequence = dag_to_sequence statement.dag  in*)
  let rec sol = { null_sol with 
    init_run = run;
    partial_runs_todo = Solutions.empty ;
    sequence = sequence ;
    restricted_dag = test.statement.dag ;
  }
  and run =
   { empty_run with 
     test = test ;
     sol = sol ; 
     remaining_actions = sequence ;
     pending_qthreads = !old_threads;
     qthreads = final ;
     failed_qthreads = failure;
   } in
   sol.partial_runs_todo <- Solutions.singleton run;
   sol

(** Technical function called twice in try_run *)
(** Produce a new partial_run object from already computed elements except the remaining threads *)
let next_partial_run run (action : location) full_p proc l frame locs choices =
  (*Printf.printf "next_partial_run %s \n dag = %s\n" (show_process_start 3 full_p)(show_dag run.sol.restricted_dag);*)
  let old_threads = ref run.pending_qthreads in
  let (qthreads,fqthreads) = List.fold_left 
    (fun (new_qt,flqt) ext_thread -> 
      if ext_thread.thread != full_p 
      then (ext_thread :: new_qt,flqt)
      else begin
        (*Printf.printf "start run_silent_actions %s \n" (show_process_start 3 proc);*)
        let (lqt,fail) = run_silent_actions old_threads run.test (choices_constraints run.test choices) proc (LocationSet.add action ext_thread.before_locs) frame in 
        (lqt @ new_qt, fail @ flqt) end
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
      remaining_actions = List.tl run.remaining_actions ;
      frame = frame;
      choices = choices;
      phase = l.phase;
      pending_qthreads = ! old_threads;
      qthreads = qthreads ;
      failed_qthreads = fqthreads;
      restrictions = restrictions;
      parent = Some run;
      last_exe = action;
      weird_assoc = run.weird_assoc  + (
        match l.parent,action.parent with 
        | Some l1,Some l2 -> if loc_p_to_q l2 run.corresp = l1 then 0 else 1 
        | None,None -> 0 | _ -> 1 );
      score = run.score + (if Bijection.straight (run.test.process_name) action l then 1 else -25);
      consequences = [];
      completions = [];
    }
    with
    LocPtoQ i -> (Printf.eprintf "next_partial_run error \n"; raise (LocPtoQ i))
    

  
let rec apply_frame recipe (prun : partial_run) =
       try(
  match recipe with
    | Fun({ id=Frame(l)}, []) -> Inputs.get (Bijection.loc_p_to_q l prun.corresp) prun.frame
    | Fun({ id=InputVar(l)}, []) -> Inputs.get l prun.frame
    | Fun(f, args) -> Fun(f, List.map (fun x -> apply_frame x prun) args)
    | Var(x) -> try 
        let ba = List.find (fun ba -> ba.recipe = Var(x) ) prun.test.statement.body in 
        ba.term 
      with Not_found -> Printf.printf "unbound recipe variable %s in %s" (show_term recipe)(show_raw_statement prun.test.statement); assert false
     ) with
      LocPtoQ i -> (Printf.printf "apply_frame error %s \nrun:%s\n" (show_term recipe)(show_partial_run prun); raise (LocPtoQ i))
      
let show_verbose_action (action : location) run  =
    if !verbose_execution then (
    Printf.printf "%2d[%d]%3d > %3d: %s\n" 
    (Dag.cardinal run.corresp.a)
    action.phase
    (match action.parent with Some l -> l.p | None -> 0) 
    action.p 
    (match action.io with 
    | Input(c) -> "in(" ^ c.name ^ "," ^ action.name ^ (if !use_xml then "&lt;-" else "<-") ^ (show_term (Inputs.get action run.test.statement.recipes)) ^ ")"
    | Output(c,t) -> "out(" ^ c.name ^ ") l." ^ action.name
    | _ -> assert false)
    )

(** Given a partial_run run, try to execute action on one of the available threads of Q *)        
let try_run run (action : location) ext_thread =
  (*Printf.printf "constraints %s \n" (show_correspondance run.test.constraints );*)
  let free_cond = fun (action : location) (l : location) -> (
        match action.io , l.io with 
        | Input c1, Input c2 
        | Output (c1, _) ,Output (c2, _) -> c1 == c2
        | _ -> false
        )
        && action.phase <= l.phase in
  let condition = if is_empty_correspondance run.test.constraints 
    then 
      free_cond
    else 
      fun action l -> try 
        loc_p_to_q action run.test.constraints = l 
        with LocPtoQ i -> (
          if !about_rare 
          then Printf.printf "partial constraint (no %d): %s\n%s\n%!" l.p (show_correspondance run.test.constraints)(show_extra_thread ext_thread); 
          free_cond action l) in
  (* Printf.printf "Testing %d against %s\n" action.p (show_process_start 1 ext_thread.thread);*)
  (*let intern_phase = Dag.fold (fun k _ maxphase -> 
      match k.io with Input(_)| Output(_,_) -> max k.phase maxphase | _ -> maxphase 
    ) ext_thread.made_choices.c 0 in
    if ! verbose_execution then Printf.printf "phase: %d\n%s\n" intern_phase (Inputs.show_choices ext_thread.made_choices);*)
  match Inputs.merge_choices run.choices ext_thread.made_choices with
  | None -> None
  | Some choices -> 
   match ext_thread.thread with
   | SeqP(Input(l),p) -> 
     if condition action l (* make sure channel still work *)
     then 
       begin 
         let new_frame = Inputs.add_to_frame l 
            (Rewriting.normalize (apply_frame (Inputs.get action run.test.statement.recipes) run)(! Parser_functions.rewrite_rules)) run.frame in
         show_verbose_action action run;
         let npr = next_partial_run run action ext_thread.thread p l new_frame ext_thread.before_locs choices in
         (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
        Some (npr,l) 
       end
       else None
   | SeqP(Output(l,t),p) -> 
     if condition action l
     then begin
       let new_frame = Inputs.add_to_frame l (Rewriting.normalize (apply_subst_inputs t run.frame)(! Parser_functions.rewrite_rules)) run.frame in
       let npr = next_partial_run run action ext_thread.thread p l new_frame ext_thread.before_locs choices in
       (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
       show_verbose_action action run;
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

(** Given a partial_run select an action to execute and test this action on available threads of Q *)
(*let next_run partial_run : (partial_run list * location)= 
  let first_actions = first_actions_among partial_run.test.statement.dag partial_run.remaining_actions in
  let current_loc = 
    try LocationSet.choose first_actions 
    with
    Not_found -> 
      begin Printf.printf "No run on %s [%s] \n" (show_dag partial_run.test.statement.dag) (show_loc_set partial_run.remaining_actions); 
      assert false end
  in
  next_run_with_action current_loc partial_run*)
(*  let (new_runs,locs) = List.fold_left (fun (new_runs,locs) lp -> 
    match try_run partial_run current_loc lp with
    | None -> (new_runs,locs)
    | Some (npr,l) -> (npr ::  new_runs, LocationSet.add l locs)
    ) ([],LocationSet.empty) partial_run.qthreads in
  (new_runs, current_loc)*)



 
(*
let compatible constraints constraints_back locP locQ = 
  try locQ = Dag.find locP constraints.a
  with Not_found -> begin 
    try Dag.find locQ constraints_back.a  =  locP 
    with Not_found -> true end
          
let compatible_prun constraints constraints_back (prun : partial_run)=
  Dag.for_all (compatible constraints constraints_back) prun.corresp.a
  *)
    
let rec get_all_new_roots before after dag =
  if LocationSet.is_empty before then []
  else 
  let locset = last_actions_among dag before in
  LocationSet.fold (fun loc result -> 
    let before = LocationSet.remove loc before in
    let after = LocationSet.add loc after in
    List.concat [[(before,after)];(get_all_new_roots before after dag); result]) locset [] 
  

let rec next_solution solution =
  let pr = Solutions.min_elt solution.partial_runs_todo in  
  solution.partial_runs_todo <- Solutions.remove pr solution.partial_runs_todo;
  if !about_rare && pr.weird_assoc > 0 then
    Printf.printf "Running a weird association for %s\n" (show_raw_statement pr.test.statement);
  if LocationSet.is_empty pr.restrictions then begin
    let current_loc = List.hd pr.remaining_actions in
    try
      let (new_runs,new_loc) = next_run_with_action current_loc pr in 
      if !debug_execution && new_runs = [] then Printf.printf "No possible run from this trace \n"  ;
      List.iter (fun partial_run -> 
        (* if !debug_execution then Printf.printf "New p. run %s \n\n" (show_partial_run partial_run); *)
        if partial_run.remaining_actions = []
        then
          solution.possible_runs_todo <- Solutions.add partial_run solution.possible_runs_todo 
        else 
          solution.partial_runs_todo <- Solutions.add partial_run solution.partial_runs_todo 
      ) new_runs 
    with
    | LocPtoQ i -> Printf.printf "error loc_p_to_q %d while executing on %d %s \n %s \n constraints %s\n" 
      i current_loc.p (show_partial_run pr) (show_test pr.test)(show_correspondance pr.test.constraints); assert false
  end
  else
    (
    if not (is_empty_correspondance pr.test.constraints)
    then  (Printf.printf "error with test %s \nand %s\n" (show_test pr.test)(show_partial_run pr); assert false)
    (*Printf.printf "%s of %d \n" (show_loc_set pr.restrictions ) pr.test.id;*)
    else
    if !debug_execution || !about_rare
    then Printf.printf "A restricted run is being tested from %s \n which test is \n %s \n" (show_partial_run pr)(show_test pr.test) ;
    let par = match pr.parent with Some par -> par | _ -> assert false in
    let roots = get_all_new_roots pr.restrictions LocationSet.empty par.sol.restricted_dag in
    let new_dag = dag_with_one_action_at_end pr.restrictions pr.last_exe in
    let restr_dag = merge pr.sol.restricted_dag new_dag in
    pr.sol.restricted_dag <- restr_dag;  
    List.iter (
      fun (before,after) -> 
        if !debug_execution 
        then 
          Printf.printf "\n**** Starting the restriction for %s  < %d < %s ****\n%s\n" 
            (show_loc_set before) pr.last_exe.p (show_loc_set after)(show_dag pr.sol.restricted_dag);
        let new_dag = { rel = LocationSet.fold 
          (fun l dag -> Dag.add l (LocationSet.singleton pr.last_exe) dag) 
          after (dag_with_one_action_at_end before pr.last_exe).rel } in
        let restr_dag = merge pr.sol.restricted_dag new_dag in
        if not (List.exists (fun s -> 
            Dag.equal (fun x y -> LocationSet.equal x y) s.restricted_dag.rel restr_dag.rel) 
          (pr.test.solutions_done @ pr.test.solutions_todo )) 
        then (
          (*Printf.printf "%s\n" (show_dag restr_dag);
          List.iter (fun s -> Printf.printf "%s\n" (show_dag s.restricted_dag))(pr.test.solutions_done @ pr.test.solutions_todo )*)
          let sequence = dag_to_sequence restr_dag in
          let new_solution =
          { null_sol with 
            init_run = pr.sol.init_run;
            partial_runs_todo = Solutions.singleton pr.sol.init_run;
            sequence = sequence ;
            restricted_dag = restr_dag; 
          } in
          pr.test.solutions_todo <- new_solution :: pr.test.solutions_todo
        )
    )  roots 
    )
    
let check_recipes partial_run (b,r,r')=
  (*Printf.printf "checking %s = %s\n with %s\n" (show_term r)(show_term r')(show_correspondance partial_run.corresp);*)
  let r = apply_frame r partial_run in
  let r' = apply_frame r' partial_run in
  (*let r'' = Rewriting.normalize r (! Parser_functions.rewrite_rules) in
  let r''' = Rewriting.normalize r' (! Parser_functions.rewrite_rules) in
  Printf.printf "recipes %s and %s\n %s\n>> %s \n=? %s\n" 
    (show_term r)(show_term r')(Inputs.show_inputs partial_run.frame)(show_term r'')(show_term r''');*)
  Rewriting.equals_r r r' (! Parser_functions.rewrite_rules) 
  
let check_equalities run head =
  (EqualitiesSet.for_all (check_recipes run) head.equalities)
  
let remove_false_disequalities run head = 
  head.disequalities <- EqualitiesSet.filter (fun dis -> 
    let r = not (check_recipes run dis) in
    if r || not !about_rare then r else  (Printf.printf "A disequality has been removed in %s \n" (show_test_head head); false)
  ) head.disequalities
  
let check_identities run head = 
  check_equalities run head
  && (EqualitiesSet.for_all ( fun dis -> not (check_recipes run dis)) head.disequalities)
  
  
let rec find_possible_run reachable solution =
  if Solutions.is_empty solution.possible_runs_todo 
  then begin
      if (Solutions.is_empty solution.partial_runs_todo) 
      then reachable
      else begin 
        next_solution solution; 
        find_possible_run reachable solution 
      end
  end
  else begin
    let run =  Solutions.min_elt solution.possible_runs_todo in
    solution.possible_runs_todo <- Solutions.remove run solution.possible_runs_todo ;
    if check_identities run (get_test_head run.test.statement.head)
    then (
      if !debug_execution then Printf.printf "\nSelected execution: \n %s \n"(show_run run) ;
      solution.selected_run <- Some run;
      reachable )
    else (
      if !debug_execution then Printf.printf "\nSolution fails the tests: \n %s \n" (show_partial_run run) ;
      find_possible_run true solution )
  end
  
let find_possible_run solution =  find_possible_run false solution 
