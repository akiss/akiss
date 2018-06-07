open Util
open Types
open Dag
open Base
open Process
open Bijection
open Term
open Process_execution

let recipes_of_head head = 
  match head with
  | Tests(equal,diseq) -> equal , diseq
  | Identical(r,r') -> EqualitiesSet.singleton (r,r'),EqualitiesSet.empty
  | Knows(_)
  | Reach -> EqualitiesSet.empty,EqualitiesSet.empty
  | Unreachable -> assert false


let clean_unused_variables st = 
  if st.nbvars = 0 then st
  else
  let fake_fun = Some zero in
  let sigma_repl = Array.make st.nbvars fake_fun in
  let term_to_recipe = Array.make st.nbvars None in
  let sigma = (sigma_repl, Array.make 0 fake_fun) in
  st.binder := Master;
  let body = List.filter (fun k -> 
    match k.recipe, k.term with
    | Var(r),Var(t) ->
      if sigma_repl.(t.n) = fake_fun 
      then begin
        sigma_repl.(t.n) <- None ;
        if sigma_repl.(r.n) = fake_fun
        then begin
          sigma_repl.(r.n) <- None;
          term_to_recipe.(t.n) <- Some k.recipe;
          true end
        else
          assert false
      end
      else
        if sigma_repl.(r.n) = fake_fun 
        then begin sigma_repl.(r.n) <- term_to_recipe.(t.n); false end
        else false
    | _ -> assert false
  ) st.body in
  (*Printf.printf "Subst %s \n%!" (Rewriting.show_subst_array sigma_repl);*)
  let sigma = Rewriting.pack sigma in
  Horn.apply_subst_statement { st with body=body;} sigma
  
(* from two statements (ie tests) generate the merge of these tests, like equation rule *)
let merge_tests (fa : raw_statement) (fb : raw_statement) =
  if ! debug_merge then Printf.printf "Try to merge: %s\n and %s\n" (show_raw_statement fa)(show_raw_statement fb);
  match Inputs.merge_choices fa.choices fb.choices with
    None -> []
  | Some merged_choice ->
  let merged_dag = merge fa.dag fb.dag in
  if is_cyclic merged_dag 
  then [] 
  else
    let sigma = ((Array.make fa.nbvars None),(Array.make fb.nbvars None)) in
    fa.binder:= Master;
    fb.binder:= Slave;
    let sigmas = Inputs.csu sigma fa.inputs fb.inputs in
    if sigmas = [] 
    then []
    else 
    let fa_head_equal, fa_head_diseq = recipes_of_head fa.head in
    let fb_head_equal, fb_head_diseq = recipes_of_head fb.head in  
    let r =
    List.map
      (fun sigm ->
          let sigma = Rewriting.pack sigma in
          if  !debug_merge then Printf.printf "A merge has been found: %s\n%!" (show_substitution sigma);
          let result =
             let body =
               List.fold_left (fun bod x ->
               let t = Rewriting.apply_subst_term x.term sigma in
               match t with
               | Var(_) -> 
               {
               loc =  x.loc ; 
               recipe = Rewriting.apply_subst_term x.recipe sigma ;
               term = t ;
               marked = false } :: bod
               | _ -> bod
                 ) []
                 (fa.body @ fb.body) 
             in
          {
           binder = sigma.binder ;
           nbvars = sigma.nbvars ;
           dag = merged_dag ;
           choices = merged_choice ;
           inputs = Inputs.merge sigma fa.inputs fb.inputs;
           recipes = Inputs.merge_recipes sigma fa.recipes fb.recipes;
           head = Tests( EqualitiesSet.map 
             (fun (r,rp) -> 
               Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term rp sigma)
             (EqualitiesSet.union fa_head_equal fb_head_equal),
             EqualitiesSet.map 
             (fun (r,rp) -> 
               Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term rp sigma)
             (EqualitiesSet.union fa_head_diseq fb_head_diseq)); 
           body = body }
           in
           (*if true then Format.printf "The merged test: %s\n"
               (show_raw_statement result);*)
           let result = clean_unused_variables result in
           if !debug_merge then Format.printf "New merged test: %s\n%!"
               (show_raw_statement result);
           result)
        sigmas
    in
    fa.binder:= New;
    fb.binder:= New;  
    r 

    exception Attack   

let actual_test process_name (st : raw_statement) =
  let corr = {a = Dag.mapi (fun k _ -> k) st.dag.rel} in
  let test = {
    nb_actions = 0;
    new_actions = 0;
    process_name = process_name;
    statement = st;
    origin = Completion;(*irrelevant*)
    id = - 7 ;
    from = IntegerSet.empty;
    constraints = corr;
    constraints_back = corr;
  } in
  let run_init = init_run process_name st (proc process_name) test in
  let solution =
  { empty_solution with
       partial_runs = [run_init] ;
       partial_runs_todo = Solutions.singleton run_init;
       (*possible_restricted_runs = [];
       possible_runs = Solutions.empty;
       possible_runs_todo = Solutions.empty;
       failed_partial_run = [];
       failed_run = [];
       partitions = [] ;
       movable = 0 ;*)
     } in
  match find_possible_run solution with
    None ->  false 
  | Some sol -> true

    
let map_dag dag corresp =
  {rel = Dag.fold (fun key lset ndag -> Dag.add (loc_p_to_q key corresp) (LocationSet.map (fun l -> loc_p_to_q l corresp) lset) ndag) dag.rel (Dag.empty)}

let apply_frame_2 sigma recipe run =
  Rewriting.apply_subst_term (apply_frame recipe run) sigma
  
let transpose_inputs sigma (recipes : Inputs.inputs) (run : partial_run) : Inputs.inputs =
  {i = Dag.fold (fun key recipe ninputs -> Dag.add (loc_p_to_q key run.corresp) (apply_frame_2 sigma recipe run) ninputs) recipes.i (Dag.empty)}

let rec transpose_recipe recipe (prun : partial_run) =
  match recipe with
    | Fun({ id=Frame(l)}, []) ->  Fun({ id=Frame(Bijection.loc_p_to_q l prun.corresp);has_variables=false }, []) 
    | Fun({ id=Input(l)}, []) -> assert false
    | Fun(f, args) -> Fun(f, List.map (fun x -> transpose_recipe x prun) args)
    | Var(x) -> Var(x) 
  
let transpose_recipes (recipes : Inputs.inputs) (run : partial_run) : Inputs.inputs =
  {i = Dag.fold (fun key recipe nrec -> Dag.add (loc_p_to_q key run.corresp) (transpose_recipe recipe run) nrec) recipes.i (Dag.empty)}

(* take a run and provide a statement which is the test of the run transposed in the other process *)  
let conj run =
  let stP = run.test.statement in
  let identity_sigma = Rewriting.identity_subst stP.nbvars in
  (*let binder = identity_sigma.binder in*)
  stP.binder := Master;
  let st = Horn.apply_subst_statement stP identity_sigma in
  let r = 
  {
  binder = st.binder ;
  nbvars = st.nbvars ;
  dag = map_dag st.dag run.corresp;
  inputs =  transpose_inputs identity_sigma st.recipes run  ;
  choices = run.choices ;
  head = (let eq, diseq = recipes_of_head st.head in Tests(
    EqualitiesSet.map (fun (s,t) -> (transpose_recipe s run,transpose_recipe t run)) eq,
    EqualitiesSet.map (fun (s,t) -> (transpose_recipe s run,transpose_recipe t run)) diseq));
  body = List.map (fun ba -> {
    loc = (match ba.loc with None -> None | Some l -> Some (loc_p_to_q l run.corresp));
    recipe = transpose_recipe ba.recipe run;
    term = apply_frame_2 identity_sigma ba.recipe run;
    marked = false;
    }) st.body ;
  recipes = transpose_recipes st.recipes run ; 
  } in
  stP.binder := New;
  r
  
let statement_to_tests process_name origin (statement : raw_statement) otherProcess =
  let statement = match origin with Initial _ -> same_term_same_recipe statement | _-> statement in
  let nb = Dag.cardinal statement.dag.rel in
  if nb != 0 && actual_test process_name statement
  then
     let init = init_run process_name statement otherProcess in 
     (* init is a partial function to allow cycle reference between test and partial run *)
     push statement process_name origin init 
   

let completion_to_test comp =
  let test = {
    nb_actions = 0;
    new_actions = 0;
    process_name = comp.from_base;
    statement = comp.st_c;
    origin = Completion;
    id = - 6 ;
    from = IntegerSet.empty;
    constraints = comp.corresp_back_c;
    constraints_back = comp.corresp_c;
  } in
  let run_init = init_run comp.from_base comp.st_c (proc (other comp.from_base )) test in
  let solution =
  { empty_solution with 
       partial_runs = [run_init] ;
       partial_runs_todo = Solutions.singleton run_init;
       (* possible_restricted_runs = [];
       possible_runs = Solutions.empty;
       possible_runs_todo = Solutions.empty;
       failed_partial_run = [];
       failed_run = [];
       partitions = [] ;
       movable = 0 ; *)
     } in
  match find_possible_run solution with
    None -> if !about_completion then Printf.printf "The completion is not executable \n" 
  | Some [pr] -> 
    if !about_completion then Printf.printf "Execution of the completion  %s\n" (show_run pr);
    statement_to_tests (other comp.from_base) Completion (conj pr)(proc (comp.from_base ))
  | Some _ -> assert false
  
let add_to_completion (run : partial_run) (completion : completion) = 
  if !about_completion then Printf.printf "Try completing a completion between \n run %s \n whose test is %s \n and partial completion %s\n" (show_run run)(show_raw_statement run.test.statement) (show_completion completion);
  let exception NonBij in
  try
  let corr = { a = Dag.union (fun locP x y -> if x = y then Some x else raise NonBij) run.corresp.a completion.corresp_c.a } in
  let corr_back = { a = Dag.union (fun locQ x y -> if x = y then Some x else raise NonBij) run.corresp_back.a completion.corresp_back_c.a } in
  let missing = LocationSet.filter (fun loc -> try ignore (Dag.find loc corr_back.a); false with Not_found -> true) completion.missing_actions in
  let conjrun = conj run in
  if !about_completion then Printf.printf "Conj = %s " (show_raw_statement conjrun);
  let sts = merge_tests conjrun completion.st_c in
  List.iter (fun st -> 
    let eq, diseq = recipes_of_head st.head in
    if EqualitiesSet.is_empty (EqualitiesSet.inter eq diseq) then begin
    let new_comp = {
        from_base = completion.from_base;
        initial_statement = completion.initial_statement;
        st_c = st;
        corresp_c = corr;
        corresp_back_c = corr_back;
        missing_actions = missing ;
        selected_action = pick_last_or_null st.dag missing ;
        most_general_completions = [];
      } in
    register_completion new_comp ;  
    if LocationSet.is_empty missing 
    then begin
      if !about_completion then Printf.printf "Completion complete, checking test %s\n" (show_raw_statement st)(*todo*);
      completion_to_test new_comp
    end
    else begin
      if !about_completion then Printf.printf "Adding partial completion %s\n" (show_raw_statement st);
      if completion.from_base = P then 
        bijection.todo_completion_P <- new_comp :: bijection.todo_completion_P
      else
        bijection.todo_completion_Q <- new_comp :: bijection.todo_completion_Q
    end
    end
    else
    if !about_completion then Printf.printf "Absurd completion\n";
  ) sts
  with 
  | NonBij -> ()
      
let negate_statement (st : raw_statement) =
  match st.head with
  | Unreachable -> 
    {st with head = Tests(EqualitiesSet.empty,EqualitiesSet.empty)}
  | Identical(s,t) -> {st with head = Tests(EqualitiesSet.empty,EqualitiesSet.singleton (s,t))}
  | _ -> assert false

  
let statement_to_completion process_name (st : raw_statement) =
  let locs = locations_of_dag st.dag in 
  {
    from_base = process_name ;
    initial_statement = st ;
    st_c = st ;
    corresp_c = empty_correspondance ;
    corresp_back_c = empty_correspondance ;
    missing_actions = locs ;
    selected_action = pick_last_or_null st.dag locs ;
    most_general_completions = [];
  }

(* From solved statements create tests. 
Opti: when children are identical with same world merge them with the reach parent to reduce number of tests *)  
let rec statements_to_tests process_name (statement : statement) otherProcess =
   match statement.st.head with
  | Identical _ -> 
    statement_to_tests process_name (Initial(statement)) (statement.st) otherProcess;
    register_completion (statement_to_completion process_name (negate_statement statement.st)) (* Identical don't have children *)
  | _ -> let new_eq = List.fold_left 
    (fun new_eq st -> let is_identical = match st.st.head with Identical _ -> true | _ -> false in
      if is_identical && (st.st.inputs,st.st.dag,st.st.choices,st.st.body) = (statement.st.inputs,statement.st.dag,statement.st.choices,statement.st.body) 
      then begin
        match st.st.head with 
        Identical (s,t) -> 
          register_completion (statement_to_completion process_name (negate_statement st.st));
          EqualitiesSet.add (s,t) new_eq
        | _ -> assert false end
      else begin
        statements_to_tests process_name st otherProcess; 
        new_eq end)
    (EqualitiesSet.empty) statement.children in
    statement_to_tests process_name (Initial(statement)) {statement.st with head = Tests(new_eq,EqualitiesSet.empty)} otherProcess
    
  

(* Create new tests from prun which is in conflict with all tests in runset *)
let add_merged_tests prun =
  (* let (prun,runset)=sol.execution,sol.conflicts in *)
  let runset = Bijection.compatible prun in 
  if false && !debug_tests && not (RunSet.is_empty runset) 
  then Printf.printf "Conflicts with " ; 
  RunSet.iter (fun par ->
    if false && !debug_tests 
    then Printf.printf "[%d] " (par.test.id); 
    if prun.test.process_name = par.test.process_name 
    then
      let eq_par, diseq_par = recipes_of_head par.test.statement.head in
      let eq_prun, diseq_prun = recipes_of_head prun.test.statement.head in
      if ((Inputs.contains prun.test.statement.inputs par.test.statement.inputs) 
        &&  (EqualitiesSet.subset (eq_par)(eq_prun)) 
        &&  (EqualitiesSet.subset (eq_par)(eq_prun)))
      || ((Inputs.contains par.test.statement.inputs prun.test.statement.inputs) 
        &&  (EqualitiesSet.subset (diseq_prun)(diseq_par)) 
        && (EqualitiesSet.subset (diseq_prun)(diseq_par)))
      then (if false && !debug_tests then Printf.printf "s,")  else
      begin
        let merged_statements =   merge_tests prun.test.statement par.test.statement in (* only one without xor *)
        if false && merged_statements = [] then (if !debug_tests then Printf.printf "i,")
        else
        List.iter (fun raw_st -> 
          if false && !debug_tests then Printf.printf "T,";
          statement_to_tests prun.test.process_name (Composed(prun,par)) raw_st (proc (other prun.test.process_name))
          ) merged_statements
      end
     else begin
      if false && !debug_tests  
      then Printf.printf "P/Q," ; 
      (*raise Attack*)()
      end 
  ) runset;
  if false && !debug_tests  then Printf.printf "\n"
  
let rec register_solution solution (sol : partial_run list) =
  match sol with
  | [] -> assert false
  | [pr] ->  begin
    let test = pr.test in
    let cardi = IntegerSet.cardinal test.from in
    if ! debug_tests then 
      if !use_xml 
      then Printf.printf "%s\n" (show_correspondance pr.corresp) 
      else Printf.printf "Success of test %d: %s \n\n" test.id (show_correspondance pr.corresp);
    if solution.movable >= cardi 
    || match test.origin with
      | Composed (run1,run2) -> 
          if find_compatible_run_init pr.corresp pr.corresp_back run1 &&
          find_compatible_run_init pr.corresp pr.corresp_back run2 
          then begin if ! debug_tests then Printf.printf "The initial tests have been changed \n"; false end
          (* ne pas ajouter le test... *)
          else begin if ! debug_tests then Printf.printf "Actual conflict \n"; true end
      | _ -> true
    then begin
      add_merged_tests pr;
      Bijection.add_run solution pr;
      solution.partitions <- [pr];
      solution.movable <- cardi
    end
  end 
  | pr1 :: _  -> 
    if ! debug_tests then  Printf.printf "Solution made of several runs\n";
    solution.partitions <- sol;
    List.iter (fun pr -> 
      add_merged_tests pr;
      Bijection.add_run solution pr;
      solution.movable <- 100000) sol
  
and find_compatible_run_init constraints constraints_back run  =
  if  (compatible_prun constraints constraints_back run) then true
  else
  let solution = try Tests.find run.test bijection.registered_tests 
    with Not_found -> Printf.eprintf "error test %d not found\n%!" run.test.id; raise Not_found in
  match 
    try Some [(Solutions.choose (Solutions.filter (fun sol -> 
      compatible_prun constraints constraints_back sol) solution.possible_runs))]
    with 
    | Not_found ->
      solution.partial_runs_todo <- Solutions.filter (fun x -> compatible_prun constraints constraints_back x) (solution.partial_runs_todo);
      run.test.constraints <- constraints ;
      run.test.constraints_back <- constraints_back ;
      find_possible_run solution
  with
  | Some [sol] -> 
      Bijection.remove_run run; 
      register_solution solution [sol];
      if !debug_tests then Printf.printf "Solution %s replaced by %s \n" (show_run run) (show_run sol);
      true
  | None -> false
  | Some _ -> assert false



(* Compute the completions from the base of process_name *)      
let rec compute_new_completions process_name  =
  match if process_name = P then bijection.runs_for_completions_Q else bijection.runs_for_completions_P with
  (* First match all run with all completions *)
  | run :: lst -> 
    if !about_completion then Printf.printf "\nChecking if run can complete a completion %s\n" (show_run run);
    if process_name = P then bijection.runs_for_completions_Q <- lst else bijection.runs_for_completions_P <- lst ;
    List.iter (fun (_,l) ->
    List.iter (fun completion -> add_to_completion run completion) 
      (try Dag.find l (if process_name = P then bijection.partial_completions_P else bijection.partial_completions_Q) with Not_found -> []))
    (Dag.bindings run.corresp.a);
    compute_new_completions process_name
  (* Then for all new partial completion just created match them with all runs *)  
  | [] -> 
    if !about_completion then (Printf.printf "\nCompleting new completions\n "; show_bijection());
    while (if process_name = P then bijection.todo_completion_P else bijection.todo_completion_Q) != [] do
      let todo_completion = if process_name = P then bijection.todo_completion_P else bijection.todo_completion_Q in
      let comp :: lst = todo_completion in 
      if !about_completion then Printf.printf "Remains %d completions, processing %s \n" (List.length todo_completion)(show_completion comp);
      if process_name = P then bijection.todo_completion_P <- lst else bijection.todo_completion_Q <- lst ;
      Dag.iter (fun locQ runset ->
        if !about_completion then Printf.printf "- at loc %d:\n" locQ.p;
        RunSet.iter (fun run -> 
          if run.test.process_name <> process_name 
          then add_to_completion run comp ) runset)
      (try Dag.find comp.selected_action (if process_name = P then bijection.indexP else bijection.indexQ) with Not_found -> Dag.empty)
    done
 

let base_to_tests process_name base process other_process = 
  (*List.iter (fun st -> 
    statement_to_tests process_name (Initial(st)) st.st other_process;
    register_completion (statement_to_completion (negate_statement st.st))
    ) base.identity_solved;
  List.iter (fun st -> 
    statement_to_tests process_name (Initial(st)) st.st other_process
    ) base.reachable_solved;*)
  List.iter (fun st -> 
    register_completion (statement_to_completion process_name (negate_statement st.st))
    ) base.unreachable_solved;
  statements_to_tests process_name base.rid_solved other_process 

let equivalence p q =
  Printf.printf (if !use_xml then "<?xml-stylesheet type='text/css' href='style.css' ?><all>" else "Saturating P\n");
  let (locP,satP) = Horn.saturate p in
  if  !about_saturation then
    Printf.printf (if !use_xml then "%s" else "Saturation of P:\n %s\n") (Base.show_kb satP);
  if not !use_xml then Printf.printf "Saturating Q:\n%!";
   let (locQ,satQ) = Horn.saturate q in
  if  !about_saturation then
    Printf.printf (if !use_xml then "%s" else "Saturation of Q:\n %s\n") (Base.show_kb satQ);
  let processP = (CallP({p = locP;io=Call;name="main";parent=None},
    p,Array.make 0 zero,Array.make 0 null_chan)) in
  let processQ = (CallP({p = locQ;io=Call;name="main";parent=None}, 
    q,Array.make 0 zero,Array.make 0 null_chan)) in 
  bijection.p <- processP ;
  bijection.q <- processQ ;
  bijection.satP <- satP ;
  bijection.satQ <- satQ ;
  if !about_progress then Printf.printf "Building tests\n%!";
  base_to_tests P satP processP processQ ;
  base_to_tests Q satQ processQ processP ; 
  if !about_completion then
    begin 
    Printf.printf "Completions of P\n%!";
    show_all_completions bijection.partial_completions_P;
    Printf.printf "Completions of Q\n";
    show_all_completions bijection.partial_completions_Q end ;
  Bijection.reorder_tests () ;
  try
    while not (Tests.is_empty bijection.tests) do
      if !about_progress then Printf.printf "Testing %d tests\n%!" (Tests.cardinal bijection.tests);
      while not (Tests.is_empty bijection.tests) do
        let (test, solution) = pop () in
        (* We check that the two tests to merge have not been replaced by a different mapping *)
        let valid = 
          match test.origin with
          | Initial _ -> true
          | Composed (run1,run2) -> begin try
            let sol1 = Tests.find run1.test bijection.registered_tests in
            let sol2 = Tests.find run2.test bijection.registered_tests in
            (List.mem run1 sol1.partitions) && (List.mem run2 sol2.partitions)
            with Not_found -> Printf.eprintf "Error on main \n%!"; raise Not_found end
        (* | Refined(run,st) -> let sol = Tests.find run.test bijection.registered_tests in
            List.mem run sol.partitions *)
          | Completion -> true 
        in
        if valid then begin
          if !debug_tests then Printf.printf (if !use_xml then "<opentest>%s" else "Open %s\n%!") (show_test test);
          (*if test.id = 335 then debug_execution := true ;*)
          match find_possible_run solution with 
          | None ->  Printf.printf "Failure to pass %s\n" (show_test test);
              (*List.iter (fun (pr : partial_run) -> Printf.printf "%s\n" (show_correspondance pr.corresp)) solution.partial_runs;*)
            raise Attack;
          | Some sol -> register_solution solution sol; if !debug_tests && !use_xml then Printf.printf "</opentest>"
        end
      done ;
    if !about_progress then 
      Printf.printf "\n\n __Actualization of completions of P (%d runs)__\n" (List.length bijection.runs_for_completions_Q);
    compute_new_completions P ; 
    if !about_progress then 
      Printf.printf "\n\n __Actualization of completions of Q (%d runs)__\n" (List.length bijection.runs_for_completions_P);
    compute_new_completions Q ; 
    Printf.printf "\n\n+++++ Starting a new cycle +++++\n\n";
    done ;
    if !about_bijection then Bijection.show_bijection();
    Printf.printf "P and Q are trace equivalent. \n" ;
    if ! use_xml then Printf.printf "</all>"
  with
  | Attack -> begin 
  if !about_bijection then Bijection.show_bijection();
  Printf.printf "P and Q are not trace equivalent. \n" 
  end
