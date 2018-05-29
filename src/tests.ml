open Util
open Types
open Dag
open Base
open Process
open Bijection
open Term
open Process_execution

(* from two statements (ie tests) generate the merge of these tests, like equation rule *)
let merge_tests (fa : raw_statement) (fb : raw_statement) =
  if ! debug_execution then Printf.printf "Try to merge: %s\n and %s\n" (show_raw_statement fa)(show_raw_statement fb);
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
      let fa_head_equal = 
        match fa.head with
        | Tests(equal,diseq) -> equal
        | Identical(r,r') -> [(r,r')]
        | Knows(_)
        | Reach -> [] in
      let fb_head_equal = 
        match fb.head with
        | Tests(equal,diseq) -> equal
        | Identical(r,r') -> [(r,r')]
        | Knows(_)
        | Reach -> [] in  
    let r =
    List.map
      (fun sigm ->
          let sigma = Rewriting.pack sigma in
          if !debug_execution then Printf.printf "A merge has been found: %s\n%!" (show_substitution sigma);
          let result =
             let body =
               List.map (fun x ->
               {
               loc =  x.loc ; 
               recipe = Rewriting.apply_subst_term x.recipe sigma ;
               term = Rewriting.apply_subst_term x.term sigma ;
               marked = false }
                 )
                 (fa.body @ fb.body) 
             in
          {
           binder = sigma.binder ;
           nbvars = sigma.nbvars ;
           dag = merged_dag ;
           choices = merged_choice ;
           inputs = Inputs.merge sigma fa.inputs fb.inputs;
           recipes = Inputs.merge_recipes sigma fa.recipes fb.recipes;
           head = Tests( List.map 
             (fun (r,rp) -> 
               Rewriting.apply_subst_term r sigma,Rewriting.apply_subst_term rp sigma)
             (Util.unique(fa_head_equal @ fb_head_equal)), []); (* TODO > diseq *)
           body = body }
           in
           (*if !debug_execution then Format.printf "The merged test: %s\n"
               (show_raw_statement result);*)
           let result = Horn.simplify_statement result in
           if !debug_execution then Format.printf "New merged test: %s\n"
               (show_raw_statement result);
           result)
        sigmas
    in
    fa.binder:= New;
    fb.binder:= New;  
    r 

    exception Attack   

let get_lst_of_test test =
  match test with 
  Tests(equal,diseq) -> equal
  | Identical(r,r') -> [(r,r')]
  | _ -> []

let map_dag dag corresp =
  {rel = Dag.fold (fun key lset ndag -> Dag.add (loc_p_to_q key corresp) (LocationSet.map (fun l -> loc_p_to_q l corresp) lset) ndag) dag.rel (Dag.empty)}

let transpose_inputs (recipes : Inputs.inputs) (run : partial_run) : Inputs.inputs =
  {i = Dag.fold (fun key recipe ninputs -> Dag.add (loc_p_to_q key run.corresp) (apply_frame recipe run) ninputs) recipes.i (Dag.empty)}
  
let conj run =
  let stP = run.test.statement in
  let identity_sigma = Rewriting.identity_subst stP.nbvars in
  (*let binder = identity_sigma.binder in*)
  stP.binder := Master;
  let st = Horn.apply_subst_statement stP identity_sigma in
  {
  binder = st.binder ;
  nbvars = st.nbvars ;
  dag = map_dag st.dag run.corresp;
  inputs =  transpose_inputs st.recipes run  ;
  choices = run.choices ;
  head = st.head ;
  body = st.body ;
  recipes = st.recipes ; 
  }

  
let add_to_completion (run : partial_run) (completion : completion) = 
  if !about_completion then Printf.printf "Try comp %s \n with %s\n" (show_run run) (show_completion completion);
  let exception NonBij in
  try
  let corr = { a = Dag.union (fun locP x y -> if x = y then Some x else raise NonBij) run.corresp.a completion.corresp_c.a } in
  let corr_back = { a = Dag.union (fun locQ x y -> if x = y then Some x else raise NonBij) run.corresp_back.a completion.corresp_back_c.a } in
  let missing = LocationSet.filter (fun loc -> try ignore (Dag.find loc corr.a); false with Not_found -> true) completion.missing_actions in
  let sts = merge_tests run.test.statement completion.st_c in
  List.iter (fun st -> 
    if LocationSet.is_empty missing then Printf.printf "Todo add test %s\n" (show_raw_statement st)(*todo*)
    else
    register_completion (other run.test.process_name){
      initial_statement = completion.initial_statement;
      st_c = st;
      corresp_c = corr;
      corresp_back_c = corr_back;
      missing_actions = missing ;
      most_general_completions = [];
    }
  ) sts
  with 
  | NonBij -> ()
      
let negate_statement (st : raw_statement) =
  match st.head with
  | Unreachable -> 
    {st with head = Tests([],[])}
  | Identical(s,t) -> {st with head = Tests([],[(s,t)])}

  
let statement_to_completion st =
  {
  initial_statement = st ;
  st_c = st ;
  corresp_c = empty_correspondance ;
  corresp_back_c = empty_correspondance ;
  missing_actions = locations_of_dag st.dag ;
  most_general_completions = [];
  }

let statement_to_tests process_name origin (statement : raw_statement) otherProcess =
  let statement = match origin with Initial _ -> same_term_same_recipe statement | _-> statement in
  let nb = Dag.cardinal statement.dag.rel in
  if nb != 0 
  then
     let init = init_run process_name statement otherProcess in 
     (* init is a partial function to allow cycle reference between test and partial run *)
     push statement process_name origin init 
   
let rec statements_to_tests process_name (statement : statement) otherProcess =
  statement_to_tests process_name (Initial(statement)) (statement.st) otherProcess;
  match statement.st.head with
  | Identical _ -> register_completion process_name (statement_to_completion (negate_statement statement.st)) (* Identical don't have children *)
  | _ -> List.iter (fun st -> statements_to_tests process_name st otherProcess) statement.children
    
  

(* Create new tests from prun which is in conflict with all tests in runset *)
let add_merged_tests sol =
  let (prun,runset)=sol.execution,sol.conflicts in
  if !debug_tests && not (RunSet.is_empty runset) 
  then Printf.printf "Conflicts on %s\n with " (show_loc_set sol.conflicts_loc); 
  RunSet.iter (fun par ->
    if !debug_tests 
    then Printf.printf "[%d] " (par.test.id); 
    if prun.test.process_name = par.test.process_name 
    then
      
      if ((Inputs.contains prun.test.statement.inputs par.test.statement.inputs) &&  (Util.list_diff (get_lst_of_test par.test.statement.head)(get_lst_of_test prun.test.statement.head) =[]))
      || ((Inputs.contains par.test.statement.inputs prun.test.statement.inputs) &&  (Util.list_diff (get_lst_of_test prun.test.statement.head)(get_lst_of_test par.test.statement.head) =[]))
      then ()  else
      begin
        let merged_statements =   merge_tests prun.test.statement par.test.statement in (* only one without xor *)
        List.iter (fun raw_st -> 
          if false && !debug_tests then Printf.printf "New test %s \n" (show_raw_statement raw_st);
          statement_to_tests prun.test.process_name (Composed(prun,par)) raw_st (proc (other prun.test.process_name))
          ) merged_statements
      end
    (* else begin
      if !debug_execution 
      then Printf.printf "\n TODO : coarse equivalence not enough\n" ; 
      (*raise Attack*)()
   end *)
  ) runset;
  if !debug_tests  then Printf.printf "\n"
  
let rec register_solution solution sol =
  let pr = sol.execution in
  let test = pr.test in
  let cardi = IntegerSet.cardinal test.from in
  if ! debug_tests then if !use_xml then Printf.printf "%s\n" (show_correspondance pr.corresp) else Printf.printf "Success of test %d: %s \n\n" test.id (show_correspondance pr.corresp);
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
    add_merged_tests sol;
    Bijection.add_run solution pr;
    solution.partitions <- [pr];
    solution.movable <- cardi;
    (*consider_disequalities pr;*)
  end
  
and find_compatible_run_init constraints constraints_back run  =
  if  (compatible_prun constraints constraints_back run) then true
  else
  let solution = try Tests.find run.test bijection.registered_tests 
    with Not_found -> Printf.eprintf "error  test %d not found\n%!" run.test.id; raise Not_found in
  match 
    try Some (Solutions.choose (Solutions.filter (fun sol -> 
      compatible_prun constraints constraints_back sol.execution) solution.possible_runs))
    with 
    | Not_found ->
      let (prio, not_prio) = List.partition (compatible_prun constraints constraints_back ) (solution.partial_runs_todo @ solution.partial_runs_priority_todo) in
      solution.partial_runs_todo <- not_prio ;
      solution.partial_runs_priority_todo <- prio ;
      run.test.constraints <- constraints ;
      run.test.constraints_back <- constraints_back ;
      find_compatible_run solution
  with
  | Some sol -> 
      Bijection.remove_run run; 
      register_solution solution sol;
      if !debug_tests then Printf.printf "Solution %s replaced by %s \n" (show_run run) (show_run sol.execution);
      true
  | None -> false




      
let rec compute_new_completions process_name  =
  match if process_name = P then bijection.runs_for_completions_P else bijection.runs_for_completions_Q with
  | [] -> ()
  | run :: lst -> Printf.printf "xxx %s\n" (show_run run);
    if process_name = P then bijection.runs_for_completions_P <- lst else bijection.runs_for_completions_Q <- lst ;
    List.iter (fun (l,_) ->
    List.iter (fun completion -> add_to_completion run completion) 
      (try Dag.find l (if process_name = P then bijection.to_be_completed_P else bijection.to_be_completed_Q) with Not_found -> []))
    (Dag.bindings run.dag.rel);
    compute_new_completions process_name
  

let base_to_tests process_name base process other_process = 
  (*List.iter (fun st -> 
    statement_to_tests process_name (Initial(st)) st.st other_process;
    register_completion (statement_to_completion (negate_statement st.st))
    ) base.identity_solved;
  List.iter (fun st -> 
    statement_to_tests process_name (Initial(st)) st.st other_process
    ) base.reachable_solved;*)
  List.iter (fun st -> 
    register_completion process_name (statement_to_completion (negate_statement st.st))
    ) base.unreachable_solved;
  statements_to_tests process_name base.rid_solved other_process 

let equivalence p q =
  Printf.printf (if !use_xml then "<?xml-stylesheet type='text/css' href='style.css' ?><all>" else "Saturating P\n");
  let (locP,satP) = Horn.saturate p in
  if  !Util.about_saturation then
    Printf.printf (if !use_xml then "%s" else "Saturation of P:\n %s\n") (Base.show_kb satP);
  if not !use_xml then Printf.printf "Saturating Q:\n%!";
   let (locQ,satQ) = Horn.saturate q in
  if  !Util.about_saturation then
    Printf.printf (if !use_xml then "%s" else "Saturation of Q:\n %s\n") (Base.show_kb satQ);
  let processP = (CallP({p = locP;io=Call;name="main";parent=None},
    p,Array.make 0 zero,Array.make 0 null_chan)) in
  let processQ = (CallP({p = locQ;io=Call;name="main";parent=None}, 
    q,Array.make 0 zero,Array.make 0 null_chan)) in 
  bijection.p <- processP ;
  bijection.q <- processQ ;
  bijection.satP <- satP ;
  bijection.satQ <- satQ ;
  Printf.printf "Building tests\n%!";
  base_to_tests P satP processP processQ ;
  base_to_tests Q satQ processQ processP ; 
  Printf.printf "Completions\n%!";
  if !about_completion then
    begin show_all_completions bijection.to_be_completed_P;
    Printf.printf "Q\n";
    show_all_completions bijection.to_be_completed_Q end ;
  Bijection.reorder_tests () ;
  Printf.printf "Testing %d tests\n%!" (Tests.cardinal bijection.tests);
  try
    while not (Tests.is_empty bijection.tests) do
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
          with Not_found -> Printf.printf "Error on main \n%!"; raise Not_found end
       (* | Refined(run,st) -> let sol = Tests.find run.test bijection.registered_tests in
          List.mem run sol.partitions *)
        | Completion -> assert false 
      in
      if valid then begin
        if !debug_tests then Printf.printf (if !use_xml then "<opentest>%s" else "Open %s\n%!") (show_test test);
        match find_possible_run solution with 
        | None ->  Printf.printf "Failure to pass %s\n" (show_test test);
            List.iter (fun (pr : partial_run) -> Printf.printf "%s\n" (show_correspondance pr.corresp)) solution.partial_runs;
          raise Attack;
        | Some sol -> register_solution solution sol; if !debug_tests && !use_xml then Printf.printf "</opentest>"
      end
    done ;
    if !about_completion then 
      Printf.printf "Actualization of completions (P: %d runs, Q: %d runs) \n" (List.length bijection.runs_for_completions_P)(List.length bijection.runs_for_completions_Q);
    compute_new_completions P ; 
    compute_new_completions Q ; 
    done ;
    if !about_execution then Bijection.show_bijection();
    Printf.printf "P and Q are coarse trace equivalent. \n" ;
    if ! use_xml then Printf.printf "</all>"
  with
  | Attack -> begin 
  if !about_execution then Bijection.show_bijection();
  Printf.printf "P and Q are not trace equivalent. \n" 
  end
