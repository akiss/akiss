open Util
open Types
open Dag
open Base
open Process
open Bijection
open Bijection.Run
open Term
open Process_execution

let negate_statement (st : raw_statement) =
  match st.head with
  | Unreachable -> 
    {st with 
      head = Tests({
        head_binder = st.binder;
        equalities = EqualitiesSet.empty ; 
        disequalities = EqualitiesSet.empty})}
  | Identical(s,t) -> 
    {st with 
      head = Tests({
        head_binder = st.binder;
        equalities = EqualitiesSet.empty ; 
        disequalities = EqualitiesSet.singleton (s,t)})}
  | _ -> Printf.printf "negation of %s " (show_raw_statement st); assert false

  
let statement_to_completion process_name (st : raw_statement) =
  let locs = locations_of_dag st.dag in 
  {
    st_c = st ;
    corresp_c = empty_correspondance ;
    corresp_back_c = empty_correspondance ;
    core_corresp = [] ;
    missing_actions = locs ;
    selected_action = pick_last_or_null st.dag locs ;
    root = { 
      from_base = process_name ;
      initial_statement = st ;
      directory = Dag.empty ;};
    further_completions = [];
    generated_test = None;
  }
  

  (* This function canonize statements by replacing several recipes for the same term by one recipe
  and removing predicates in the body with a recipe in a later location
  The function return the substitution which has been used and the new statement *)
let same_term_same_recipe st =
  let sigma_repl = Array.make st.nbvars None in
  let sigma = (sigma_repl, Array.make 0 None) in
  st.binder := Master;
  if !debug_merge then Printf.printf "simplification of %s\n" (show_raw_statement st);
  let (useless,body) =
    List.partition
      (fun a ->
         let recipe_var = Term.unbox_var a.recipe in
         let t = a.term in
         try
         let is_better =  List.find 
           (fun a' -> let recipe_var' = Term.unbox_var a'.recipe in
              t = a'.term && not (is_before st.dag a.loc a'.loc) && recipe_var.n > recipe_var'.n
           ) st.body in
           let x = Term.unbox_var(is_better.recipe) in
           sigma_repl.(x.n) <- Some a.recipe ;
           a.loc = is_better.loc      
         with Not_found -> false
         )
       st.body
  in
  let body = List.sort_uniq (fun x y -> Pervasives.compare (x.loc,(unbox_var x.term).n) (y.loc,(unbox_var y.term).n)) body in
  if !debug_merge then
    List.iter (fun a -> Format.printf "Removed %s\n" (show_body_atom a)) useless ;
(*  if useless = [] then st 
  else *)
  let sigma = Rewriting.pack sigma in
  let r = apply_subst_statement { st with body = body; } sigma in
  (*st.binder := New;*)
  (sigma,r)
  

let rec recipe_with_earlier_messages dag some_loc recipe =
  match recipe with
  | Var(x) -> true (*Not that true*)
  | Fun({ id=Frame(l)}, []) -> is_before dag (Some l) some_loc
  | Fun({ id=Input(l)}, []) -> assert false
  | Fun(f, args) -> List.for_all (fun x -> recipe_with_earlier_messages dag some_loc x) args
  
let rec messages_of_recipes recipe =
  match recipe with
  | Var(x) -> LocationSet.empty (*Not that true*)
  | Fun({ id=Frame(l)}, []) -> LocationSet.singleton l 
  | Fun({ id=Input(l)}, []) -> assert false
  | Fun(f, args) -> List.fold_left (fun lset x -> LocationSet.union (messages_of_recipes x) lset) LocationSet.empty args

exception No_recipe
  
let best_recipe base st new_dag unsolved x =
  let Some l = x.loc in
  let my_loc = LocationSet.singleton l in
  let other_locs = List.fold_left (fun lset p -> if p.recipe = x.recipe then let Some l' = p.loc in LocationSet.add l' lset else lset) my_loc unsolved in
  if !debug_merge then Printf.printf "From loc %d other identical recipes : %s \n" l.p (show_loc_set other_locs);
  try 
    let r = 
    Horn.consequence {st with 
      head = Knows(x.recipe,x.term);
      dag = preceding_dag !new_dag l} base (! Parser_functions.rewrite_rules) in
    if other_locs <> my_loc then new_dag := merge !new_dag (dag_with_actions_at_end (messages_of_recipes r)  other_locs)  ;
    r
  with
  | Horn.Not_a_consequence -> 
    if !debug_merge then Printf.printf "No recipe...\n";
    if other_locs = my_loc then raise No_recipe
    else
      let r = Horn.consequence {st with 
        head = Knows(x.recipe,x.term);
        dag = expurge_dag_after !new_dag l} base (! Parser_functions.rewrite_rules) in
      new_dag := merge !new_dag (dag_with_one_action_at_end (messages_of_recipes r)  l)  ;
      r


let opti_find_recipe sigm merged_dag fa fb =
  let sigm' = Rewriting.copy_subst sigm in
  let exception Broken_Precedence in
  let fab_body = fa.body @ fb.body in
  try
  let sigma = Inputs.csu_recipes sigm' fa.recipes fb.recipes in
  match sigma with 
  | sigma :: _ -> begin
    let sigma = Rewriting.pack sigma in
    if  !debug_merge then Printf.printf "A merge has been found: %s\n%!" (show_substitution sigma);
    let body, unsolved =
      List.fold_left (fun (bod,unsolved) x ->
        let predi = {
          loc =  x.loc ; 
          recipe = Rewriting.apply_subst_term x.recipe sigma ;
          term = Rewriting.apply_subst_term x.term sigma ;
          marked = false 
        } in
        match predi.term with
        | Var(_) -> 
          predi :: bod, unsolved
        | _ -> begin
          match predi.recipe with 
          | Var(_) -> bod, predi :: unsolved
          | _ -> 
            if recipe_with_earlier_messages merged_dag predi.loc predi.recipe 
            then bod, unsolved
            else raise Broken_Precedence
          end
      ) ([],[]) fab_body  in
    (sigma,body,unsolved) end
  | _ -> assert false
  with
  | Broken_Precedence -> 
    if !debug_merge then Printf.printf "No simple recipes, entering safe mode\n";
    let sigma = Rewriting.pack sigm in 
    let body,useless = List.partition (fun x -> is_var x.term) 
      (List.map (fun x-> {x with recipe = Rewriting.apply_subst_term x.recipe sigma; term = Rewriting.apply_subst_term x.term sigma }) fab_body) in
    (sigma,body,useless)
            
(* from two statements (ie tests), the function generate the merge of these tests, like equation rule
 The function returns a list of posible merges with the substitution which has been used *)
let merge_tests process_name (fa : raw_statement) (fb : raw_statement) =
  if ! debug_merge then Printf.printf "Try to merge: %s\n and %s\n%!" (show_raw_statement fa)(show_raw_statement fb);
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
    then begin 
      fa.binder:= New;
      fb.binder:= New; 
      [] end
    else 
    let fa_head_equal, fa_head_diseq = recipes_of_head fa.head in
    let fb_head_equal, fb_head_diseq = recipes_of_head fb.head in  
    let r =
    List.fold_left
      (fun lst sigm ->
        let sigma , body , unsolved = opti_find_recipe sigm merged_dag fa fb in
        let st_without_recipes =
            {
            binder = sigma.binder ;
            nbvars = sigma.nbvars ;
            dag = merged_dag ;
            choices = merged_choice ;
            inputs = Inputs.merge sigma fa.inputs fb.inputs;
            recipes = Inputs.merge sigma fa.recipes fb.recipes;
            head = Tests({
              head_binder = sigma.binder ;
              equalities= EqualitiesSet.map (fun (r,rp) -> 
               Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term rp sigma)
                (EqualitiesSet.union fa_head_equal fb_head_equal);
              disequalities = EqualitiesSet.map (fun (r,rp) -> 
               Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term rp sigma)
                (EqualitiesSet.union fa_head_diseq fb_head_diseq)});
            body = body;
            involved_copies = BangSet.union fa.involved_copies fb.involved_copies}
        in
        sigma.binder := Master;
        let tau = (Array.make sigma.nbvars None) in
        if !debug_merge then Format.printf "The merged test without (all) recipes from subst %s:\n %s\nunsolved = %s %!"
            (show_substitution sigma)(show_raw_statement st_without_recipes)(show_atom_list unsolved);
        let new_dag = ref merged_dag in
        try
          List.iter (fun x ->  
          let n = (unbox_var x.recipe).n in
          let base = if process_name = P then bijection.satP else bijection.satQ in
          match tau.(n) with
          | None ->
            if !debug_merge then Printf.printf "Looking for a recipe in %s for %s\n" (show_which_process process_name)(show_term x.term);
                let recipe = best_recipe base st_without_recipes new_dag unsolved x (* try 
                  Horn.consequence {st_without_recipes with 
                    head = Knows(x.recipe,x.term);
                    dag = preceding_dag !new_dag l} base (! Parser_functions.rewrite_rules)
                  with
                  | Horn.Not_a_consequence -> 
                    let r = Horn.consequence {st_without_recipes with 
                      head = Knows(x.recipe,x.term);
                      dag = expurge_dag_after !new_dag l} base (! Parser_functions.rewrite_rules) in
                    new_dag := merge !new_dag (dag_with_one_action_at_end (messages_of_recipes r)  l)  ;
                    r *)
                in
                if !debug_merge then Printf.printf "recipe = %s\n" (show_term recipe);
                tau.(n) <- Some recipe (*;
                if not (recipe_with_earlier_messages merged_dag x.loc recipe)
                then failwith "Not implemented yet\n"*)
            | Some recipe -> 
                if not (recipe_with_earlier_messages !new_dag x.loc recipe)
                then failwith ("There is a bug with " ^ (show_term recipe))
              ) unsolved;
           let tau = Rewriting.pack (tau, Array.make 0 None) in
           let result = apply_subst_statement {st_without_recipes with dag = !new_dag} tau in
           if !debug_merge then Format.printf "The merged test: %s\n%!" (show_raw_statement result);
           let (sigm,result) = same_term_same_recipe result in
           if !debug_merge then Format.printf "New clean merged test: %s\n%!" (show_raw_statement result);
           let rho = Rewriting.compose sigma (Rewriting.compose_master tau sigm) in
           if !debug_merge then Format.printf "Final substitution rho: %s\n%!" (show_substitution rho);
           (rho,result) :: lst
           with
            No_recipe -> 
              if !debug_merge then Format.printf "No recipe found for some input aborting...\n"  ; 
              lst
        (*end 
        | _ -> assert false*))
       [] sigmas
    in
    fa.binder:= New;
    fb.binder:= New;  
    r 

   

(* This function returns false if the statement is not executable in his own processus
(due to disequalities) true otherwise *) 
let actual_test process_name (st : raw_statement) =
  let corr = {a = Dag.mapi (fun k _ -> k) st.dag.rel} in
  let test = { null_test with
    process_name = process_name;
    statement = st;
    constraints = corr;
    constraints_back = corr;
  } in
  let solution = init_sol process_name st (proc process_name) test in
  if !debug_execution then Printf.printf "\nChecking actual of %s \nwith dag = %s\n" (show_test test)(show_dag st.dag);
  match find_possible_run solution with
    None ->  false 
  | Some sol -> true

    
let map_dag dag corresp =
  {rel = Dag.fold (fun key lset ndag -> Dag.add (loc_p_to_q key corresp) (LocationSet.map (fun l -> loc_p_to_q l corresp) lset) ndag) dag.rel (Dag.empty)}

let apply_frame_2 sigma recipe run =
  Rewriting.normalize (Rewriting.apply_subst_term (apply_frame recipe run) sigma) (! Parser_functions.rewrite_rules)
  
let transpose_inputs sigma (recipes : Inputs.inputs) (run : partial_run) : Inputs.inputs =
  {i = Dag.fold (fun key recipe ninputs -> Dag.add (loc_p_to_q key run.corresp) (apply_frame_2 sigma recipe run) ninputs) recipes.i (Dag.empty)}

let rec transpose_recipe sigma recipe (prun : partial_run) =
  match recipe with
    | Fun({ id=Frame(l)}, []) ->  Fun({ id=Frame(Bijection.loc_p_to_q l prun.corresp);has_variables=false }, []) 
    | Fun({ id=Input(l)}, []) -> assert false
    | Fun(f, args) -> Fun(f, List.map (fun x -> transpose_recipe sigma x prun) args)
    | Var(x) -> Rewriting.apply_subst_term recipe sigma 
  
let transpose_recipes sigma (recipes : Inputs.inputs) (run : partial_run) : Inputs.inputs =
  {i = Dag.fold (fun key recipe nrec -> Dag.add (loc_p_to_q key run.corresp) (transpose_recipe sigma recipe run) nrec) recipes.i (Dag.empty)}

(* take a run and provide a statement which is the test of the run transposed in the other process *)  
let conj run =
  let stP = run.test.statement in
  let identity_sigma = Rewriting.identity_subst stP.nbvars in
  (*let binder = identity_sigma.binder in*)
  stP.binder := Master;
  let st = apply_subst_statement stP identity_sigma in
  let r = 
  {
  binder = st.binder ;
  nbvars = st.nbvars ;
  dag = map_dag st.dag run.corresp;
  inputs =  transpose_inputs identity_sigma st.recipes run  ;
  choices = run.choices ;
  head = (let eq, diseq = recipes_of_head st.head in Tests({
    head_binder = identity_sigma.binder ;
    equalities = EqualitiesSet.map (fun (s,t) -> (transpose_recipe identity_sigma s run,transpose_recipe identity_sigma t run)) eq;
    disequalities = EqualitiesSet.map (fun (s,t) -> (transpose_recipe  identity_sigma s run,transpose_recipe identity_sigma t run)) diseq}));
  body = List.map (fun ba -> {
    loc = (match ba.loc with None -> None | Some l -> Some (loc_p_to_q l run.corresp));
    recipe = transpose_recipe identity_sigma ba.recipe run;
    term = apply_frame_2 identity_sigma ba.recipe run;
    marked = false;
    }) st.body ;
  recipes = transpose_recipes identity_sigma st.recipes run ; 
  involved_copies = BangSet.empty ; (* TODO *)
  } in
  stP.binder := New;
  (identity_sigma,r)
  
let rec try_other_runs head solution =
  if Solutions.is_empty solution.possible_runs_todo then None
  else begin
    let pr =  Solutions.min_elt solution.possible_runs_todo in
    solution.possible_runs_todo <- Solutions.remove pr solution.possible_runs_todo ;
    if check_identities pr head then begin
      if !debug_execution then Printf.printf "New selected execution:\n %s\n"(show_run pr) ;
      solution.selected_run <- Some pr;
      Some pr end
    else
      try_other_runs head solution
  end

let rec add_identities_to_completions head process_name compl =
  let h = get_test_head (compl.st_c.head) in
  h.equalities <- EqualitiesSet.union h.equalities head.equalities;
  h.disequalities <- EqualitiesSet.union h.disequalities head.disequalities ;
  List.iter (fun (sigma,compl) -> add_identities_to_completions (apply_subst_test_head head sigma) process_name compl) compl.further_completions;
  match compl.generated_test with
  | None -> ()
  | Some (subst,test) -> complete_set_of_identities (apply_subst_test_head head subst) process_name test


and complete_set_of_identities head process_name old_test =
  let old_eq,old_diseq = recipes_of_head old_test.statement.head in
  let new_eq,new_diseq = head.equalities,head.disequalities in
  let diff_eq = EqualitiesSet.diff new_eq old_eq in
  let diff_diseq = EqualitiesSet.diff new_diseq old_diseq in
  if not( EqualitiesSet.is_empty diff_eq && EqualitiesSet.is_empty diff_diseq)
  then begin (* If the old test is more expressive: nothing to do *)
    let h = get_test_head old_test.statement.head in
    if !debug_merge then Printf.printf "upgraded with %s test\n %s\n" (show_test_head head)(show_raw_statement old_test.statement);
    h.equalities <- EqualitiesSet.union (diff_eq)(old_eq);
    h.disequalities <- EqualitiesSet.union (diff_diseq)(old_diseq) ;
    if !debug_merge then Printf.printf "to get %s\n"(show_raw_statement old_test.statement);
    try 
      List.iter 
        (fun sol ->
          let Some pr = sol.selected_run in
          if not (check_identities pr head) then
          begin
            Bijection.remove_run pr;
            sol.selected_run <- None ;
            match try_other_runs head sol with
            | Some pr -> 
              sol.selected_run <- Some pr;
              add_merged_tests pr;
              Bijection.add_run pr
            | None ->
              old_test.solutions_todo <- sol :: old_test.solutions_todo;
              find_set_of_runs old_test
          end ;
          let head' = {head with equalities=diff_eq;disequalities=diff_diseq} in
          List.iter (fun (status,sigma,derived_test) -> 
              head.head_binder := status;
              let tau = apply_subst_test_head head' sigma in
              head.head_binder := New;              
              complete_set_of_identities tau process_name derived_test) 
            pr.consequences;
          List.iter (fun (sigma,compl) -> add_identities_to_completions (apply_subst_test_head head' sigma) process_name compl) pr.completions
        ) old_test.solutions_done
    with
    Not_found -> () (* the old test is still waiting to be processed: nothing to do *)
  end

and statement_to_tests process_name origin (statement : raw_statement) otherProcess =
  (* let statement = match origin with Initial _ -> same_term_same_recipe statement | _-> statement in *)
  let nb = Dag.cardinal statement.dag.rel in
  if nb != 0 && actual_test process_name statement
  then begin
    let statement = canonize_statement statement in
    statement.binder := New;
    let hash_statement = raw_to_hash_test statement in
    try 
      let test = Hashtbl.find bijection.htable_st hash_statement in
      let sigma = Rewriting.merging_subst test.statement.nbvars test.statement.binder in
      let head_t = get_test_head statement.head in
      statement.binder := Master;
      if !debug_merge then 
        Printf.printf "Updating an existing test which is \n%s\nwith %s \n subst %s \n"
          (show_test test)(show_raw_statement statement)(show_substitution sigma);
      let head' = apply_subst_test_head head_t sigma in
      statement.binder := New ;
      complete_set_of_identities head' process_name test ;
      Some test
    with 
    Not_found -> 
      let init = init_sol process_name statement otherProcess in 
      (* init is a partial function to allow cycle reference between test and partial run *)
      let new_test = push statement process_name origin init in
      Hashtbl.add bijection.htable_st hash_statement new_test;
      Some new_test
  end
  else None
  

(* Create new tests from prun which is in conflict with all tests in runset *)
and add_merged_tests prun =
  (* let (prun,runset)=sol.execution,sol.conflicts in *)
  let runset = Bijection.compatible prun in 
  (* if false && !debug_tests && not (RunSet.is_empty runset) then Printf.printf "Conflicts with " ; *)
  RunSet.iter (fun par ->
  (*  if false && !debug_tests then Printf.printf "[%d] " (par.test.id); *)
    if prun.test.process_name = par.test.process_name 
    then
     (* let eq_par, diseq_par = recipes_of_head par.test.statement.head in
      let eq_prun, diseq_prun = recipes_of_head prun.test.statement.head in
      if ((Inputs.contains prun.test.statement.inputs par.test.statement.inputs) 
        &&  (EqualitiesSet.subset (eq_par)(eq_prun)) 
        &&  (EqualitiesSet.subset (eq_par)(eq_prun)))
      || ((Inputs.contains par.test.statement.inputs prun.test.statement.inputs) 
        &&  (EqualitiesSet.subset (diseq_prun)(diseq_par)) 
        && (EqualitiesSet.subset (diseq_prun)(diseq_par)))
      then (*if false && !debug_tests then Printf.printf "s,"*)()  else
      begin *)
        if !debug_merge then Printf.printf "Try merge between < %d + %d >" prun.test.id par.test.id; 
        let merged_statements = merge_tests prun.test.process_name 
          { prun.test.statement with dag = prun.sol.restricted_dag } 
          { par.test.statement with dag = par.sol.restricted_dag } in (* only one without xor *)
        (* if false && merged_statements = [] then (if !debug_tests then Printf.printf "i,")
        else *)
        List.iter (fun ((sigma : substitution),raw_st) -> 
          (*if false && !debug_tests then Printf.printf "T,";*)
          match statement_to_tests prun.test.process_name (Composed(prun,par)) raw_st (proc (other prun.test.process_name)) with
          | Some new_test ->
            prun.consequences <- (Master,sigma,new_test) :: prun.consequences;
            par.consequences <-  (Slave,sigma,new_test) :: par.consequences
          | None -> ()
        ) merged_statements
      (*end*)
  ) runset;
  (*if false && !debug_tests  then Printf.printf "\n"*)

and find_set_of_runs test =
  match test.solutions_todo with
  | [] -> if ! debug_tests then Printf.printf "Success of test %d\n" test.id 
  | sol :: queue -> 
    test.solutions_todo <- queue;
    match find_possible_run sol with
    | None -> raise (Bijection.Attack(test,sol))
    | Some pr -> 
      test.solutions_done <- sol :: test.solutions_done; 
      if ! debug_tests then Printf.printf "Execution of test %d: %s \n\n" test.id (show_correspondance pr.corresp);
      add_merged_tests pr;
      Bijection.add_run pr;
      find_set_of_runs test

let completion_to_test comp =
  let test = { null_test with
    process_name = comp.root.from_base;
    statement = comp.st_c;
    constraints = comp.corresp_back_c;
    constraints_back = comp.corresp_c;
  } in
  let solution = init_sol comp.root.from_base comp.st_c (proc (other comp.root.from_base )) test in
  match find_possible_run solution with
    None -> 
      if !about_completion then Printf.printf "The completion is not executable \n" 
  | Some pr -> 
    if !about_completion then Printf.printf "Execution of the completion  %s\n" (show_run pr);
    let sigma, conjrun = conj pr in 
    begin
    match statement_to_tests (other comp.root.from_base) (Completion) conjrun (proc (comp.root.from_base )) with
    | Some test ->
      comp.generated_test <- Some (sigma, test) 
    | None -> () end

let add_to_completion (run : partial_run) (completion : completion) = 
  if !about_completion then Printf.printf "Try completing a completion between \n run %s \n whose test is %s \n and partial completion %s\n" (show_run run)(show_raw_statement run.test.statement) (show_completion completion);
  let exception NonBij in
  try
  let corr = { a = Dag.union (fun locP x y -> if x = y then Some x else raise NonBij) run.corresp.a completion.corresp_c.a } in
  let corr_back = { a = Dag.union (fun locQ x y -> if x = y then Some x else raise NonBij) run.corresp_back.a completion.corresp_back_c.a } in
  let missing = LocationSet.filter (fun loc -> try ignore (Dag.find loc corr_back.a); false with Not_found -> true) completion.missing_actions in
  let tau, conjrun = conj run in
  if !about_completion then Printf.printf "Conj = %s " (show_raw_statement conjrun);
  if !debug_merge then Printf.printf "Merge run %d with comp %s\n" run.test.id (show_raw_statement completion.root.initial_statement);
  let sts = merge_tests completion.root.from_base conjrun completion.st_c in
  List.iter (fun (sigma,st) -> 
    let new_comp = {
        st_c = canonize_statement st;
        corresp_c = corr;
        corresp_back_c = corr_back;
        core_corresp = List.filter (fun (l,l') -> try ignore (Dag.find l completion.root.initial_statement.dag.rel); true with Not_found -> false) (Dag.bindings corr.a);
        missing_actions = missing ;
        selected_action = pick_last_or_null st.dag missing ;
        root = completion.root ;
        further_completions = [];
        generated_test = None;
      } in
    completion.further_completions <- (sigma,new_comp) :: completion.further_completions;
    run.completions <- (tau,new_comp) :: run.completions;
    if register_completion new_comp 
    then  begin
      if !about_completion then Printf.printf "Completion complete, checking test %s\n" (show_raw_statement st)(*todo*);
      completion_to_test new_comp 
    end
  ) sts
  with 
  | NonBij -> ()

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
      match todo_completion with
      | [] -> assert false
      |comp :: lst -> 
        if !about_completion then Printf.printf "Remains %d completions, processing %s \n" (List.length todo_completion)(show_completion comp);
        if process_name = P then bijection.todo_completion_P <- lst else bijection.todo_completion_Q <- lst ;
        Dag.iter (fun locQ runset ->
          if !about_completion then Printf.printf "- at loc %d:\n" locQ.p;
          RunSet.iter (fun run -> 
            if run.test.process_name <> process_name 
            then add_to_completion run comp ) runset)
      (try Dag.find comp.selected_action (if process_name = P then bijection.indexP else bijection.indexQ) with Not_found -> Dag.empty)
    done

(* From solved statements create tests. 
Opti: when children are identical with same world merge them with the reach parent to reduce number of tests *)  
let rec statements_to_tests process_name (statement : statement) otherProcess equalities =
  let _,raw_statement' = same_term_same_recipe statement.st in
  let raw_statement = { raw_statement' with head= head_predicate_to_test raw_statement'.binder raw_statement'.head } in
   match statement.st.head with
  | Identical _ -> 
    ignore (statement_to_tests process_name (Initial(statement)) raw_statement otherProcess);
    ignore (register_completion (statement_to_completion process_name (negate_statement raw_statement'))) (* Identical don't have children *)
  | _ -> 
    let new_eq, children = List.fold_left 
    (fun (new_eq,children) st -> 
      let is_identical = match st.st.head with Identical _ -> true | _ -> false in
      if is_identical && (st.st.inputs,st.st.dag,st.st.choices,st.st.body) = (statement.st.inputs,statement.st.dag,statement.st.choices,statement.st.body) 
      then begin
        match st.st.head with 
        Identical (s,t) -> 
          let _,st = same_term_same_recipe st.st in
          ignore (register_completion (statement_to_completion process_name (negate_statement st)));
          (EqualitiesSet.add (s,t) new_eq, children)
        | _ -> assert false end
      else begin
        (*statements_to_tests process_name st otherProcess; *)
        (new_eq,st :: children) end)
    (equalities, []) statement.children in
    ignore (statement_to_tests process_name (Initial(statement)) 
      {raw_statement with head = Tests({
        head_binder = raw_statement.binder;
        equalities= new_eq; 
        disequalities = EqualitiesSet.empty})} 
      otherProcess);
    List.iter (fun st -> statements_to_tests process_name st otherProcess new_eq) children
   
    

let base_to_tests process_name base process other_process = 
  List.iter (fun st -> let _, st' = same_term_same_recipe st.st in 
    ignore (register_completion (statement_to_completion process_name (negate_statement st')))
    ) base.unreachable_solved;
  statements_to_tests process_name base.rid_solved other_process EqualitiesSet.empty

let equivalence p q =
  let time = if !about_bench then Sys.time () else 0. in
  if !use_xml then Printf.printf "<?xml-stylesheet type='text/css' href='style.css' ?><all>" ;
  if !about_progress then Printf.printf "Saturating P\n\n%!";
  let (locP,satP) = Horn.saturate p in
  if  !about_saturation then
    Printf.printf (if !use_xml then "%s" else "Saturation of P:\n %s\n") (show_kb satP);
  if !about_progress && not !use_xml then Printf.printf "Saturating Q\n\n%!";
   let (locQ,satQ) = Horn.saturate q in
  if  !about_saturation then
    Printf.printf (if !use_xml then "%s" else "Saturation of Q:\n %s\n") (show_kb satQ);
  let processP = (CallP({p = locP;io=Call;name="main";phase=0;parent=None},
    1,p,Array.make 0 zero,Array.make 0 null_chan)) in
  let processQ = (CallP({p = locQ;io=Call;name="main";phase=0;parent=None}, 
    1,q,Array.make 0 zero,Array.make 0 null_chan)) in 
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
  let nb_open = ref 0 in
  try
    while not (Tests.is_empty bijection.tests) do
      if !about_progress then Printf.printf "\n\n+++++ New iteration of the big loop +++++\n";
      if !about_progress then Printf.printf "Testing %d tests\n%!" (Tests.cardinal bijection.tests);
      while not (Tests.is_empty bijection.tests) do
        let test = pop () in
        if !debug_tests then Printf.printf (if !use_xml then "<opentest>%s" else "Open %s\n%!") (show_test test);
        if !about_progress && (not !debug_tests) 
        then 
          (incr nb_open; 
          if !nb_open mod 250 = 0 then Printf.printf "Open test #%d (%d in stack)\n" test.id (Tests.cardinal bijection.tests));
        (*if test.id = 335 then debug_execution := true ;*)
        find_set_of_runs test ;
        if !debug_tests && !use_xml then Printf.printf "</opentest>"
      done ;
    if !about_progress && !about_bijection then Bijection.show_bijection();
    if !about_progress then 
      Printf.printf "\n\n __Actualization of completions of P (%d runs)__\n" (List.length bijection.runs_for_completions_Q);
    compute_new_completions P ; 
    if !about_progress then 
      Printf.printf "\n\n __Actualization of completions of Q (%d runs)__\n" (List.length bijection.runs_for_completions_P);
    compute_new_completions Q ; 
    done ;
    if !about_tests then show_hashtbl ();
    if !about_bijection then Bijection.show_bijection();
    if !about_bench then  Printf.printf "Time: %F equivalence \n" (Sys.time() -. time)
    else  Printf.printf "\nP and Q are trace equivalent. \n" ;
    if ! use_xml then Printf.printf "</all>"
  with
  | Attack(test,sol) -> begin 
    if !about_tests then show_hashtbl ();
    if !about_bijection then Bijection.show_bijection();
    Printf.printf "\nAn attack has been found for the test %s \n with specific order %s \n\nP and Q are not trace equivalent. \n" 
    (show_test test)(show_dag sol.restricted_dag)
    end
