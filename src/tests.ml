(** The functions of the main algorithm *)

open Util
open Types
open Dag
open Base
open Process
open Bijection
open Bijection.Run
open Bijection.Test
open Process_execution


        

(** the negation function from the theory *)
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
        disequalities = EqualitiesSet.singleton ([],s,t)})}
  | _ -> Printf.printf "negation of %s " (show_raw_statement st); assert false

(** [statement_to_completion process_name statement st] creates a new empty completion from [st] which comes from [statement] *)  
let statement_to_completion process_name (statement : statement) (st : raw_statement) =
  bijection.next_comp_id <- bijection.next_comp_id + 1;
  let locs = locations_of_dag (only_observable st.dag) in 
  {
    id_c = bijection.next_comp_id;
    st_c = st ;
    corresp_c = empty_correspondance ;
    corresp_back_c = empty_correspondance ;
    choices_c = Inputs.new_choices ;
    (*core_corresp = [] ;*)
    missing_actions = locs ;
    selected_action = pick_last_or_null st.dag locs ;
    root = { 
      from_base = process_name ;
      from_statement = statement ;
      initial_statement = st ;
      hash_initial_statement = test_to_hash st;
      directory = Dag.empty ;};
    further_completions = [];
    generated_test = None;
  }
  
            
(** [merge_tests fa fb] is f_a |X|_K f_b, the merge of test from the theory
 The function returns the list of resulting statement with the substitution which has been used *)
let merge_tests process_name (fa : raw_statement) (fb : raw_statement) =
  if ! debug_merge then Printf.printf "Try to merge: %s\n and %s\n%!" (show_raw_statement fa)(show_raw_statement fb);
  match Inputs.merge_choices fa.choices fb.choices with
  | None -> []
  | Some merged_choice ->
  let merged_dag = merge fa.dag fb.dag in
  if is_cyclic merged_dag 
  then  [] 
  else (
    let sigma = Term.sigma_maker_init fa.nbvars fb.nbvars in
    fa.binder:= Master;
    fb.binder:= Slave;
    let sigmas =
      match Inputs.csu_recipes sigma fa.recipes fb.recipes with
      | [] -> []
      | [s] -> Inputs.csu s fa.inputs fb.inputs
      | lst -> List.concat (List.rev_map (fun s -> Inputs.csu s fa.inputs fb.inputs) lst ) in 
    if sigmas = [] 
    then begin 
      fa.binder:= New;
      fb.binder:= New; 
      [] end
    else (
    let fa_head_equal, fa_head_diseq = recipes_of_head fa.head in
    let fb_head_equal, fb_head_diseq = recipes_of_head fb.head in  
    let r =
    List.fold_left
      (fun lst sigma ->
        (*Printf.printf "Here sigma = %s\n%!" (show_subst_maker sigma);*)
        let sigma = Rewriting.pack sigma in
        (*let sigma , body , unsolved = opti_find_recipe sigm merged_dag fa fb in*)
        let body =
               List.map (fun x -> {
               loc = x.loc ; 
               recipe = Rewriting.apply_subst_term x.recipe sigma ;
               term = Rewriting.apply_subst_term x.term sigma ;
               marked = x.marked;
               recipize = x.recipize}
                 )
                 (fa.body @ fb.body)
             in 
        let test_merge_init =
            {
            binder = sigma.binder ;
            nbvars = sigma.nbvars ;
            dag = merged_dag ;
            choices = merged_choice ;
            inputs = Inputs.merge sigma fa.inputs fb.inputs;
            recipes = Inputs.merge_recipes sigma fa.recipes fb.recipes;
            head = Tests({
              head_binder = sigma.binder ;
              equalities= EqualitiesSet.map (fun (b,r,rp) -> 
               b,Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term rp sigma)
                (EqualitiesSet.union fa_head_equal fb_head_equal);
              disequalities = EqualitiesSet.map (fun (b,r,rp) -> 
               b,Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term rp sigma)
                (EqualitiesSet.union fa_head_diseq fb_head_diseq)});
            body = body;
            involved_copies = BangSet.union fa.involved_copies fb.involved_copies}
        in
        sigma.binder := Master;
        (*let tau = (Array.make sigma.nbvars None) in*)
        if !debug_merge then Printf.printf "The init merged test from subst %s \nis %s\n%!"(show_substitution sigma)(show_raw_statement test_merge_init);
        match Horn.normalize_new_statement test_merge_init with
        | None -> lst
        | Some test_merge_init -> 
          if !debug_merge then Printf.printf "after normalization %s\n%!" (show_raw_statement test_merge_init);
          let kb = base_of_name process_name in
          let new_canonical_statements = Horn.canonical_form kb.solved_deduction test_merge_init in
          List.fold_left (fun lst (tau,test_merge_init)  ->
            let rho = Rewriting.compose sigma tau in
            if !debug_merge then Printf.printf "The canonized init merged test from subst %s:\n %s \n\n rho = %s\n%!"
              (show_substitution tau)(show_raw_statement test_merge_init)(show_substitution rho);
            if Horn.is_solved test_merge_init then 
              (rho,test_merge_init)::lst
            else (
            let st = {
              id = kb.next_id ; 
              st = test_merge_init ;
              children = [] ;
              process = None ;
              master_parent = kb.temporary_merge_test;
              slave_parent = kb.temporary_merge_test;
              test_parent = kb.temporary_merge_test;
              } in 
            kb.temporary_merge_test.children <- [st];
            kb.temporary_merge_test_result <- [];
            Queue.add st kb.ns_todo;
            if !about_rare 
              then Printf.printf "Saturation triggered for %s \nfrom fa = %s\n and fb = %s\nwith subst %s\n%!" 
                (show_raw_statement test_merge_init)(show_raw_statement fa)(show_raw_statement fb)(show_substitution rho);
            Horn.merge_sat kb;
            if !about_rare 
            then ( 
              if List.length kb.temporary_merge_test_result > 1 
              then 
                Printf.printf "%d solutions have been found:\n%s\n%!"
                  (List.length kb.temporary_merge_test_result)
                (List.fold_right (fun st str -> str ^ (show_statement " *" st)) kb.temporary_merge_test_result "")
              else Printf.printf "No soluTion\n"
            );
            let res = (List.fold_left (fun lst st -> 
              if !debug_merge then Printf.printf "merge result st matched with: \n%s\n%s\n" (show_statement "" st)(show_raw_statement test_merge_init);
              if st.st.nbvars = 0 then 
                (rho,st.st)::lst
              else 
                if Dag.cardinal st.st.inputs.i <>  Dag.cardinal test_merge_init.inputs.i
                then (if !about_rare then Printf.printf "The saturation have involved new actions in %s.\n%!" (show_raw_statement st.st); lst)
                else ( rho.binder := Master;
                  if !about_rare then Printf.printf "Need to merge variables after saturation.\nrho'= %s\n%!"(show_substitution rho);
                  (*st.st.binder := Extra(5);*)
                  let match_terms = Inputs.csm false st.st.binder test_merge_init.inputs st.st.inputs in
                  let match_recipes = Inputs.csm_recipes false st.st.binder test_merge_init.recipes st.st.recipes in
                  match match_terms, match_recipes with
                  | [subst_inputs],[subst_recipes] -> 
                      rho.binder := Master;
                      let new_sigma = Rewriting.compose_with_subst_lst st.st.binder st.st.nbvars rho (subst_inputs @ subst_recipes) in
                      (*st.st.binder := Rule;
                      Printf.printf "new sub is %s \nfrom %s \n and %s\n%!" (show_substitution new_sigma)(show_substitution rho)(show_subst_lst (subst_inputs @ subst_recipes));
                      st.st.binder := New;*)
                      (new_sigma,st.st)::lst
                  | [], _ -> if !about_rare then Printf.printf "No term matcher\n%!"; lst
                  | _, [] -> if !about_rare then Printf.printf "No recipe matcher\n%!"; lst
                  | subst_inputs :: _ , subst_recipes :: _ -> 
                      if !about_rare then 
                        Printf.printf "This unification case is problematic.\n"; 
                      (Rewriting.compose_with_subst_lst st.st.binder st.st.nbvars rho (subst_inputs @ subst_recipes),st.st)::lst
                  )
              ) lst kb.temporary_merge_test_result
            ) in
            (* assert (res != [] || kb.temporary_merge_test_result= []);*) (* assertion is false when doing overapproximation with recipes *)
            res)
          ) lst new_canonical_statements
     (* with
      Horn.Unsound_Statement -> 
        if !debug_merge then Printf.printf "Unsound statement %s\n%!" (show_raw_statement test_merge_init);
        lst *)
      ) [] sigmas
    in
    fa.binder:= New;
    fb.binder:= New;  
    r ))

   

(** This function returns false if the statement is not executable in his own processus
(due to disequalities or identities) true otherwise.
Correspond to actual reach of the theory *) 
let actual_test process_name sequence (st : raw_statement) =
  let corr = {a = Dag.mapi (fun k _ -> k) st.dag.rel} in
  let test = { null_test with
    process_name = process_name;
    reflexive = true;
    statement = {st with head = Tests({(get_test_head st.head) with disequalities = EqualitiesSet.empty})};
    constraints = corr;
    constraints_back = corr;
    choice_constraints = st.choices
  } in
  if !debug_execution 
  then Printf.printf "\nChecking actual of %s \nwith dag = %s\n%!" (show_test test)(show_dag st.dag);
  let solution = init_sol process_name st (proc process_name) sequence test in
  let reachable = find_possible_run solution in
  if !debug_tests then (
    match solution.selected_run with
    | None ->  Printf.printf "No execution for this test (reachable %b)\n" reachable 
    | Some pr -> ());
  reachable, solution.selected_run
  
(** compute the frame for st (when st is a variant of another statement) *)  
let get_xor_variant_frame run st =
  let test = { null_test with
    process_name = run.test.process_name;
    reflexive = false;
    statement = st;
    constraints = run.corresp;
    constraints_back = run.corresp_back;
  } in
  if !debug_xor 
  then Printf.printf "\nChecking frame variant of %s \nwith dag = %s\n%!" (show_test test)(show_dag st.dag);
  let solution = init_sol run.test.process_name st (proc (other run.test.process_name)) run.sol.sequence test in
  ignore (find_possible_run solution );
  match solution.selected_run with
    | None ->  Printf.printf "A xor variant of a running trace does not run:\n%s\n%s\n%s\n%!"
        (show_run run)(show_test run.test)(show_raw_statement st);assert false 
    | Some pr -> pr.frame


(** {2 trans P->Q and trunc A stuff} *)   
    
let map_dag dag corresp =
  {rel = Dag.fold (fun key lset ndag -> Dag.add (loc_p_to_q key corresp) (LocationSet.map (fun l -> loc_p_to_q l corresp) lset) ndag) dag.rel (Dag.empty)}

let trunc_map_dag dag set corresp =
  {rel = Dag.fold (fun key lset ndag -> 
    if LocationSet.mem key set then
    Dag.add (loc_p_to_q key corresp) (LocationSet.map (fun l -> loc_p_to_q l corresp) (LocationSet.inter set lset)) ndag
    else ndag ) dag.rel (Dag.empty)}

let apply_frame_2 sigma recipe run =
  Rewriting.normalize (Rewriting.apply_subst_term (apply_frame recipe run) sigma) (! Parser_functions.rewrite_rules)
  
let transpose_inputs sigma (recipes : Inputs.inputs) (run : partial_run) : Inputs.inputs =
  {i = Dag.fold (fun key recipe ninputs -> Dag.add (loc_p_to_q key run.corresp) (apply_frame_2 sigma recipe run) ninputs) recipes.i (Dag.empty)}

let rec transpose_recipe sigma recipe corresp =
  match recipe with
    | Fun({ id=Frame(l)}, []) ->  Fun({ id=Frame(Bijection.loc_p_to_q l corresp);has_variables=false }, []) 
    | Fun({ id=InputVar(l)}, []) -> assert false
    | Fun(f, args) -> Fun(f, List.map (fun x -> transpose_recipe sigma x corresp) args)
    | Var(x) -> Rewriting.apply_subst_term recipe sigma (* Does sigma do the transposition? *)
  
let transpose_recipes sigma (recipes : Inputs.inputs) corresp : Inputs.inputs =
  {i = Dag.fold (fun key recipe nrec -> Dag.add (loc_p_to_q key corresp) (transpose_recipe sigma recipe corresp) nrec) recipes.i (Dag.empty)}

let transpose_test_head head (sigma :  substitution) corresp =
  {
    head_binder = sigma.binder ;
    equalities = EqualitiesSet.map (fun (b,s,t) -> (b,transpose_recipe sigma s corresp,transpose_recipe sigma t corresp)) head.equalities;
    disequalities = EqualitiesSet.map (fun (b,s,t) -> (b,transpose_recipe sigma s corresp,transpose_recipe sigma t corresp)) head.disequalities}
  
let transpose_head head (sigma :  substitution) corresp =
  Tests( transpose_test_head (get_test_head head) sigma corresp)
  
(** take a run and provide a statement which is the test of the run transposed in the other process *)  
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
  dag = map_dag (only_observable run.sol.restricted_dag) run.corresp;
  inputs =  transpose_inputs identity_sigma st.recipes run  ;
  choices = run.choices ;
  head = transpose_head st.head identity_sigma run.corresp;
  body = List.map (fun ba -> {
    loc = LocationSet.map (fun l -> loc_p_to_q l run.corresp) ba.loc;
    recipe = transpose_recipe identity_sigma ba.recipe run.corresp;
    term = apply_frame_2 identity_sigma ba.recipe run;
    marked = false;
    recipize = false
    }) st.body ;
  recipes = transpose_recipes identity_sigma st.recipes run.corresp ; 
  involved_copies = BangSet.empty ; (* TODO *)
  } in
  let sigm, r = Horn.simplify_statement r in
  stP.binder := New;
  (*Printf.printf "conjrun %s => %s\n"(show_raw_statement stP) (show_raw_statement r);*)
  (Rewriting.compose identity_sigma sigm,r)
  
let filter_atom set a =
  LocationSet.exists (fun l -> LocationSet.mem l set) a.loc
  
let filter_dag set dag =
  {rel = Dag.filter (fun l _ -> LocationSet.mem l set) dag.rel}
  
let filter_inputs set (inputs : Inputs.inputs) :Inputs.inputs =
  {i = Dag.filter (fun l _ -> LocationSet.mem l set) inputs.i}
  
(** remove choice indexes from [choices] which are not before [set] *)  
let filter_choices set (choices : Inputs.choices) : Inputs.choices = 
  (*Printf.printf "loc: %s | %s \n" (show_loc_set set)(Inputs.show_choices choices);*)
  let result = ref LocationSet.empty in
  let rec parent_set add_it set = 
    List.iter (fun (loc : location) -> 
      (*Printf.printf " %d" loc.p;*)
      if add_it then 
        result := LocationSet.add loc !result;
      List.iter (fun (l : location) -> 
        if not( LocationSet.mem l !result) 
        then (
          result := LocationSet.add l !result;
          (*Printf.printf "+%d" l.p;*)
          match l.io with 
          | Choice -> ()
          | _ ->
              let l' = Inputs.get_output_of_input choices l in
              result := LocationSet.add l' !result;
              (*Printf.printf "--%d" l'.p;*)
              parent_set true l'.parent_choices))
        loc.parent_choices) set 
        in
  parent_set false (LocationSet.elements set) ;
  (*Printf.printf "\nfinal loc: %s \n" (show_loc_set !result);*)
  {c = Dag.filter (fun l _ -> LocationSet.mem l !result) choices.c }
  
let trunconj set run =
  let stP = run.test.statement in
  let identity_sigma = Rewriting.identity_subst stP.nbvars in
  (*let binder = identity_sigma.binder in*)
  stP.binder := Master;
  let st = apply_subst_statement stP identity_sigma in
  let filtered_inputs = filter_inputs set st.recipes in
  let filtered_choices = filter_choices (LocationSet.map (fun l -> loc_p_to_q l run.corresp) set) run.choices in
  (*Printf.printf ">filtered_input: %s\n%!" (Inputs.show_inputs filtered_inputs);
  Printf.printf ">filtered_choices: %s\n%!" (Inputs.show_choices filtered_choices);*)
  let r = 
  {
  binder = st.binder ;
  nbvars = st.nbvars ;
  dag = trunc_map_dag (only_observable run.sol.restricted_dag) set run.corresp;
  inputs =  transpose_inputs identity_sigma filtered_inputs run ;
  recipes = transpose_recipes identity_sigma filtered_inputs run.corresp ; 
  choices = filtered_choices ; 
  head = Tests({head_binder = st.binder; equalities=EqualitiesSet.empty; disequalities=EqualitiesSet.empty;});
  body = List.map (fun ba -> {
    loc = LocationSet.map (fun l -> loc_p_to_q l run.corresp) ba.loc;
    recipe = transpose_recipe identity_sigma ba.recipe run.corresp;
    term = apply_frame_2 identity_sigma ba.recipe run;
    marked = false;
    recipize = false;
    }) (List.filter (filter_atom set) st.body) ;
  involved_copies = BangSet.empty ; (* TODO *)
  } in
  (*let sigm, r = Horn.simplify_statement r in*)
  (*Printf.printf "conjrun %s => %s\n"(show_raw_statement stP) (show_raw_statement r);*)
  stP.binder := New;
  (identity_sigma,r)
  
(** {2 variants stuff} *)
  
let is_complex_xor_statement st = !Parser_functions.use_xor && List.exists (fun a -> match a.term with Fun(_) -> true | _ -> false) st.body

let gen_alt_tests p test1 dag1 test2 dag2 =
  let lst = ref [] in
  lst := merge_tests p 
          { test1.statement with dag = dag1 } 
          { test2.statement with dag = dag2 };
  List.iter (fun (_,(sigm1,st1)) -> 
    if !debug_xor then Printf.printf "Merge (1) xor variants %s\n%!" (show_raw_statement st1);
    test1.statement.binder := Master;
    let head1 = apply_subst_pred test1.statement.head sigm1 in 
    let st1 = {st1 with head = head1 ; dag = dag1} in
    let new_tests = List.map (fun (sigma,st) -> (Rewriting.compose_merge sigm1 (Rewriting.identity_subst test2.statement.nbvars) sigma,st)) (merge_tests p st1 { test2.statement with dag = dag2 }) in
    lst := List.rev_append new_tests !lst
  ) test1.xor_class;
  List.iter (fun (_,(sigm2,st2)) -> 
    if !debug_xor then Printf.printf "Merge (2) xor variants %s\n%!" (show_raw_statement st2);
    test2.statement.binder := Master;
    let head2 = apply_subst_pred test2.statement.head sigm2 in 
    let st2 = {st2 with head = head2 ; dag = dag2} in
    let new_tests = List.map (fun (sigma,st) -> (Rewriting.compose_merge (Rewriting.identity_subst test1.statement.nbvars) sigm2 sigma,st)) (merge_tests p { test1.statement with dag = dag1 } st2) in
    lst := List.rev_append new_tests !lst
  ) test2.xor_class;
  List.iter (fun (_,(sigm1,st1)) -> 
    if !debug_xor then Printf.printf "Merge (3) xor variants %s\n%!" (show_raw_statement st1);
    test1.statement.binder := Master;
    let head1 = apply_subst_pred  test1.statement.head sigm1 in 
    let st1 = {st1 with head = head1 ; dag = dag1} in
    List.iter (fun (_,(sigm2,st2)) ->
      test2.statement.binder := Master;
      let head2 = apply_subst_pred test2.statement.head sigm2 in 
      let st2 = {st2 with head = head2 ; dag = dag2} in
      let new_tests = List.map (fun (sigma,st) -> (Rewriting.compose_merge sigm1 sigm2 sigma,st)) (merge_tests p st1 st2) in
      lst := List.rev_append new_tests  !lst
    ) test2.xor_class
  ) test1.xor_class;
  !lst

let get_all_variants_of_test statement =
    statement.binder := Master ;
    let tuple = Fun({id=Tuple(0); has_variables=true},List.map (fun b -> b.term) statement.body) in
    let variants = Rewriting.variants statement.nbvars tuple 
      [Parser_functions.rewrite_rule_xor_1;
      Parser_functions.rewrite_rule_xor_2;
      Parser_functions.rewrite_rule_xor_3] in
    List.map (fun (_,sigma) ->
      let st = apply_subst_normalize_statement statement sigma in
      Printf.printf "_____________ %s\n" (show_raw_statement st);
      [],(sigma,st))
      variants 
      

  
(*
let rec add_identities_to_completions head (*process_name*) compl = 
  let h = get_test_head (compl.st_c.head) in
  h.equalities <- EqualitiesSet.union h.equalities head.equalities;
  h.disequalities <- EqualitiesSet.union h.disequalities head.disequalities ;
  List.iter (fun (sigma,compl) -> add_identities_to_completions (apply_subst_test_head head sigma) (*process_name*) compl) compl.further_completions;
  match compl.generated_test with
  | None -> ()
  | Some (subst,test) -> complete_set_of_identities (transpose_test_head head subst compl.corresp_back_c) (*process_name*) test *)
  

(** [complete_set_of_identities head old_test] add the identities in [head] on [old_test] and its children 
(instead of maintaining two statements where the former is useless)*)
let rec complete_set_of_identities head old_test =
  let old_eq,old_diseq = recipes_of_head old_test.statement.head in
  let new_eq,new_diseq = head.equalities,head.disequalities in
  let diff_eq = EqualitiesSet.diff new_eq old_eq in
  let diff_diseq = EqualitiesSet.diff new_diseq old_diseq in
  (* assert (old_test.reflexive_run != empty_run);
  Printf.printf "run : %s\n" (show_partial_run old_test.reflexive_run);*)
  if not( EqualitiesSet.is_empty diff_eq && EqualitiesSet.is_empty diff_diseq) &&  ( check_identities old_test.reflexive_run head)
  then begin (* If the old test is more expressive: nothing to do *)
    let h = get_test_head old_test.statement.head in
    if !debug_merge then Printf.printf "The following test is upgraded with %s test\n %s\n" (show_test_head head)(show_test old_test);
    h.equalities <- EqualitiesSet.union (diff_eq)(old_eq);
    h.disequalities <- EqualitiesSet.union (diff_diseq)(old_diseq) ;
    if !debug_merge then Printf.printf " the new head is %s\n" (show_test_head h);
    List.iter (fun sol -> 
        match sol.selected_run with
        | None -> if not !about_all_attacks then (Printf.printf "Test %d has no solution\n" old_test.id;assert false)
        | Some pr -> 
          if not (check_identities pr head) then
          begin
            if !about_rare || !debug_tests then Printf.printf "Wrong run for %s\n%s\n caused by %s\n%!" (show_test old_test)(show_run pr) (show_test_head head);
            Bijection.remove_run pr;
            sol.selected_run <- None ;
            old_test.solutions_todo <- sol :: old_test.solutions_todo; 
            (*todo remove sol from done*)
            find_set_of_runs old_test
          end ;
          let head' = {head with equalities=diff_eq; disequalities=diff_diseq} in
          List.iter (fun (status,sigma,derived_test) -> 
              (*Printf.printf "apply subt %s\non %s\n%!" (show_substitution sigma)(show_test_head head');*)
              head.head_binder := status;
              let nhead = apply_subst_test_head head' sigma in
              head.head_binder := New;              
              complete_set_of_identities nhead derived_test) 
            pr.consequences
    ) old_test.solutions_done
  end

(** [statement_to_tests] takes [statement] check that actual([statement]) e.g. the statement execute on [process_name]
and add it to [bijection] if it does not already exists or update the head of an existing statement with the same world. *)  
and statement_to_tests process_name origin (statement : raw_statement) otherProcess =
  (* let statement = match origin with Initial _ -> same_term_same_recipe statement | _-> statement in *)
  (*Printf.printf "st2tests %s\n" (show_raw_statement statement);*)
  let exception CyclicDag in
  let nb = Dag.cardinal statement.dag.rel in
  try
  if nb != 0 
  then begin 
    let dag = if Process.processes_infos.max_phase = 0 then statement.dag 
      else (
        let loc_phase = Array.make (Process.processes_infos.max_phase+2) LocationSet.empty in
        Dag.iter (fun loc _ -> loc_phase.(loc.phase) <- LocationSet.add loc loc_phase.(loc.phase)) statement.dag.rel ;
        for i = Process.processes_infos.max_phase - 1 downto 1 do
          loc_phase.(i) <- LocationSet.union loc_phase.(i) loc_phase.(i+1)
        done ;
        let dag = {rel = Dag.mapi (fun loc lset -> LocationSet.union loc_phase.(loc.phase + 1) lset) statement.dag.rel} in
        if is_cyclic dag then (Printf.printf "cycle on %s\n"(show_dag dag) ;raise CyclicDag) else dag ) (*maybe a bug here: how cycle is found ? *)
    in
    let statement = Horn.clean_recipe_variable { statement with dag = dag } in
    statement.binder := New;
    let sequence = dag_to_sequence dag in
    let hash_trace = (Inputs.choices_to_hash statement.choices,dag_to_hash statement.dag) in
    let trace_node, vars1, nbv1 = get_trace_tree statement sequence in
    (*let is_complex_xor = is_complex_xor_statement statement in*)
    match  TraceNodes.find_opt hash_trace trace_node.node with
    | Some Impossible -> None
    | Some(Possible(nbv2,vars2,test)) -> (
        if !debug_tests then 
          Printf.printf "Updating an existing test which is \n%s\nwith %s \n"
            (show_test test)(show_predicate statement.head)(*show_substitution sigma*);
        (*
        let hash_body = Base.body_to_hash statement.body in 
        if hash_body <> test.hash_body_xor 
        then (
          match List.assoc_opt hash_body test.xor_class with
          | Some (sigma,rawst) -> ()
          | None -> 
              if test.solutions_done = [] 
              then (
                let sigm = subst_from_trace_subst vars2 vars1 statement.binder statement.nbvars in
                test.xor_class <- (hash_body,(sigm,statement))::test.xor_class ;
                if !debug_xor then 
                Printf.printf "New variation for test %d : %s\n%s\n" test.id (show_raw_statement statement)(show_substitution sigm);
              )
              else  
              ( if !debug_xor then
                Printf.printf "New xor test while main test already done\n%s\n" (show_test test);
                List.iter (fun (h,(s,st)) -> Printf.printf ">> %s\n" (show_raw_statement st)) test.xor_class;
                (*assert false*));
                (* because all elements of a class are created in the same step by init merge or completion except for net rounds... *)
                (* problem knows_13(x7,x3+x5),knows_12(x6,x2+x5),knows_11(x4,x2+x3) and knows_13(x7,x2+x5),knows_12(x6,x3+x5),knows_11(x4,x2+x3) *)
        );
        *)
        let sigma = subst_from_trace_subst vars1 vars2 test.statement.binder test.statement.nbvars in
        let head_t = get_test_head statement.head in
        statement.binder := Master;
        let head' = apply_subst_test_head head_t sigma in
        remove_false_disequalities test.reflexive_run head';
        if !debug_tests then 
          Printf.printf "Start update of %d with subst %s\n%!" test.id (show_substitution sigma);
        statement.binder := New ;
        complete_set_of_identities head' test ;
        if !debug_tests then 
          Printf.printf "End of update of %d\n%!" (test.id);
          Some (Some sigma,test)
        )
    | None -> (
      match actual_test process_name sequence statement with
      | _, Some pr -> 
        let head_of_statement = get_test_head statement.head in
        remove_false_disequalities pr head_of_statement;
        let init = init_sol process_name statement otherProcess sequence in 
        (* init is a partial function to allow cycle reference between test and partial run *)
        let new_test = push statement process_name origin init in
        new_test.reflexive_run <- pr;
        trace_node.node <- TraceNodes.add hash_trace (Possible(nbv1,vars1,new_test)) trace_node.node;
        if is_complex_xor_statement statement then (
          let variants = get_all_variants_of_test statement in
          new_test.xor_class <- variants );
        Some (None,new_test)
      | reachable, None -> 
          if not reachable then
            trace_node.node <- TraceNodes.add hash_trace Impossible trace_node.node;
          None )
  end
  else None
  with CyclicDag -> None
  

(** Create new tests from [prun] which is in conflict with all tests in [runset] *)
(** Correspond to the "New Test" rule applied once with all tests in conflict *)
and add_merged_tests prun =
  (* let (prun,runset)=sol.execution,sol.conflicts in *)
  let runset = Bijection.compatible prun in 
  (* if false && !debug_tests && not (RunSet.is_empty runset) then Printf.printf "Conflicts with " ; *)
  RunSet.iter (fun par ->
    (*Printf.printf "is merge between < %d + %d >?\n%!" prun.test.id par.test.id;*) 
    (* Check that we are merging test which have not been discarded before in the loop *)
    if Rewriting.get_option (par.sol.selected_run) == par
    || Rewriting.get_option (prun.sol.selected_run) == prun
    && prun.test.process_name = par.test.process_name
    then begin
        if !debug_merge then Printf.printf "Try merge between < %d + %d >" prun.test.id par.test.id; 
        (*let merged_statements = merge_tests prun.test.process_name 
          { prun.test.statement with dag = prun.sol.restricted_dag } 
          { par.test.statement with dag = par.sol.restricted_dag } in *)
        let merged_statements = gen_alt_tests prun.test.process_name prun.test prun.sol.restricted_dag par.test par.sol.restricted_dag in
        if !debug_xor then Printf.printf "Got %d variants from %d and %d\n" (List.length merged_statements) prun.test.id par.test.id;
        List.iter (fun ((sigma : substitution),raw_st) -> 
          if !debug_tests then Printf.printf "Merge of %d with %d corresp %s\n" prun.test.id par.test.id (show_correspondance prun.corresp);
          assert (sigma.binder == raw_st.binder);
          (*if false && !debug_tests then Printf.printf "T,";*)
          match statement_to_tests prun.test.process_name (Composed(prun,par)) raw_st (proc (other prun.test.process_name)) with
          | Some (sigm,new_test) -> (
            let sigma = 
              match sigm with
              | None -> sigma 
              | Some sigm -> 
                (* Printf.printf "composition \n%s\n%s\n%!" (show_substitution sigma) (show_substitution sigm);*)
                sigma.binder := Master;
                let s = Rewriting.compose sigma sigm in
                s 
            in
            (*Printf.printf "consequences: %s\n for %s\nfrom %s \nand %s \n\n%!" (show_substitution sigma) (show_test new_test)(show_test prun.test)(show_test par.test);*)
            assert (sigma.binder == new_test.statement.binder) ;
            assert (prun.test.statement.nbvars = Array.length sigma.master);
            assert (par.test.statement.nbvars = Array.length sigma.slave);
            if not (List.exists (fun (_,_,t) -> t==new_test) prun.consequences) then
              prun.consequences <- (Master,sigma,new_test) :: prun.consequences;
            if not (List.exists (fun (_,_,t) -> t==new_test) par.consequences) then
              par.consequences <-  (Slave,sigma,new_test) :: par.consequences )
          | None -> ()
        ) merged_statements 
      
    end
  ) runset;
  (*if false && !debug_tests then Printf.printf "\n"*)


(** Correspond to the "New Sol" rule of the algorithm *)  
and find_set_of_runs test =
  (*Printf.printf "find_set_of_runs %d\n" test.id ;
  List.iter (fun sol -> Printf.printf ">%s\n" (show_partial_run sol.init_run) ) test.solutions_todo;
  List.iter (fun sol -> Printf.printf "}%s\n" (show_run (match sol.selected_run with Some x -> x | None -> sol.init_run)) ) test.solutions_done;*)
  match test.solutions_todo with
  | [] -> if ! debug_tests then Printf.printf "Success for all solutions of test %d\n\n" test.id 
  | sol :: queue -> (
    test.solutions_todo <- queue;
    ignore (find_possible_run sol );
    match sol.selected_run with
    | None -> 
        bijection.attacks <- (test,sol):: bijection.attacks; 
        if not !about_all_attacks 
        then raise (Attack(test,sol))
    | Some pr -> 
      test.solutions_done <- sol :: test.solutions_done; 
      if ! debug_tests then Printf.printf "Execution of test %d \n with %s\n%!" test.id (show_run pr);
      Bijection.add_run pr;
      add_merged_tests pr;
      if ! debug_tests then Printf.printf "End of merges for %d \n%!" test.id;
      find_set_of_runs test
    )

(** The "completed" rule of the main algorithm *)      
let completion_to_test comp =
  let test = { null_test with
    process_name = comp.root.from_base;
    statement = comp.st_c;
    constraints = comp.corresp_back_c;
    constraints_back = comp.corresp_c;
    choice_constraints = comp.choices_c;
  } in
  let sequence = dag_to_sequence comp.st_c.dag in
  let solution = init_sol comp.root.from_base comp.st_c (proc (other comp.root.from_base )) sequence test in
  let _ = find_possible_run solution in
  match solution.selected_run with
    None -> 
      if !debug_completion then Printf.printf "The completion is not executable \n" 
  | Some pr -> 
    if !debug_completion then Printf.printf "The completion can be run  %s\n" (show_run pr);
    test.reflexive_run <- { pr with corresp = { a= Dag.mapi (fun s t -> s) pr.corresp_back.a}};
    let sigma, conjrun = conj pr in 
    begin
    let origin =
      match comp.root.from_statement.st.head with 
      | Unreachable -> CompletionUnreach(comp.root.from_statement)
      | Identical(_,_) -> CompletionIdentity(comp.root.from_statement)
      | _ -> assert false in 
    match statement_to_tests (other comp.root.from_base) origin conjrun (proc (comp.root.from_base )) with
    | Some (_,test) -> if !debug_completion || !debug_tests then Printf.printf "Got test from the completion\n %s\n" (show_test test);
      comp.generated_test <- Some (test) 
    | None -> if !debug_completion then Printf.printf "No test from the completion\n"; () end
    
let nb_comp = ref 0

(** Perform the rule "New Con" *)
let add_to_completion (run : partial_run) (completion : completion) = 
  if !debug_completion then 
    Printf.printf "Try completing a completion between \n run %s \n whose test is %s \n and partial completion %s\n" 
    (show_run run)(show_raw_statement run.test.statement) (show_completion completion);
  let exception NonBij in
  try
  let over_corr_back = { a = Dag.union 
      (fun locQ x y -> if x = y then Some x else raise NonBij) 
      run.corresp_back.a completion.corresp_back_c.a } in
  let missing = LocationSet.filter (fun loc -> not (Dag.mem loc over_corr_back.a)) completion.missing_actions in
  match Inputs.merge_choices completion.st_c.choices run.choices with
  | None -> ()
  | Some over_merged_choices -> 
  if LocationSet.is_empty missing && not(interesting_to_complete null_location over_corr_back over_merged_choices completion) then
    ()
  else (
  let llocs, _ = List.split (Dag.bindings completion.root.initial_statement.dag.rel) in
  let set = restr_set run.sol.restricted_dag 
    (only_observable run.test.statement.dag)
    (List.fold_left (fun lst l -> try (loc_p_to_q  l run.corresp_back)::lst with LocPtoQ _ -> lst) [] llocs) in
  let filtered_choices = filter_choices set run.test.statement.choices in
  (* Printf.printf "restr_set %s\n%!" (show_loc_set set); *)
  (* Printf.printf "filter_choices_run :%s\n%!" (Inputs.show_choices filtered_choices);*)
  match Inputs.merge_choices completion.choices_c filtered_choices with
  | None -> ()
  | Some completed_choices -> 
  let corr = { a = Dag.merge (fun locP x y -> 
    match x , y with
    | Some x, Some y -> if x = y then Some x else raise NonBij
    | Some x, None -> if LocationSet.mem locP set then Some x else None
    | None, Some y -> Some y
    | None, None -> None) run.corresp.a completion.corresp_c.a } in
  let corr_back = { a= Dag.filter (fun q p -> Dag.mem p corr.a) over_corr_back.a } in
  (*if !debug_completion then Printf.printf "Conj = %s \n" (show_raw_statement conjrun);*)
  if !debug_merge then Printf.printf "Merge run %d with comp %s\n" run.test.id (show_raw_statement completion.root.initial_statement);
  let _, conjrun = trunconj set run in
  let sts = List.fold_left (fun lst (_,(sigma,st)) -> 
    run.test.statement.binder := Master;
    if !debug_xor then Printf.printf "A xor variant: %s\n" (show_raw_statement st);
    let frame = get_xor_variant_frame run st in
    let _, conjrun = trunconj set {run with 
      test = {run.test with statement = {st with head = apply_subst_pred run.test.statement.head sigma}};
      frame = frame }
    in
    List.rev_append (merge_tests completion.root.from_base conjrun completion.st_c) lst
    )
    (merge_tests completion.root.from_base conjrun completion.st_c)
    run.test.xor_class in
  (*if !debug_completion && sts = [] then  Printf.printf "merge is not possible\n\n";*)
  List.iter (fun ((sigma : substitution),st) -> 
    bijection.next_comp_id <- bijection.next_comp_id + 1;
    let new_comp' = {
        id_c = bijection.next_comp_id;
        st_c = (*canonize_statement*) st;
        corresp_c = corr;
        corresp_back_c = corr_back;
        choices_c = completed_choices;
        missing_actions = missing ;
        selected_action = pick_last_or_null st.dag missing ;
        root = completion.root ;
        further_completions = [];
        generated_test = None;
      } in
    if !about_progress then (
      incr nb_comp ;
      if !nb_comp mod 10000 = 0 then Printf.printf "Adding partial comp %d %s\n%!" !nb_comp (show_completion new_comp'));
    if !debug_completion then 
      Printf.printf "Registering a new completion %s\n from old\n %s \n and %s \n" 
      (show_completion new_comp')(show_completion completion)(show_run run);
    (*Printf.printf "for %d:" (completion.id_c);*)
    match register_completion new_comp' with
    | add_test, Some new_comp ->
      (*
      let sigma = 
        if new_comp.st_c.head = new_comp'.st_c.head then sigma
        else (
          let head = get_test_head new_comp'.st_c.head in
          let sig_id = Rewriting.merging_subst sigma.nbvars new_comp.st_c.binder in
          head.head_binder := Master ; 
          add_identities_to_completions (apply_subst_test_head head sig_id) new_comp;
          let sigm = Rewriting.compose sigma sig_id in
          head.head_binder := New ;
          sigm) in
      *)
      if not (List.exists (fun c -> c.id_c = new_comp.id_c) completion.further_completions) then
        completion.further_completions <- new_comp :: completion.further_completions;
      if not (List.exists (fun c -> c.id_c = new_comp.id_c) run.completions) then
        run.completions <- new_comp :: run.completions;
      if add_test then 
      begin
        if !debug_completion then Printf.printf "Completion complete, checking test %s\n" (show_raw_statement st);
        completion_to_test new_comp ;
        if !debug_completion then Printf.printf "Completion complete, end of %s\n" (show_raw_statement st);
      end
    | _ , None -> ()
  ) sts)
  with 
  | NonBij -> ()

(** [compute_new_completions] applies the rule "New Con" for new solutions and new partial contradiction for [process_name] *)      
let rec compute_new_completions process_name  =
  match if process_name = P then bijection.runs_for_completions_Q else bijection.runs_for_completions_P with
  (* First match all run with all completions *)
  | run :: lst -> 
    if !debug_completion then Printf.printf "\nChecking if the following run can complete a completion %s\n%s\n" (show_raw_statement run.test.statement)(show_run run);
    if process_name = P then bijection.runs_for_completions_Q <- lst else bijection.runs_for_completions_P <- lst ;
    List.iter (fun (_,l) ->
    List.iter (fun completion -> add_to_completion run completion) 
      (try Dag.find l (if process_name = P then bijection.partial_completions_P else bijection.partial_completions_Q) with Not_found -> []))
    (Dag.bindings run.corresp.a);
    compute_new_completions process_name
  (* Then for all new partial completion just created match them with all runs *)  
  | [] -> 
    if !debug_completion then (Printf.printf "\nCompleting new completions\n\n");
    while (if process_name = P then bijection.todo_completion_P else bijection.todo_completion_Q) != [] do
      let todo_completion = if process_name = P then bijection.todo_completion_P else bijection.todo_completion_Q in
      match todo_completion with
      | [] -> assert false
      |comp :: lst -> 
        if !debug_completion then Printf.printf "Remains %d completions, processing %s \n" (List.length todo_completion)(show_completion comp);
        if process_name = P then bijection.todo_completion_P <- lst else bijection.todo_completion_Q <- lst ;
        Dag.iter (fun locQ runset ->
          if !debug_completion then Printf.printf "- at loc %d:\n" locQ.p;
          RunSet.iter (fun run -> 
            if run.test.process_name <> process_name 
            then add_to_completion run comp ) runset)
      (try Dag.find comp.selected_action (if process_name = P then bijection.indexP else bijection.indexQ) with Not_found -> Dag.empty)
    done

(** [statements_to_tests] computes "Tests" and "PartialC" from the saturated knowledge base except "Unreachable" statement.
Opti: when children are identical with same world merge them with the reach parent to reduce number of tests *)  
let rec statements_to_tests t c process_name (statement : statement) otherProcess equalities =
  if !debug_tests then Printf.printf "Getting test (%d) %s %s \n%!" statement.id (if t then "yes" else "no") (show_raw_statement statement.st); 
  let raw_statement' = statement.st in
  let sigma = Rewriting.merging_subst raw_statement'.nbvars raw_statement'.binder in
  let eq_vars,body = List.partition (fun b -> LocationSet.is_empty b.loc) raw_statement'.body in
  if eq_vars <> [] then (Printf.eprintf "To be implemented: presence of free variables in test %s" (show_raw_statement raw_statement'); assert false);
  let equalities = EqualitiesSet.map (fun (b,s,t) -> (b,Rewriting.apply_subst_term s sigma,Rewriting.apply_subst_term t sigma)) equalities in
  let equalities = 
    match raw_statement'.head with
    | Identical (s,t) -> 
      if c then (
        let compl = statement_to_completion process_name statement (negate_statement raw_statement') in
        ignore (register_completion compl);
        bijection.initial_completions <- compl :: bijection.initial_completions );
      EqualitiesSet.add ([], s, t) equalities
    | _ -> equalities in
  let new_eq = List.fold_left 
    (fun new_eq st -> 
      match st.st.head with
      | Identical (s,t) -> 
          if (st.st.inputs,st.st.dag,st.st.choices,st.st.body) = (statement.st.inputs,statement.st.dag,statement.st.choices,body)
          then EqualitiesSet.add ([],Rewriting.apply_subst_term s sigma,Rewriting.apply_subst_term t sigma) new_eq
          else new_eq
      | _ -> new_eq )
    equalities statement.children in
    if t then ignore (statement_to_tests process_name (Initial(statement)) 
      {raw_statement' with 
        head = Tests( {
          head_binder = raw_statement'.binder;
          equalities= new_eq; 
          disequalities = EqualitiesSet.empty} )} 
      otherProcess);
    List.iter (fun st -> statements_to_tests t c process_name st otherProcess new_eq) statement.children
   
    
(** [unreach_to_completion] initialize "PartialC" with "Unreachable" statement. *)
let unreach_to_completion process_name base = 
  List.iter (fun st -> 
    let compl = statement_to_completion process_name st (negate_statement st.st) in
    ignore (register_completion compl) ;
    bijection.initial_completions <- compl :: bijection.initial_completions
    ) base.unreachable_solved

let base_to_tests t c process_name base other_process = 
  statements_to_tests t c process_name base.rid_solved other_process EqualitiesSet.empty
  
(** for benchmarking *)  
let get_time()= Unix.gettimeofday() (*(Unix.times()).tms_utime*)

(** [equivalence both p q] checks if [p] is equivalent to [q] when [both] or trace included when [not both] *)
let equivalence both p q =
  let time = get_time() in
  if !use_xml then Printf.printf "<?xml-stylesheet type='text/css' href='../style.css' ?><all>" ;
  if !about_progress then Printf.printf "Saturating P\n\n%!";
  let (locP,satP) = Horn.saturate p in
  if  !about_saturation then
    Printf.printf (if !use_xml then "<satp>%s</satp>" else "Saturation of P:\n %s\n") (show_kb satP);
  if !about_progress && not !use_xml then Printf.printf "Saturating Q\n\n%!";
   let (locQ,satQ) = Horn.saturate q in
  if  !about_saturation then
    Printf.printf (if !use_xml then "<satq>%s</satq>" else "Saturation of Q:\n %s\n") (show_kb satQ);
  let processP = (CallP(root_location locP,1,p,Array.make 0 zero,Array.make 0 null_chan)) in
  let processQ = (CallP(root_location locQ,1,q,Array.make 0 zero,Array.make 0 null_chan)) in 
  bijection.p <- processP ;
  bijection.q <- processQ ;
  bijection.satP <- satP ;
  bijection.satQ <- satQ ;
  let nb_statements = satP.next_id + satQ.next_id in 
  let time_sat = if !about_bench then get_time() else 0. in
  if !about_progress then Printf.printf "Building tests from %d statements\n%!" nb_statements;
  base_to_tests true both P satP processQ ; 
  base_to_tests both true Q satQ processP ; 
  unreach_to_completion Q satQ ;
  if both then 
  unreach_to_completion P satP ;
  if !debug_completion then
    begin 
    Printf.printf "Completions of P\n%!";
    show_all_completions bijection.partial_completions_P;
    Printf.printf "Completions of Q\n";
    show_all_completions bijection.partial_completions_Q end ;
  Bijection.reorder_tests () ;
  let nb_tests_init = bijection.next_id in
  if !about_progress then Printf.printf "Testing %d tests\n%!" bijection.next_id;
  let nb_open = ref 0 in
  let time_start_tests = if !about_bench then get_time() else 0. in  
  let time_ten_tests = ref time_start_tests in (
  try
    while not (Bijection.Tests.is_empty bijection.tests) do
      (*if !about_progress then Printf.printf "\n\n+++++ New iteration of the big loop +++++\n%!";
      if !about_progress then Printf.printf "Testing %d tests\n%!" (Tests.cardinal bijection.tests);*)
      (*while not (Tests.is_empty bijection.tests) do*)
        let test = pop () in
        incr nb_open;
        if !about_bench && !nb_open = 10 then time_ten_tests := get_time();
        if !debug_tests then Printf.printf (if !use_xml then "<opentest>%s" else "\nApply \"New Sol\" on %s\n%!") (show_test test);
        if !about_progress && (not !debug_tests) 
        then 
          ( 
          if !nb_open mod 125 = 0 then 
            let nbstack = (Bijection.Tests.cardinal bijection.tests) in 
            Printf.printf "%d> Open test #%d (%d in stack%s), comp: %d, at %.1f\n%!" !nb_open test.id nbstack (if nbstack < 50 then Bijection.show_test_set bijection.tests else "") bijection.next_comp_id (get_time() -. time);
          if !nb_open mod 5000 = 0 && !about_bijection then Bijection.show_bijection()  
          );
        find_set_of_runs test ;
        if !debug_tests && !use_xml then Printf.printf "</opentest>";
      (*done ;
    if !about_progress && !about_bijection then Bijection.show_bijection();
    if !about_progress then 
      Printf.printf "\n\n __Actualization of completions of P (%d runs)__\n%!" (List.length bijection.runs_for_completions_Q);*)
    compute_new_completions P ; 
    (*if !about_progress then 
      Printf.printf "\n\n __Actualization of completions of Q (%d runs)__\n%!" (List.length bijection.runs_for_completions_P);*)
    compute_new_completions Q ; 
    done ;
  with
  | Attack(test,sol) -> ());
  
    if !about_tests then show_all_tests ();
    if !about_completion then show_final_completions ();
    if !about_bijection then show_bijection();
    if !about_bench then  Printf.printf 
      " time:%6.2f %s (%3d tests, mg:%3d, 10:%4.3f)%5d sat>%4d ded+%4d ri+%4d unr in%5.2f\n"  
      (get_time() -. time) 
      (if bijection.attacks = [] then if both then "tr equiv" else "tr incl " else " attack ")
      bijection.next_id (bijection.next_id - nb_tests_init)(!time_ten_tests -. time_start_tests)(nb_statements)  (count_statements bijection.satP.solved_deduction + count_statements bijection.satQ.solved_deduction)
      (count_statements bijection.satP.rid_solved + count_statements bijection.satQ.rid_solved)
      (List.length bijection.satP.unreachable_solved + List.length bijection.satQ.unreachable_solved)
      (time_sat -. time)
    else if !do_latex then (
      let t = (get_time() -. time) in
      if  t < 0.9 
      then Printf.printf "\\newcommand{\\%s}{$< 1$s}\n" !latex_identifier 
      else Printf.printf "\\newcommand{\\%s}{$%.0f$s}\n" !latex_identifier t)
    else (
      if bijection.attacks = [] 
      then (
          if both 
          then Printf.printf "\nP and Q are trace equivalent. \n" 
          else Printf.printf "\nTraces of P are included in Q. \n")
      else (
        verbose_execution:= true;
        let nba = List.length bijection.attacks in
        if nba=1 
        then Printf.printf "\nAn attack has been found:\n"
        else Printf.printf "\n%d attacks have been found:\n" nba;
        List.iter (fun (test,sol) -> 
          if !about_tests then Printf.printf "\n-A witness is %s \n with specific order %s"(show_test test)(show_dag sol.restricted_dag);
          Printf.printf "\nTrace of %s which is not possible in %s:\n" (show_which_process test.process_name)(show_which_process (other(test.process_name)));
          match actual_test test.process_name sol.sequence {test.statement with dag = sol.restricted_dag} with
          | _,None -> assert false
          | _,Some _ -> Printf.printf "Final identities:\n %s\n" (show_test_head (get_test_head(test.statement.head)))
          )
        bijection.attacks;
        verbose_execution:= false; ));
      clean_bijection();
      if ! use_xml then Printf.printf "</all>"
