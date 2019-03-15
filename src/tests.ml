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
  
            
(** from two statements (ie tests), the function generate the merge of these tests, like equation rule
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
    else 
    let fa_head_equal, fa_head_diseq = recipes_of_head fa.head in
    let fb_head_equal, fb_head_diseq = recipes_of_head fb.head in  
    let r =
    List.fold_left
      (fun lst sigma ->
        let sigma = Rewriting.pack sigma in
        (*let sigma , body , unsolved = opti_find_recipe sigm merged_dag fa fb in*)
        let body =
               List.map (fun x -> {
               loc = x.loc ; 
               recipe = Rewriting.apply_subst_term x.recipe sigma ;
               term = Rewriting.apply_subst_term x.term sigma ;
               marked = x.marked }
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
        try 
        let (tau,test_merge_init) = Horn.simplify_statement test_merge_init in
        match Horn.normalize_new_statement test_merge_init with
        None -> lst
        | Some test_merge_init ->
        if !debug_merge then Printf.printf "The init merged test from subst %s:\n %s \n%!"
          (show_substitution sigma)(show_raw_statement test_merge_init);
        let rho = Rewriting.compose sigma tau in
        if Horn.is_solved test_merge_init then 
          (rho,test_merge_init)::lst
        else (
        let kb = base_of_name process_name in
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
        Horn.merge_sat kb;
        if !about_rare 
        then ( 
          Printf.printf "Saturation triggered for %s \n" (show_raw_statement test_merge_init);
          if List.length kb.temporary_merge_test_result > 1 
          then 
            Printf.printf "%d solutions have been found:\n%s\n%!"
              (List.length kb.temporary_merge_test_result)
            (List.fold_right (fun st str -> str ^ (show_statement " *" st)) kb.temporary_merge_test_result "")
        );
        let res = (List.fold_left (fun lst st -> 
          if !debug_merge then Printf.printf "merge result st matched with: \n%s\n%s\n" (show_statement "" st)(show_raw_statement test_merge_init);
          if st.st.nbvars = 0 then 
            (rho,st.st)::lst
          else ( Printf.eprintf "|*|\n%!";
            match Inputs.csm false test_merge_init.binder test_merge_init.inputs st.st.inputs, 
              Inputs.csm_recipes false test_merge_init.binder test_merge_init.recipes st.st.recipes with
            | [subst_inputs],[subst_recipes] -> (Rewriting.compose_with_subst_lst rho (subst_inputs @ subst_recipes),st.st)::lst
            | [], _ -> assert false
            | _, [] -> lst
            | _ -> Printf.eprintf "This unification case has not been implemented yet." ; assert false
             )
          ) lst kb.temporary_merge_test_result
        ) in
        assert (res != [] || kb.temporary_merge_test_result= []);
        res)
        (*let new_dag = ref merged_dag in
        try
          List.iter (fun x ->  
            let n = (Term.unbox_var x.recipe).n in
            let base = if process_name = P then bijection.satP else bijection.satQ in
            match tau.(n) with
            | None ->
              if !debug_merge then Printf.printf "Looking for a recipe in %s for %s\n" (show_which_process process_name)(show_term x.term);
                let recipe = best_recipe base test_merge_init new_dag unsolved x in
                if !debug_merge then Printf.printf "recipe = %s\n" (show_term recipe);
                tau.(n) <- Some recipe (*;
                if not (recipe_with_earlier_messages merged_dag x.loc recipe)
                then (Printf.eprintf "Not implemented yet:\n %d -> %s < %s in\n%s" n (show_term recipe)(show_loc_set x.loc) (show_raw_statement test_merge_init);exit 1) *)
            | Some recipe -> ()
              ) unsolved;
          let tau = Rewriting.pack {m=tau; s=Array.make 0 None;e=[]} in
          let result = apply_subst_statement {test_merge_init with dag = !new_dag} tau in
          if !debug_merge then Printf.printf "The merged test: %s\n%!" (show_raw_statement result);
          let (sigm,result) = same_term_same_recipe result in
          if !debug_merge then Printf.printf "New clean merged test: %s\n%!" (show_raw_statement result);
          let rho = Rewriting.compose sigma (Rewriting.compose_master tau sigm) in
          if !debug_merge then Printf.printf "Final substitution rho: %s\n%!" (show_substitution rho);
          (rho,result) :: lst
        with
        No_recipe -> 
          if !debug_merge then Printf.printf "No recipe found for some input aborting...\n%!"  ; 
          lst *)
      with
      Horn.Unsound_Statement -> lst
      ) [] sigmas
    in
    fa.binder:= New;
    fb.binder:= New;  
    r 

   

(** This function returns false if the statement is not executable in his own processus
(due to disequalities or identities) true otherwise.
Correspond to actual reach of the theory *) 
let actual_test process_name sequence (st : raw_statement) =
  let corr = {a = Dag.mapi (fun k _ -> k) st.dag.rel} in
  let test = { null_test with
    process_name = process_name;
    reflexive = true;
    statement = st;
    constraints = corr;
    constraints_back = corr;
  } in
  if !debug_execution 
  then Printf.printf "\nChecking actual of %s \nwith dag = %s\n%!" (show_test test)(show_dag st.dag);
  let solution = init_sol process_name st (proc process_name) sequence test in
  let pr = find_possible_run solution in
  if !debug_tests then (
    match pr with
    | None ->  Printf.printf "No execution for this test\n" 
    | Some pr -> ());
  pr

    
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
    }) st.body ;
  recipes = transpose_recipes identity_sigma st.recipes run.corresp ; 
  involved_copies = BangSet.empty ; (* TODO *)
  } in
  stP.binder := New;
  (identity_sigma,r)
  
let filter_atom set a =
  LocationSet.exists (fun l -> LocationSet.mem l set) a.loc
  
let filter_dag set dag =
  {rel = Dag.filter (fun l _ -> LocationSet.mem l set) dag.rel}
  
let filter_inputs set (inputs : Inputs.inputs) :Inputs.inputs =
  {i = Dag.filter (fun l _ -> LocationSet.mem l set) inputs.i}
  
  
let filter_choices set (choices : Inputs.choices) : Inputs.choices = 
  (*Printf.printf "loc: %s | %s \n" (show_loc_set set)(Inputs.show_choices choices);*)
  let result = ref LocationSet.empty in
  let rec parent_set set = 
    List.iter (fun loc -> 
    List.iter (fun (l : location) -> 
      (*Printf.printf "%d-" l.p;*)
      if not( LocationSet.mem l !result) 
      then (
        result := LocationSet.add l !result;
      match l.io with 
      | Choice -> ()
      | _ ->
          let l' = Inputs.get_output_of_input choices l in
          result := LocationSet.add l' !result;
          parent_set l'.parent_choices))
       loc.parent_choices) set 
       in
  parent_set (LocationSet.elements set) ;
  (*Printf.printf "loc: %s \n" (show_loc_set !result);*)
  {c = Dag.filter (fun l _ -> LocationSet.mem l !result) choices.c }
  
let trunconj set run =
  let stP = run.test.statement in
  let identity_sigma = Rewriting.identity_subst stP.nbvars in
  (*let binder = identity_sigma.binder in*)
  stP.binder := Master;
  let st = apply_subst_statement stP identity_sigma in
  let filtered_inputs = filter_inputs set st.recipes in
  let r = 
  {
  binder = st.binder ;
  nbvars = st.nbvars ;
  dag = trunc_map_dag (only_observable run.sol.restricted_dag) set run.corresp;
  inputs =  transpose_inputs identity_sigma filtered_inputs run  ;
  recipes = transpose_recipes identity_sigma filtered_inputs  run.corresp ; 
  choices = filter_choices (LocationSet.map (fun l -> loc_p_to_q l run.corresp) set) run.choices; 
  head = Tests({head_binder = st.binder; equalities=EqualitiesSet.empty; disequalities=EqualitiesSet.empty;});
  body = List.map (fun ba -> {
    loc = LocationSet.map (fun l -> loc_p_to_q l run.corresp) ba.loc;
    recipe = transpose_recipe identity_sigma ba.recipe run.corresp;
    term = apply_frame_2 identity_sigma ba.recipe run;
    marked = false;
    }) (List.filter (filter_atom set) st.body) ;
  involved_copies = BangSet.empty ; (* TODO *)
  } in
  (*Printf.printf "conjrun = %s\n" (show_raw_statement r);*)
  stP.binder := New;
  (identity_sigma,r)
  
let is_complex_xor_statement st = !Parser_functions.use_xor && List.exists (fun a -> match a.term with Fun(_) -> true | _ -> false) st.body

(*let identities_to_hash eqset vars=
  let next_id = ref 0 in
  term_to_hash_cano false next_id vars term*)

(*
let rec add_identities_to_completions head (*process_name*) compl = 
  let h = get_test_head (compl.st_c.head) in
  h.equalities <- EqualitiesSet.union h.equalities head.equalities;
  h.disequalities <- EqualitiesSet.union h.disequalities head.disequalities ;
  List.iter (fun (sigma,compl) -> add_identities_to_completions (apply_subst_test_head head sigma) (*process_name*) compl) compl.further_completions;
  match compl.generated_test with
  | None -> ()
  | Some (subst,test) -> complete_set_of_identities (transpose_test_head head subst compl.corresp_back_c) (*process_name*) test *)
  

(** [complete_set_of_identities head old_test] add the identities in [head] on [old_test] and its children *)
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
    if !debug_merge then Printf.printf " the new head is %s\n"(show_test_head h);
    List.iter (fun sol ->
      match sol.selected_run with
      | None -> if not !about_all_attacks then (Printf.printf "Test %d has no solution\n" old_test.id;assert false)
      | Some pr -> (
        match sol.bundle with
        | None ->
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
              head.head_binder := status;
              let tau = apply_subst_test_head head' sigma in
              head.head_binder := New;              
              complete_set_of_identities tau derived_test) 
            pr.consequences;
          (*head.head_binder := Master;
          List.iter (fun (sigma,compl) -> add_identities_to_completions (transpose_test_head (head') sigma compl.corresp_c) (*process_name*) compl) pr.completions;*)
          head.head_binder := New;
        | Some bundle -> assert false
          )
        ) old_test.solutions_done
  end

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
    let statement =  { statement with dag = dag } in
    statement.binder := New;
    let sequence = dag_to_sequence dag in
    let hash_trace = (Inputs.choices_to_hash statement.choices,dag_to_hash statement.dag) in
    let trace_node, vars = get_trace_tree statement sequence in
    let is_complex_xor = is_complex_xor_statement statement in
    match  TraceNodes.find_opt hash_trace trace_node.node with
    | Some Impossible -> None
    | Some (Simple(test,sol)) ->
      assert (not is_complex_xor);
      let sigma = Rewriting.merging_subst test.statement.nbvars test.statement.binder in
      let head_t = get_test_head statement.head in
      statement.binder := Master;
      let head' = apply_subst_test_head head_t sigma in
      if !debug_tests then 
        Printf.printf "Updating an existing test which is \n%s\nwith %s \n"
          (show_test test)(show_predicate statement.head)(*show_substitution sigma*);
      statement.binder := New ;
      complete_set_of_identities head' test ;
      if !debug_tests then 
        Printf.printf "End of update of %d\n" (test.id);
      Some (Some sigma,test)
    | Some(Bundle(lst)) -> (
        assert is_complex_xor;
        let hash_body = Base.body_to_hash statement.body in 
        match List.assoc_opt hash_body lst.sts with
        | Some (test,sol) ->
              let sigma = Rewriting.merging_subst test.statement.nbvars test.statement.binder in
              let head_t = get_test_head statement.head in
              statement.binder := Master;
              let head' = apply_subst_test_head head_t sigma in
              if !debug_tests then 
                Printf.printf "Updating an existing test which is \n%s\nwith %s \n"
                  (show_test test)(show_predicate statement.head)(*show_substitution sigma*);
              statement.binder := New ;
              complete_set_of_identities head' test ;
              if !debug_tests then 
                Printf.printf "End of update of %d\n" (test.id);
              Some (Some sigma,test)
        | None -> (
            match actual_test process_name sequence statement with
            | Some pr -> 
              let init = init_sol process_name statement otherProcess sequence in 
              let new_test = push statement process_name origin init in
              new_test.reflexive_run <- pr;
              lst.sts <- (hash_body,(new_test,List.hd new_test.solutions_todo)) :: lst.sts;
              Some (None,new_test)
            | None -> assert false
            )
        )
    | None -> (
      match actual_test process_name sequence statement with
      | Some pr -> 
        let init = init_sol process_name statement otherProcess sequence in 
        (* init is a partial function to allow cycle reference between test and partial run *)
        let new_test = push statement process_name origin init in
        new_test.reflexive_run <- pr;
        if is_complex_xor 
        then (
          trace_node.node <- TraceNodes.add hash_trace (
            Bundle({
              eq_hash = [];
              diseq_hash = [];
              corr_bundle = empty_correspondance;
              corr_back_bundle = empty_correspondance;
              sts =[Base.body_to_hash new_test.statement.body,( new_test,List.hd new_test.solutions_todo)]})
            )trace_node.node)
        else (
          trace_node.node <- TraceNodes.add hash_trace (Simple(new_test,List.hd new_test.solutions_todo))trace_node.node);
      Some (None,new_test)
      | None -> 
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
    (*Printf.printf "is merge between < %d + %d >?\n" prun.test.id par.test.id; *)
    (* Check that we are merging test which have not been discarded before in the loop *)
    if Rewriting.get_option (par.sol.selected_run) == par
    || Rewriting.get_option (prun.sol.selected_run) == prun
    && prun.test.process_name = par.test.process_name
    then begin
        if !debug_merge then Printf.printf "Try merge between < %d + %d >" prun.test.id par.test.id; 
        let merged_statements = merge_tests prun.test.process_name 
          { prun.test.statement with dag = prun.sol.restricted_dag } 
          { par.test.statement with dag = par.sol.restricted_dag } in (* only one without xor *)
        (* if false && merged_statements = [] then (if !debug_tests then Printf.printf "i,")
        else *)
        List.iter (fun ((sigma : substitution),raw_st) -> 
          if !debug_tests && not(!debug_merge) then Printf.printf "Merge of %d with %d corresp %s\n" prun.test.id par.test.id (show_correspondance prun.corresp);
          assert (sigma.binder == raw_st.binder);
          (*if false && !debug_tests then Printf.printf "T,";*)
          match statement_to_tests prun.test.process_name (Composed(prun,par)) raw_st (proc (other prun.test.process_name)) with
          | Some (sigm,new_test) -> (
            let sigma = match sigm with
              | None -> sigma 
              | Some sigm -> 
                (*Printf.printf "composition \n%s\n%s\n%!" (show_substitution sigma) (show_substitution sigm); *)
                sigma.binder := Master;
                let s = Rewriting.compose sigma sigm in
                s in
            assert (sigma.binder == new_test.statement.binder) ;           
            if not (List.exists (fun (_,_,t) -> t==new_test) prun.consequences) then
              prun.consequences <- (Master,sigma,new_test) :: prun.consequences;
            if not (List.exists (fun (_,_,t) -> t==new_test) par.consequences) then
              par.consequences <-  (Slave,sigma,new_test) :: par.consequences )
          | None -> ()
        ) merged_statements 
      
    end
  ) runset;
  (*if false && !debug_tests then Printf.printf "\n"*)

(*(** When running a test several executions may have been found, look in this set to find a run which satisfies the new head *)  
and try_other_runs head solution =
  if Solutions.is_empty solution.possible_runs_todo then None
  else begin
    let pr =  Solutions.min_elt solution.possible_runs_todo in
    solution.possible_runs_todo <- Solutions.remove pr solution.possible_runs_todo ;
    if check_identities pr head then begin
      if !debug_execution || !debug_tests then Printf.printf "New selected execution:\n %s\n"(show_run pr) ;
      solution.selected_run <- Some pr;
      Some pr end
    else
      try_other_runs head solution
  end*)

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
      if ! debug_tests then Printf.printf "Execution of test %d \n with %s\n" test.id (show_run pr);
      Bijection.add_run pr;
      add_merged_tests pr;
      find_set_of_runs test
    )

(** The "completed" rule of the main algorithm *)      
let completion_to_test comp =
  let test = { null_test with
    process_name = comp.root.from_base;
    statement = comp.st_c;
    constraints = comp.corresp_back_c;
    constraints_back = comp.corresp_c;
  } in
  let sequence = dag_to_sequence comp.st_c.dag in
  let solution = init_sol comp.root.from_base comp.st_c (proc (other comp.root.from_base )) sequence test in
  match find_possible_run solution with
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
      | Identical(_,_) -> (*Printf.printf "*" ;*) CompletionIdentity(comp.root.from_statement)
      | _ -> assert false in 
    match statement_to_tests (other comp.root.from_base) origin conjrun (proc (comp.root.from_base )) with
    | Some (_,test) -> if !debug_completion || !debug_tests then Printf.printf "Got test from the completion\n %s\n" (show_test test);
      comp.generated_test <- Some (test) 
    | None -> if !debug_completion then Printf.printf "No test from the completion\n"; () end
    
let nb_comp = ref 0

(** Perform the rule "New Comp" *)
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
  let tau, conjrun = trunconj set run in
  let corr = { a = Dag.merge (fun locP x y -> 
    match x , y with
    | Some x, Some y -> if x = y then Some x else raise NonBij
    | Some x, None -> if LocationSet.mem locP set then Some x else None
    | None, Some y -> Some y
    | None, None -> None) run.corresp.a completion.corresp_c.a } in
  let corr_back = { a= Dag.filter (fun q p -> Dag.mem p corr.a) over_corr_back.a } in
  (*if !debug_completion then Printf.printf "Conj = %s \n" (show_raw_statement conjrun);*)
  if !debug_merge then Printf.printf "Merge run %d with comp %s\n" run.test.id (show_raw_statement completion.root.initial_statement);
  let sts = merge_tests completion.root.from_base conjrun completion.st_c in
  (*if !debug_completion && sts = [] then  Printf.printf "merge is not possible\n\n";*)
  List.iter (fun ((sigma : substitution),st) -> 
    bijection.next_comp_id <- bijection.next_comp_id + 1;
    let new_comp' = {
        id_c = bijection.next_comp_id;
        st_c = (*canonize_statement*) st;
        corresp_c = corr;
        corresp_back_c = corr_back;
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
        if !debug_completion then Printf.printf "Completion complete, checking test %s\n" (show_raw_statement st)(*todo*);
        completion_to_test new_comp ;
        if !debug_completion then Printf.printf "Completion complete, end of %s\n" (show_raw_statement st)(*todo*);
      end
    | _ , None -> ()
  ) sts)
  with 
  | NonBij -> ()

(** Compute the completions from the base of process_name *)      
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

(** From solved statements create tests. 
Opti: when children are identical with same world merge them with the reach parent to reduce number of tests *)  
let rec statements_to_tests t c process_name (statement : statement) otherProcess equalities =
  if !debug_tests then Printf.printf "Getting test (%d) %s %s \n%!" statement.id (if t then "yes" else "no") (show_raw_statement statement.st); 
  let sigma,raw_statement' = Horn.simplify_statement statement.st in (*sigma should be useless *)
  (*Printf.printf "simplified: %s\n" (show_raw_statement raw_statement');*)
  let equalities = 
    match statement.st.head with
    | Identical (s,t) -> 
      if c then (
        let compl = statement_to_completion process_name statement (negate_statement raw_statement') in
        ignore (register_completion compl);
        bijection.initial_completions <- compl :: bijection.initial_completions );
      EqualitiesSet.add ([],s,t) equalities
    | _ -> equalities in
  let new_eq = List.fold_left 
    (fun new_eq st -> 
      match st.st.head with
      | Identical (s,t) -> 
          if (st.st.inputs,st.st.dag,st.st.choices,st.st.body) = (statement.st.inputs,statement.st.dag,statement.st.choices,statement.st.body)
          then EqualitiesSet.add ([],s,t) new_eq
          else new_eq
      | _ -> new_eq )
    equalities statement.children in
    if t then ignore (statement_to_tests process_name (Initial(statement)) 
      {raw_statement' with 
        head = Tests(apply_subst_test_head {
          head_binder = statement.st.binder;
          equalities= new_eq; 
          disequalities = EqualitiesSet.empty} sigma)} 
      otherProcess);
    List.iter (fun st -> statements_to_tests t c process_name st otherProcess new_eq) statement.children
   
    

let unreach_to_completion process_name base = 
  List.iter (fun st -> let _, st' = Horn.simplify_statement st.st in 
    let compl = statement_to_completion process_name st (negate_statement st') in
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
          assert (None != actual_test test.process_name sol.sequence {test.statement with dag = sol.restricted_dag});
          Printf.printf "Final identities:\n %s\n" (show_test_head (get_test_head(test.statement.head)))
          )
        bijection.attacks;
        verbose_execution:= false; ));
      clean_bijection();
      if ! use_xml then Printf.printf "</all>"
