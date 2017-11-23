(** {2 Executing and testing processes} *)
open Util
open Types
open Dag
open Base
open Process
open Bijection
open Term


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
      let fa_head = 
        match fa.head with
        | Tests(l) -> l
        | Identical(r,r') -> [(r,r')]
        | Knows(_)
        | Reach -> [] in
      let fb_head = 
        match fb.head with
        | Tests(l) -> l
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
             (Util.unique(fa_head @ fb_head)));
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
  
let init_run process_name (statement : raw_statement) processQ test : partial_run=
  let (qt,fqt) = run_until_io processQ LocationSet.empty Inputs.new_inputs in
   {
     test = test ;
     corresp = { a = Dag.empty } ;
     corresp_back = { a = Dag.empty } ;
     remaining_actions = LocationSet.of_list(List.map (fun (x,y) -> x) (Dag.bindings statement.dag.rel)) ;
     frame = Inputs.new_inputs; (* inputs maps to received terms and outputs maps to sent terms *)
     choices = Inputs.new_choices;
     dag = empty;
     disequalities = [] ;
     qthreads = qt ;
     failed_qthreads = fqt;
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
  {
     test = run.test ;
     corresp = { a = Dag.add action l run.corresp.a } ;
     corresp_back = { a = Dag.add l action run.corresp_back.a } ;
     remaining_actions = LocationSet.remove action run.remaining_actions ;
     frame = frame;
     choices = choices;
     dag = merge run.dag (dag_with_one_action_at_end locs action);
     disequalities = diseq @ run.disequalities;
     qthreads = qt ;
     failed_qthreads = fqt @ run.failed_qthreads ;
  }
  

  
let rec apply_frame recipe prun =
  match recipe with
    | Fun({ id=Frame(l)}, []) -> Inputs.get (Bijection.loc_p_to_q l prun.corresp) prun.frame
    | Fun({ id=Input(l)}, []) -> Inputs.get l prun.frame
    | Fun(f, args) -> Fun(f, List.map (fun x -> apply_frame x prun) args)
    | Var(x) -> Var(x)

(* Given a partial_run run, try to execute action action on one of the available threads of Q *)        
let try_run run action (choices,locs,diseq,process)  =
   (*Printf.printf "Testing %s against %s\n" action.chan.name (show_process_start 1 process);*)
   match Inputs.merge_choices run.choices choices with
   | None -> []
   | Some choices -> 
   match process with
   | SeqP(Input(l),p) -> 
     if action.io = l.io (* make sure channel still work *)
     then 
       begin 
         let new_frame = Inputs.add_to_frame l 
            (apply_frame (Inputs.get action run.test.statement.recipes) run) run.frame in
         let npr = next_partial_run run action process p l new_frame locs choices diseq in
         (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
        [npr] 
       end
       else []
   | SeqP(Output(l,t),p) -> 
     if action.io = l.io 
     then begin
       let new_frame = Inputs.add_to_frame l (apply_subst_inputs t run.frame) run.frame in
       let npr = next_partial_run run action process p l new_frame locs choices diseq in
       (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
       [npr]
     end
     else []
   | _ -> assert false

(* Given a partial_run select an action to execute and test this action on all available threads of Q *)
let next_run partial_run = 
  if ! debug_execution then Printf.printf "Next execution step on %s" (show_partial_run partial_run);
  let first_actions = first_actions_among partial_run.test.statement.dag partial_run.remaining_actions in
  let current_loc = 
    try LocationSet.choose first_actions 
    with
    Not_found -> begin Printf.printf "No run on %s [%s] \n" (show_dag partial_run.test.statement.dag) (show_loc_set partial_run.remaining_actions); assert false end
  in
  List.fold_left (fun new_runs lp -> (try_run partial_run current_loc lp) @ new_runs ) [] partial_run.qthreads ,
  current_loc

(* When two recipes are provided for the same term just choose one *)
let same_term_same_recipe st =
  let sigma_repl = Array.make st.nbvars None in
  let sigma = (sigma_repl, Array.make 0 None) in
  st.binder := Master;
  (*Printf.printf "simplification of %s\n" (show_raw_statement st);*)
  let (useless,body) =
    List.partition
      (fun a ->
         let recipe_var = Term.unbox_var a.recipe in
         let t = a.term in
         try
         let is_better =  List.find 
           (fun a' -> let recipe_var' = Term.unbox_var a'.recipe in
              recipe_var.n < recipe_var'.n &&
              t = a'.term ) st.body in
           let x = Term.unbox_var(is_better.recipe) in
           sigma_repl.(x.n) <- Some a.recipe ;
           true       
         with Not_found -> false
         )
       st.body
  in
  if !about_canonization then
    List.iter (fun a -> Format.printf "Removed %s\n" (show_body_atom a)) useless ;
  if useless = [] then st 
  else 
    let sigma = Rewriting.pack sigma in
    Horn.apply_subst_statement { st with body = body;} sigma


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
  List.iter (fun st -> statements_to_tests process_name st otherProcess) statement.children
  
let base_to_tests process_name base otherProcess = 
  List.iter (fun st -> 
    statement_to_tests process_name (Initial(st)) st.st otherProcess) base.other_solved;
  statements_to_tests process_name base.solved_deduction otherProcess  

let compatible constraints constraints_back locP locQ = 
  try locQ = Dag.find locP constraints.a
  with Not_found -> begin 
    try Dag.find locQ constraints_back.a  =  locP 
    with Not_found -> true end
          
let compatible_prun constraints constraints_back prun =
  Dag.for_all (compatible constraints constraints_back) prun.corresp.a
  
let check_recipes partial_run (r,r')=
  let r = apply_frame r partial_run in
  let r' = apply_frame r' partial_run in
  (*let r'' = Rewriting.normalize r (! Parser_functions.rewrite_rules) in
  let r''' = Rewriting.normalize r' (! Parser_functions.rewrite_rules) in
  Printf.printf "recipes %s and %s\n %s\n>> %s \n=? %s\n" 
    (show_term r)(show_term r')(Inputs.show_inputs partial_run.frame)(show_term r'')(show_term r''');*)
  Rewriting.equals_r r r' (! Parser_functions.rewrite_rules) 

let next_solution solution =
  match solution.partial_runs_priority_todo with
  | [] -> assert false
  | pr :: q -> 
    (*Printf.printf "next solution of\n%s"(show_partial_run pr) ;*)
    solution.partial_runs_priority_todo <- q ;
    solution.partial_runs <- pr :: solution.partial_runs;
    let (new_runs,new_loc) = next_run pr in 
    if !debug_execution && new_runs = [] then Printf.printf "No possible run from this trace \n"  ;
    List.iter (fun partial_run -> 
      if LocationSet.is_empty partial_run.remaining_actions 
      then begin
        if 
        match partial_run.test.statement.head with 
        | Knows(_)
        | Reach -> true
        | Identical(t,t') -> check_recipes partial_run (t,t') 
        | Tests(l) -> List.for_all (check_recipes partial_run) l 
        then 
          begin if !debug_execution then Printf.printf "Solution succeeds the tests \n"  ;
          solution.possible_runs_todo <- partial_run :: solution.possible_runs_todo end
        else
          begin if !debug_execution then Printf.printf "Solution fails the tests \n"  ;
          solution.failed_run <- partial_run :: solution.failed_run end
      end
      else begin
        if 
          if is_empty_correspondance partial_run.test.constraints 
          then Bijection.straight new_loc (loc_p_to_q new_loc partial_run.corresp) (* TODO: restricted run should not have priority *)
          else compatible_prun partial_run.test.constraints partial_run.test.constraints_back partial_run
        then begin if !debug_execution then Printf.printf "Straight \n"  ;
          solution.partial_runs_priority_todo <- partial_run :: solution.partial_runs_priority_todo end
        else begin if !debug_execution then Printf.printf "Not Straight \n"  ;
          solution.partial_runs_todo <- partial_run :: solution.partial_runs_todo end
      end
      ) new_runs 




let next_solution_else constraints constraints_back solution =
  match solution.partial_runs_priority_todo with
  | [] -> assert false
  | pr :: q -> 
    (*Printf.printf "next solution of\n%s"(show_partial_run pr) ;*)
    solution.partial_runs_priority_todo <- q ;
    solution.partial_runs <- pr :: solution.partial_runs;
    let (new_runs,new_loc) = next_run pr in 
    if !debug_execution && new_runs = [] then Printf.printf "No possible run from this trace \n"  ;
    List.iter (fun partial_run -> 
        (*Printf.printf "constraints: %s\n" (show_correspondance constraints);*)
        if compatible constraints constraints_back new_loc (loc_p_to_q new_loc partial_run.corresp)
        then 
        begin 
          if LocationSet.is_empty partial_run.remaining_actions 
          then begin
            if !debug_execution then Printf.printf "The reverse trace ends \n"  ;
            solution.possible_runs_todo <- partial_run :: solution.possible_runs_todo 
          end
          else begin if !debug_execution then Printf.printf "Straight \n"  ;
          solution.partial_runs_priority_todo <- partial_run :: solution.partial_runs_priority_todo end
        end
        else if !debug_execution then Printf.printf "Not allowed \n"  
      ) new_runs      
      
 let rec find_all_run constraints constraints_back solution =
  match solution.possible_runs_todo with
  | [] -> begin
    if solution.partial_runs_priority_todo = [] 
    then begin 
      if solution.partial_runs_todo = []
      then 
        if Solutions.is_empty solution.possible_runs 
        then begin
          if solution.possible_restricted_runs = [] then
            Solutions.empty
          else begin Printf.printf "Further investigation are required (%d partial dags not considered).\n" (List.length solution.possible_restricted_runs); 
            Solutions.empty end 
          end
        else begin (* All possible run have been tested, return the resulting set *)
          solution.possible_runs 
        end 
      else begin
        if !debug_execution then Printf.printf "No priority partial run anymore \n" ;
        solution.partial_runs_priority_todo <- solution.partial_runs_todo ;
        solution.partial_runs_todo <- [];
        find_all_run constraints constraints_back solution end
      end
    else (* All solutions from the last execution have been performed, start a new one *)
      begin next_solution_else constraints constraints_back solution; 
      find_all_run constraints constraints_back solution end
    end
  | pr::q ->
    solution.possible_runs_todo <- q ;
    if !debug_execution then Printf.printf "complete run: %s\n"(show_run pr) ;
    if subset pr.dag pr.test.statement.dag 
    then begin
      let conflicts = Bijection.compatible pr in
      solution.possible_runs <- Solutions.add conflicts solution.possible_runs;
      find_all_run constraints constraints_back solution
    end
    else begin
      if !debug_execution then Printf.printf "Partial dag\n";
      solution.possible_restricted_runs <- pr :: solution.possible_restricted_runs;
      find_all_run constraints constraints_back solution
      end

let rec transpose term corresp = 
  match term with
  | Var(_) -> term
  | Fun({id=Frame(loc)} as f, []) -> Fun({f with id=Frame(loc_p_to_q loc corresp)}, [])
  | Fun(f,args) -> Fun(f,List.map (fun t -> transpose t corresp) args)
  
let apply_var_set_pred predi subst corresp =
  Printf.printf "corresp %s \n" (show_correspondance corresp);
  match predi with
  | Reach -> Reach
  | Knows(_) -> Reach
  | Identical(r,r') -> 
    Identical(apply_var_set_subst (transpose r corresp) subst,apply_var_set_subst (transpose r' corresp) subst)
  | Tests(lst) -> Tests(List.map (fun (r,r') -> 
    (apply_var_set_subst (transpose r corresp) subst,apply_var_set_subst (transpose r' corresp) subst)) lst)

let partial_run_to_shrink_statement pr =
  if !debug_else then Printf.printf "run to shrink %s\n" (show_run pr);
  let binder = ref Master in
  let (body,map,map_loc_recipe,map_recipe,nbv) = 
    Dag.fold (fun loc t (body,map,map_loc_recipe,map_recipe',nb) -> 
      match loc.io with 
      | Input(_) -> 
      let (body,map,map_recipe,nb) = 
        VariableSet.fold (fun x (body,map,map_recipe,nb) ->  
          let (x',nw,map) =
            try (VarMap.find x map,0,map)
            with Not_found -> begin 
              let x' = Var{n = nb; status = binder} in  
              (x',1,VarMap.add x x' map) end
          in
          let new_recipe = Var {n = nb + nw; status = binder} in
          let map_recipe = VarMap.add x new_recipe map_recipe in
          let premisse = {
            loc = Some loc; 
            recipe = new_recipe ;
            term = x'; 
            marked = false} in
          (premisse :: body, map,map_recipe, nb + 1 + nw))
        (Term.var_set_of_term (VariableSet.empty) t) (body,map,VarMap.empty,nb) in
      (body, map, Dag.add loc map_recipe map_loc_recipe, VarMap.union (fun x r r' -> Some r) map_recipe map_recipe' , nb)
      | _ -> (body,map,map_loc_recipe,map_recipe',nb)
      ) pr.frame.i ([],VarMap.empty,Dag.empty,VarMap.empty,0) in
  let binder = ref Master in
  if !debug_else then Printf.printf "which test is %s \n" (show_raw_statement pr.test.statement);
  ({
    binder = binder ;
    nbvars = nbv ;
    dag = { rel = Dag.fold (fun loc locset dag -> 
        Dag.add (loc_p_to_q loc pr.corresp) (LocationSet.map (fun l -> loc_p_to_q l pr.corresp) locset) dag) 
      pr.dag.rel Dag.empty} ;
    inputs = { i = Dag.map (fun term -> apply_var_set_subst term map) 
      (Dag.filter (fun loc _ -> 
        match loc.io with 
        Input(_) -> true 
        | _ -> false) pr.frame.i) };
    recipes = { i = Dag.fold (fun loc term dag -> 
      match loc.io with 
      | Virtual _ -> Dag.add loc term dag
      | Input _ ->
      let loc = loc_p_to_q loc pr.corresp in 
      Dag.add loc
      (transpose (apply_var_set_subst term (
        try Dag.find loc map_loc_recipe 
        with Not_found ->  failwith "stop")) pr.corresp)
      dag) 
      pr.test.statement.recipes.i (
        VarMap.fold (fun x r recipe -> 
          let p = Process.processes_infos.next_location + 1 in
          Process.processes_infos.next_location <- p ;
          Dag.add {p= p; io = Virtual(x); name = "v"} r recipe) map_recipe Dag.empty)};
    choices = pr.choices ;
    head = Reach ;
    body = body ; 
  },map)
  
let refine_recipes test st corresp =
  let (recipes,varset) = Dag.fold (fun loc t (recipes,varset) -> 
    match loc.io with 
    | Virtual(x) -> (recipes,VarMap.add x t varset)
    | _ -> (Dag.add loc t recipes, varset)) st.recipes.i (Dag.empty,VarMap.empty) in
  {
    st with
    recipes = {i = recipes} ;
    head = apply_var_set_pred test.head varset corresp
  }
  
let consider_disequalities partial_run =
  if partial_run.disequalities = [] then ()
  else 
    let (st,subst) = partial_run_to_shrink_statement partial_run in
    if !debug_else then Printf.printf "shrunk statement %s" (show_raw_statement st);
    let kb = match partial_run.test.process_name with
    | P -> bijection.satQ
    | Q -> bijection.satP in
    kb.other_solved <- [] ; (* All new tests will be collected here, need to clean from previous tests *)
    List.iter (fun (t,t') ->
      let t = apply_var_set_subst (apply_subst_inputs t  partial_run.frame) subst in
      let t'= apply_var_set_subst (apply_subst_inputs t' partial_run.frame) subst in
      Printf.printf "-diseq %s = %s\n" (show_term t)(show_term t'); 
      List.iter 
        (fun subst -> 
          let raw_st = Horn.apply_subst_statement st subst in
          Horn.add_statement kb null_statement kb.not_solved None raw_st;
          while not (Queue.is_empty(kb.ns_todo)) do
            begin let unsolved = Queue.take(kb.ns_todo) in
            if !debug_saturation then Printf.printf "[else] Start resolutions of #%d\n" unsolved.id;
            List.iter (fun solved -> Horn.process_resolution_new_unsolved kb solved unsolved) kb.solved_deduction.children end
          done 
        ) 
        (Rewriting.unifiers st.nbvars t t' (! Parser_functions.rewrite_rules)))
      partial_run.disequalities ;
    List.iter (fun st -> 
      if !debug_else then Printf.printf "Trace to test %s \n" (show_statement ">" st);
      let test = {
        nb_actions = 0;
        new_actions = 0;
        process_name = (other partial_run.test.process_name);
        statement = st.st;
        origin = Else;
        id = 0;
        from = IntegerSet.empty;
        constraints = partial_run.corresp_back;
        constraints_back = partial_run.corresp;
      }   
      in
      let prun = init_run (other partial_run.test.process_name) st.st (proc partial_run.test.process_name) test in
      let solution =
      {
        partial_runs = [prun] ;
        partial_runs_todo = [] ;
        partial_runs_priority_todo = [prun] ;
        possible_restricted_runs = [];
        possible_runs = Solutions.empty;
        possible_runs_todo = [];
        failed_partial_run = [];
        failed_run = [];
        partitions = [] ;
      } in
      let solutions = find_all_run partial_run.corresp_back partial_run.corresp solution in
      show_solution_set solutions;
      Solutions.iter (fun pr -> 
        let(raw_st,_) = partial_run_to_shrink_statement {pr.execution with dag = merge pr.execution.dag st.st.dag} in 
        Printf.printf "** %s \n %s" (show_raw_statement raw_st)(show_run pr.execution);
        let raw_st = refine_recipes partial_run.test.statement raw_st pr.execution.corresp_back in
        Printf.printf "++ %s " (show_raw_statement raw_st);
        statement_to_tests partial_run.test.process_name (Refined(partial_run,st)) raw_st (proc (other partial_run.test.process_name))
        )
        solutions 
    ) kb.other_solved
    
      
      
let rec find_compatible_run solution =
  match solution.possible_runs_todo with
  | [] -> begin
    if solution.partial_runs_priority_todo = [] 
    then begin 
      if solution.partial_runs_todo = []
      then 
        if Solutions.is_empty solution.possible_runs 
        then begin
          if solution.possible_restricted_runs = [] then
            None
          else begin Printf.printf "Further investigation are required (%d partial dags not considered).\n" (List.length solution.possible_restricted_runs); 
            None end 
          end
        else begin (* All possible run have been tested, we take the better one and add the tests of its conflicts *)
          try Some (Solutions.min_elt (Solutions.filter (fun sol -> 
              compatible_prun sol.execution.test.constraints sol.execution.test.constraints_back sol.execution)
            solution.possible_runs)) 
          with Not_found -> None end
      else begin
        if !debug_execution then Printf.printf "No priority partial run anymore \n" ;
        None (* because other partial run are not compatible *)
        end
      end
    else (* All solutions from the last execution have been performed, start a new one *)
      begin next_solution solution; 
      find_compatible_run solution end
    end
  | pr::q ->
    solution.possible_runs_todo <- q ;
    if !debug_execution then Printf.printf "complete run: %s\n"(show_run pr) ;
    if subset pr.dag pr.test.statement.dag 
    then begin
      let conflicts = Bijection.compatible pr in
      if compatible_prun pr.test.constraints pr.test.constraints_back pr then
        begin
        (*Bijection.add_partial_run pr;
        solution.partitions <- [pr];
        consider_disequalities pr;*)
        (*solution.possible_runs <- pr :: solution.possible_runs;*)
        Some conflicts
        end
      else begin 
        if !debug_execution then Printf.printf "Solution in conflict \n";
        solution.possible_runs <- Solutions.add conflicts solution.possible_runs;
        find_compatible_run solution
        end
      end
    else begin
      if !debug_execution then Printf.printf "Partial dag\n";
      solution.possible_restricted_runs <- pr :: solution.possible_restricted_runs;
      find_compatible_run solution
      end
 


      
      
exception Attack   

let get_lst_of_test test =
  match test with 
  Tests(t) -> t
  | Identical(r,r') -> [(r,r')]
  | _ -> []

(* Create new tests from prun which is in conflict with all tests in runset *)
let add_merged_tests sol =
  let (prun,runset)=sol.execution,sol.conflicts in
  if !debug_tests 
  then Printf.printf "Conflicts on %s\n" (show_loc_set sol.conflicts_loc); 
  RunSet.iter (fun par ->
    if false && !debug_tests 
    then Printf.printf "   with %s\n" (show_test par.test); 
    if prun.test.process_name = par.test.process_name 
    then
      
      if ((Inputs.contains prun.test.statement.inputs par.test.statement.inputs) &&  (Util.list_diff (get_lst_of_test par.test.statement.head)(get_lst_of_test prun.test.statement.head) =[]))
      || ((Inputs.contains par.test.statement.inputs prun.test.statement.inputs) &&  (Util.list_diff (get_lst_of_test prun.test.statement.head)(get_lst_of_test par.test.statement.head) =[]))
      then ()  else
      begin
        let merged_statements =   merge_tests prun.test.statement par.test.statement in (* only one without xor *)
        List.iter (fun raw_st -> 
          if !debug_tests then Printf.printf "New test %s \n" (show_raw_statement raw_st);
          statement_to_tests prun.test.process_name (Composed(prun,par)) raw_st (proc (other prun.test.process_name))
          ) merged_statements
      end
    else begin
      if !debug_execution 
      then Printf.printf " TODO : coarse equivalence not enough\n" ; 
      (*raise Attack*)()
   end
  ) runset
  

let find_compatible_run_init constraints constraints_back run  =
  if  (compatible_prun constraints constraints_back run) then true
  else
  let solution = Tests.find run.test bijection.registered_tests in
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
      Bijection.add_run solution sol.execution; 
      solution.partitions <- [sol.execution] ;
      add_merged_tests sol; (*Attention ça peut boucler ici *)
      (*consider_disequalities sol.execution;*)
      if !debug_tests then Printf.printf "Solution %s replaced by %s \n" (show_run run) (show_run sol.execution);
      true
  | None -> false


      
let rec find_possible_run solution =
  match solution.possible_runs_todo with
  | [] -> begin
    if solution.partial_runs_priority_todo = [] 
    then begin 
      if solution.partial_runs_todo = []
      then 
        if Solutions.is_empty solution.possible_runs 
        then begin
          if solution.possible_restricted_runs = [] then
            None
          else begin Printf.printf "Further investigation are required (%d partial dags not considered).\n" (List.length solution.possible_restricted_runs); 
            None end 
          end
        else begin (* All possible run have been tested, we take the better one and add the tests of its conflicts *)
          let sol = Solutions.min_elt solution.possible_runs in
          (*add_merged_tests sol; 
          Bijection.add_run solution sol.execution;
          solution.partitions <- [sol.execution];*)
          Some sol end 
      else begin
        if !debug_execution then Printf.printf "No priority partial run anymore \n" ;
        solution.partial_runs_priority_todo <- solution.partial_runs_todo ;
        solution.partial_runs_todo <- [];
        find_possible_run solution end
      end
    else (* All solutions from the last execution have been performed, start a new one *)
      begin next_solution solution; 
      find_possible_run solution end
    end
  | pr::q ->
    solution.possible_runs_todo <- q ;
    if !debug_execution then Printf.printf "complete run: %s\n"(show_run pr) ;
    if subset pr.dag pr.test.statement.dag 
    then begin
      let conflicts = Bijection.compatible pr in
      if conflicts.score = 0 then
        begin
        (* Bijection.add_run solution pr;
        solution.partitions <- [pr]; *)
        (*consider_disequalities pr;*)
        solution.possible_runs <- Solutions.add conflicts solution.possible_runs;
        Some conflicts
        end
      else begin 
        if !debug_execution then Printf.printf "Solution in conflict \n";
        solution.possible_runs <- Solutions.add conflicts solution.possible_runs;
        find_possible_run solution
        end
      end
    else begin
      if !debug_execution then Printf.printf "Partial dag\n";
      solution.possible_restricted_runs <- pr :: solution.possible_restricted_runs;
      find_possible_run solution
      end
      
 



let equivalence p q =
  Printf.printf "Saturating P\n";
  let (locP,satP) = Horn.saturate p in
  if  !Util.about_saturation then
    Printf.printf "Saturation of P:\n %s\n" (Base.show_kb satP);
  Printf.printf "Saturating Q:\n%!";
   let (locQ,satQ) = Horn.saturate q in
  if  !Util.about_saturation then
    Printf.printf "Saturation of Q:\n %s\n" (Base.show_kb satQ);
  let processP = (CallP({p = locP;io=Call;name="main"},
    p,Array.make 0 zero,Array.make 0 null_chan)) in
  let processQ = (CallP({p = locQ;io=Call;name="main"}, 
    q,Array.make 0 zero,Array.make 0 null_chan)) in 
  bijection.p <- processP ;
  bijection.q <- processQ ;
  bijection.satP <- satP ;
  bijection.satQ <- satQ ;
  Printf.printf "Building tests\n%!";
  base_to_tests P satP processQ ;
  base_to_tests Q satQ processP ; 
  Bijection.reorder_tests () ;
  Printf.printf "Testing %d tests\n%!" (Tests.cardinal bijection.tests);
  try
    while not (Tests.is_empty bijection.tests) do
      let (test, solution) = pop () in
      let valid = 
        match test.origin with
        | Initial _ -> true
        | Composed (run1,run2) -> 
          let sol1 = Tests.find run1.test bijection.registered_tests in
          let sol2 = Tests.find run2.test bijection.registered_tests in
          (List.mem run1 sol1.partitions) && (List.mem run2 sol2.partitions)
        | Refined(run,st) -> let sol = Tests.find run.test bijection.registered_tests in
          List.mem run sol.partitions
        | Else -> assert false 
      in
      if valid then begin
        if !debug_tests then Printf.printf "Open %s\n%!" (show_test test);
        match find_possible_run solution with 
        | None ->  Printf.printf "Failure to pass %s\n" (show_test test);
            List.iter (fun pr -> Printf.printf "%s\n" (show_correspondance pr.corresp)) solution.partial_runs;
          raise Attack;
        | Some sol -> 
          let pr = sol.execution in
          if ! debug_tests then Printf.printf "Success of test %d: %s \n\n" test.id (show_correspondance pr.corresp);
          if match test.origin with
            | Composed (run1,run2) -> 
                if find_compatible_run_init pr.corresp pr.corresp_back run1 &&
                find_compatible_run_init pr.corresp pr.corresp_back run2 
                then false
                (* ne pas ajouter le test... *)
                else true 
            | _ -> true
          then begin
                  add_merged_tests sol; 
                  Bijection.add_run solution pr;
                  solution.partitions <- [pr];
                  (*consider_disequalities pr;*)
          end
      end
    done ;
    if !about_execution then Bijection.show_bijection();
    Printf.printf "P and Q are coarse trace equivalent. \n" 
  with
  | Attack -> begin 
  if !about_execution then Bijection.show_bijection();
  Printf.printf "P and Q are not trace equivalent. \n" 
  end
