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
  

  
let rec apply_frame recipe (prun : partial_run) =
  match recipe with
    | Fun({ id=Frame(l)}, []) -> Inputs.get (Bijection.loc_p_to_q l prun.corresp) prun.frame
    | Fun({ id=Input(l)}, []) -> Inputs.get l prun.frame
    | Fun(f, args) -> Fun(f, List.map (fun x -> apply_frame x prun) args)
    | Var(x) -> Var(x)

(* Given a partial_run run, try to execute action on one of the available threads of Q *)        
let try_run all run action (choices,locs,diseq,process)  =
  let condition = if all 
    then 
      fun action l -> Bijection.mapping_exists run.test.process_name action l  
    else 
      fun action l -> action.io = l.io in 
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
            (apply_frame (Inputs.get action run.test.statement.recipes) run) run.frame in
         let npr = next_partial_run run action process p l new_frame locs choices diseq in
         (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
        Some (npr,l) 
       end
       else None
   | SeqP(Output(l,t),p) -> 
     if condition action l 
     then begin
       let new_frame = Inputs.add_to_frame l (apply_subst_inputs t run.frame) run.frame in
       let npr = next_partial_run run action process p l new_frame locs choices diseq in
       (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
       Some (npr,l)
     end
     else None
   | _ -> assert false

(* Given a partial_run select an action to execute and test this action on all available threads of Q *)
let next_run all partial_run : (partial_run list * location)= 
  if ! debug_execution then Printf.printf "Next execution step on %s" (show_partial_run partial_run);
  let first_actions = first_actions_among partial_run.test.statement.dag partial_run.remaining_actions in
  let current_loc = 
    try LocationSet.choose first_actions 
    with
    Not_found -> begin Printf.printf "No run on %s [%s] \n" (show_dag partial_run.test.statement.dag) (show_loc_set partial_run.remaining_actions); assert false end
  in
  let (new_runs,locs) = List.fold_left (fun (new_runs,locs) lp -> 
    match try_run false partial_run current_loc lp with
    | None -> (new_runs,locs)
    | Some (npr,l) -> (npr ::  new_runs, LocationSet.add l locs)
    ) ([],LocationSet.empty) partial_run.qthreads in
  if not all then
    (new_runs, current_loc)
  else 
  let mapping = Bijection.mappings_of partial_run.test.process_name current_loc in
  if Dag.for_all (fun loc _ -> LocationSet.mem loc locs) mapping then
    (new_runs, current_loc)
  else
    failwith "todo else"
    
let next_run_reverse partial_run actionP = ()


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
 

let compatible constraints constraints_back locP locQ = 
  try locQ = Dag.find locP constraints.a
  with Not_found -> begin 
    try Dag.find locQ constraints_back.a  =  locP 
    with Not_found -> true end
          
let compatible_prun constraints constraints_back (prun : partial_run)=
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
    let (new_runs,new_loc) = next_run false pr in 
    if !debug_execution && new_runs = [] then Printf.printf "No possible run from this trace \n"  ;
    List.iter (fun partial_run -> 
      if LocationSet.is_empty partial_run.remaining_actions 
      then begin
        if 
        match partial_run.test.statement.head with 
        | Knows(_)
        | Reach -> true
        | Identical(t,t') -> check_recipes partial_run (t,t') 
        | Tests(equal,diseq) -> (List.for_all (check_recipes partial_run) equal) && (List.for_all ( fun dis -> not (check_recipes partial_run dis)) diseq)
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




let next_solution_else solution =
  match solution.partial_runs_priority_todo with
  | [] -> assert false
  | pr :: q -> 
    (*Printf.printf "next solution of\n%s"(show_partial_run pr) ;*)
    solution.partial_runs_priority_todo <- q ;
    solution.partial_runs <- pr :: solution.partial_runs;
    let (new_runs,new_loc) = next_run true pr in 
    if !debug_execution && new_runs = [] then Printf.printf "No possible run from this trace \n"  ;
    List.iter (fun partial_run -> 
        (*Printf.printf "constraints: %s\n" (show_correspondance constraints);*)
        if true (*compatible new_loc (loc_p_to_q new_loc partial_run.corresp)*)
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
      
 let rec find_all_run solution =
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
        find_all_run solution end
      end
    else (* All solutions from the last execution have been performed, start a new one *)
      begin next_solution_else solution; 
      find_all_run solution end
    end
  | pr::q ->
    solution.possible_runs_todo <- q ;
    if !debug_execution then Printf.printf "complete run: %s\n"(show_run pr) ;
    if subset pr.dag pr.test.statement.dag 
    then begin
      let conflicts = Bijection.compatible pr in
      solution.possible_runs <- Solutions.add conflicts solution.possible_runs;
      find_all_run solution
    end
    else begin
      if !debug_execution then Printf.printf "Partial dag\n";
      solution.possible_restricted_runs <- pr :: solution.possible_restricted_runs;
      find_all_run solution
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
  | Tests(equal,diseq) -> Tests(List.map (fun (r,r') -> 
    (apply_var_set_subst (transpose r corresp) subst,apply_var_set_subst (transpose r' corresp) subst)) equal,
    List.map (fun (r,r') -> 
    (apply_var_set_subst (transpose r corresp) subst,apply_var_set_subst (transpose r' corresp) subst)) diseq)

 
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
          else begin Printf.eprintf "Further investigation are required (%d partial dags not considered).\n" (List.length solution.possible_restricted_runs); 
            None end 
          end
        else begin (* All possible run have been tested, we take the better one and add the tests of its conflicts *)
          let sol = Solutions.min_elt solution.possible_runs in
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

      
      
