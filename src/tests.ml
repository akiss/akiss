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
  
let rec register_solution solution sol =
  let pr = sol.execution in
  let test = pr.test in
  let cardi = IntegerSet.cardinal test.from in
  if ! debug_tests then Printf.printf "Success of test %d: %s \n\n" test.id (show_correspondance pr.corresp);
  if solution.movable >= cardi 
  || match test.origin with
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
    solution.movable <- cardi;
    (*consider_disequalities pr;*)
  end
  
and find_compatible_run_init constraints constraints_back run  =
  if  (compatible_prun constraints constraints_back run) then true
  else
  let solution = try Tests.find run.test bijection.registered_tests 
    with Not_found -> Printf.printf "error  test %d not found\n%!" run.test.id; raise Not_found in
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
      (* We check that the two tests to merge have not been replaced by a different mapping *)
      let valid = 
        match test.origin with
        | Initial _ -> true
        | Composed (run1,run2) -> begin try
          let sol1 = Tests.find run1.test bijection.registered_tests in
          let sol2 = Tests.find run2.test bijection.registered_tests in
          (List.mem run1 sol1.partitions) && (List.mem run2 sol2.partitions)
          with Not_found -> Printf.printf "Error on main \n%!"; raise Not_found end
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
        | Some sol -> register_solution solution sol
      end
    done ;
    if !about_execution then Bijection.show_bijection();
    Printf.printf "P and Q are coarse trace equivalent. \n" 
  with
  | Attack -> begin 
  if !about_execution then Bijection.show_bijection();
  Printf.printf "P and Q are not trace equivalent. \n" 
  end
