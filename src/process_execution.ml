(** {2 Executing and testing processes} *)
open Util
open Types
open Dag
open Base
open Process
open Bijection



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


let rec run_until_io process first frame =
  (*Printf.printf "run until io %s \n" (show_process_start 3 process);*)
  match process with
  | EmptyP -> ([],[])
  | ParallelP(proclst) -> List.fold_left (fun (lst1,lst2) (x,y) -> (x @ lst1 , y @ lst2)) ([],[]) (List.map (fun p -> run_until_io p first frame ) proclst)
  | ChoiceP(l,proclst) -> 
    List.fold_left (fun (lst1,lst2) (x,y) -> (x @ lst1 , y @ lst2)) ([],[])
    (List.map (fun (i,p) -> 
      let (lst1,lst2) = run_until_io p first frame in
      (List.map (fun (c,ls,p) -> (Inputs.add_choice l i c, ls, p)) lst1, lst2)
      ) proclst)
  | SeqP(Input(l),p) 
  | SeqP(Output(l,_),p) -> ([(Inputs.new_choices,first,process)],[])
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
      ([],[(Inputs.new_choices,first,process)]) end
  | SeqP(TestInequal(t,t'),p) ->
    let t = apply_subst_inputs t frame in
    let t' = apply_subst_inputs t' frame in
    if not (Rewriting.equals_r t t' (! Parser_functions.rewrite_rules)) 
    then run_until_io p first frame 
    else ([],[])
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
     qthreads = qt ;
     failed_qthreads = fqt;
   } 
  
let next_partial_run run action full_p proc l frame locs choices =
  (*Printf.printf "next_partial_run %s \n" (show_process_start 3 full_p);*)
  let (qt,fqt) = List.fold_left 
    (fun (lst,flst) (chs,ls,p) -> 
      if p != full_p 
      then ((chs,ls,p) :: lst,flst)
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
     qthreads = qt ;
     failed_qthreads = fqt @ run.failed_qthreads ;
  }
  

  
let rec apply_frame recipe prun =
  match recipe with
    | Fun({ id=Frame(l)}, []) -> Inputs.get (Bijection.loc_p_to_q l prun.corresp) prun.frame
    | Fun({ id=Input(l)}, []) -> Inputs.get l prun.frame
    | Fun(f, args) -> Fun(f, List.map (fun x -> apply_frame x prun) args)
    | Var(x) -> Var(x)

       
let try_run run action (choices,locs,process)  =
   (*Printf.printf "Testing %s against %s\n" action.chan.name (show_process_start 1 process);*)
   match Inputs.merge_choices run.choices choices with
   | None -> []
   | Some choices -> 
   match process with
   | SeqP(Input(l),p) -> 
     if action.io = Input &&  action.chan = l.chan 
     then 
       begin 
         let new_frame = Inputs.add_to_frame l 
            (apply_frame (Inputs.get action run.test.statement.recipes) run) run.frame in
         let npr = next_partial_run run action process p l new_frame locs choices in
         (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
        [npr] 
       end
       else []
   | SeqP(Output(l,t),p) -> 
     if action.io = Output &&  action.chan = l.chan 
     then begin
       let new_frame = Inputs.add_to_frame l (apply_subst_inputs t run.frame) run.frame in
       let npr = next_partial_run run action process p l new_frame locs choices in
       (*Printf.printf "Possible: %s\n"(show_partial_run npr) ;*)
       [npr]
     end
     else []
   | _ -> assert false

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
     push statement process_name origin init 
   
let rec statements_to_tests process_name (statement : statement) otherProcess =
  statement_to_tests process_name (Initial(statement)) (statement.st) otherProcess;
  List.iter (fun st -> statements_to_tests process_name st otherProcess) statement.children
  
let base_to_tests process_name base otherProcess = 
  List.iter (fun st -> 
    statement_to_tests process_name (Initial(st)) st.st otherProcess) base.other_solved;
  statements_to_tests process_name base.solved_deduction otherProcess  

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
        if Bijection.straight new_loc (loc_p_to_q new_loc partial_run.corresp) (* TODO: partial run should not have priority *)
        then begin if !debug_execution then Printf.printf "Straight \n"  ;
          solution.partial_runs_priority_todo <- partial_run :: solution.partial_runs_priority_todo end
        else begin if !debug_execution then Printf.printf "Not Straight \n"  ;
          solution.partial_runs_todo <- partial_run :: solution.partial_runs_todo end
      end
      ) new_runs 

let find_all_run solution =
  while solution.partial_runs_priority_todo != [] 
  do next_solution solution done ;
  solution.partial_runs_priority_todo <- solution.partial_runs_todo ;
  while solution.partial_runs_priority_todo != [] 
  do next_solution solution done ;
      
exception Attack   

let get_lst_of_test test =
  match test with 
  Tests(t) -> t
  | Identical(r,r') -> [(r,r')]
  | _ -> []

(* Create new tests from prun which is in conflict with all tests in runset *)
let add_merged_tests (prun,runset) =
  if !debug_execution 
  then Printf.printf "Merging tests of %s\n" (show_test prun.test); 
  RunSet.iter (fun par ->
    if !debug_execution 
    then Printf.printf "   with %s\n" (show_test par.test); 
    if prun.test.process_name = par.test.process_name 
    then
      
      if ((Inputs.contains prun.test.statement.inputs par.test.statement.inputs) &&  (Util.list_diff (get_lst_of_test par.test.statement.head)(get_lst_of_test prun.test.statement.head) =[]))
      || ((Inputs.contains par.test.statement.inputs prun.test.statement.inputs) &&  (Util.list_diff (get_lst_of_test prun.test.statement.head)(get_lst_of_test par.test.statement.head) =[]))
      then ()  else
      begin
        let merged_statements =   merge_tests prun.test.statement par.test.statement in (* only one without xor *)
        List.iter (fun raw_st -> 
          if !debug_execution then Printf.printf "New test %s \n" (show_raw_statement raw_st);
          statement_to_tests prun.test.process_name (Composed(prun.test,par.test)) raw_st (proc (other prun.test.process_name))
          ) merged_statements
      end
    else begin
      if !debug_execution 
      then Printf.printf " TODO : coarse equivalence not enough\n" ; 
      (*raise Attack*)()
   end
  ) runset
      
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
        else begin
          let sol = Solutions.min_elt solution.possible_runs in
          add_merged_tests (sol.execution,sol.conflicts); 
          Bijection.add_partial_run sol.execution;
          Some sol.execution end 
      else begin
        if !debug_execution then Printf.printf "No priority partial run anymore \n" ;
        solution.partial_runs_priority_todo <- solution.partial_runs_todo ;
        solution.partial_runs_todo <- [];
        find_possible_run solution end
      end
    else
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
        Bijection.add_partial_run pr;
        solution.partitions <- [pr];
        (*solution.possible_runs <- pr :: solution.possible_runs;*)
        Some pr
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
  let (locP,satP) = Horn.saturate p in
  if !Util.about_saturation then
  begin 
    Printf.printf "Saturation of P:\n %s\n" (Base.show_kb satP);
  end ;
   let (locQ,satQ) = Horn.saturate q in
  if !Util.about_saturation then
  begin 
    Printf.printf "Saturation of Q:\n %s\n" (Base.show_kb satQ)
  end ;
  let processP = (CallP({p = locP;io=Call;chan=null_chan;name="main"},
    p,Array.make 0 zero,Array.make 0 null_chan)) in
  let processQ = (CallP({p = locQ;io=Call;chan=null_chan;name="main"}, 
    q,Array.make 0 zero,Array.make 0 null_chan)) in 
  base.p <- processP ;
  base.q <- processQ ;
  base_to_tests P satP processQ ;
  base_to_tests Q satQ processP ; 
  Printf.printf "Testing \n%!" ;
  try
    while not (Tests.is_empty base.tests) do
      let (test, sol) = pop () in
      if true || !debug_execution then Printf.printf "Open %s\n" (show_test test);
      match find_possible_run sol with 
      | None ->  Printf.printf "Failure to pass %s\n" (show_test test);
          List.iter (fun pr -> Printf.printf "%s\n" (show_correspondance pr.corresp)) sol.partial_runs;
        raise Attack;
      | Some pr -> 
            if true || ! debug_execution 
            then Printf.printf "Success of test %d: %s \n\n" test.id (show_correspondance pr.corresp)
    done ;
    if !about_execution then Bijection.show_base();
    Printf.printf "P and Q are trace equivalent. \n" 
  with
  | Attack -> begin 
  if !about_execution then Bijection.show_base();
  Printf.printf "P and Q might not be trace equivalent. \n" 
  end
(*let rec apply_subst_tr pr sigma = match pr with
  | NullTrace -> NullTrace
  | Trace(Input(ch, x), rest) -> 
    if bound x sigma then 
      raise Bound_variable
    else if bound ch sigma then
      raise Bound_variable
    else
      Trace(Input(ch, x), apply_subst_tr rest sigma)
  | Trace(Test(x, y), rest) ->
    Trace(Test(apply_subst x sigma, apply_subst y sigma), apply_subst_tr rest sigma)
  | Trace(TestInequal(x, y), rest) ->
    Trace(TestInequal(apply_subst x sigma, apply_subst y sigma), apply_subst_tr rest sigma)
  | Trace(Output(ch, x), rest) ->
    Trace(Output(ch, apply_subst x sigma), apply_subst_tr rest sigma)
;;

let rec variabilize str term =
	match term with
	| Fun(f,[]) when (startswith f "!n!") -> Var(str^(String.sub f 3 ((String.length f) - 3)))
	| Fun(f,a) -> Fun(f,List.map (variabilize str) a)
	| Var(x) -> Var(x)


let rec has_inequalities process = 
	match process with 
	| NullTrace -> false
	| Trace(Input(_, _), pr) -> has_inequalities pr
	| Trace(Test(_, _), pr) -> has_inequalities pr
	| Trace(TestInequal(_, _), _) -> true
	| Trace(Output(_,_),pr)-> has_inequalities pr

let rec execute_h_dumb process instructions =
  (
    (* extraOutput about_else
       "Executing: %s\nInstructions: %s\n\n%!" 
       (show_trace process) 
       (show_term instructions); *)
    match (process, instructions) with
      | (NullTrace, Fun("empty", [])) -> true
      | (NullTrace, _) -> false
      | (_, Fun("empty", [])) -> true
      | (Trace(Input(ch, x), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
	  if chp = Fun(ch, []) then
	    execute_h_dumb pr ir
	  else
	   false
      | (Trace(Test(x, y), pr), Fun("world", _)) -> execute_h_dumb pr instructions
      | (Trace(TestInequal(x, y), pr), Fun("world", _)) -> execute_h_dumb pr instructions
      | (Trace(Output(ch, x), pr), Fun("world", [Fun("!out!", [chp]); ir])) ->
	  if chp = Fun(ch, []) then
	    execute_h_dumb pr ir 
	  else
	   false 
      | _ ->  false
  )
;;
*)


(*
let rec execute_h process frame  instructions rules =
  (if !about_execution then Format.printf "%s ; %s \n%!" (show_trace process)(show_term instructions);
    match (process, instructions) with
      | (NullTrace, Fun("empty", [])) -> frame
      | (NullTrace, _) -> raise Too_many_instructions
      | (_, Fun("empty", [])) -> frame
      | (Trace(Input(ch, x), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
	  if chp = Fun(ch, []) then
	    execute_h (apply_subst_tr pr [(x, (apply_subst_inputs r frame))]) frame  ir rules
	  else
	    raise Invalid_instruction
      | (Trace(Test(x, y), pr), Fun("world", _)) -> if !about_execution then Format.printf "> Testing (%s = %s) \n%!" (show_term x)(show_term y); 
	  if R.equals x y rules then begin if !about_execution then Format.printf "> test (%s = %s) is satisfied \n%!" (show_term x)(show_term y); 
	    execute_h pr frame  instructions rules end
	  else 
	    begin if !about_execution then Format.printf "> test (%s = %s) not satisfied \n" (show_term x)(show_term y); raise Process_blocked end
      | (Trace(TestInequal(x, y), pr), Fun("world", _)) -> 
	  if not (R.equals x y rules) then begin if !about_execution then Format.printf "> test (%s != %s) is satisfied \n%!" (show_term x)(show_term y); 
	    execute_h pr frame  instructions rules end
	  else 
	    begin if !about_execution then Format.printf "> test (%s != %s) not satisfied \n" (show_term x)(show_term y); raise Process_blocked end
      | (Trace(Output(ch, x), pr), Fun("world", [Fun("!out!", [chp]); ir])) ->
	  if chp = Fun(ch, []) then
	    execute_h pr (List.append frame [x])  ir rules
	  else
	    raise Invalid_instruction
      | _ -> raise Invalid_instruction
  )
;;

module StringSet = Set.Make (String)

let rec variables_of_term t =
  match t with
  | Var x -> StringSet.singleton x
  | Fun (_, ts) ->
     List.fold_left (fun accu t ->
       StringSet.union accu (variables_of_term t)
     ) StringSet.empty ts

	

(* Shrink a process to some instructions *)
let rec shrink process frame instructions vars =
    (*extraOutput about_else "    %s\n>%s\n%!" (show_trace process)(show_term instructions);*)
      match (process, instructions) with
      | (NullTrace, Fun("empty", [])) -> NullTrace
      | (NullTrace, _) -> raise Too_many_instructions
      | (_, Fun("empty", [])) -> NullTrace (* Maybe exception *)
      | (Trace(Input(ch, x), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
	  if chp = Fun(ch, []) then
		let rv = variabilize "Z" r in
		let new_vars = StringSet.diff (variables_of_term rv) vars in
		let next_vars = StringSet.union vars new_vars in
		StringSet.fold 
			(fun v pro -> Trace(Input("!hidden!" ^ v,v),pro)) 
			new_vars 
			(Trace(Input(ch,x),Trace(Test(apply_subst_inputs rv frame,Var(x)), shrink pr frame  ir next_vars))) 
	  else
	    begin if !about_else then Format.printf "    invalid channel: %s\n>%s\n%!" (show_trace process)(show_term instructions); raise Invalid_instruction end
      | (Trace(Test(x, y), pr), Fun("world", _)) -> 
            Trace(Test(x,y),shrink pr frame  instructions vars)
      | (Trace(TestInequal(x, y), pr), Fun("world", _)) -> 
	      Trace(TestInequal(x,y),shrink pr frame instructions vars)
      | (Trace(Output(ch, x), pr), Fun("world", [Fun("!out!", [chp]); ir])) ->
	  if chp = Fun(ch, []) then
		Trace(Output(ch, x), shrink pr (List.append frame [x])  ir vars)
	  else
	    begin if ! about_else then Format.printf "    invalid channel: %s\n>%s\n%!" (show_trace process)(show_term instructions); raise Invalid_instruction end
      | _ -> begin if ! about_else then Format.printf "    invalid misc: %s\n>%s\n%!" (show_trace process)(show_term instructions); raise Invalid_instruction end

let rec free process = 
    match process with
       | NullTrace -> NullTrace
       | Trace(TestInequal(x, y), pr) -> free pr
       | Trace(instr,pr) -> Trace(instr, free pr)

let rec negate process =
    (*extraOutput about_else "    %s\n%!" (show_trace process);*)
    match process with
      | NullTrace -> []
      | Trace(TestInequal(x, y), pr) -> Trace(Test(x, y), free pr) :: (negate pr)
      | Trace(instr,pr) -> List.map (fun t -> Trace(instr, t)) (negate pr)

let rec size_of instr =
	match instr with 
	| Fun("empty", []) -> 0
	| Fun("world", [i;n]) -> 1 + (size_of n)
      | _ -> raise Invalid_instruction

(*let get_the_reach n tests =
	let rec size_of tr =
	match tr with
	| Fun("empty", []) -> 0
	| Fun("world", [Fun("!in!",[Fun(ch,[]); _]);w]) -> if startswith ch "!hidden!" then (size_of w) else 1 + (size_of w)
	| Fun("world", [Fun("!out!",_);w]) ->  1 + (size_of w)
	| Fun("world", [i;w]) ->(size_of w)
      | _ -> raise Invalid_instruction in
	List.filter (function Predicate("reach",[w]) ->  size_of w = n | _ -> true) tests*)

let tests_of_trace_reach size rew t=
  if !debug_seed then Format.printf "      Computing seed of the negate process: %s \n" (show_trace t); 
  let seed = Seed.seed_statements ~one_reach:true t rew in
    let kb = initial_kb seed rew in
	if !about_seed  then Format.printf "      |Initial seed: %s \n\n"   (show_kb kb);
      saturate ~only_reach:true  kb rew ;
	if !about_saturation then Format.printf  "      |Saturated base:  %s\n%!" (show_kb kb);
      checks kb rew




let rec worldfilter_h f w a =
  match w with
    | Fun("empty", []) -> a
    | Fun("world", [h; t]) -> 
	if f h then
	  worldfilter_h f t (Fun("world", [h; a]))
	else
	  worldfilter_h f t a
    | Var(_) -> invalid_arg("worldfilter_h variable")
    | x ->  begin Format.printf "Error: %s\n" (show_term x); 
		invalid_arg("worldfilter_h") end
;;

let worldfilter f w =
  revworld (worldfilter_h f w (Fun("empty", [])))
;;

let slim instructions = 
	worldfilter 
       (fun x -> match x with
	 | Fun("!test!", []) -> false
	 | _ -> true)
       instructions

let rec truncate n process = 
	if n = 0 then NullTrace
	else
	match process with 
	| NullTrace -> NullTrace
	| Trace(Input(c, x), pr) -> Trace(Input(c, x),truncate (n - 1) pr)
	| Trace(Test(s, t), pr) -> Trace(Test(s, t),truncate n pr)
	| Trace(TestInequal(s, t), pr) ->Trace(TestInequal(s, t), truncate n pr)
	| Trace(Output(c,t),pr)->  Trace(Output(c,t),truncate (n - 1) pr)

let cut_from instr pr =
	let w= 
	match instr with
	| Fun("check_run",[w]) -> w
	| Fun("check_identity",[w;r;s]) -> w
	| _ -> assert false in
	let n = size_of (slim w) in
	truncate n pr

let execute process frame instructions rules =
  if execute_h_dumb process (slim instructions) then (* Avoid testing non compatible trace*)
   begin
       if !about_execution
       then Format.printf "Executing: %s\n with instructions: %s\n%!" 
      (show_trace process) 
      (show_term instructions); 
    execute_h
    process
    frame 
    (slim instructions)
    rules end
  else begin if !about_execution then Format.printf "[trace with a different shape] " ; 
	raise Process_blocked end
;;

let is_executable process instructions rules =
	(try(
		ignore (execute process [] instructions rules); true
	  )
	with 
	  | Process_blocked -> false
	  | Too_many_instructions -> false
	  | Not_a_recipe -> false
	  | Invalid_instruction -> false
	  | Bound_variable -> invalid_arg("the process binds twice the same variable")
      )


let is_reach_test test = match test with
  | Fun("check_run", _) -> true
  | _ -> false
;;

let is_ridentical_test test = match test with
  | Fun("check_identity", [_; _; _]) -> true
  | _ -> false
;;


(* Forward equivalence use static equivalence on frame but this induces collision
with alpha renaming *)
let rec rename_free_names term =
	match term with
	| Fun(n,[]) when startswith n "!n!" -> Fun("!!"^n^"!!",[])
	| Fun(f,x) -> Fun(f, List.map rename_free_names x)
	| Var(x)->Var(x)

let rec trace_from_frame frame =
(* create trace out(c,t1). ... .out(c,tn).0 from frame [t1, ..., tn] *)
  match frame with
  | [] ->  NullTrace
  | h::t -> Trace(Output("c",rename_free_names h), trace_from_frame t)
;;



let interpret (r,t) = r && t = []

(*let rec find_sub_term t frame r =
	if apply_subst_inputs r frame = t then Some r else
	match r with
	| Fun(f, args) -> List.fold_left (fun x recipe -> match x with | Some r -> Some r | None -> find_sub_term t frame recipe) None args
	| _ -> None
*)


let rec build_instructions instr1 instr2 subst =
	match (instr1,instr2) with
      | (Fun("empty", []), Fun("empty", [])) -> (Fun("empty", []),subst)
	| (_,Fun("world", [Fun("!test!",[]);ir2])) -> build_instructions instr1 ir2 subst
	| (Fun("world", [Fun("!test!",[]);ir1]),_) -> build_instructions ir1 instr2 subst
	| (_,Fun("world", [Fun("!in!", [Fun(ch,[]); r2]); ir2])) when startswith ch "!hidden!" -> 
		build_instructions instr1 ir2 ((String.sub ch 8 ((String.length ch) - 8), r2)::subst)
      | (Fun("world", [Fun("!in!", [ch; r1]); ir1]), Fun("world", [Fun("!in!", [chp; r2]); ir2])) ->
		let (new_instr,sub) = build_instructions ir1 ir2 subst in
		(Fun("world", [Fun("!in!", [chp;apply_subst r1 sub]); new_instr]) ,sub)
      | (Fun("world", [Fun("!out!", [ch]); ir1]), Fun("world", [Fun("!out!", [chp]); ir2])) ->
		let (new_instr,sub) = build_instructions ir1 ir2 subst in
		(Fun("world", [Fun("!out!", [chp]); new_instr]) ,sub)
	|  _ -> assert false

	

let auxi_reach source process w rules r rp =
	let slim_w = (slim w) in
	let size = size_of (slim_w) in
	let frame = execute process [] slim_w rules in
	if !about_execution then Format.printf  " Result of execution of %s\n%!" (show_term w);
	let t1 = apply_subst_inputs r frame in
	let t2 = apply_subst_inputs rp frame in
	if(not (R.equals t1 t2 rules)) then 
		begin if !about_tests then Format.printf "   The identity of %s and %s is not satisfied\n" (show_term t1)(show_term t2);
		 (false,[]) end 
	else begin 
	if not(has_inequalities process) then 
		begin if !about_tests then Format.printf "   Success\n";
		(true,[]) end 
	else begin
	let shrinked = shrink process (List.map (fun t-> variabilize "Z" t) frame) (slim_w) StringSet.empty in 
	if !about_else then Format.printf "  Checking else branches with shrink %s\n%!" (show_trace shrinked);
	let neg_process = negate shrinked in
	let all_tests = List.concat (List.map (
			fun pr -> 
				if !about_else then Format.printf "  -negation process: %s\n%!" (show_trace pr); 
				tests_of_trace_reach size rules pr)
		neg_process) in
	let tests = List.fold_left (fun acc check -> 
		let test = match check with
		| Fun("check_run",[tst]) -> tst
		| _ -> assert false
		in
		let (tst,delta) = build_instructions (variabilize "Z" w) test [] in 
		if !about_else then Format.printf "      -one test to check is %s\n%!" (show_term tst);
		if is_executable source tst rules
		then begin let t =
			if (r = rp )
			then Fun("check_run",[tst])
			else
				Fun("check_identity",[tst;apply_subst (variabilize "Z" r) delta;apply_subst (variabilize "Z" rp) (delta)])
			in 
			if !about_else then Format.printf  "    - New test: %s\n%!" (show_term t);
			t::acc
		end
		else
			acc ) [] all_tests in
	(true,tests)
	end
	end

let check_reach source process test_reach rules = 
  match test_reach with
  | Fun("check_run", [w]) ->
      (
	try
	  (
		if !about_else then Format.printf  "\n*** Check reach of %s ***\n    on: %s\n%!" (show_term test_reach) (show_trace process);
		let (result,tests) = auxi_reach source process w rules (Fun("!x!",[])) (Fun("!x!",[])) in
		(*extraOutput about_else "RESULT of the test %s\n on %s\n is %b with list of size %d\n\n%!" (show_term test_reach) (show_trace process) result (List.length tests);*)
		(result,tests)
	  )
	with 
	  | Process_blocked -> if !about_else then Format.printf  "Process blocked! \n%!"; (false,[])
	  | Too_many_instructions -> if !about_else then Format.printf  "Too many instruction! \n%!"; (false,[])
	  | Not_a_recipe -> if !about_else then Format.printf  "Not a recipe! \n%!"; (false,[])
	  | Invalid_instruction -> if !about_else then Format.printf  "Invalid instruction! \n%!"; (false,[])
	  | Bound_variable -> invalid_arg("the process binds twice the same variable")
      )
  | _ -> invalid_arg("check_reach")
;;

let check_ridentical source process test_ridentical rules = 
  match test_ridentical with
  | Fun("check_identity", [w; r; rp]) ->
    (
      try
		if !about_else then Format.printf  "\n*** Check identity of %s ***\n     on: %s\n%!" (show_term test_ridentical) (show_trace process);
		let (result,tests) = auxi_reach source process w rules r rp in
		(*extraOutput about_else "RESULT of the test %s\n on %s\n is %b with list of size %d\n\n%!" (show_term test_ridentical) (show_trace process) result (List.length tests);*)
		(result,tests)
      with 
	| Process_blocked ->  if !about_else then Format.printf  "Process blocked ! \n%!"; (false,[])
	| Too_many_instructions -> (false,[])
	| Not_a_recipe -> (false,[])
	| Invalid_instruction -> (false,[])
	| Bound_variable -> invalid_arg("the process binds twice the same variable")
    )
  | _ -> invalid_arg("check_ridentical")
;;

let rec restrict_frame_to_channels frame trace ch =
(* given a trace and a frame resulting from an execution of trace, restrict elements in frame to outputs on channels in ch *)
  match frame with 
  | [] -> []
  | h :: tframe ->
    (
      match trace with 
      | NullTrace -> []
      | Trace(a, rest) ->
	(
	  match a with
	  | Output(chan, term) -> if List.exists (fun x -> x = chan) ch then h::restrict_frame_to_channels tframe rest ch  else restrict_frame_to_channels tframe rest ch
	  | _ -> restrict_frame_to_channels frame rest ch
	)
    )
;;


exception Unknown_test;;

let check_test source process test rules =
	let result = 
  if is_ridentical_test test then
    interpret (check_ridentical source process test rules) 
  else if is_reach_test test then
    interpret (check_reach source process test rules)
  else
    raise Unknown_test
	in
 result
;;

let update_tests source process test rules =
	let (r,lst) = 
  if is_ridentical_test test then
    check_ridentical source process test rules
  else if is_reach_test test then
    check_reach source process test rules
  else
    raise Unknown_test
	in 
	if !about_tests then Format.printf  "--- End of update: %s , %i ---\n%!" (if r then "ok" else "failure")(List.length lst);
      (r,lst)
;;



let rec check_reach_tests source trace reach_tests rules =
  match reach_tests with
    | h :: t ->
	(
	  if not (interpret(check_reach source trace h rules)) then
	    Some h
	  else
	    check_reach_tests source trace t rules
	)
    | [] -> None
;;

let rec check_ridentical_tests source trace ridentical_tests rules =
  match ridentical_tests with
    | h :: t ->
	(
	  if not (interpret(check_ridentical source trace h rules)) then
	    Some h
	  else
	    check_ridentical_tests source trace t rules
	)
    | [] -> None
;;
 
*)
