open Process
open Term
open Util
open Seed
open Horn
module R = Theory.R
(** {2 Executing and testing processes} *)

exception Process_blocked;;
exception Not_a_recipe;;    
exception Bound_variable;;
exception Invalid_instruction;;
exception Too_many_instructions;;

let is_parameter name = 
  (String.sub name 0 1 = "w") &&
    (try
       let pcounter = (String.sub name 1 ((String.length name) - 1)) in
       let ipcounter = (int_of_string pcounter) in
       (ipcounter >= 0) && (pcounter = string_of_int ipcounter)
     with _ -> false)
;;

let param_count name =
  int_of_string (String.sub name 1 ((String.length name) - 1))
;;


let rec apply_frame term frame =
  match term with
    | Fun(name, []) when is_parameter name ->
      (
	try
	  List.nth frame (param_count name)
	with _ -> raise Not_a_recipe
      )
    | Fun(f, tl) ->
      Fun(f, trmap (fun x -> apply_frame x frame) tl)
    | Var(x) ->
      Var(x)
;;

let rec apply_subst_tr pr sigma = match pr with
  | NullTrace -> NullTrace
  | Trace(Input(ch, x), rest) -> 
    if bound x sigma then 
      raise Bound_variable
    else if bound ch sigma then
      raise Bound_variable
    else
      Trace(Input(ch, x), apply_subst_tr rest sigma)
  | Trace(InputMatch(ch, t), rest) ->
      Trace(InputMatch(ch, apply_subst t sigma), apply_subst_tr rest sigma)
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
     | (Trace(InputMatch(ch, t), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
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

let rec execute_h process frame inequalities instructions rules =
  (extraOutput about_execution "%s ; %s \n%!" (show_trace process)(show_term instructions);
    match (process, instructions) with
      | (NullTrace, Fun("empty", [])) -> (frame,inequalities)
      | (NullTrace, _) -> raise Too_many_instructions
      | (_, Fun("empty", [])) -> (frame,inequalities)
      | (Trace(Input(ch, x), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
	  if chp = Fun(ch, []) then
	    execute_h (apply_subst_tr pr [(x, (apply_frame r frame))]) frame inequalities ir rules
	  else
	    raise Invalid_instruction
      | (Trace(InputMatch(ch, t), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
	  if chp = Fun(ch, []) then begin
		let recipe = (variabilize "W" (apply_frame r frame)) in
		extraOutput about_execution "Matching  %s and %s \n%!" (show_term recipe)(show_term t);
		let substs = R.matchers t recipe [] in
		match substs with 
		| [] -> raise Process_blocked
		| [subst] -> extraOutput about_execution "Matchers=  %s\n%!" (show_subst subst);
	    execute_h (apply_subst_tr pr subst) frame inequalities ir rules
		| _ -> assert false
		end
	  else
	    raise Invalid_instruction
      | (Trace(Test(x, y), pr), Fun("world", _)) -> extraOutput about_execution "> Testing (%s = %s) \n%!" (show_term x)(show_term y); 
	  if R.equals x y rules then begin extraOutput about_execution "> test (%s = %s) is satisfied \n%!" (show_term x)(show_term y); 
	    execute_h pr frame inequalities instructions rules end
	  else 
	    begin extraOutput about_execution "> test (%s = %s) not satisfied " (show_term x)(show_term y); raise Process_blocked end
      | (Trace(TestInequal(x, y), pr), Fun("world", _)) -> 
	    execute_h pr frame (TestInequal(R.normalize x rules,R.normalize y rules) :: inequalities) instructions rules
      | (Trace(Output(ch, x), pr), Fun("world", [Fun("!out!", [chp]); ir])) ->
	  if chp = Fun(ch, []) then
	    execute_h pr (List.append frame [x]) inequalities ir rules
	  else
	    raise Invalid_instruction
      | _ -> raise Invalid_instruction
  )
;;



let rec negate_instruction process frame  instructions rules =
  (
    match (process, instructions) with
      | (NullTrace, Fun("empty", [])) -> (NullTrace,[])
      | (NullTrace, _) -> raise Too_many_instructions
      | (_, Fun("empty", [])) -> (NullTrace,[])
      | (Trace(Input(ch, x), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
		let rv = variabilize "Z" r in
	  if chp = Fun(ch, []) then
	    let (new_process,inequalities) = negate_instruction (apply_subst_tr pr [(x, (apply_frame rv frame))]) frame  ir rules in
		(Trace(InputMatch(ch,apply_frame rv frame),new_process),inequalities)
	  else
	    raise Invalid_instruction
      | (Trace(Test(x, y), pr), Fun("world", _)) -> 
	  if R.equals x y rules then
            begin  let (new_process,inequalities) =negate_instruction pr frame  instructions rules in 
            (Trace(Test(x,y),new_process),inequalities) end
	  else 
	    begin raise Process_blocked end
      | (Trace(TestInequal(x, y), pr), Fun("world", _)) -> 
	   let (new_process,inequalities) =  negate_instruction pr frame  instructions rules in
		(new_process,(Test(R.normalize  x rules,R.normalize y rules) :: inequalities))
      | (Trace(Output(ch, x), pr), Fun("world", [Fun("!out!", [chp]); ir])) ->
	  if chp = Fun(ch, []) then
	    let (new_process,inequalities) = negate_instruction pr (List.append frame [x])  ir rules in
		(Trace(Output(ch, x), new_process),inequalities)
	  else
	    raise Invalid_instruction
      | _ -> raise Invalid_instruction
  )
;;

let tests_of_trace rew t=
extraOutput debug_seed "Computing seed of the negate process: %s \n" (show_trace t); 
  let seed = Seed.seed_statements t rew in
    let kb = initial_kb seed rew in
	extraOutput about_seed "|Initial seed: %s \n\n"   (show_kb kb);
      saturate kb rew ;
	extraOutput about_saturation "|Saturated base:  %s\n%!" (show_kb kb);
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
    | _ -> invalid_arg("worldfilter_h")
;;

let worldfilter f w =
  revworld (worldfilter_h f w (Fun("empty", [])))
;;

let execute process frame instructions rules =
  let slimmed_instructions = (worldfilter 
       (fun x -> match x with
	 | Fun("!test!", []) -> false
	 | _ -> true)
       instructions) in
  if execute_h_dumb process slimmed_instructions then (* Avoid testing non compatible trace*)
   begin
 	(* Printf.printf "Smart test \n" ;*)
     extraOutput about_execution
      "Executing: %s\n with instructions: %s\n%!" 
      (show_trace process) 
      (show_term instructions); 
    execute_h
    process
    frame []
    (worldfilter 
       (fun x -> match x with
	 | Fun("!test!", []) -> false
	 | _ -> true)
       instructions)
    rules end
  else begin extraOutput about_tests "> non compatible " ; raise Process_blocked end
;;

let rec add_test_at_end i pr = 
	match pr with
	| Trace(a,b) -> List.map (fun tr -> Trace(a,tr)) (add_test_at_end i b)
	| NullTrace -> List.map (fun ineq -> Trace(ineq,Trace(Output("then",Fun("xx",[])),NullTrace))) i

let rec has_test_at_end pr =
	match pr with
	| Fun("empty",[]) -> false
	| Fun("world", [Fun("!out!", [Fun("then",[])]);Fun("empty",[])]) -> true
	| Fun("world",[a;b]) -> has_test_at_end b
	| _ -> assert(false)


let negate process frame instructions rules =
  let slimmed_instructions = (worldfilter 
       (fun x -> match x with
	 | Fun("!test!", []) -> false
	 | _ -> true)
       instructions) in
  if execute_h_dumb process slimmed_instructions then (* Avoid testing non compatible trace*)
   begin
     extraOutput about_else 
      "Computing negation: %s\n with instructions: %s\n%!" 
      (show_trace process) 
      (show_term instructions); 
	let (pr,ineq) = negate_instruction process frame slimmed_instructions rules in
	let lst = add_test_at_end ineq pr in
	extraOutput about_else 
      "Result of the negation:\n";
	List.iter (fun tr ->
	extraOutput about_else 
      "- %s\n" (show_trace tr)) lst ;
	extraOutput about_else 
      "\n%!"; lst
end
  else begin extraOutput about_tests "> non compatible " ; raise Process_blocked end
;;

let is_reach_test test = match test with
  | Fun("check_run", _) -> true
  | _ -> false
;;

let is_ridentical_test test = match test with
  | Fun("check_identity", [_; _; _;_]) -> true
  | _ -> false
;;


(*let rec term_to_ineq term = match term with
	| Fun("liste",[Fun("ineq",[w;x;y]);v]) -> TestInequal(x,y)::(term_to_ineq v)
	| Fun("empty",[])-> []
	| _ -> assert(false)*)


(*let rec ineq_in ineq lstineq =
	match ineq with 
	| TestInequal(u,v)  -> begin
	match lstineq with
	| TestInequal(s,t) :: q -> if (u = s && v = t) || (u = t && v = s) then true else ineq_in ineq q
	| [] -> false
	| _ -> assert false
	end
	| _ -> assert false

let rec ineq_incl l1 l2 =
	match l1 with 
	| t :: q -> if ineq_in t l2 then ineq_incl q l2 else false
	| [] -> true

let ineq_equal l1 l2 =
	ineq_incl l1 l2 && ineq_incl l2 l1*)

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

let get_the_test tests =
	List.find (function Fun("check_run",[w;_]) -> has_test_at_end w | _ -> false) tests

let rec auxi_reach source process w rules r rp =
	    let (frame, inequalities) = execute process [] w rules in
		extraOutput about_execution "Result of execution: there are %d inequalities:\n - %s\n%!" (List.length inequalities) (show_action_lst inequalities);
		let t1 = apply_frame r frame in
		let t2 = apply_frame rp frame in
		if(not (R.equals t1 t2 rules)) then (false,[]) else
		if(inequalities = []) then (true,[]) else
		let neg_process = negate process [] w rules in
		let neg_source = negate source [] w rules in
            let tests = List.filter (
			fun x -> try let tst = get_the_test (tests_of_trace rules x) in 
				extraOutput about_else "The test to check is %s\n%!" (show_term tst); 
				not (List.exists (fun y -> check_reach NullTrace y tst rules) neg_source)
				with 
				| Not_found -> false) 
			neg_process in
		List.iter (fun x -> extraOutput about_else "Failure of: %s\n%!" (show_trace x)) tests;
		(true,tests)

and check_reach source process test_reach rules = 
  match test_reach with
  | Fun("check_run", [w;ineq]) ->
      (
	(* debugOutput *)
	(*   "CHECK FOR: %s\nREACH: %s\n\n%!" *)
	(*   (show_trace process) *)
	(*   (show_term w); *)
	(*Printf.printf "r ";*)
	try
	  (
		extraOutput about_else "\n  Check reach of %s\non: %s\n%!" (show_term test_reach) (show_trace process);
		let (result,tests) = auxi_reach source process w rules (Fun("!x!",[])) (Fun("!x!",[])) in
		extraOutput about_else "RESULT of the test %s\n on %s\n is %b with list of size %d\n\n%!" (show_term test_reach) (show_trace process) result (List.length tests);
		result && tests = []
	  )
	with 
	  | Process_blocked -> false
	  | Too_many_instructions -> false
	  | Not_a_recipe -> false
	  | Invalid_instruction -> false
	  | Bound_variable -> invalid_arg("the process binds twice the same variable")
      )
  | _ -> invalid_arg("check_reach")
;;

let check_ridentical source process test_ridentical rules = 
  match test_ridentical with
  | Fun("check_identity", [w; r; rp; ineq]) ->
    (
	(*Printf.printf "ri %s" (show_term test_ridentical);*)
      try
	(*let (frame, inequalities) = execute process [] w rules in
	let t1 = apply_frame r frame in
	let t2 = apply_frame rp frame in
	  R.equals t1 t2 rules*)
		extraOutput about_else "\n  Check identity of %s\non: %s\n%!" (show_term test_ridentical) (show_trace process);
		let (result,tests) = auxi_reach source process w rules r rp in
		extraOutput about_else "RESULT of the test %s\n on %s\n is %b with list of size %d\n\n%!" (show_term test_ridentical) (show_trace process) result (List.length tests);
		result && tests = []
      with 
	| Process_blocked -> false
	| Too_many_instructions -> false
	| Not_a_recipe -> false
	| Invalid_instruction -> false
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
    check_ridentical source process test rules
  else if is_reach_test test then
    check_reach source process test rules
  else
    raise Unknown_test
	in  result
;;

let rec check_reach_tests source trace reach_tests rules =
  match reach_tests with
    | h :: t ->
	(
	  if not (check_reach source trace h rules) then
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
	  if not (check_ridentical source trace h rules) then
	    Some h
	  else
	    check_ridentical_tests source trace t rules
	)
    | [] -> None
;;
 
