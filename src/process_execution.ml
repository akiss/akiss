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
	    begin extraOutput about_execution "> test (%s = %s) not satisfied \n" (show_term x)(show_term y); raise Process_blocked end
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
	

(* Shrink a process to some instructions *)
let rec shrink process frame instructions =
    (*extraOutput about_else "    %s\n>%s\n%!" (show_trace process)(show_term instructions);*)
      match (process, instructions) with
      | (NullTrace, Fun("empty", [])) -> NullTrace
      | (NullTrace, _) -> raise Too_many_instructions
      | (_, Fun("empty", [])) -> NullTrace (* Maybe exception *)
      | (Trace(Input(ch, x), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
		let rv = variabilize "Z" r in
	  if chp = Fun(ch, []) then
	    let new_process = shrink (apply_subst_tr pr [(x, (apply_frame rv frame))]) frame ir  in
		Trace(InputMatch(ch,apply_frame rv frame),new_process)
	  else
	    raise Invalid_instruction
      | (Trace(Test(x, y), pr), Fun("world", _)) -> 
            Trace(Test(x,y),shrink pr frame  instructions)
      | (Trace(TestInequal(x, y), pr), Fun("world", _)) -> 
	      Trace(TestInequal(x,y),shrink pr frame instructions)
      | (Trace(Output(ch, x), pr), Fun("world", [Fun("!out!", [chp]); ir])) ->
	  if chp = Fun(ch, []) then
		Trace(Output(ch, x), shrink pr (List.append frame [x])  ir)
	  else
	    raise Invalid_instruction
      | _ -> raise Invalid_instruction

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

(*let rec negate_instruction process frame  instructions rules =
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
;;*)

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

let slim instructions = 
	worldfilter 
       (fun x -> match x with
	 | Fun("!test!", []) -> false
	 | _ -> true)
       instructions

let execute process frame instructions rules =
  if execute_h_dumb process (slim instructions) then (* Avoid testing non compatible trace*)
   begin
 	(* Printf.printf "Smart test \n" ;*)
     extraOutput about_execution
      "Executing: %s\n with instructions: %s\n%!" 
      (show_trace process) 
      (show_term instructions); 
    execute_h
    process
    frame []
    (slim instructions)
    rules end
  else begin extraOutput about_tests "> non compatible " ; raise Process_blocked end
;;

(*let rec add_test_at_end i pr = 
	match pr with
	| Trace(a,b) -> List.map (fun tr -> Trace(a,tr)) (add_test_at_end i b)
	| NullTrace -> List.map (fun ineq -> Trace(ineq,Trace(Output("then",Fun("xx",[])),NullTrace))) i*)

(*let rec has_test_at_end pr =
	match pr with
	| Fun("empty",[]) -> false
	| Fun("world", [Fun("!out!", [Fun("then",[])]);Fun("empty",[])]) -> true
	| Fun("world",[a;b]) -> has_test_at_end b
	| _ -> assert(false)
*)

(*let negate process frame instructions rules =
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
*)

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

let get_the_tests n tests =
	List.filter (function Fun("check_run",[w]) -> n = size_of w | _ -> false) tests

let interpret (r,t) = r && t = []

let rec auxi_reach source process w rules r rp =
		let size = size_of w in
	      let (frame, inequalities) = execute process [] w rules in
		extraOutput about_execution "Result of execution of %s\n%!" (show_term w);
		let t1 = apply_frame r frame in
		let t2 = apply_frame rp frame in
		if(not (R.equals t1 t2 rules)) then begin extraOutput about_execution "   Failure of recipe\n";(false,[]) end else
		if(inequalities = []) then 
			begin extraOutput about_execution "   Success\n";(true,[]) end 
		else begin
		extraOutput about_else "  Checking else branches...\n%!";
		let neg_process = negate (shrink process [] (slim w)) in
		let all_tests = List.concat (List.map (
				fun pr -> extraOutput about_else "  -negation process: %s\n%!" (show_trace pr); 
					get_the_tests size (tests_of_trace rules pr))
			neg_process) in
		let neg_source = negate source in
            let base_tests = List.filter (
				fun tst ->
				extraOutput about_else "      -one test to check is %s\n%!" (show_term tst); 
				not (List.exists (fun trc -> interpret (check_reach NullTrace trc tst rules)) neg_source)
			)
			all_tests in
		let words = List.map (function  Fun("check_run",[w]) -> w | _ -> invalid_arg("check_reach_2")) base_tests in
		let tests = List.map (function  Fun("check_run",[w]) -> 
			if (r = rp) 
			then Fun("check_run",[w]) 
			else Fun("check_identity",[w;r;rp]) | _ -> invalid_arg("check_reach_2")) base_tests in
		extraOutput about_else "    o The test %s returns\n" (show_term w);
		List.iter (fun x -> extraOutput about_else "    - Failure of: %s\n%!" (show_term x)) tests;
		if (List.mem w words) then 
			begin extraOutput about_else "Loop ! \n%!";(false,tests) end 
		else (true,tests)
		end

and check_reach source process test_reach rules = 
  match test_reach with
  | Fun("check_run", [w]) ->
      (
	try
	  (
		extraOutput about_else "\n  Check reach of %s\non: %s\n%!" (show_term test_reach) (show_trace process);
		let (result,tests) = auxi_reach source process w rules (Fun("!x!",[])) (Fun("!x!",[])) in
		extraOutput about_else "RESULT of the test %s\n on %s\n is %b with list of size %d\n\n%!" (show_term test_reach) (show_trace process) result (List.length tests);
		(result,tests)
	  )
	with 
	  | Process_blocked -> (false,[])
	  | Too_many_instructions -> (false,[])
	  | Not_a_recipe -> (false,[])
	  | Invalid_instruction -> (false,[])
	  | Bound_variable -> invalid_arg("the process binds twice the same variable")
      )
  | _ -> invalid_arg("check_reach")
;;

let check_ridentical source process test_ridentical rules = 
  match test_ridentical with
  | Fun("check_identity", [w; r; rp]) ->
    (
      try
		extraOutput about_else "\n  Check identity of %s\non: %s\n%!" (show_term test_ridentical) (show_trace process);
		let (result,tests) = auxi_reach source process w rules r rp in
		extraOutput about_else "RESULT of the test %s\n on %s\n is %b with list of size %d\n\n%!" (show_term test_ridentical) (show_trace process) result (List.length tests);
		(result,tests)
      with 
	| Process_blocked -> (false,[])
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
	in  result
;;

let update_tests source process test rules =
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
 
