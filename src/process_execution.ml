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

let rec execute_h process frame  instructions rules =
  (if !about_execution then Format.printf "%s ; %s \n%!" (show_trace process)(show_term instructions);
    match (process, instructions) with
      | (NullTrace, Fun("empty", [])) -> frame
      | (NullTrace, _) -> raise Too_many_instructions
      | (_, Fun("empty", [])) -> frame
      | (Trace(Input(ch, x), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
	  if chp = Fun(ch, []) then
	    execute_h (apply_subst_tr pr [(x, (apply_frame r frame))]) frame  ir rules
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
			(Trace(Input(ch,x),Trace(Test(apply_frame rv frame,Var(x)), shrink pr frame  ir next_vars))) 
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
    | x -> begin if !about_execution  then Format.printf "Error: %s\n" (show_term x); 
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
	let n = size_of (slim instr) in
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
	if apply_frame r frame = t then Some r else
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
	let t1 = apply_frame r frame in
	let t2 = apply_frame rp frame in
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
	let tests = List.fold_left (fun acc (Fun("check_run",[test])) -> 
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
 
