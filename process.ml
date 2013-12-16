open Parser;;
open Util;;
open Term;;
open Horn;;

type var = string
type rules = (term*term) list
type subst = (var*term) list
module type REWRITING = sig
  val unifiers : term -> term -> rules -> subst list
  val normalize : term -> rules -> term
  val variants : term -> rules -> (term*subst) list
  val equals : term -> term -> rules -> bool
end
module R : REWRITING = struct
  let normalize = Maude.normalize
  let equals = Maude.equals
  let unifiers = Maude.unifiers
  let variants = Tamarin.variants
end

(** {2 Processes} *)

type action = 
  | Input of id * id
  | Output of id * term
  | Test of term * term
;;

type trace =
  | NullTrace
  | Trace of action * trace
;;

let rec trace_size = function
  | NullTrace -> 0
  | Trace(_, t) -> 1 + (trace_size t)
;;


type process = trace list;;

(** {3 Printing} *)

let str_of_tr tr = match tr with
  | Some(t) -> show_term t
  | None -> "ok"
;;

let show_frame fr = 
  show_string_list (trmap show_term fr)
;;

let show_action = function
  | Input(ch, x) -> Printf.sprintf "in(%s,%s)" ch x
  | Output(ch, t) -> Printf.sprintf "out(%s,%s)" ch (show_term t)
  | Test(s,t) -> Printf.sprintf "[%s=%s]" (show_term s) (show_term t)
;;

let rec show_trace = function
  | NullTrace -> "0"
  | Trace(a, rest) -> (show_action a) ^ "." ^ (show_trace rest)
;;

let rec show_process process =
  String.concat "\n\n" (trmap show_trace process)
;;

(** {3 Parsing} *)

let rec parse_action = function
  | TempActionOut(ch, t) -> Output(ch, parse_term t)
  | TempActionIn(ch, x) -> Input(ch, x)
  | TempActionTest(s, t) -> Test(parse_term s, parse_term t)
;;

let rec replace_tail first second = match first with
  | Trace(a, next) -> Trace(a, replace_tail next second)
  | NullTrace -> second
;;

let rec sequence_traces (tll : trace list list) : trace list =
  match tll with
    | head :: tail ->
	trmap
	  (fun (x, y) -> replace_tail x y)
	  (combine head (sequence_traces tail))
    | [] -> [NullTrace]
;;

(* let rec parse_trace = function *)
(*   | [] -> NullTrace *)
(*   | a :: t -> Trace(parse_action a, parse_trace t) *)
(* ;; *)

let rec split_opt s = 
  match s with
    | NullTrace -> (NullTrace, NullTrace)
    | Trace(a, rest) ->
	(
	  match a with
	    | Input(_, _) as i -> (Trace(i, NullTrace), rest)
	    | Output(_, _) as o -> (Trace(o, NullTrace), rest)
	    | Test(_, _) as t ->
		(
		  let (f, l) = split_opt rest in
		  (Trace(t, f), l)
		)
	)
;;

let rec prepend_trace t to_what =
  match t with
    | NullTrace -> to_what
    | Trace(a, rest) -> Trace(a, prepend_trace rest to_what)
;;

let rec interleave_opt_two_non_testending_traces s t =
  match (s, t) with
    | (NullTrace, _) -> [t]
    | (_, NullTrace) -> [s]
    | (_, _) ->
	(
	  let (sf, sl) = split_opt s in
	  let (tf, tl) = split_opt t in
	  List.append
	    (trmap (fun x -> prepend_trace sf x) (interleave_opt_two_non_testending_traces sl t))
	    (trmap (fun x -> prepend_trace tf x) (interleave_opt_two_non_testending_traces s tl))
	)
;;

let rec split_endingtests s =
  match s with
    | NullTrace -> (NullTrace, NullTrace)
    | Trace(Test(_) as a, rest) ->
	(
	  match split_endingtests rest with
	    | (NullTrace, t) -> (NullTrace, Trace(a, t))
	    | (r, t) -> (Trace(a, r), t)
	)
    | Trace(a, rest) ->
	let (r, t) = split_endingtests rest in
	(Trace(a, r), t)	    
;;

let interleave_opt_two_traces s t =
  let (sb, se) = split_endingtests s in
  let (tb, te) = split_endingtests t in
  let list = interleave_opt_two_non_testending_traces sb tb in
  trmap (fun x -> (prepend_trace (prepend_trace x se) te)) list
;;

let rec interleave_opt_traces (tlist : trace list) : trace list =
  match tlist with 
    | [] -> [NullTrace]
    | hd :: [] -> [hd]
    | hd :: hdp :: tl ->
	List.concat
	  (List.map
	     (fun x -> interleave_opt_traces (x :: tl))
	     (interleave_opt_two_traces hd hdp))
;;

let rec interleave_opt_trace_process (t : trace) (p : trace list) : trace list =
  match p with
  | [] -> []
  | hd :: tl ->
      List.concat
        [(interleave_opt_two_traces t hd); interleave_opt_trace_process t tl]
;;

let rec interleave_opt_two_processes (tl1 : trace list) (tl2 : trace list) : trace list =
  match tl1 with
  | [] -> []
  | hd :: tl ->
      List.concat
        [interleave_opt_trace_process hd tl2; interleave_opt_two_processes tl tl2]
;;

let replace_var_in_term x t term =
  apply_subst term [(x, t)]
;;

let rec replace_var_in_trace x t trace = 
  match trace with
  | NullTrace -> NullTrace
  | Trace(Input(c, var), rest) -> 
    if x = var then
      trace
    else
      Trace(Input(c, var),
	    replace_var_in_trace x t rest)
  | Trace(Output(id, term), rest) -> Trace(Output(id, replace_var_in_term x t term),
					   replace_var_in_trace x t rest)
  | Trace(Test(term1, term2), rest) -> Trace(Test(replace_var_in_term x t term1, replace_var_in_term x t term2),
					     replace_var_in_trace x t rest)
;;

let replace_var_in_process x t process = 
  trmap (fun trace -> (replace_var_in_trace x t trace)) process
;;

let rec parse_process (process : tempProcess)
    (processes : (string * trace list) list) : trace list =
  match process with
  | TempEmpty -> [ NullTrace ]
  | TempAction(a) -> [ Trace(parse_action a, NullTrace) ]
  | TempSequence(t1, t2) -> 
    let p1 = parse_process t1 processes in
    let p2 = parse_process t2 processes in
    sequence_traces [p1; p2]
  | TempInterleave(t1, t2) ->
    let p1 = parse_process t1 processes in
    let p2 = parse_process t2 processes in
    interleave_opt_two_processes p1 p2
  | TempLet(x, tt, process) ->
    let t = parse_term tt in
    let p = parse_process process processes in
    replace_var_in_process x t p
  | TempProcessRef(name) ->
    List.assoc name processes
;;

(** {1 Seed statements}
  * We are concerned only with the part of seed statements that comes
  * from the process. The part coming from the signature is computed
  * in Main. *)

let current_parameter oc = 
  "w" ^ (string_of_int oc) 
;;

let worldadd w t =
  revworld (Fun("world", [t; revworld w]))
;;

let rec worldreplempty w wp =
  match w with
    | Fun("empty", []) -> wp
    | Fun("world", [f; r]) -> Fun("world", [f; worldreplempty r wp])
    | Var(_) -> invalid_arg("worldreplempty for var")
    | _ -> invalid_arg("worldreplempty")
;;

(** {2 Compute knows statements from a trace} *)

(** Core statements without variant computations *)
let rec knows_statements_h oc tr antecedents world clauses =
  match tr with 
    | NullTrace -> List.rev clauses
    | Trace(Output(ch, t), remaining_trace) -> 
	let next_world = worldadd world (Fun("!out!", [Fun(ch, [])])) in
	let next_head = Predicate("knows",
	       [worldreplempty next_world (Var(fresh_variable ()));
		Fun(current_parameter oc, []);
		t]) in
	let new_clause = (next_head, antecedents) in
	knows_statements_h (oc + 1) remaining_trace antecedents 
	  next_world (new_clause :: clauses)
    | Trace(Input(ch, v), remaining_trace) ->
	let next_world = worldadd world (Fun("!in!", [Fun(ch, []); Var(v)])) in
	let ancedent = Predicate("knows", [world;
				     Var(fresh_variable ());
				     Var(v)]) in
	let next_antecedents = (List.append antecedents [ancedent]) in
	knows_statements_h oc remaining_trace next_antecedents
	  next_world clauses
    | Trace(Test(s, t), remaining_trace) -> 
	let next_world = worldadd world (Fun("!test!", [])) in
	knows_statements_h oc remaining_trace antecedents
	  next_world clauses
;;

let normalize_msg_atom rules = function
  | Predicate("knows", [w; r; t]) ->
      Predicate("knows", [R.normalize w rules; r; R.normalize t rules])
  | Predicate("reach", [w]) -> 
      Predicate("reach", [R.normalize w rules])
  | Predicate("identical", [w; r; rp]) -> 
      Predicate("identical", [R.normalize w rules; r; rp])
  | Predicate("ridentical", [w; r; rp]) -> 
      Predicate("ridentical", [R.normalize w rules; r; rp])
  | _ -> invalid_arg("normalize_msg_atom")
;;

let normalize_msg_st (head, body) rules =
  (normalize_msg_atom rules head, trmap (fun x -> normalize_msg_atom rules x) body)
;;

let apply_subst_msg_atom sigma = function
  | Predicate("knows", [w; r; t]) ->
      Predicate("knows", [apply_subst w sigma; r; apply_subst t sigma])
  | Predicate("reach", [w]) -> 
      Predicate("reach", [apply_subst w sigma])
  | Predicate("identical", [w; r; rp]) -> 
      Predicate("identical", [apply_subst w sigma; r; rp])
  | Predicate("ridentical", [w; r; rp]) -> 
      Predicate("ridentical", [apply_subst w sigma; r; rp])
  | _ -> invalid_arg("apply_subst_msg_atom")
;;

let apply_subst_msg_st (head, body) sigma = 
  (apply_subst_msg_atom sigma head,
   trmap (fun x -> apply_subst_msg_atom sigma x) body)
;;

let knows_variantize (head, body) rules =
  match head with
    | Predicate("knows", [world; recipe; t]) ->
	let v = R.variants t rules in
	let new_clause (_, sigma) = 
          Horn.new_clause
            (normalize_msg_st (apply_subst_msg_st (head, body) sigma) rules)
	in
	trmap new_clause v
    | _ -> invalid_arg("variantize")
;;

let knows_statements tr rules = 
  let kstatements = knows_statements_h 0 tr [] (Fun("empty", [])) [] in
    List.concat
      (List.map (function x -> knows_variantize x rules) kstatements)
;;

(** {3 Computing reach statements from a trace} *)

let rec reach_statements_h tr antecedents world result =
  match tr with
    | NullTrace -> List.rev result
    | Trace(Output(ch, t), remaining_trace) ->
	let next_world = worldadd world (Fun("!out!", [Fun(ch, [])])) in
	let new_clause = (Predicate(
			    "reach",
			    [next_world]),
			  antecedents)  in
	reach_statements_h remaining_trace antecedents next_world 
	  (new_clause :: result)
    | Trace(Input(ch, v), remaining_trace) ->
	let next_world = worldadd world (Fun("!in!", [Fun(ch, []); Var(v)])) in
	let antecedent = Predicate("knows", [world;
					     Var(fresh_variable ());
					     Var(v)]) in
	let next_antecedents = List.append antecedents [antecedent] in
	let new_clause = (Predicate(
			    "reach",
			    [next_world]),
			  next_antecedents)  in
	reach_statements_h remaining_trace next_antecedents next_world 
	  (new_clause :: result)
    | Trace(Test(s, t), remaining_trace) ->
	let next_world = worldadd world (Fun("!test!", [])) in
	let antecedent = Predicate("!equals!", [s; t]) in
	let next_antecedents = List.append antecedents [antecedent] in
	let new_clause = (Predicate(
			    "reach",
			    [next_world]),
			  next_antecedents)  in
	reach_statements_h remaining_trace next_antecedents next_world 
	  (new_clause :: result)
;;

let reach_equationalize (head, body) rules =
  let eqns = List.filter (function (Predicate(x, _)) -> x = "!equals!") body in
  let lefts = trmap (function 
			  | (Predicate(_, [x;_])) -> x 
			  | _ -> invalid_arg("lefts")) eqns in
  let rights = trmap (function 
			   | (Predicate(_, [_;y])) -> y
			   | _ -> invalid_arg("rights")) eqns in
  let t1 = Fun("!tuple!", lefts) in
  let t2 = Fun("!tuple!", rights) in
  let sigmas = R.unifiers t1 t2 rules in
  let newbody = List.filter (function (Predicate(x, _)) -> x <> "!equals!") body in
  let newatom sigma = function
    | (Predicate(x, [y; z; t])) -> 
	Predicate(x, [apply_subst y sigma; z; apply_subst t sigma])
    | _ -> invalid_arg("newatom") in
  let newhead sigma = match head with 
    | Predicate("reach", [w]) -> Predicate("reach", [apply_subst w sigma])
    | _ -> invalid_arg("wrong head") in
  let newclause sigma =
    (newhead sigma, trmap (fun x -> newatom sigma x) newbody) in
  trmap newclause sigmas
;;

let reach_variantize (head, body) rules =
  match head with
    | Predicate("reach", [w]) ->
	let v = R.variants w rules in
	let newhead sigma = Predicate("reach", 
				[R.normalize (apply_subst w sigma) rules]) in
	let newbody sigma = trmap
	  (function 
	     | Predicate("knows", [x; y; z]) -> 
		 Predicate("knows", [R.normalize (apply_subst x sigma) rules; 
				     y; 
				     R.normalize (apply_subst z sigma) rules])
	     | _ -> invalid_arg("reach_variantize")) body in
	trmap (fun (_, sigma) -> Horn.new_clause (newhead sigma, newbody sigma)) v
    | _ -> invalid_arg("reach_variantize")
;;

let reach_statements tr rules =
  let statements = reach_statements_h tr [] (Fun("empty", [])) [] in
    List.concat
      (List.map
         (fun x -> reach_variantize x rules)
         (List.concat
            (List.map (fun x -> reach_equationalize x rules) statements)))
;;

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
  | Trace(Output(ch, x), rest) ->
    Trace(Output(ch, apply_subst x sigma), apply_subst_tr rest sigma)
;;

let rec execute_h process frame instructions rules =
  (
    (* debugOutput *)
    (*   "Executing: %s\nFrame: %s\nInstructions: %s\n\n%!" *)
    (*   (show_trace process) *)
    (*   (show_term_list frame) *)
    (*   (show_term_list instructions); *)
    match (process, instructions) with
      | (NullTrace, Fun("empty", [])) -> frame
      | (NullTrace, _) -> raise Too_many_instructions
      | (_, Fun("empty", [])) -> frame
      | (Trace(Input(ch, x), pr), Fun("world", [Fun("!in!", [chp; r]); ir])) ->
	  if chp = Fun(ch, []) then
	    execute_h (apply_subst_tr pr [(x, (apply_frame r frame))]) frame ir rules
	  else
	    raise Invalid_instruction
      | (Trace(Test(x, y), pr), Fun("world", _)) ->
	  if R.equals x y rules then
	    execute_h pr frame instructions rules
	  else
	    raise Process_blocked
      | (Trace(Output(ch, x), pr), Fun("world", [Fun("!out!", [chp]); ir])) ->
	  if chp = Fun(ch, []) then
	    execute_h pr (List.append frame [x]) ir rules
	  else
	    raise Invalid_instruction
      | _ -> raise Invalid_instruction
  )
;;

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
  execute_h
    process
    frame
    (worldfilter 
       (fun x -> match x with
	 | Fun("!test!", []) -> false
	 | _ -> true)
       instructions)
    rules
;;

let is_reach_test test = match test with
  | Fun("check_run", _) -> true
  | _ -> false
;;

let check_reach process test_reach rules = match test_reach with
  | Fun("check_run", [w]) ->
      (
	(* debugOutput *)
	(*   "CHECK FOR: %s\nREACH: %s\n\n%!" *)
	(*   (show_trace process) *)
	(*   (show_term w); *)
	try
	  (
	    ignore (execute process [] w rules);
	    true
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

let is_ridentical_test test = match test with
  | Fun("check_identity", [_; _; _]) -> true
  | _ -> false
;;


let rec trace_from_frame frame =
(* create trace out(c,t1). ... .out(c,tn).0 from frame [t1, ..., tn] *)
  match frame with
  | [] ->  NullTrace
  | h::t -> Trace(Output("c", h), trace_from_frame t)
;;


let check_ridentical process test_ridentical rules = match test_ridentical with
  | Fun("check_identity", [w; r; rp]) ->
    (
      try
	let frame = execute process [] w rules in
	let t1 = apply_frame r frame in
	let t2 = apply_frame rp frame in
	  R.equals t1 t2 rules
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

let check_test process test rules =
  if is_ridentical_test test then
    check_ridentical process test rules
  else if is_reach_test test then
    check_reach process test rules
  else
    raise Unknown_test
;;

let rec check_reach_tests trace reach_tests rules =
  match reach_tests with
    | h :: t ->
	(
	  if not (check_reach trace h rules) then
	    Some h
	  else
	    check_reach_tests trace t rules
	)
    | [] -> None
;;

let rec check_ridentical_tests trace ridentical_tests rules =
  match ridentical_tests with
    | h :: t ->
	(
	  if not (check_ridentical trace h rules) then
	    Some h
	  else
	    check_ridentical_tests trace t rules
	)
    | [] -> None
;;
