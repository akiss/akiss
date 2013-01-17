open Lexer
open Parser
open Util
open Term
open Process
open Horn

module Variants = Maude

let usage = Printf.sprintf
  "Usage: %s [-verbose] [-debug] < specification-file.api"
  (Filename.basename Sys.argv.(0))
;;

let args = ref []

let command_line_options_list = [
  ("-verbose", Arg.Unit (fun () -> verbose_output := true),
   "Enable verbose output");
  ("-debug", Arg.Unit (fun () -> debug_output := true),
   "Enable debug output")  
];;

let channels = ref [];;

let evchannels = ref [];;

let rewrite_rules = ref [];;

let evrewrite_rules = ref [];;

let processes = ref [];;

let appendto lref l = lref := List.append !lref l;;

let addto lref e = appendto lref [e];;

let rec declare_symbols symbolList =
  appendto fsymbols symbolList
;;

let rec declare_names nameList = 
  appendto private_names nameList
;;

let rec declare_channels nameList =
  appendto channels nameList
;;

let rec declare_evchannels nameList =
  appendto channels nameList;
  appendto evchannels nameList
;;


let rec declare_vars varList = 
  appendto vars varList
;;

let rec declare_rewrite t1 t2 = 
  addto rewrite_rules ((parse_term t1), (parse_term t2))
;;

let rec declare_evrewrite t1 t2 = 
  addto evrewrite_rules ((parse_term t1), (parse_term t2))
;;


(* let rec declare_trace traceName actionList = *)
(*   addto processes (traceName, [parse_trace actionList]) *)
(* ;; *)

let rec declare_process name process =
  addto processes (name, parse_process process !processes)
;;

(** Compute the part of seed statements that comes from the theory. *)
let context_statements symbol arity rules =
  let w = Var(fresh_variable ()) in
  let vYs = trmap fresh_variable (create_list () arity) in
  let vZs = trmap fresh_variable (create_list () arity) in
  let add_knows x y = Predicate("knows", [w; x; y]) in
  let box_vars names = trmap (function x -> Var(x)) names in
  let body sigma = List.map2 
    (add_knows) 
    (box_vars vYs) 
    (trmap (function x -> apply_subst x sigma) (box_vars vZs))
  in
  let t = Fun(symbol, box_vars vZs) in
  let v = Variants.variants t rules in
  trmap
    (function (x,y) ->
       new_clause
         (Predicate("knows", 
                    [w;
                     Fun(symbol, box_vars vYs);
                     x
                    ]),
          body y))
    v
;;

let seed_statements trace rew =
  let (l1, l2) = List.split !fsymbols in
  let context_clauses = trconcat
    (List.map2
       (fun x -> fun y ->
	  context_statements x y rew)
       l1 l2)
  in
  let trace_clauses =
    knows_statements trace rew
  in
  let reach_clauses =
    reach_statements trace rew
  in
  trconcat [context_clauses; trace_clauses; reach_clauses]
;;

let tests_of_trace t rew =
  verboseOutput "Constructing seed statements\n%!";
  let seed = seed_statements t rew in
  (* Printf.printf "\n\nSeed statements of %s:\n\n%s\n\n%!" (show_trace t) (show_kb seed); *)
  (
    verboseOutput "Constructing initial kb\n%!";
    let kb_can = initial_kb seed in
    (
(*      Printf.printf "\n\nInitial knowledge base of %s:\n\n%s\n\n%!" (show_trace t) (show_kb kb_can); *)
      verboseOutput "Saturating knowledge base\n%!";
      let kb_sat = saturate kb_can rew in
(*      Printf.printf "\n\nSaturated knowledge base of %s:\n\n%s\n\n%!" (show_trace t) (show_kb kb_can);*)
      checks kb_sat
    )
  )
;;

let check_test_multi test trace_list =
  List.exists (fun x -> check_test x test !rewrite_rules) trace_list
;;

let trace_counter = ref 0;;
let count_traces = ref 0;;

let reset_count new_count =
  (
    trace_counter := 0;
    count_traces := new_count;
  )
;;

let do_count () = 
  (
    trace_counter := !trace_counter + 1;
    verboseOutput "On the %d-th saturation out of %d\n%!" !trace_counter !count_traces
  )
;;

let query s t =
  verboseOutput "Checking equivalence of %s and %s\n%!" (show_string_list s) (show_string_list t);
  let (straces : trace list) = trconcat (trmap (fun x -> List.assoc x !processes) s) in
  let ttraces = trconcat (trmap (fun x -> List.assoc x !processes) t) in
  let _ = reset_count ((List.length straces) + (List.length ttraces)) in
  let stests = trconcat (trmap (fun x ->
				  (
				    do_count ();
				    tests_of_trace x !rewrite_rules
				  ))
			   straces) in
  let ttests = trconcat (trmap (fun x ->
				  (
				    do_count ();
				    tests_of_trace x !rewrite_rules
				  ))
			   ttraces) in
  let fail_stests = List.filter (fun x -> not (check_test_multi x ttraces)) stests in
  let fail_ttests = List.filter (fun x -> not (check_test_multi x straces)) ttests in
  if (List.length fail_stests) = 0 && (List.length fail_ttests) = 0 then
    Printf.printf "%s and %s are TRACE EQUIVALENT!\n%!" (show_string_list s) (show_string_list t)
  else
    (
      if (List.length fail_stests) <> 0 then
	Printf.printf "The following tests work on %s but not on %s:\n%s\n%!"
	  (show_string_list s) (show_string_list t) (show_tests fail_stests);
      if (List.length fail_ttests) <> 0 then
	Printf.printf "The following tests work on %s but not on %s:\n%s\n%!"
	  (show_string_list t) (show_string_list s) (show_tests fail_ttests);
    )
;;

exception OneToMoreFail of trace * term list;;

let check_one_to_one (tests1, trace1) (tests2, trace2) rew =
  let fail1 = List.filter
    (fun x -> not (check_test trace2 x rew)) tests1 in
  let fail2 = List.filter
    (fun x -> not (check_test trace1 x rew)) tests2 in
  ((List.length fail1 = 0) && (List.length fail2 = 0))
;;

let check_one_to_more (tests1, trace1) list rew =
  if List.exists (fun x -> check_one_to_one (tests1, trace1) x rew) list then
    ()
  else
    raise (OneToMoreFail(trace1, tests1))
;;

let square s t =
  (
    verboseOutput "Checking fine grained equivalence of %s and %s\n%!" (show_string_list s) (show_string_list t);
    let ls = trconcat (trmap (fun x -> List.assoc x !processes) s) in
    let lt = trconcat (trmap (fun x -> List.assoc x !processes) t) in
    let _ = reset_count ((List.length ls) + (List.length lt)) in
    let stests = trmap (fun x -> 
			  (
			    do_count ();
			    ((tests_of_trace x !rewrite_rules), x)
			  )
		       ) ls in
    let ttests = trmap (fun x -> 
			  (
			    do_count ();
			    ((tests_of_trace x !rewrite_rules), x)
			  )
		       ) lt in
    try
      (
	ignore (trmap (fun x -> check_one_to_more x ttests !rewrite_rules) stests);
	ignore (trmap (fun x -> check_one_to_more x stests !rewrite_rules) ttests);
	Printf.printf "%s and %s are trace equivalent\n%!"
	  (show_string_list s) (show_string_list t)
      )
    with
	OneToMoreFail(tr, tests) -> 
	  (
	    Printf.printf "cannot establish trace equivalence of %s and %s\n%!" 
	      (show_string_list s) (show_string_list t);
	    Printf.printf "the trace %s has no equivalent trace on the other side\n%!"
	      (show_trace tr);
	    Printf.printf "its tests are\n%!%s\n%!"
	      (show_tests tests);
	  )
  )
;;

let stat_equiv frame1 frame2 rew =
  
  verboseOutput "Checking static equivalence of frames %s and %s \n%!" (show_frame frame1) (show_frame frame2);
    
  let t1 = trace_from_frame frame1 in
  let t2 = trace_from_frame frame2 in  
  
  let tests1 = tests_of_trace t1 rew in
  let tests2 = tests_of_trace t2 rew in
  (*  check_one_to_one  (tests1, t1) (tests2, t2) rew *)

  let fail1 = List.filter
    (fun x -> not (check_test t2 x rew)) tests1 in
  let fail2 = List.filter
    (fun x -> not (check_test t1 x rew)) tests2 in

  if ((List.length fail1 = 0) && (List.length fail2 = 0)) then true 
  else
    (
      (* verboseOutput "Tests of frame1 that fail on frame2: \n %s \n" (show_tests fail1); *)
      false
    )

;;


let check_ev_ind_test trace1 trace2 test = 
  (* check that reach test from trace1 is reachable in trace2 and check static equiv of two resulting frames *)
  match test with
  | Fun("check_run", [w]) ->
    (
	(* debugOutput *)
	(*   "CHECK FOR: %s\nREACH: %s\n\n%!" *)
	(*   (show_trace process) *)
	(*   (show_term w); *)
      let f1 = execute trace1 [] w !rewrite_rules in
      try
	(
	  let f2 = execute trace2 [] w !rewrite_rules in
	  let rf1 = restrict_frame_to_channels f1 trace1 !evchannels in
	  let rf2 = restrict_frame_to_channels f2 trace2 !evchannels in
	  let r = stat_equiv rf1 rf2 !evrewrite_rules in (if r then (verboseOutput "static equivalence verified\n%!"; r) else (verboseOutput "static equivalence not verified\n%!"; r))
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


let ev_check_one_to_one (tests1, trace1) (tests2, trace2) =
  let fail1 = List.filter
    (fun x -> not (check_ev_ind_test trace1 trace2 x)) tests1 in
  let fail2 = List.filter
    (fun x -> not (check_ev_ind_test trace2 trace1 x)) tests2 in
  ((List.length fail1 = 0) && (List.length fail2 = 0))
;;

let ev_check_one_to_more (tests1, trace1) list =
  if List.exists (fun x -> ev_check_one_to_one (tests1, trace1) x ) list then
    ()
  else
    raise (OneToMoreFail(trace1, tests1))
;;

let evequiv s t =
  verboseOutput "Checking forward indistinguishability for %s and %s\n%!" (show_string_list s) (show_string_list t);
    let ls = trconcat (trmap (fun x -> List.assoc x !processes) s) in (* list of traces of s *)
    let lt = trconcat (trmap (fun x -> List.assoc x !processes) t) in (* list of traces of t *)
    let _ = reset_count ((List.length ls) + (List.length lt)) in
    let stests = trmap 
      (fun x -> 
	(
	  do_count ();
	  ((List.filter is_reach_test (tests_of_trace x !rewrite_rules)), x)
	)
      ) ls in
    let ttests = trmap 
      (fun x -> 
	(
	  do_count ();
	  ((List.filter is_reach_test (tests_of_trace x !rewrite_rules)), x)
	)
      ) lt in 
    try
      (
	ignore (trmap (fun x -> ev_check_one_to_more x ttests ) stests);
	ignore (trmap (fun x -> ev_check_one_to_more x stests ) ttests);
	Printf.printf "%s and %s are forward indistinguishable\n%!"
	  (show_string_list s) (show_string_list t)
      )
    with
	OneToMoreFail(tr, tests) -> 
	  (
	    Printf.printf "cannot establish forward equivalence of %s and %s\n%!" 
	      (show_string_list s) (show_string_list t);
	    Printf.printf "the trace %s has no equivalent trace on the other side\n%!"
	      (show_trace tr);
	    Printf.printf "its tests are\n%!%s\n%!"
	      (show_tests tests);
	  )

;;

type atom_type =  
  | Channel
  | Name
  | Symbol of int
  | Variable
;;

exception No_duplicate;;

let rec find_dup l = 
  match l with
    | [] -> raise No_duplicate
    | _ :: [] -> raise No_duplicate
    | (x, _) :: ((y, _) as hd) :: tl ->
	if y = x then
	  x
	else
	  find_dup (hd :: tl)
;;

exception Parse_error_semantic of string;;

let check_atoms () =
  let atoms = 
    trconcat [
      trmap (fun (x, y) -> (x, Symbol(y))) !fsymbols;
      trmap (fun x -> (x, Channel)) !channels;
      trmap (fun x -> (x, Variable)) !vars;
      trmap (fun x -> (x, Name)) !private_names;
    ] in
  let sorted_atoms = List.sort (fun (x, _) (xp, _) -> compare x xp) atoms in
  try
    let duplicate = find_dup sorted_atoms in
    raise (Parse_error_semantic
	     (Printf.sprintf "Identifier \"%s\" declared more than once." duplicate))
  with
    | No_duplicate -> ()
    | Parse_error_semantic(e) -> raise (Parse_error_semantic(e))
;;

let trace_of_process (p : process) : trace =
  match p with
    | [t] -> t
    | _ -> invalid_arg("trace_of_process: not a trace")
;;

let interleave_opt tnl =
  let tl = trmap (fun x -> trace_of_process(List.assoc x !processes)) tnl in
  interleave_opt_traces tl
;;

let remove_end_tests_traces (tlist : trace list) =
  trmap (fun x -> fst (split_endingtests x)) tlist
;;

let remove_end_tests tnl =
  let tl = trmap (fun x -> trace_of_process(List.assoc x !processes)) tnl in
  remove_end_tests_traces tl
;;

let rec interleave_two_traces s t =
  match (s, t) with
    | (NullTrace, _) -> [t]
    | (_, NullTrace) -> [s]
    | (Trace(a, sn), Trace(b, tn)) ->
	List.append
	  (trmap (fun x -> Trace(a, x)) (interleave_two_traces sn t))
	  (trmap (fun x -> Trace(b, x)) (interleave_two_traces s tn))
;;

let rec interleave_traces (tlist : trace list) : trace list =
  match tlist with
    | [] -> [NullTrace]
    | hd :: [] -> [hd]
    | hd :: hdp :: tl ->
	trconcat
	  (trmap
	     (fun x -> interleave_traces (x :: tl))
	     (interleave_two_traces hd hdp))
;;

let interleave tnl =
  let tl = trmap (fun x -> trace_of_process(List.assoc x !processes)) tnl in
  interleave_traces tl
;;

let declare_interleave traceName traceList =
  addto processes (traceName, interleave traceList)
;;

let declare_interleave_opt traceName traceList =
  addto processes (traceName, interleave_opt traceList)
;;

let declare_remove_end_tests traceName traceList =
  addto processes (traceName, remove_end_tests traceList)
;;

let print_trace_list (tlist : trace list) = 
  Printf.printf "%s\n%!" (String.concat "\n" (trmap show_trace tlist))
;;

let print_traces tnl =
  Printf.printf "Printing the list of traces of %s\n%!" (String.concat ", " tnl);
  let tl = trconcat (trmap (fun x -> (List.assoc x !processes)) tnl) in
  print_trace_list tl
;;

let sequence tnl =
  let tl = trmap (fun x -> List.assoc x !processes) tnl in
  sequence_traces tl
;;

let declare_sequence traceName traceList =
  addto processes (traceName, sequence traceList)
;;

let query_print traceName =
  let t = trace_of_process(List.assoc traceName !processes) in
  let kb_seed = seed_statements t !rewrite_rules in
  (
    Printf.printf "\n\nSeed statements of %s:\n\n%s%!" traceName (show_kb kb_seed);
    let kb_ini = initial_kb kb_seed in
    (
      Printf.printf "\n\nInitial knowledge base of %s:\n\n%s%!" traceName (show_kb kb_ini);
      let kb_sat = saturate kb_ini !rewrite_rules in
      let tests = checks kb_sat in
      (
	Printf.printf "\n\nAfter saturation:\n\n%s\n\nKnows solved statements in saturation: %s\n\nKnows statements in saturation: %s\n\nTests:\n%s\n\n%!" (show_kb kb_sat) (show_kb (only_solved (only_knows kb_sat))) (show_kb (only_knows kb_sat)) (show_tests tests);
	let trace = trace_of_process (List.assoc traceName !processes) in
	Printf.printf "Running reach self tests: %s\nRunning ridentical self tests: %s\n\n%!"
	  (str_of_tr (check_reach_tests trace (List.filter is_reach_test tests) !rewrite_rules))
	  (str_of_tr (check_ridentical_tests trace (List.filter is_ridentical_test tests) !rewrite_rules))
      )
    )
  )
;;

let processCommand (c : cmd) =
  match c with
  | DeclSymbols symbolList ->
    Printf.printf "Declaring symbols\n%!";
    declare_symbols symbolList;
    check_atoms ()
  | DeclChannels channelList ->
    Printf.printf "Declaring symbols\n%!";
    declare_channels channelList;
    check_atoms ()
  | DeclEvChannels evchannelList ->
    Printf.printf "Declaring symbols\n%!";
    declare_evchannels evchannelList;
    check_atoms ()
  | DeclPrivate nameList ->
    Printf.printf "Declaring private names\n%!";
    declare_names nameList;
    check_atoms ()
  | DeclVar varList ->
    Printf.printf "Declaring variables\n%!";
    declare_vars varList;
    check_atoms ()
  | DeclRewrite(t1, t2) ->
    Printf.printf "Declaring rewrite rule\n%!";
    declare_rewrite t1 t2
  | DeclEvRewrite(t1, t2) ->
    Printf.printf "Declaring rewrite rule\n%!";
    declare_evrewrite t1 t2
  | DeclProcess(name, process) ->
    Printf.printf "Declaring process %s\n%!" name;
    declare_process name process
  | DeclInterleave(traceName, traceList) ->
    Printf.printf "Declaring trace as interleaving\n%!";
    declare_interleave traceName traceList
  | DeclInterleaveOpt(traceName, traceList) ->
    Printf.printf "Declaring trace as optimal interleaving\n%!";
    declare_interleave_opt traceName traceList
  | DeclRemoveEndTests(traceName, traceList) ->
    Printf.printf "Declaring trace by removing end tests\n%!";
    declare_remove_end_tests traceName traceList
  | DeclSequence(traceName, traceList) ->
    Printf.printf "Declaring trace as sequence\n%!";
    declare_sequence traceName traceList
  | QueryEquivalent(traceList1, traceList2) ->
    query traceList1 traceList2
  | QuerySquare (traceList1, traceList2) ->
    Printf.printf "Checking fine grained equivalence of %s and %s\n%!" (show_string_list traceList1) (show_string_list traceList2);
    square traceList1 traceList2

  | QueryEvSquare (traceList1, traceList2) ->
    Printf.printf "Checking forward indistinguishability of  %s and %s\n%!" (show_string_list traceList1) (show_string_list traceList2);
    evequiv traceList1 traceList2

  | QueryPrint traceName ->
    Printf.printf "Printing information about %s\n%!" traceName;
    query_print traceName
  | QueryPrintTraces traceList ->
    Printf.printf "Printing trace list of %s\n%!" (show_string_list traceList);
    print_traces traceList
;;

let process (cmdlist : cmd list) = 
  ignore (trmap processCommand cmdlist)
;;

let _ =
  let collect arg = args := !args @ [arg] in
  let _ = Arg.parse command_line_options_list collect usage in
  let lexbuf = Lexing.from_channel stdin in
  try
    process (Parser.main Lexer.token lexbuf)
  with Parsing.Parse_error ->
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    Printf.printf "Syntax error at line %d, column %d!\n" line cnum;
