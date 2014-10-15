(****************************************************************************)
(* Akiss                                                                    *)
(* Copyright (C) 2011-2014 Baelde, Ciobaca, Delaune, Kremer                 *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

open Lexer
open Parser
open Util
open Term
open Process
open Horn
open Theory

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
  let v = R.variants t rules in
    trmap
    (function (t',sigma) ->
      let clause =
        new_clause
          (Predicate("knows", 
                     [w;
                      Fun(symbol, box_vars vYs);
                      t'
                     ]),
           body sigma)
      in
        (* Mark recipe variables in non-trivial variants of the plus clause. *)
        if Theory.ac && symbol = "plus" && sigma <> [] then
          try
            let r =
              match
                List.find
                  (function
                     | Predicate("knows",[_;_;Fun("plus",_)]) -> true
                     | _ -> false)
                  (get_body clause)
              with
                | Predicate (_,[_;Var r;_]) -> r
                | _ -> assert false
            in
            let p = fresh_string "P" in
              apply_subst_st clause [r,Var p]
          with Not_found ->
            if not Horn.extra_static_marks then clause else
              begin match
                List.find
                  (function
                     | Predicate("knows",[_;_;Var _]) -> true
                     | _ -> false)
                  (get_body clause)
              with
                | Predicate (_,[_;Var r;_]) ->
                    let p = fresh_string "P" in
                      apply_subst_st clause [r,Var p]
                | _ -> assert false
              end
        else
          clause)
    v

let seed_statements trace rew =
  let context_clauses =
    List.concat
      (List.map
         (fun (f,a) ->
            context_statements f a rew)
         (List.sort (fun (_,a) (_,a') -> compare a a') Theory.fsymbols))
  in
  let trace_clauses =
    knows_statements trace rew
  in
  let reach_clauses =
    reach_statements trace rew
  in
    List.concat [context_clauses; trace_clauses; reach_clauses]

let tests_of_trace t rew =
  verboseOutput "Constructing seed statements\n%!";
  let seed = seed_statements t rew in
    verboseOutput "Constructing initial kb\n%!";
    let kb = initial_kb seed rew in
      verboseOutput "Saturating knowledge base\n%!";
      saturate kb rew ;
      checks kb

let check_test_multi test trace_list =
  List.exists (fun x -> check_test x test Theory.rewrite_rules) trace_list

(** Processes and traces *)

let processes = ref []

let rec declare_process name process =
  addto processes (name, parse_process process !processes)

let trace_counter = ref 0
let count_traces = ref 0

let reset_count new_count =
  trace_counter := 0 ;
  count_traces := new_count

let do_count () = 
  trace_counter := !trace_counter + 1;
  verboseOutput
    "On the %d-th saturation out of %d\n%!"
    !trace_counter !count_traces

let query ?(expected=true) s t =
  verboseOutput
    "Checking %sequivalence of %s and %s\n%!"
    (if expected then "" else "in")
    (show_string_list s) (show_string_list t);
  let (straces : trace list) =
    List.concat (List.map (fun x -> List.assoc x !processes) s)
  in
  let ttraces = List.concat (List.map (fun x -> List.assoc x !processes) t) in
  let _ = reset_count ((List.length straces) + (List.length ttraces)) in
  let stests =
    List.concat
      (List.map
         (fun x ->
            do_count ();
            tests_of_trace x Theory.rewrite_rules)
         straces)
  in
  let ttests =
    List.concat
      (List.map
         (fun x ->
            do_count ();
            tests_of_trace x Theory.rewrite_rules)
         ttraces)
  in
  let fail_stests = List.filter (fun x -> not (check_test_multi x ttraces)) stests in
  let fail_ttests = List.filter (fun x -> not (check_test_multi x straces)) ttests in
  if (List.length fail_stests) = 0 && (List.length fail_ttests) = 0 then begin
    Printf.printf
      "%s and %s are TRACE EQUIVALENT!\n%!"
      (show_string_list s) (show_string_list t) ;
    if not expected then exit 1
  end else begin
    if (List.length fail_stests) <> 0 then
      Printf.printf "The following tests work on %s but not on %s:\n%s\n%!"
        (show_string_list s) (show_string_list t) (show_tests fail_stests);
    if (List.length fail_ttests) <> 0 then
      Printf.printf "The following tests work on %s but not on %s:\n%s\n%!"
        (show_string_list t) (show_string_list s) (show_tests fail_ttests);
    if expected then exit 1
  end

exception OneToMoreFail of trace * term list

let check_one_to_one (tests1, trace1) (tests2, trace2) rew =
  let fail1 =
    List.filter
      (fun x -> not (check_test trace2 x rew))
      tests1
  in
  let fail2 =
    List.filter
      (fun x -> not (check_test trace1 x rew))
      tests2
  in
    fail1 = [] && fail2 = []

let check_one_to_more (tests1, trace1) list rew =
  if List.exists (fun x -> check_one_to_one (tests1, trace1) x rew) list then
    ()
  else
    raise (OneToMoreFail(trace1, tests1))

let square s t =
  verboseOutput
    "Checking fine grained equivalence of %s and %s\n%!"
    (show_string_list s) (show_string_list t);
  let ls = List.concat (List.map (fun x -> List.assoc x !processes) s) in
  let lt = List.concat (List.map (fun x -> List.assoc x !processes) t) in
  let _ = reset_count ((List.length ls) + (List.length lt)) in
  let stests =
    List.map
      (fun x -> 
         do_count ();
         ((tests_of_trace x Theory.rewrite_rules), x))
      ls
  in
  let ttests =
   List.map
     (fun x -> 
        do_count ();
        ((tests_of_trace x Theory.rewrite_rules), x))
     lt
  in
  try
    ignore
      (List.iter
         (fun x -> check_one_to_more x ttests Theory.rewrite_rules)
         stests);
    ignore
      (List.iter
         (fun x -> check_one_to_more x stests Theory.rewrite_rules)
         ttests);
    Printf.printf "%s and %s are trace equivalent\n%!"
      (show_string_list s) (show_string_list t)
  with
    | OneToMoreFail(tr, tests) -> 
        Printf.printf
          "cannot establish trace equivalence of %s and %s\n%!" 
          (show_string_list s) (show_string_list t);
        Printf.printf
          "the trace %s has no equivalent trace on the other side\n%!"
          (show_trace tr);
        Printf.printf "its tests are\n%!%s\n%!"
          (show_tests tests)

let stat_equiv frame1 frame2 rew =
  
  verboseOutput
    "Checking static equivalence of frames %s and %s \n%!"
    (show_frame frame1) (show_frame frame2);
    
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

let check_ev_ind_test trace1 trace2 test = 
  (* check that reach test from trace1 is reachable in trace2 and check static equiv of two resulting frames *)
  match test with
  | Fun("check_run", [w]) ->
      let f1 = execute trace1 [] w Theory.rewrite_rules in
      begin try
        let f2 = execute trace2 [] w Theory.rewrite_rules in
        let rf1 = restrict_frame_to_channels f1 trace1 Theory.evchannels in
        let rf2 = restrict_frame_to_channels f2 trace2 Theory.evchannels in
        let r = stat_equiv rf1 rf2 Theory.evrewrite_rules in
          if r then
            verboseOutput "static equivalence verified\n%!"
          else
            verboseOutput "static equivalence not verified\n%!";
          r
      with
        | Process_blocked -> false
        | Too_many_instructions -> false
        | Not_a_recipe -> false
        | Invalid_instruction -> false
        | Bound_variable -> invalid_arg "the process binds twice the same variable"
      end
  | _ -> invalid_arg("check_reach")


let ev_check_one_to_one (tests1, trace1) (tests2, trace2) =
  let fail1 =
    List.filter
      (fun x -> not (check_ev_ind_test trace1 trace2 x))
      tests1
  in
  let fail2 =
    List.filter
      (fun x -> not (check_ev_ind_test trace2 trace1 x))
      tests2
  in
    fail1 = [] && fail2 = []

let ev_check_one_to_more (tests1, trace1) list =
  if List.exists (fun x -> ev_check_one_to_one (tests1, trace1) x ) list then
    ()
  else
    raise (OneToMoreFail(trace1, tests1))

let evequiv s t =
  verboseOutput
    "Checking forward indistinguishability for %s and %s\n%!"
    (show_string_list s) (show_string_list t);
  (* list of traces of s, then t *)
  let ls =
    List.concat (List.map (fun x -> List.assoc x !processes) s)
  in
  let lt =
    List.concat (List.map (fun x -> List.assoc x !processes) t)
  in
  let _ = reset_count ((List.length ls) + (List.length lt)) in
  let stests =
    List.map
      (fun x -> 
         do_count ();
         ((List.filter is_reach_test (tests_of_trace x Theory.rewrite_rules)), x))
      ls
  in
  let ttests =
    List.map
      (fun x -> 
         do_count ();
         ((List.filter is_reach_test (tests_of_trace x Theory.rewrite_rules)), x))
      lt
  in 
    try
      ignore (trmap (fun x -> ev_check_one_to_more x ttests ) stests);
      ignore (trmap (fun x -> ev_check_one_to_more x stests ) ttests);
      Printf.printf
        "%s and %s are forward indistinguishable\n%!"
        (show_string_list s) (show_string_list t)
    with
      |	OneToMoreFail(tr, tests) -> 
          Printf.printf
            "cannot establish forward equivalence of %s and %s\n%!" 
            (show_string_list s) (show_string_list t);
          Printf.printf
            "the trace %s has no equivalent trace on the other side\n%!"
            (show_trace tr);
          Printf.printf
            "its tests are\n%!%s\n%!"
            (show_tests tests)

let trace_of_process (p : process) : trace =
  match p with
    | [t] -> t
    | _ -> invalid_arg "trace_of_process: not a trace"

let interleave_opt tnl =
  let tl =
    List.map (fun x -> trace_of_process(List.assoc x !processes)) tnl
  in
  interleave_opt_traces tl

let remove_end_tests_traces (tlist : trace list) =
  List.map (fun x -> fst (split_endingtests x)) tlist

let remove_end_tests tnl =
  let tl =
    List.map (fun x -> trace_of_process(List.assoc x !processes)) tnl
  in
  remove_end_tests_traces tl

let rec interleave_two_traces s t =
  match (s, t) with
    | (NullTrace, _) -> [t]
    | (_, NullTrace) -> [s]
    | (Trace(a, sn), Trace(b, tn)) ->
	List.append
	  (List.map (fun x -> Trace(a, x)) (interleave_two_traces sn t))
	  (List.map (fun x -> Trace(b, x)) (interleave_two_traces s tn))

let rec interleave_traces (tlist : trace list) : trace list =
  match tlist with
    | [] -> [NullTrace]
    | hd :: [] -> [hd]
    | hd :: hdp :: tl ->
	List.concat
	  (List.map
	     (fun x -> interleave_traces (x :: tl))
	     (interleave_two_traces hd hdp))

let interleave tnl =
  let tl =
    List.map (fun x -> trace_of_process(List.assoc x !processes)) tnl
  in
  interleave_traces tl

let declare_interleave traceName traceList =
  addto processes (traceName, interleave traceList)

let declare_interleave_opt traceName traceList =
  addto processes (traceName, interleave_opt traceList)

let declare_remove_end_tests traceName traceList =
  addto processes (traceName, remove_end_tests traceList)

let print_trace_list (tlist : trace list) = 
  Printf.printf "%s\n%!" (String.concat "\n" (trmap show_trace tlist))

let print_traces tnl =
  Printf.printf "Printing the list of traces of %s\n%!" (String.concat ", " tnl);
  let tl = List.concat (trmap (fun x -> (List.assoc x !processes)) tnl) in
  print_trace_list tl

let sequence tnl =
  let tl = List.map (fun x -> List.assoc x !processes) tnl in
  sequence_traces tl

let declare_sequence traceName traceList =
  addto processes (traceName, sequence traceList)

let query_print traceName =
  let print_kbs ?(filter=fun _ -> true) s =
    let c = ref 0 in
      Base.S.iter
        (fun f -> if filter f then begin
           incr c ;
           Printf.printf "%s\n" (show_statement f)
         end)
        s ;
      Printf.printf "(total: %d statements)\n" !c
  in
  let t = trace_of_process(List.assoc traceName !processes) in
  let kb_seed = seed_statements t Theory.rewrite_rules in
    Printf.printf
      "\n\nSeed statements of %s:\n%s\n\n%!"
      traceName (show_kb_list kb_seed);
    let kb = initial_kb kb_seed Theory.rewrite_rules in
      Printf.printf
        "Initial knowledge base of %s:\n\n%s%!"
        traceName (show_kb kb);
      saturate kb Theory.rewrite_rules ;
      Printf.printf "\n\nAfter saturation:\n" ;
      print_kbs (Base.solved kb) ;
      Printf.printf "\n" ;
      print_kbs (Base.not_solved kb) ;
      Printf.printf "\n\nKnows solved statements in saturation:\n" ;
      print_kbs ~filter:is_deduction_st (Base.solved kb) ;
      Printf.printf "\n\nKnows unsolved statements in saturation:\n" ;
      print_kbs ~filter:is_deduction_st (Base.not_solved kb) ;
      let tests = checks kb in
        Printf.printf "\n\nTests:\n%s\n\n%!" (show_tests tests);
        let trace = trace_of_process (List.assoc traceName !processes) in
          Printf.printf
            "Running reach self tests: %s\n\
             Running ridentical self tests: %s\n\n%!"
            (str_of_tr
               (check_reach_tests
                  trace
                  (List.filter is_reach_test tests)
                  Theory.rewrite_rules))
            (str_of_tr
               (check_ridentical_tests
                  trace
                  (List.filter is_ridentical_test tests)
                  Theory.rewrite_rules))

open Ast

let processCommand = function

  | DeclProcess(name, process) ->
    Printf.printf "Declaring process %s\n%!" name;
    declare_process name process
  | DeclInterleave(traceName, traceList) ->
    Printf.printf "Declaring %s as interleaving\n%!" traceName;
    declare_interleave traceName traceList
  | DeclInterleaveOpt(traceName, traceList) ->
    Printf.printf "Declaring %s as optimal interleaving\n%!" traceName;
    declare_interleave_opt traceName traceList
  | DeclRemoveEndTests(traceName, traceList) ->
    Printf.printf "Declaring %s by removing end tests\n%!" traceName;
    declare_remove_end_tests traceName traceList
  | DeclSequence(traceName, traceList) ->
    Printf.printf "Declaring %s as sequence\n%!" traceName;
    declare_sequence traceName traceList

  | QueryEquivalent(traceList1, traceList2) ->
    query ~expected:true traceList1 traceList2
  | QueryInequivalent(traceList1, traceList2) ->
    query ~expected:false traceList1 traceList2
  | QuerySquare (traceList1, traceList2) ->
    Printf.printf
      "Checking fine grained equivalence of %s and %s\n%!"
      (show_string_list traceList1) (show_string_list traceList2);
    square traceList1 traceList2
  | QueryEvSquare (traceList1, traceList2) ->
    Printf.printf
      "Checking forward indistinguishability of  %s and %s\n%!"
      (show_string_list traceList1) (show_string_list traceList2);
    evequiv traceList1 traceList2
  | QueryPrint traceName ->
    Printf.printf "Printing information about %s\n%!" traceName;
    query_print traceName
  | QueryPrintTraces traceList ->
    Printf.printf
      "Printing trace list of %s\n%!"
      (show_string_list traceList);
    print_traces traceList

  | _ ->
    Printf.eprintf "Illegal declaration outside preamble!\n" ;
    exit 1

let () =
  List.iter processCommand cmdlist
