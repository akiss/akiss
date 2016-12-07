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
open Process_execution
open Horn
open Theory
open Lwt_compat
open Lwt

let ppool, plwt = Nproc.create jobs

let trace_counter = ref 0
let count_traces = ref 0
let test_counter = ref 0
let count_tests = ref 0


let reset_count new_count =
  trace_counter := 0 ;
  count_traces := new_count

let do_count () =
  trace_counter := !trace_counter + 1;
  normalOutput "\x0dComputed tests %d/%d%!" !trace_counter !count_traces;
  verboseOutput
    "Finished %d-th saturation out of %d\n%!"
    !trace_counter !count_traces

let do_count_tests test =
	test_counter := !test_counter +1;
	verboseOutput "Test %d/%d : %s \n%!" 
	!test_counter !count_tests (show_term test)

let tests_of_trace_job t rew =
  verboseOutput "Constructing seed statements\n%!";
  let seed = Seed.seed_statements t rew in
    verboseOutput "Constructing initial kb\n%!";
    let kb = initial_kb seed rew in
	extraOutput about_seed "Initial seed: %s \n\n"   (show_kb kb);
      verboseOutput "Saturating knowledge base\n%!";
      saturate kb rew ;
	extraOutput about_saturated "Saturated base:  %s\n%!" (show_kb kb);
      checks kb rew

let tests_of_trace show_progress t rew =
  Nproc.submit ppool (tests_of_trace_job t) rew >>= fun x ->
  match x with
  | Some y ->
     if show_progress then do_count ();
     return y
  | None -> failwith "fatal error in tests_of_trace"

let check_test_multi_job source test trace_list =
	extraOutput about_tests "\n\nStarting checks about %s \n%!" (show_term test);
 let result = List.exists (fun x -> check_test source x test Theory.rewrite_rules) trace_list in
	extraOutput about_tests "Result of checks about %s : %b \n%!" (show_term test) result;
	result

let check_test_multi source test trace_list =
  do_count_tests test;
  Nproc.submit ppool (check_test_multi_job source test) trace_list >>= fun x ->
  match x with
  | Some y -> return y
  | None -> assert false

let wait_pending2 x y =
  let r = Lwt_unix.run (x >>= fun x -> y >>= fun y -> return (x, y)) in
  Printf.printf "\n%!"; r

(** Processes and traces *)

let processes = ref []

let rec declare_process name process =
  addto processes (name, parse_process process !processes)

module StringSet = Set.Make (String)

let rec variables_of_term t =
  match t with
  | Var x -> StringSet.singleton x
  | Fun (_, ts) ->
     List.fold_left (fun accu t ->
       StringSet.union accu (variables_of_term t)
     ) StringSet.empty ts

exception MultiplyBoundVariable of string

(** Computes fvs, bvs, where fvs is the set of free variables and bvs
    the set of bound variables. *)
let rec variables_of_trace t =
  match t with
  | NullTrace -> StringSet.empty, StringSet.empty
  | Trace (a, t) ->
     let fvs, bvs = variables_of_trace t in
     match a with
     | Input (_, x) ->
        if StringSet.mem x bvs then
          (* the Barendregt convention is not honoured *)
          raise (MultiplyBoundVariable x);
       StringSet.remove x fvs, StringSet.add x bvs
     | InputMatch(_, t) -> let xs =  variables_of_term t in
       StringSet.diff fvs xs, StringSet.union xs bvs
     | Output (_, t) -> StringSet.union fvs (variables_of_term t), bvs
     | Test (t1, t2) ->
        let xs1 = variables_of_term t1 in
        let xs2 = variables_of_term t2 in
        StringSet.(union fvs (union xs1 xs2)), bvs
     | TestInequal (t1, t2) ->
        let xs1 = variables_of_term t1 in
        let xs2 = variables_of_term t2 in
        StringSet.(union fvs (union xs1 xs2)), bvs

let check_free_variables t =
  try
    let xs, _ = variables_of_trace t in
    if not (StringSet.is_empty xs) then begin
      Printf.eprintf "Process has free variables: %s.\n%!"
        (String.concat ", " (StringSet.elements xs));
      exit 2
    end
  with MultiplyBoundVariable x ->
    Printf.eprintf "Variable %s is bound multiple times.\n%!" x;
    exit 2

let rec remove_duplicate lst =
	match lst with
	| [] -> []
	| t :: q -> let qs = remove_duplicate q in 
		if List.exists (fun x -> (x = t)) qs then qs else t :: qs


let slim lst = lst (*
	debugOutput "\nThere were %d tests in total\n" (List.length lst);
	let qs = remove_duplicate lst in 
	let qs = List.filter (fun t -> not (List.exists (fun x -> (is_smaller_reach_test t x)) qs)) qs in
	count_tests :=  (List.length qs);
	test_counter := 0;
	verboseOutput "There are %d tests to check\n" (List.length qs);
	qs*)

let blop (x,lst) =
	List.map (fun y -> (x,y)) lst

let query ?(expected=true) s t =
  Printf.printf
    "Checking coarse trace %sequivalence of %s and %s\n%!"
    (if expected then "" else "in")
    (show_string_list s) (show_string_list t);
  let straces = List.concat (List.map (fun x -> traces @@ List.assoc x !processes) s) in
  let ttraces = List.concat (List.map (fun x -> traces @@ List.assoc x !processes) t) in
  let () = List.iter check_free_variables straces in
  let () = List.iter check_free_variables ttraces in
  let () = reset_count ((List.length straces) + (List.length ttraces)) in
  verboseOutput "Checking %d traces...\n%!" !count_traces;
  let stests =
    Lwt_list.rev_map_p
      (fun x -> (tests_of_trace true x Theory.rewrite_rules) >>= fun y -> return (x, y) >>= wrap1 blop)
      straces >>= wrap1 List.concat >>= wrap1 slim
  and ttests =
    Lwt_list.rev_map_p
      (fun x -> (tests_of_trace true x Theory.rewrite_rules) >>= fun y -> return (x, y) >>= wrap1 blop)
      ttraces >>= wrap1 List.concat >>= wrap1 slim
  in
  let fail_stests =
    stests >>=
      Lwt_list.filter_p (fun (s,x) -> check_test_multi s x ttraces >>= wrap1 not)
  and fail_ttests =
    ttests >>=
      Lwt_list.filter_p (fun (s,x) -> check_test_multi s x straces >>= wrap1 not)
  in
  let fail_stests, fail_ttests = wait_pending2 fail_stests fail_ttests in
  if fail_stests = [] && fail_ttests = [] then begin
    Printf.printf
      "%s and %s are coarse trace equivalent!\n%!"
      (show_string_list s) (show_string_list t) ;
    if not expected then exit 1
  end else begin
    if fail_stests <> [] then
      Printf.printf "The following tests work on %s but not on %s:\n%s\n%!"
        (show_string_list s) (show_string_list t) (show_tests (List.map (fun (x,y) -> y)fail_stests));
    if fail_ttests <> [] then
      Printf.printf "The following tests work on %s but not on %s:\n%s\n%!"
        (show_string_list t) (show_string_list s) (show_tests (List.map (fun (x,y) -> y)fail_ttests));
    if expected then exit 1
  end


let inclusion_ct ?(expected=true) s t =
  Printf.printf
    "Checking coarse trace %sinclusion of %s in %s\n%!"
    (if expected then "" else "non")
    (show_string_list s) (show_string_list t);
  let straces = Util.union (List.map (fun x -> traces @@ List.assoc x !processes) s) in
  let ttraces = Util.union (List.map (fun x -> traces @@ List.assoc x !processes) t) in
  let () = List.iter check_free_variables straces in
  let () = List.iter check_free_variables ttraces in
  let () = reset_count (List.length straces) in
  let stests =
    Lwt_list.rev_map_p
      (fun x -> tests_of_trace true x Theory.rewrite_rules >>= fun y -> return (x, y) >>= wrap1 blop)
      straces >>= wrap1 List.concat >>= wrap1 slim

  in
    let fail_stests =
    stests >>=
      Lwt_list.filter_p (fun (s,x) -> check_test_multi s x ttraces >>= wrap1 not)
  and fail_ttests = return []
  in
  let fail_stests, fail_ttests = wait_pending2 fail_stests fail_ttests in
  if fail_stests = [] then begin
    Printf.printf
      "%s is coarse trace included in %s!\n%!"
      (show_string_list s) (show_string_list t) ;
    if not expected then exit 1
  end else begin
    if fail_stests <> [] then
      Printf.printf "The following tests work on %s but not on %s:\n%s\n%!"
        (show_string_list s) (show_string_list t) (show_tests (List.map (fun (x,y) -> y)fail_stests));
    if expected then exit 1
  end

exception OneToMoreFail of trace * term list

let check_one_to_one (tests1, trace1) (tests2, trace2) rew =
  let fail1 =
    List.filter
      (fun x -> not (check_test trace1 trace2 x rew))
      tests1
  in
  let fail2 =
    List.filter
      (fun x -> not (check_test trace2 trace1 x rew))
      tests2
  in
    fail1 = [] && fail2 = []

let check_one_to_more (tests1, trace1) list rew =
  if List.exists (fun x -> check_one_to_one (tests1, trace1) x rew) list then
    ()
  else
    raise (OneToMoreFail(trace1, tests1))

let square ~expected s t =
  Printf.printf
    "Checking fine grained %sequivalence of %s and %s\n%!"
    (if expected then "" else "in")
    (show_string_list s) (show_string_list t);
  let ls = List.concat (List.map (fun x -> traces @@ List.assoc x !processes) s) in
  let lt = List.concat (List.map (fun x -> traces @@ List.assoc x !processes) t) in
  let () = List.iter check_free_variables ls in
  let () = List.iter check_free_variables lt in
  let () = reset_count ((List.length ls) + (List.length lt)) in
  let stests =
    Lwt_list.rev_map_p
      (fun x ->
       tests_of_trace true x Theory.rewrite_rules >>= fun y -> return (y, x))
      ls
  and ttests =
    Lwt_list.rev_map_p
      (fun x ->
       tests_of_trace true x Theory.rewrite_rules >>= fun y -> return (y, x))
      lt
  in
  let stests, ttests = wait_pending2 stests ttests in
  try
    ignore
      (List.iter
         (fun x -> check_one_to_more x ttests Theory.rewrite_rules)
         stests);
    ignore
      (List.iter
         (fun x -> check_one_to_more x stests Theory.rewrite_rules)
         ttests);
    Printf.printf "%s and %s are fine-grained trace equivalent\n%!"
      (show_string_list s) (show_string_list t);
    if not expected then exit 1
  with
    | OneToMoreFail(tr, tests) -> 
        Printf.printf
          "cannot establish trace equivalence of %s and %s\n%!" 
          (show_string_list s) (show_string_list t);
        Printf.printf
          "the trace %s has no equivalent trace on the other side\n%!"
          (show_trace tr);
        Printf.printf "its tests are\n%!%s\n%!"
          (show_tests tests);
        if expected then exit 1

let inclusion_ft ~expected s t =
  Printf.printf
    "Checking fine grained %sinclusion of %s in %s\n%!"
    (if expected then "" else "non")
    (show_string_list s) (show_string_list t);
  let ls = List.concat (List.map (fun x -> traces @@ List.assoc x !processes) s) in
  let lt = List.concat (List.map (fun x -> traces @@ List.assoc x !processes) t) in
  let () = List.iter check_free_variables ls in
  let () = List.iter check_free_variables lt in
  let () = reset_count (List.length ls) in
  let stests =
    Lwt_list.rev_map_p
      (fun x ->
       tests_of_trace true x Theory.rewrite_rules >>= fun y -> return (y, x))
      ls
  and ttests =
    Lwt_list.rev_map_p
      (fun x ->
	return [] >>= fun y -> return (y, x))
      lt
  in
  let stests, ttests = wait_pending2 stests ttests in
  try
    ignore
      (List.iter
         (fun x -> check_one_to_more x ttests Theory.rewrite_rules)
         stests);
    Printf.printf "%s is fine-grained trace included in %s\n%!"
      (show_string_list s) (show_string_list t);
    if not expected then exit 1
  with
    | OneToMoreFail(tr, tests) -> 
        Printf.printf
          "cannot establish trace inclusion of %s in %s\n%!" 
          (show_string_list s) (show_string_list t);
        Printf.printf
          "the trace %s has no equivalent trace on the other side\n%!"
          (show_trace tr);
        Printf.printf "its tests are\n%!%s\n%!"
          (show_tests tests);
        if expected then exit 1
	  
let stat_equiv frame1 frame2 rew =
  
  verboseOutput
    "Checking static equivalence of frames %s and %s \n%!"
    (show_frame frame1) (show_frame frame2);
    
  let t1 = trace_from_frame frame1 in
  let t2 = trace_from_frame frame2 in  
  
  let tests1 = tests_of_trace false t1 rew in
  let tests2 = tests_of_trace false t2 rew in
  (*  check_one_to_one  (tests1, t1) (tests2, t2) rew *)

  let fail1 =
    tests1 >>= Lwt_list.filter_p (fun x -> return (not (check_test NullTrace t2 x rew)))
  and fail2 =
    tests2 >>= Lwt_list.filter_p (fun x -> return (not (check_test NullTrace t1 x rew)))
  in

  fail1 >>= fun fail1 -> fail2 >>= fun fail2 ->
  if fail1 = [] && fail2 = [] then return true
  else
    (
      (* verboseOutput "Tests of frame1 that fail on frame2: \n %s \n" (show_tests fail1); *)
      return false
    )

let check_ev_ind_test trace1 trace2 test = 
  (* check that reach test from trace1 is reachable in trace2 and check static equiv of two resulting frames *)
  match test with
  | Fun("check_run", [w]) ->
      let (f1,_) = execute trace1 [] w Theory.rewrite_rules in
      begin try
        let (f2,_) = execute trace2 [] w Theory.rewrite_rules in
        let rf1 = restrict_frame_to_channels f1 trace1 Theory.evchannels in
        let rf2 = restrict_frame_to_channels f2 trace2 Theory.evchannels in
        stat_equiv rf1 rf2 Theory.evrewrite_rules >>= fun r ->
          if r then
            verboseOutput "static equivalence verified\n%!"
          else
            verboseOutput "static equivalence not verified\n%!";
          return r
      with
        | Process_blocked -> return false
        | Too_many_instructions -> return false
        | Not_a_recipe -> return false
        | Invalid_instruction -> return false
        | Bound_variable -> invalid_arg "the process binds twice the same variable"
      end
  | _ -> invalid_arg("check_reach")


let ev_check_one_to_one (tests1, trace1) (tests2, trace2) =
  let fail1 =
    Lwt_list.filter_p
      (fun x -> check_ev_ind_test trace1 trace2 x >>= wrap1 not) tests1
  and fail2 =
    Lwt_list.filter_p
      (fun x -> check_ev_ind_test trace2 trace1 x >>= wrap1 not) tests2
  in
  fail1 >>= fun fail1 -> fail2 >>= fun fail2 ->
  return (fail1 = [] && fail2 = [])

let ev_check_one_to_more (tests1, trace1) list =
  if List.exists
       (fun x -> Lwt_unix.run (ev_check_one_to_one (tests1, trace1) x)) list
  then
    ()
  else
    raise (OneToMoreFail(trace1, tests1))

let evequiv ~expected s t =
  Printf.printf
    "Checking forward %sdistinguishability for %s and %s\n%!"
    (if expected then "in" else "")
    (show_string_list s) (show_string_list t);
  (* list of traces of s, then t *)
  let ls =
    List.concat (List.map (fun x -> traces @@ List.assoc x !processes) s)
  in
  let lt =
    List.concat (List.map (fun x -> traces @@ List.assoc x !processes) t)
  in
  let () = List.iter check_free_variables ls in
  let () = List.iter check_free_variables lt in
  let () = reset_count ((List.length ls) + (List.length lt)) in
  let stests =
    Lwt_list.rev_map_p
      (fun x ->
       tests_of_trace true x Theory.rewrite_rules >>= fun y ->
       return (List.filter is_reach_test y, x))
      ls
  and ttests =
    Lwt_list.rev_map_p
      (fun x ->
       tests_of_trace true x Theory.rewrite_rules >>= fun y ->
       return (List.filter is_reach_test y, x))
      lt
  in
  let stests, ttests = wait_pending2 stests ttests in
    try
      ignore (trmap (fun x -> ev_check_one_to_more x ttests ) stests);
      ignore (trmap (fun x -> ev_check_one_to_more x stests ) ttests);
      Printf.printf
        "%s and %s are forward indistinguishable\n%!"
        (show_string_list s) (show_string_list t);
      if not expected then exit 1
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
            (show_tests tests);
          if expected then exit 1

let trace_of_process (p : process) : trace =
  match p with
    | [t] -> t
    | _ -> invalid_arg "trace_of_process: not a trace"

let print_trace_list (tlist : trace list) = 
  Printf.printf "%s\n%!" (String.concat "\n" (trmap show_trace tlist))

let print_traces tnl =
  Printf.printf "Printing the list of traces of %s\n%!" (String.concat ", " tnl);
  let tl = List.concat (trmap (fun x -> (traces @@ List.assoc x !processes)) tnl) in
  print_trace_list tl

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
  let t = trace_of_process(traces @@ List.assoc traceName !processes) in
  let kb_seed = Seed.seed_statements t Theory.rewrite_rules in
    Printf.printf
      "\n\nSeed statements of %s:\n%s\n\n%!"
      traceName (show_kb_list kb_seed);
    let kb = initial_kb kb_seed Theory.rewrite_rules in
      Printf.printf
        "Initial knowledge base of %s:\n\n%s%!"
        traceName (show_kb kb);
      saturate kb Theory.rewrite_rules ;
      Printf.printf "\n\nSolved statements after saturation:\n\n" ;
      print_kbs (Base.solved kb) ;
      Printf.printf "\nUnsolved statements after saturation:\n\n" ;
      print_kbs (Base.not_solved kb) ;
      Printf.printf "\n\nKnows solved statements in saturation:\n\n" ;
      print_kbs ~filter:is_deduction_st (Base.solved kb) ;
      Printf.printf "\n\nKnows unsolved statements in saturation:\n\n" ;
      print_kbs ~filter:is_deduction_st (Base.not_solved kb) ;
      let tests = checks kb Theory.rewrite_rules in
        Printf.printf "\n\nTests:\n\n%s\n\n%!" (show_tests tests);
        let trace = trace_of_process (traces @@ List.assoc traceName !processes) in
          Printf.printf
            "Running reach self tests: %s\n\
             Running ridentical self tests: %s\n\n%!"
            (str_of_tr
               (check_reach_tests t
                  trace
                  (List.filter is_reach_test tests)
                  Theory.rewrite_rules))
            (str_of_tr
               (check_ridentical_tests t
                  trace
                  (List.filter is_ridentical_test tests)
                  Theory.rewrite_rules))

open Ast

let processCommand = function

  | DeclProcess(name, process) ->
    verboseOutput "Declaring process %s\n%!" name;
    declare_process name process

  | QueryNegatable (expected, NegEquivalent (traceList1, traceList2)) ->
    query ~expected traceList1 traceList2
  | QueryNegatable (expected, NegSquare (traceList1, traceList2)) ->
    square ~expected traceList1 traceList2
  | QueryNegatable (expected, NegEvSquare (traceList1, traceList2)) ->
    evequiv ~expected traceList1 traceList2
  | QueryNegatable (expected, NegIncFt (traceList1, traceList2)) ->
    inclusion_ft ~expected traceList1 traceList2
  | QueryNegatable (expected, NegIncCt (traceList1, traceList2)) ->
    inclusion_ct ~expected traceList1 traceList2

  | QueryPrint traceName ->
    Printf.printf "Printing information about %s\n%!" traceName;
    query_print traceName
  | QueryPrintTraces traceList ->
    Printf.printf
      "Printing trace list of %s\n%!"
      (show_string_list traceList);
    print_traces traceList
  | QueryVariants tt -> 
    let t = parse_term tt in
    Printf.printf
      "Computing variants of %s\n%!" (show_term t);

    let vl = (R.variants t Theory.rewrite_rules) in
    let varst = vars_of_term t in
    let vl_cleaned =
      List.map ( fun (vt, subst) -> (vt, restrict subst varst ) ) vl in 
		     
    Printf.printf "%s\n" (show_variant_list vl_cleaned);
    Printf.printf "%i Variants Found\n" (List.length vl_cleaned)
  | QueryUnifiers (tt1, tt2) -> 
    let t1 = parse_term tt1 in
    let t2 = parse_term tt2 in
    Printf.printf
      "Computing unifiers of %s and %s\n%!" (show_term t1) (show_term t2);
    let sl = (R.unifiers t1 t2 Theory.rewrite_rules) in
    let v = vars_of_term_list [t1;t2] in
    let sl_cleaned =
      List.map ( fun subst -> restrict subst v ) sl in 
    Printf.printf "%s\n" (show_subst_list sl_cleaned);
    Printf.printf "%i Unifier%s Found\n"
      (List.length sl_cleaned)
      (if (List.length sl_cleaned) > 1 then "s" else "") 
  | QueryNormalize tt -> 
    let t = parse_term tt in
    Printf.printf
      "Computing normal form of %s\n%!" (show_term t);
    let tn = (R.normalize t Theory.rewrite_rules) in
    Printf.printf "%s\n" (show_term tn);
  | _ ->
    Printf.eprintf "Illegal declaration outside preamble!\n" ;
    exit 1

      
let () =
  List.iter processCommand cmdlist
