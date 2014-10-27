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

open Parser
open Util
open Term
open Horn

module R = Theory.R

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

open Ast

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
