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

(** This module defines the internal representations of processes,
  * together with their operational semantics, process transformations,
  * and transformation from the source language used in parsing. *)

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

let is_io_action a =
  match a with
  | Input(_,_)
  | Output(_,_) -> true
  | Test (_,_) -> false

let remove_term_in_io_action a =
  match a with
  | Input(c,_) -> Input(c,"")
  | Output(c,_) -> Output(c,Var(""))
  | Test(t1,t2) -> Test(t1,t2)

module ActionSet = struct
  include
    Set.Make (struct
                let compare = Pervasives.compare
                type t = action
              end)
  let of_list l = List.fold_left (fun x s -> add s x) empty l
end

type trace =
  | NullTrace
  | Trace of action * trace

let rec trace_size = function
  | NullTrace -> 0
  | Trace(_, t) -> 1 + (trace_size t)

type process = trace list

(** {3 Printing} *)

let str_of_tr tr = match tr with
  | Some(t) -> show_term t
  | None -> "ok"

let show_frame fr =
  show_string_list (trmap show_term fr)

let show_action = function
  | Input(ch, x) -> Printf.sprintf "in(%s,%s)" ch x
  | Output(ch, t) -> Printf.sprintf "out(%s,%s)" ch (show_term t)
  | Test(s,t) -> Printf.sprintf "[%s=%s]" (show_term s) (show_term t)

let rec show_trace = function
  | NullTrace -> "0"
  | Trace(a, rest) -> (show_action a) ^ "." ^ (show_trace rest)

let rec show_process process =
  String.concat "\n\n" (trmap show_trace process)

(** {2 Frames} *)

(* Forward equivalence use static equivalence on frame but this induces collision
with alpha renaming *)
let rec rename_free_names term =
  match term with
    | Fun(n,[]) when startswith n "!n!" -> Fun("!!"^n^"!!",[])
    | Fun(f,x) -> Fun(f, List.map rename_free_names x)
    | Var(x)->Var(x)

(** Create trace [out(c,t1). ... .out(c,tn).0] from frame [[t1; ...; tn]]. *)
let rec trace_from_frame frame =
  match frame with
  | [] ->  NullTrace
  | h::t -> Trace(Output("c",rename_free_names h), trace_from_frame t)

(** Given a trace and a frame resulting from an execution of that trace,
  * restrict elements in frame to outputs on the given channels list. *)
let rec restrict_frame_to_channels frame trace ch =
  match frame with
  | [] -> []
  | h :: tframe ->
      begin match trace with
        | NullTrace -> []
        | Trace(a, rest) ->
            begin match a with
              | Output(chan, term) ->
                  if List.exists (fun x -> x = chan) ch then
                    h::restrict_frame_to_channels tframe rest ch
                  else
                    restrict_frame_to_channels tframe rest ch
              | _ -> restrict_frame_to_channels frame rest ch
            end
      end

(** {2 Symbolic processes} *)

open Ast

type symbProcess =
  | SymbNul
  | SymbAct of action list (* non-empty list *)
  | SymbSeq of symbProcess * symbProcess
  | SymbPar of symbProcess * symbProcess
  | SymbAlt of symbProcess * symbProcess
  | SymbPhase of symbProcess * symbProcess

let rec show_symb = function
  | SymbNul -> "0"
  | SymbAct a -> "(act " ^ String.concat " " (List.map show_action a) ^ ")"
  | SymbSeq (p1, p2) -> "(seq " ^ show_symb p1 ^ " " ^ show_symb p2 ^ ")"
  | SymbPar (p1, p2) -> "(par " ^ show_symb p1 ^ " " ^ show_symb p2 ^ ")"
  | SymbAlt (p1, p2) -> "(alt " ^ show_symb p1 ^ " " ^ show_symb p2 ^ ")"
  | SymbPhase (p1, p2) -> "(phase " ^ show_symb p1 ^ " " ^ show_symb p2 ^ ")"

let rec actions_of p =
  match p with
  | SymbNul -> ActionSet.empty
  | SymbAct a -> ActionSet.of_list (List.rev_map remove_term_in_io_action (List.filter is_io_action a))
  | SymbSeq (p1, p2)
  | SymbAlt (p1, p2)
  | SymbPhase (p1, p2)
  | SymbPar (p1, p2) -> ActionSet.union (actions_of p1) (actions_of p2)

(** Check whether a symbolic process is action determinate.
  * This is a heuristic; it may return false on some action determinate
  * processes, but action determinacy is guaranteed when true is returned. *)
let action_determinate p =
  let rec ad p =
    match p with
    | SymbNul -> true
    | SymbAct a -> true
    | SymbSeq (SymbAct a, p) -> ad p
    | SymbSeq (p, SymbNul) -> ad p
    | SymbSeq (SymbSeq (p1, p2), p) -> ad p1 &&  ad (SymbSeq (p2, p))
    | SymbPar (p1, p2) -> ActionSet.is_empty (ActionSet.inter (actions_of p1) (actions_of p2)) && ( ad p1 && ad p2 )
    | SymbSeq (_, _)
    | SymbPhase (_, _)
    | SymbAlt (_, _) -> false
  in
  match p with
  | SymbPhase (p1, p2) -> ad p1 && ad p2
  | _ as p -> ad p
 
(** {4 Substitution functions} *)

let replace_var_in_term x t term =
  apply_subst term [(x, t)]

let replace_var_in_act x t a =
  match a with
  | Input (_, _) -> a
  | Output (c, term) -> Output (c, replace_var_in_term x t term)
  | Test (term1, term2) ->
     let term1 = replace_var_in_term x t term1 in
     let term2 = replace_var_in_term x t term2 in
     Test (term1, term2)

let rec replace_var_in_symb x t p =
  match p with
  | SymbNul -> SymbNul
  | SymbAct a -> SymbAct (List.map (replace_var_in_act x t) a)
  | SymbSeq (p1, p2) ->
     let p1 = replace_var_in_symb x t p1 in
     let p2 = replace_var_in_symb x t p2 in
     SymbSeq (p1, p2)
  | SymbPar (p1, p2) ->
     let p1 = replace_var_in_symb x t p1 in
     let p2 = replace_var_in_symb x t p2 in
     SymbPar (p1, p2)
  | SymbAlt (p1, p2) ->
     let p1 = replace_var_in_symb x t p1 in
     let p2 = replace_var_in_symb x t p2 in
     SymbAlt (p1, p2)
  | SymbPhase (p1, p2) ->
     let p1 = replace_var_in_symb x t p1 in
     let p2 = replace_var_in_symb x t p2 in
     SymbPhase (p1, p2)

let rec replace_var_in_trace x t = function
  | NullTrace -> NullTrace
  | Trace (Input (c,y), tt) ->
      if x = y then
        Trace (Input (c,y), tt)
      else
        Trace (Input (c,y), replace_var_in_trace x t tt)
  | Trace (Output (c,u), tt) ->
      Trace
        (Output (c, replace_var_in_term x t u),
         replace_var_in_trace x t tt)
  | Trace (Test (u,v), tt) ->
      Trace
        (Test (replace_var_in_term x t u, replace_var_in_term x t v),
         replace_var_in_trace x t tt)

(** {4 Transformations on symbolic processes} *)

(** Enforce Barendregt convention on a trace *)
let refresh p =
  let bound = ref [] in
  let seq p q = if q = SymbNul then p else SymbSeq (p,q) in

  (* The actual refreshing function works on a list
   * that represents a sequence, since inputs bind
   * in the rest of the sequence they're in. *)
  let rec aux = function
    | [] -> SymbNul
    | SymbNul :: l -> aux l
    | SymbSeq (p,q) :: l -> aux (p::q::l) (* TODO p might only bind in q *)
    | SymbPar (p,q) :: l ->
        seq (SymbPar (aux [p], aux [q])) (aux l)
    | SymbPhase (p,q) :: l ->
        seq (SymbPhase (aux [p], aux [q])) (aux l)
    | SymbAlt (p,q) :: l ->
        seq (SymbAlt (aux [p], aux [q])) (aux l)
    | SymbAct [Input (c,x)] :: l ->
        let rec fresh x =
          if List.mem x !bound then fresh (x^"_") else x
        in
        let xx = fresh x in
          bound := xx :: !bound ;
          if not (List.mem xx !vars) then vars := xx :: !vars ;
          seq (SymbAct [Input (c,xx)]) (aux (List.map (replace_var_in_symb x (Var xx)) l))
    | SymbAct [a] :: l ->
        seq (SymbAct [a]) (aux l)
    | SymbAct _ :: _ -> assert false

  in aux [p]

(** Simplify symbolic processes, exploiting the fact that the null process
  * is a unit for all composition operators. *)
let rec simplify = function
  | SymbNul -> SymbNul
  | SymbAct a -> SymbAct a
  | SymbSeq (p1, p2) ->
     (match simplify p1, simplify p2 with
     | SymbNul, p -> p
     | p, SymbNul -> p
     | p1, p2 -> SymbSeq (p1, p2))
  | SymbPar (p1, p2) ->
     (match simplify p1, simplify p2 with
     | SymbNul, p -> p
     | p, SymbNul -> p
     | p1, p2 -> SymbPar (p1, p2))
  | SymbAlt (p1, p2) ->
     (match simplify p1, simplify p2 with
     | SymbNul, p -> p
     | p, SymbNul -> p
     | p1, p2 -> SymbAlt (p1, p2))
  | SymbPhase (p1, p2) ->
      SymbPhase (simplify p1, simplify p2)

(** Avoid useless interleavings by grouping actions:
  * tests can be grouped together, and they can also be grouped
  * with the next observable action. *)
let rec optimize_tests p =
  if Theory.privchannels = []
  then unlinearize SymbNul (compress_tests [] [] (linearize p))
  else p
(* this optimization is currently disabled in the presence of private
   channels as it creates a bug in the pre-treatment: tests before a
   private communication are removed, even though they should not
   be *)

and linearize = function
  | SymbNul -> []
  | SymbAct _ as a -> [a]
  | SymbSeq (p1, p2) -> linearize p1 @ linearize p2
  | SymbPar (p1, p2) -> [SymbPar (optimize_tests p1, optimize_tests p2)]
  | SymbAlt (p1, p2) -> [SymbAlt (optimize_tests p1, optimize_tests p2)]
  | SymbPhase (p1, p2) -> [SymbPhase (optimize_tests p1, optimize_tests p2)]

and unlinearize res = function
  | [] -> res
  | x :: xs -> unlinearize (SymbSeq (x, res)) xs

and compress_tests res accu = function
  | [] -> if accu = [] then res else SymbAct accu :: res
  | SymbAct [Test (_, _) as a] :: xs ->
     compress_tests res (a :: accu) xs
  | SymbAct [Input (_, _) | Output (_, _) as a] :: xs ->
     compress_tests (SymbAct (a :: accu) :: res) [] xs
  | p :: xs ->
     let res = if accu = [] then res else SymbAct accu :: res in
     compress_tests (p :: res) [] xs

(** {4 Parsing} *)

let parse_action = function
  | TempActionOut (ch,t) ->
      if List.mem ch !channels ||
	 List.mem ch Theory.privchannels
      then
	Output (ch,parse_term t)
      else
	Printf.ksprintf failwith "Undeclared channel: %s" ch
  | TempActionIn (ch,x) ->
      if List.mem ch !channels || List.mem ch Theory.privchannels  then
	if List.mem x !vars then
	  Input (ch, x)
	else
	  Printf.ksprintf failwith "Undeclared variable: %s" x
      else
	Printf.ksprintf failwith "Undeclared channel: %s" ch
  | TempActionTest(s, t) ->
      Test (parse_term s, parse_term t)

(** Convert from temp to symb processes,
  * given an association list of (symb) process definitions. *)
let rec symb_of_temp process processes =
  match process with
  | TempEmpty -> SymbNul
  | TempAction a -> SymbAct [parse_action a]
  | TempSequence (p1, p2) ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbSeq (p1, p2)
  | TempInterleave (p1, p2) ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbPar (p1, p2)
  | TempChoice (p1, p2) ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbAlt (p1, p2)
  | TempPhase (p1, p2) ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbPhase (p1, p2)
  | TempLet (x, tt, process) ->
     let t = parse_term tt in
     let p = symb_of_temp process processes in
     replace_var_in_symb x t p
  | TempProcessRef (name) ->
     List.assoc name processes
  | TempNu (x,p) ->
     let p = symb_of_temp p processes in
     let rec fresh_name x =
       if List.mem x !private_names || List.mem x !vars
       then x else fresh_name (x^"_")
     in
     let xx = fresh_name x in
       private_names := xx :: !private_names ;
       replace_var_in_symb x (Fun (xx,[])) p
  | TempBang (i,p) ->
     let p = symb_of_temp p processes in
     let rec rep = function
       | 0 -> SymbNul
       | 1 -> p
       | i -> SymbPar (p, rep (i-1))
     in rep i

(** Transform a temporary process (source language) to a symbolic
  * process. Simplifications are automatically performed, as well
  * as renamings to enforce Barendregt's convention. *)
let parse_process p ps =
  simplify @@ refresh @@ symb_of_temp p ps

(** {4 Operational semantics} *)

let rec delta = function
  | SymbNul -> []
  | SymbAct a -> [ a, SymbNul ]
  | SymbSeq (p1, p2) ->
     List.fold_left (fun accu (a, p) ->
       (a, simplify (SymbSeq (p, p2))) :: accu
     ) [] (delta p1)
  | SymbAlt (p1, p2) -> delta p1 @ delta p2
  | SymbPar (p1, p2) ->
     let s1 =
       List.fold_left (fun accu (a, p) ->
         (a, simplify (SymbPar (p, p2))) :: accu
       ) [] (delta p1)
     in
     let s2 =
       List.fold_left (fun accu (a, p) ->
         (a, simplify (SymbPar (p1, p))) :: accu
       ) s1 (delta p2)
     in
     s2
  | SymbPhase (p1, p2) ->
      List.rev_append
        (List.map (fun (a,p) -> a, SymbPhase (p,p2)) (delta p1))
        (delta p2)

type action_classification =
  | PublicAction
  | PrivateInput of id * id
  | PrivateOutput of id * term

let classify_action = function
  | [] -> assert false
  | Test (_, _) :: _ -> PublicAction
  | Input (c, x) :: _ ->
     if List.mem c Theory.privchannels
     then PrivateInput (c, x) else PublicAction
  | Output (c, t) :: _ ->
     if List.mem c Theory.privchannels
     then PrivateOutput (c, t) else PublicAction

module Trace = struct type t = trace let compare = Pervasives.compare end
module TraceSet = Set.Make (Trace)

let rec trace_prepend a t =
  match a with
  | [] -> t
  | x :: xs -> trace_prepend xs (Trace (x, t))

let rec traces p =
  let d = delta p in
  let r =
    List.fold_left (fun accu (a, q) ->
      match classify_action a with
      | PublicAction ->
         TraceSet.fold (fun q accu ->
           TraceSet.add (trace_prepend a q) accu
         ) (traces q) accu
      | PrivateInput (_, _) -> accu
      | PrivateOutput (c, t) ->
         List.fold_left (fun accu (a, _) ->
           match classify_action a with
           | PrivateInput (c', x) when c = c' ->
              List.fold_left (fun accu (a, q) ->
                match classify_action a with
                | PrivateInput (c', x') when x = x' ->
                   assert (c = c');
                  TraceSet.fold (fun q accu ->
                    TraceSet.add q accu
                  ) (traces (replace_var_in_symb x t q)) accu
                | _ -> accu
              ) accu (delta q)
           | _ -> accu
         ) accu d
    ) TraceSet.empty d
  in
  if TraceSet.is_empty r then TraceSet.singleton NullTrace else r

(** Computing the set of traces with partial order reduction
  *
  * We implement the compressed strategy of Baelde, Hirschi & Delaune
  * for the subset of processes that is supported for it. *)

let rec canonize = function
  | SymbSeq (SymbAct [],q) -> assert false
  | SymbSeq (SymbAct [a],q) -> SymbSeq (SymbAct [a], q)
  | SymbSeq (SymbAct l,q) ->
      List.fold_left
        (fun q a -> SymbSeq (SymbAct [a], q))
        q l
  | SymbSeq (p, SymbNul) -> canonize p
  | SymbAct l -> canonize (SymbSeq (SymbAct l, SymbNul))
  | (SymbPar _ | SymbNul) as p -> p
  | SymbSeq _ | SymbAlt _ | SymbPhase _ -> failwith "unsupported"

let prepend_traces a trace_set =
  TraceSet.fold
    (fun tr accu ->
       TraceSet.add (trace_prepend [a] tr) accu)
    trace_set
    TraceSet.empty

let traces_por p =
  assert (Theory.privchannels = []) ;
  let rec traces async sync =
    match async with
      | p :: async ->
          (* While there are async processes, execute them in a fixed
           * and arbitrary order: break parallels, execute outputs
           * as well as tests *)
          begin match canonize p with
            | SymbNul ->
                traces async sync
            | SymbPar (q1,q2) ->
                traces (q1::q2::async) sync
            | SymbSeq (SymbAct [Output (c,t) as a], q) ->
                prepend_traces a (traces (q::async) sync)
            | SymbSeq (SymbAct [Test (t,t') as a], q) ->
                TraceSet.union
                  (prepend_traces a (traces (q::async) sync))
                  (traces async sync)
            | SymbSeq (SymbAct [Input _], q) ->
                traces async (p::sync)
            | _ ->
                failwith
                  (Printf.sprintf "unsupported async proc: %s" (show_symb p))
          end
      | [] ->
          (* Focus a process, execute it until focus can be released *)
          let rec focus p sync =
            match canonize p with
              | SymbSeq (SymbAct [Input (c,x) as a], q) ->
                  prepend_traces a (focus q sync)
              | SymbSeq (SymbAct [Test (t,t') as a], q) ->
                  (* In case the test fails, the continuation is null
                   * so we have an improper block: no need to explore further
                   * traces. *)
                  prepend_traces a (focus q sync)
              | SymbNul ->
                  (* Obvious improper block *)
                  TraceSet.singleton NullTrace
              | SymbPar (_,_)
              | SymbSeq (SymbAct [Output _], _) ->
                  (* In case of Par, this could be improper
                   * but we don't care and it won't happen in practice. *)
                  traces [p] sync
              | _ ->
                  failwith
                    (Printf.sprintf "unsupported sync proc: %s" (show_symb p))
          in
          let rec all_foci prev trace_set = function
            | p::next ->
                let trace_set =
                  TraceSet.union trace_set (focus p (List.rev_append prev next))
                in
                  all_foci (p::prev) trace_set next
            | [] -> trace_set
          in
          let trace_set = all_foci [] TraceSet.empty sync in
            if TraceSet.is_empty trace_set then
              TraceSet.singleton NullTrace
            else trace_set
  in
    traces [p] []

(** Extend traces_por with shallow support for phases *)
let traces_por p =
  match p with
    | SymbPhase (p1,p2) ->
        let s1 = traces_por p1 in
        let rec aux = function
          | NullTrace -> traces_por p2
          | Trace (Input _ as a, t) ->
              TraceSet.union
                (traces_por p2)
                (prepend_traces a (aux t))
          | Trace (a,t) ->
              prepend_traces a (aux t)
        in
          TraceSet.fold
            (fun t s ->
               TraceSet.union s (aux t))
            s1 TraceSet.empty
    | _ -> traces_por p

(** Compute the set of traces of a process.
  * When [Theory.por] is set, the compressed semantics will be used.
  * Before computing traces, tests are grouped together for optimization. *)
let traces p =
  let traces = if !Theory.por then traces_por else traces in
  TraceSet.elements @@ traces @@ simplify @@ optimize_tests p

(** {2 Executing and testing processes} *)

exception Process_blocked
exception Not_a_recipe
exception Bound_variable
exception Invalid_instruction
exception Too_many_instructions

let is_parameter name =
  (String.sub name 0 1 = "w") &&
    (try
       let pcounter = (String.sub name 1 ((String.length name) - 1)) in
       let ipcounter = (int_of_string pcounter) in
       (ipcounter >= 0) && (pcounter = string_of_int ipcounter)
     with _ -> false)

let param_count name =
  int_of_string (String.sub name 1 ((String.length name) - 1))

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

let rec execute_h_dumb process instructions =
  (* debugOutput *)
  (*   "Executing: %s\nFrame: %s\nInstructions: %s\n\n%!" *)
  (*   (show_trace process) *)
  (*   (show_term_list frame) *)
  (*   (show_term_list instructions); *)
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
    | (Trace(Output(ch, x), pr), Fun("world", [Fun("!out!", [chp]); ir])) ->
        if chp = Fun(ch, []) then
          execute_h_dumb pr ir
        else
         false
    | _ ->  false

let rec execute_h process frame instructions rules =
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

let worldfilter f w =
  revworld (worldfilter_h f w (Fun("empty", [])))

type frame = term list

(** [execute trace frame instructions rules]
  * attempts to execute instructions along the given trace,
  * given a starting frame and set of rewrite rules.
  * @return the resulting frame.
  * @raise Bound_variable if variable naming conventions are not respected.
  * @raise Process_blocked if the process is stuck because of a failed test.
  * @raise Invalid_instruction if two variable bindings rely on the same
  *   variable name.
  * @raise Not_a_recipe if an invalid recipe is met, relying on variable
  *   outside of the frame's domain. *)
let execute process frame instructions rules =
  let slimmed_instructions = (worldfilter
       (fun x -> match x with
          | Fun("!test!", []) -> false
          | _ -> true)
       instructions) in
  if execute_h_dumb process slimmed_instructions then
   begin
     (* Printf.printf "Smart test \n" ;*)
     execute_h
       process
       frame
       (worldfilter
          (fun x -> match x with
             | Fun("!test!", []) -> false
             | _ -> true)
          instructions)
       rules end
  else begin
  (*Printf.printf "Stupid test avoided !\n";*)
    raise Process_blocked
  end

(** {2 Tests} *)

let is_reach_test test = match test with
  | Fun("check_run", _) -> true
  | _ -> false

let check_reach process test_reach rules = match test_reach with
  | Fun("check_run", [w]) ->
      (* debugOutput *)
      (*   "CHECK FOR: %s\nREACH: %s\n\n%!" *)
      (*   (show_trace process) *)
      (*   (show_term w); *)
      (*Printf.printf "r ";*)
      begin try
        (
          ignore (execute process [] w rules); true
        )
      with
        | Process_blocked -> false
        | Too_many_instructions -> false
        | Not_a_recipe -> false
        | Invalid_instruction -> false
        | Bound_variable ->
            invalid_arg "the process binds twice the same variable"
      end
  | _ -> invalid_arg("check_reach")

let is_ridentical_test test = match test with
  | Fun("check_identity", [_; _; _]) -> true
  | _ -> false

let check_ridentical process test_ridentical rules = match test_ridentical with
  | Fun("check_identity", [w; r; rp]) ->
      (*Printf.printf "ri %s" (show_term test_ridentical);*)
      begin try
        let frame = execute process [] w rules in
        let t1 = apply_frame r frame in
        let t2 = apply_frame rp frame in
          R.equals t1 t2 rules
      with
        | Process_blocked -> false
        | Too_many_instructions -> false
        | Not_a_recipe -> false
        | Invalid_instruction -> false
        | Bound_variable ->
            invalid_arg "the process binds twice the same variable"
      end
  | _ -> invalid_arg("check_ridentical")

exception Unknown_test

(** Check if an ridentical or reachability test passes
  * against a given trace and rewrite rules.
  * @raise Unknown_test if the input term is not a ridentical
  * or reachability test. *)
let check_test trace test rules =
  if is_ridentical_test test then
    check_ridentical trace test rules
  else if is_reach_test test then
    check_reach trace test rules
  else
    raise Unknown_test

(** Given a list of reachability tests, a trace and rewrite rules,
  * checks if all tests pass.
  * @return [None] if all tests pass, [Some t] if test [t] fails. *)
let rec check_reach_tests trace reach_tests rules =
  match reach_tests with
    | h :: t ->
        if not (check_reach trace h rules) then
          Some h
        else
          check_reach_tests trace t rules
    | [] -> None

(** Given a list of ridentical tests, a trace and rewrite rules,
  * checks if all tests pass.
  * @return [None] if all tests pass, [Some t] if test [t] fails. *)
let rec check_ridentical_tests trace ridentical_tests rules =
  match ridentical_tests with
    | h :: t ->
        if not (check_ridentical trace h rules) then
          Some h
        else
          check_ridentical_tests trace t rules
    | [] -> None
