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
(*  | InputMatch of id * term *)
  | Output of id * term
  | Test of term * term
  | TestInequal of term * term
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
(*  | InputMatch(ch, t) -> Printf.sprintf "in(%s,<%s>)" ch (show_term t)*)
  | Output(ch, t) -> Printf.sprintf "out(%s,%s)" ch (show_term t)
  | Test(s,t) -> Printf.sprintf "[%s=%s]" (show_term s) (show_term t)
  | TestInequal(s,t) -> Printf.sprintf "[%s!=%s]" (show_term s) (show_term t)
;;

let rec show_action_lst = function 
	| t::q -> (show_action t)^","^(show_action_lst q)
	| [] -> "."

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
  | TempActionOut(ch, t) ->
     if List.mem ch !channels then
       Output(ch, parse_term t)
     else if List.mem ch Theory.privchannels then
       Output(ch, parse_term t)
     else
       Printf.ksprintf failwith "Undeclared channel: %s" ch
  | TempActionIn(ch, x) ->
    if List.mem ch !channels || List.mem ch Theory.privchannels  then
      if List.mem x !vars then
	Input(ch, x)
      else
	Printf.ksprintf failwith "Undeclared variable: %s" x
    else
      Printf.ksprintf failwith "Undeclared channel: %s" ch
  | TempActionTest(s, t) -> Test(parse_term s, parse_term t)
  | TempActionTestInequal(s, t) -> TestInequal(parse_term s, parse_term t)
;;

let replace_var_in_term x t term =
  apply_subst term [(x, t)]
;;

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

let replace_var_in_act x t a =
  match a with
  | Input (_, _) -> a
 (* | InputMatch (c, term) -> InputMatch (c, replace_var_in_term x t term)*)
  | Output (c, term) -> Output (c, replace_var_in_term x t term)
  | Test (term1, term2) ->
     let term1 = replace_var_in_term x t term1 in
     let term2 = replace_var_in_term x t term2 in
     Test (term1, term2)
  | TestInequal (term1, term2) ->
     let term1 = replace_var_in_term x t term1 in
     let term2 = replace_var_in_term x t term2 in
     TestInequal (term1, term2)

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
  | SymbPhase _ as p -> p

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
  | TestInequal (_, _) :: _ -> PublicAction
  | Input (c, x) :: _ ->
     if List.mem c Theory.privchannels
     then PrivateInput (c, x) else PublicAction
(*  | InputMatch (c, t) :: _ -> assert (false) (* Todo *)*)
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

let traces p =
  let traces = if Theory.por then traces_por else traces in
    TraceSet.elements @@ traces @@ simplify @@ optimize_tests p

let parse_process p ps =
  simplify @@ symb_of_temp p ps

