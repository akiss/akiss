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
open Process

module R = Theory.R

(** {1 Seed statements} *)





let normalize_msg_atom rules = function
  | Knows( l, r , t ) -> Knows( l, r, R.normalize t rules)
  | Reach(l) -> Reach(l)
  | Identical(l, r, rp) -> Identical(l, r, rp)

let normalize_input rules = function
  input -> {l = input.l ; t= R.normalize input.t rules}

let normalize_msg_st (dag, inputs, head, body) rules =
  (dag, 
  trmap (fun x -> normalize_input rules x) inputs, 
  normalize_msg_atom rules head, 
  trmap (fun x -> normalize_msg_atom rules x) body)


let apply_subst_msg_atom sigma = function
  | Knows(l, r, t) -> Knows(l, r, apply_subst t sigma)
  | Reach(l) -> Reach(l)
  | Identical(l, r, rp) -> Identical(l, r, rp)

let apply_subst_input sigma = function
  input -> {l = input.l ; t= apply_subst input.t sigma}

let apply_subst_msg_st (dag, inputs, head, body) sigma =
  (dag, trmap (fun x -> apply_subst_input sigma x) inputs, apply_subst_msg_atom sigma head,
   trmap (fun x -> apply_subst_msg_atom sigma x) body)

(** {2 Compute knows statements from a trace} *)







(** Compute the part of seed statements that comes from the theory. *)
let context_statements symbol arity rules =
  if !debug_seed then Format.printf "Computing context statement for %s \n%!" symbol;
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
  if Theory.xor && symbol = "plus" then
    (* World variable *)
    let w = Var "X" in
    (* Recipe variables, marked or not *)
    let r1 = Var "X1" in
    let r2 = Var "X2" in
    let p1 = Var "Q1" in
    let p2 = Var "Q2" in
    (* Message variables *)
    let x1 = Var "X11" in
    let x2 = Var "X12" in
    let x3 = Var "X13" in
    (* Syntactic sugar *)
    let (+) a b = Fun("plus",[a;b]) in
    let knows r x = Predicate("knows",[w;r;x]) in
    let (<=) h t = Horn.new_clause (h,t,[]) in
    let (<==) h t = Horn.new_clause ~vip:true (h,t,[]) in
      (* Kinit statements for xor *)
      [ knows (r1+r2) (x1+x2)
          <= [ knows r1 x1 ; knows r2 x2 ] ;
        knows (p1+p2) x1
          <== [ knows p1 (x1+x2) ; knows p2 x2 ] ;
        knows (p1+p2) (x1+x2)
          <== [ knows p1 (x1+x3) ; knows p2 (x2+x3) ] ]
  else
  let t = Fun(symbol, box_vars vZs) in
  let v = R.variants t rules in
    trmap
    (function (t',sigma) ->
        new_clause
          (Predicate("knows",
                     [w;
                      Fun(symbol, box_vars vYs);
                      t'
                     ]),
           body sigma, []))
    v

(** Compute everything *)
let seed_statements ?one_reach:(one_reach = false) trace rew =
  let context_clauses =
    List.concat
      (List.map
         (fun (f,a) ->
            context_statements f a rew)
         (List.sort (fun (_,a) (_,a') -> compare a a') Theory.fsymbols))
  in
  let trace_clauses =
    trace_statements ~one_reach:one_reach trace rew
  in
  if !debug_seed then Format.printf "Seed computation completed \n\n%!" ;
    List.concat [context_clauses; trace_clauses]
