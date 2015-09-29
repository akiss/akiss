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

let knows_equationalize (head, body) rules =
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
    | Predicate("knows", [w; r; t]) ->
       Predicate("knows", [apply_subst w sigma; r; apply_subst t sigma])
    | _ -> invalid_arg("wrong head") in
  let newclause sigma =
    (newhead sigma, trmap (fun x -> newatom sigma x) newbody) in
  trmap newclause sigmas
;;

let knows_statements tr rules =
  let kstatements = knows_statements_h 0 tr [] (Fun("empty", [])) [] in
    List.concat
      (List.map
         (fun x -> knows_variantize x rules)
         (List.concat (trmap (fun x -> knows_equationalize x rules) kstatements)))
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

(** Compute everything *)
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
