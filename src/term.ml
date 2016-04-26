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

open Util
open Parser

exception Parse_error_semantic of string

exception Invalid_term

let vars : (string list) ref = ref []

let fsymbols : ((string * int) list) ref = ref []

let channels : (string list) ref = ref []

let private_names : (string list) ref = ref []

type id = string

type varName = id

type funName = id

type term =
  | Fun of funName * term list
  | Var of varName

type subst =
    (varName * term) list

type rules = (term * term) list

let is_var term = match term with
  | Var(_) -> true
  | _ -> false

let unbox_var = function
  | Var(x) -> x
  | _ -> invalid_arg "unbox_var"

let rec vars_of_term_list term_list =
  unique (List.concat (List.map vars_of_term term_list))
and vars_of_term = function
  | Fun(_, term_list) -> vars_of_term_list term_list
  | Var(x) -> [x]

(** Signature extension: symbols that may be used in terms
  * in addition to the declared public symbols. *)
type extrasig = {
  vars : string list ;
  names : int list ;
  params : int list ;
  tuples : int list
}

let rec sig_of_term_list cur = function
  | [] -> cur
  | Var x :: l ->
      sig_of_term_list { cur with vars = x :: cur.vars } l
  | Fun ("!tuple!",l) :: l' ->
      let cur = { cur with tuples = List.length l :: cur.tuples } in
        sig_of_term_list cur (l@l')
  | Fun (s,[]) :: l ->
      begin try
        Scanf.sscanf s "w%d"
          (fun n ->
             let cur = { cur with params = n::cur.params } in
               sig_of_term_list cur l)
      with Scanf.Scan_failure _ ->
        begin try
          Scanf.sscanf s "!n!%d"
            (fun n ->
               let cur = { cur with names = n::cur.names } in
                 sig_of_term_list cur l)
            with Scanf.Scan_failure _ ->
              sig_of_term_list cur l
        end
      end
  | Fun (_,l) :: l' ->
      sig_of_term_list cur (List.rev_append l l')

let sig_of_term_list l =
  let { vars=vars ; names=names ; params=params ; tuples=tuples } =
    sig_of_term_list { vars = [] ; names = [] ; params = [] ; tuples = [] } l
  in
    { vars = Util.unique vars ; names = Util.unique names ;
      params = Util.unique params ; tuples = Util.unique tuples }

let is_ground t = vars_of_term t = []

let occurs var term =
  List.mem var (vars_of_term term)

let rec show_term = function
  | Fun("!out!", term_list) ->
      show_term (Fun("out", term_list))
  | Fun("!in!", term_list) ->
      show_term (Fun("in", term_list))
  | Fun("!test!", term_list) ->
      show_term (Fun("test", term_list))
  | Fun("world", [w; ws]) -> show_term w ^ "." ^ show_term ws
  | Fun("zero",[]) -> "0"
  | Fun("plus",[t1;t2]) -> (show_term t1)^"+"^(show_term t2)
  | Fun(f, l) ->
      (f ^
	 (if l <> [] then "(" else "") ^
	 (show_term_list l) ^
	 (if l <> [] then ")" else "") )
  | Var(v) -> v
and show_term_list = function
  | [x] -> show_term x
  | x :: l -> ( (show_term x) ^ "," ^ (show_term_list l) )
  | [] -> ""

let rec apply_subst term (sigma : subst) =
  match term with
    | Var(x) ->
	if List.mem_assoc x sigma then
	  List.assoc x sigma
	else
	  term
    | Fun(symbol, list) ->
	Fun(symbol, trmap (function x -> apply_subst x sigma) list)

let bound variable sigma =
  List.mem_assoc variable sigma

let apply_subst_term_list tl sigma =
  trmap (fun x -> apply_subst x sigma) tl

let show_subst sigma =
    "{ " ^
      (String.concat ", "
	 (trmap
	    (fun (x, t) -> x ^ " |-> " ^ (show_term t))
	    sigma)) ^
      " }"

let rec show_subst_list sl =
  match sl with
  | [x] -> show_subst x
  | x :: l -> ( (show_subst x) ^ "," ^ (show_subst_list l) )
  | [] -> ""

let compose (sigma : subst) (tau : subst) =
  trmap (function x -> (x, apply_subst (apply_subst (Var(x)) sigma) tau))
    (List.append (fst (List.split sigma)) (fst (List.split tau)))

let restrict (sigma : subst) (domain : varName list) =
  List.filter (fun (x, _) -> List.mem x domain) sigma

let rec parse_term (Ast.TempTermCons(x,l)) =
  if List.mem x !vars then
    if l = [] then
      Var x
    else
      raise (Parse_error_semantic
               (Printf.sprintf "variable %s used as function symbol" x))
  else if List.mem x !private_names then
      if l = [] then
        Fun(x, [])
      else
        raise (Parse_error_semantic
                 (Printf.sprintf "private name %s used as function symbol" x))
  else
      try
        let arity = List.assoc x !fsymbols in
          if List.length l = arity then
            Fun(x, trmap parse_term l)
          else
            raise
              (Parse_error_semantic
                 (Printf.sprintf
                    "function symbol %s has arity %d \
                                but is used here with arity %d"
                    x arity (List.length l)))
      with
        | Not_found ->
            raise
              (Parse_error_semantic
                 (Printf.sprintf "undeclared function symbol %s" x))
