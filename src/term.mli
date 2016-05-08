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

exception Parse_error_semantic of string
exception Invalid_term

val vars : string list ref
val channels : string list ref
val fsymbols : (string * int) list ref
val private_names : string list ref

type id = string
type varName = id
type funName = id
type term = Fun of funName * term list | Var of varName
type subst = (varName * term) list
type rules = (term * term) list

val is_var : term -> bool
val unbox_var : term -> varName
val vars_of_term_list : term list -> varName list
val vars_of_term : term -> varName list
type extrasig =
  { vars : string list ;
    names : int list ;
    params : int list ;
    tuples : int list }
val sig_of_term_list : term list -> extrasig

val is_ground : term -> bool
val occurs : varName -> term -> bool

val parse_term : Ast.tempTerm -> term
val show_term : term -> varName
val show_term_list : term list -> varName
val show_subst : subst -> string
val show_subst_list : subst list -> string
val show_variant_list: (term * subst) list -> string

val apply_subst : term -> subst -> term
val bound : varName -> subst -> bool

val compose : subst -> subst -> subst
val restrict : subst -> varName list -> subst
