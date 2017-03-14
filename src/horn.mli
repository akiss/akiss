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

(** Manipulating clauses and saturating knowledge base *)

open Term

(** {2 Flags} *)

(** {2 Predicates and clauses, conversions and printing} *)

type predicateName = id
type atom = Predicate of predicateName * term list

type statement (** a Horn clause *)


val is_deduction_st : statement -> bool
val get_body : statement -> atom list

(** {3 Printing} *)

val show_statement : statement -> string
val show_atom : atom -> string
val show_atom_body : atom -> string
val show_atom_ineq : atom -> string
val show_atom_list : atom list -> string
val apply_subst_st : statement -> subst -> statement

(** {3 Unification and substitutions} *)

val new_clause :
  ?label:string -> ?vip:bool -> ?parents:statement list -> atom * atom list  * atom list -> statement

(** {3 Knowledge bases} *)

module Base : sig
  type t (** a knowledge base, i.e. a set of well-formed statements *)
  module S : Set.S with type elt = statement
  val solved : t -> S.t
  val not_solved : t -> S.t
end

val show_kb : Base.t -> string
val show_kb_list : statement list -> string

(** {2 Initial knowledge base} *)

val initial_kb : statement list -> rules -> Base.t

(** {2 Saturation procedure} *)

val saturate : ?only_reach:bool -> Base.t -> rules -> unit

(** {2 Recipe stuff} *)

val revworld : term -> term
val checks : Base.t -> rules -> term list
val show_tests : term list -> string

(** Opti stuff *)
val is_smaller_reach_test : term -> term -> bool
