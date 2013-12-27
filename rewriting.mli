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

(** Rewriting utilities for terms.
  * This module does not support AC connectives. *)

exception Not_unifiable
exception Not_matchable

(** Unification and matching for free terms *)

val mgu : Term.term -> Term.term -> Term.subst
val mgm : Term.term -> Term.term -> Term.subst

(** Utilities for handling a (non-AC) theory *)

val normalize : Term.term -> (Term.term*Term.term) list -> Term.term

val variants :
  Term.term ->
  (Term.term * Term.term) list ->
  (Term.term * Term.subst) list
val unifiers :
  Term.term -> Term.term -> (Term.term * Term.term) list -> Term.subst list
