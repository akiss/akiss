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

open Term

val addto : 'a list ref -> 'a -> unit

(* This module parses arguments and standard input, then defines the
   following variables. *)

val dotfile : string option
val jobs : int
val cmdlist : Ast.cmd list
val xor : bool
val ac : bool
val por : bool ref
val disable_por : bool
val set_por : bool -> unit
val fsymbols : (string * int) list
val evchannels : string list
val privchannels : string list
val rewrite_rules : rules
val evrewrite_rules : rules

module type REWRITING = sig
  val unifiers : term -> term -> rules -> subst list
  val normalize : term -> rules -> term
  val variants : term -> rules -> (term * subst) list
  val equals : term -> term -> rules -> bool
  val matchers : term -> term -> rules -> subst list
end

module R : REWRITING
