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

(** {2 Processes} *)

type action =
  | Input of id * id
  | Output of id * term
  | Test of term * term

type trace =
  | NullTrace
  | Trace of action * trace

type process = trace list

(** {3 Printing} *)

val str_of_tr : term option -> varName
val show_frame : term list -> string
val show_trace : trace -> string

(** {3 Parsing} *)

val parse_process : Ast.tempProcess -> (string * process) list -> process

(** {2 Executing and testing processes} *)

exception Process_blocked
exception Not_a_recipe
exception Bound_variable
exception Invalid_instruction
exception Too_many_instructions

val execute : trace -> term list -> term -> rules -> term list

val is_reach_test : term -> bool
val is_ridentical_test : term -> bool
val trace_from_frame : term list -> trace
val restrict_frame_to_channels : term list -> trace -> id list -> term list
val check_test : trace -> term -> rules -> bool
val check_reach_tests : trace -> term list -> rules -> term option
val check_ridentical_tests : trace -> term list -> rules -> term option
