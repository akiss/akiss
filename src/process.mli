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

open Term

type action =
  | Input of id * id
  | Output of id * term
  | Test of term * term

type trace =
  | NullTrace
  | Trace of action * trace

(** Symbolic processes are intermediates between the input language
  * processes (Ast.tempProcess) and processes as sets of traces.
  * They feature less syntactic sugar than tempProcesses. *)
type symbProcess

val parse_process : Ast.tempProcess -> (string * symbProcess) list -> symbProcess

val action_determinate : symbProcess -> bool

val traces : symbProcess -> trace list

(** {2 Frames} *)

type frame = term list

val trace_from_frame : frame -> trace
val restrict_frame_to_channels : frame -> trace -> id list -> term list

(** {2 Execution of a trace} *)

exception Process_blocked
exception Not_a_recipe
exception Bound_variable
exception Invalid_instruction
exception Too_many_instructions

val execute : trace -> frame -> term -> rules -> term list

(** {2 Tests} *)

val is_reach_test : term -> bool
val check_reach_tests : trace -> term list -> rules -> term option

val is_ridentical_test : term -> bool
val check_ridentical_tests : trace -> term list -> rules -> term option

val check_test : trace -> term -> rules -> bool

(** {2 Printing} *)

val show_frame : frame -> string
val show_trace : trace -> string

(** Printing of test result. *)
val str_of_tr : term option -> string
