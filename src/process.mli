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
  | InputMatch of id * term
  | Output of id * term
  | Test of term * term
  | TestInequal of term * term

type trace =
  | NullTrace
  | Trace of action * trace

type process = trace list

type symbProcess

(** {3 Printing} *)

val str_of_tr : term option -> varName
val show_frame : term list -> string
val show_trace : trace -> string
val show_action_lst : action list -> string

(** {3 Parsing} *)

val parse_process : Ast.tempProcess -> (string * symbProcess) list -> symbProcess
val traces : symbProcess -> process


