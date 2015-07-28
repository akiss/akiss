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

type tempTerm =
  | TempTermCons of string * (tempTerm list)

type tempAction =
  | TempActionIn of string * string
  | TempActionOut of string * tempTerm
  | TempActionTest of tempTerm * tempTerm

type tempProcess =
  | TempSequence of tempProcess * tempProcess
  | TempAction of tempAction
  | TempInterleave of tempProcess * tempProcess
  | TempLet of string * tempTerm * tempProcess
  | TempEmpty
  | TempProcessRef of string
		      
type negatable_cmd =
  | NegEquivalent of (string list) * (string list)
  | NegSquare of (string list) * (string list)
  | NegEvSquare of (string list) * (string list)

type cmd =
  | SetXOR | SetAC
  | DeclSymbols of (string * int) list
  | DeclPrivate of string list
  | DeclChannels of string list
  | DeclEvChannels of string list
  | DeclVar of string list
  | DeclRewrite of tempTerm * tempTerm
  | DeclEvRewrite of tempTerm * tempTerm
  | DeclProcess of string * tempProcess
  | QueryNegatable of bool * negatable_cmd
  | QueryPrint of string
  | QueryPrintTraces of string list
  | QueryVariants of tempTerm
