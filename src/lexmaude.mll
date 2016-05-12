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

{
  open Parsemaude

  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }
}

let digit = ['0' - '9']
let digits = digit +
let lower = ['a' - 'z']
let upper = ['A' - 'Z']
let letter = lower | upper
let letters = letter (('.'| letter | digit) * )

  rule token = parse
  | "Maude> ==========================================" { Line1 }
  | "No unifier." { NoUnifiers }
  | "No more unifiers." { NoMoreUnifiers }
  | "No more variants." { NoMoreVariants }
  | "Unifier" { Unifier }
  | "Variant" { Variant }
  | "reduce" { Reduce }
  | "result" { Result }
  | "Solution" { Solution }
  | "Bool" {Bool}
  | "Term" { Term }
  | "#" { Sharp }
  | "%" { Percent }
  | "variant unify" { VariantUnify }
  | "get variants" { GetVariants }
  | "rewrites: " digits " in " digits "ms cpu (" digits "ms real) ("
    (digits | "~") " rewrites/second)" { Rewritesline }
  | "in" {  In }
  | digits "ms" { Ms }
  | "cpu" { Cpu }
  | "real" { Real }
  | "second" { Second }
  | "true" {True}
  | "false" {False}
  | "0" { Zero }
  | "-->" {Arrow}
  | "/" { Slash }
  | "+" { Plus }
  | "," { Comma }
  | ":" { Colon }
  | "=" { Equals }
  | "=?" { EqualUnify }
  | "<?" { EqualMatch }
  | "(" { LeftP }
  | ")" { RightP }
  | "." { Dot }
  | digits as n { Number n }
  | letters as s { Identifier s }
  | '\n' { incr_linenum lexbuf; token lexbuf }
  | "Bye." { Bye }
  | _ { token lexbuf }
