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
  open Parsetam

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
   | "maude tool: 'maude'" {Line1}
   | " checking version: 2.6. OK." {Line2}
   | " checking installation: OK." {Line3}
   | "Finished." { Finished }
   | "#" { Sharp }
   | ">" { Greater }
   | "<" { Less }
   | "variants of" { Variants }
   | "unify" { Unify }
   | "match" { Match }
   | "Norm :" { Norm }
   | "with" { With }
   | "pattern" { Pattern }
   | "added functions:" { FunDecl }
   | "added equations:" { EqDecl }
   | "0" { Zero }
   | "/" { Slash }
   | "+" { Plus }
   | "," { Comma }
   | ":" { Colon }
   | "=" { Equals }
   | ">" { Greater }
   | "{" { LeftCB }
   | "}" { RightCB }
   | "(" { LeftP }
   | ")" { RightP }
   | "." { Dot }
   | "'" { Quote }
   | digits as n { Int(int_of_string n) }
   | letters as s { Identifier s }
   | '\n' { incr_linenum lexbuf; token lexbuf }
   | eof { EOF }
   | _ { token lexbuf }
