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
  open Parser

  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }
  ;;
}  
let digit = ['0' - '9']
let digits = digit +
let lower = ['a' - 'z']
let upper = ['A' - 'Z']
let letter = lower | upper
let letters = letter ((letter | digit) * )
rule token = parse
    | "0" { Zero }
    | "let" { Let }
    | "#set xor" { XOR }
    | "#set ac;"  { AC }
    | "#set ac+;" { AC }
    | "symbols" { Symbols }
    | "private" { Private }
    | "channels" { Channels }
    | "evchannels" { EvChannels }
    | "privchannels" { PrivChannels }
    | "::" { InnerSequence }
    | "||" { InnerInterleave }
    | "++" { InnerChoice }
    | ">>" { InnerPhase }
    | "if" { If}
    | "then" {Then}
    | "else" {Else}
    | "print_traces" { PrintTraces }
    | "print" { Print }
    | "equivalentft?" { Square }
    | "includedft?" { Incft }
    | "includedct?" { Incct }
    | "fwdequivalentft?" { EvSquare }
    | "var" { Var }
    | "equivalentct?" { Equivalent }
    | "not" { Not }
    | "variants?" { Variants }
    | "unifiers?" { Unifiers }
    | "normalize?" { Normalize }
    | "and" { And }
    | "/*" { comment 1 lexbuf }
    | "//" { line_comment lexbuf }
    | "/" { Slash }
    | "," { Comma }
    | ";" { Semicolon }
    | "+" { Plus }
    | "var" { Var }
    | "rewrite" { Rewrite }
    | "evrewrite" { EvRewrite }
    | "->" { Arrow }
    | "!=" { Inequals }
    | "=" { Equals }
    | "out" { Out }
    | "in" { In }
    | "[" { LeftB }
    | "]" { RightB }
    | "(" { LeftP }
    | ")" { RightP }
    | "." { Dot }
    | digits as n { Int(int_of_string n) }
    | letters as s { Identifier s }
    | '\n' { incr_linenum lexbuf; token lexbuf }
    | eof { EOF }
    | _ { token lexbuf }
and comment depth = parse
    | '\n' { incr_linenum lexbuf; comment depth lexbuf }
    | "/*" { comment (depth + 1) lexbuf }
    | "*/" { if depth = 1
      then token lexbuf
      else comment (depth - 1) lexbuf }
    | _ { comment depth lexbuf }
and line_comment = parse
    | '\n' { incr_linenum lexbuf; token lexbuf }
    | _ { line_comment lexbuf }
