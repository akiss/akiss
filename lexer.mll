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
               | "0" { Zero (* :: main lexbuf *) }
	       | "let" { Let (* :: main lexbuf *) }
           | "#set xor" { XOR }
           | "#set ac;"  { AC }
           | "#set ac+;" { AC }
	       | "symbols" { Symbols (* :: main lexbuf *) }
	       | "private" { Private (* :: main lexbuf *) }
	       | "channels" { Channels (* :: main lexbuf *) }
	       | "evchannels" { EvChannels (* :: main lexbuf *) }
	       | "::" { InnerSequence (* :: main lexbuf *) }
	       | "||" { InnerInterleave (* :: main lexbuf *) }
	       | "interleave" { Interleave (* :: main lexbuf *) }
	       | "interleave_opt" { InterleaveOpt (* :: main lexbuf *) }
	       | "remove_end_tests" { RemoveEndTests (* :: main lexbuf *) }
	       | "print_traces" { PrintTraces (* :: main lexbuf *) }
	       | "sequence" { Sequence (* :: main lexbuf *) }
	       | "print" { Print (* :: main lexbuf *) }
	       | "equivalentft?" { Square (* :: main lexbuf *) }
	       | "fwdequivalentft?" { EvSquare (* :: main lexbuf *) }
	       | "var" { Var (* :: main lexbuf *) }
	       | "equivalentct?" { Equivalent (* :: main lexbuf *) }
	       | "inequivalentct?" { Inequivalent (* :: main lexbuf *) }
	       | "and" { And (* :: main lexbuf *) }
	       | "/*" { comment 1 lexbuf }
	       | "//" { line_comment lexbuf (* :: main lexbuf *) }
	       | "/" { Slash (* :: main lexbuf *) }
	       | "," { Comma (* :: main lexbuf *) }
	       | ";" { Semicolon (* :: main lexbuf *) }
	       | "var" { Var (* :: main lexbuf *) }
	       | "rewrite" { Rewrite (* :: main lexbuf *) }
	       | "evrewrite" { EvRewrite (* :: main lexbuf *) }
	       | "->" { Arrow (* :: main lexbuf *) }
	       | "=" { Equals (* :: main lexbuf *) }
	       | "out" { Out (* :: main lexbuf *) }
	       | "in" { In (* :: main lexbuf *) }
	       | "[" { LeftB (* :: main lexbuf *) }
	       | "]" { RightB (* :: main lexbuf *) }
	       | "(" { LeftP (* :: main lexbuf *) }
	       | ")" { RightP (* :: main lexbuf *) }
	       | "." { Dot (* :: main lexbuf *) }
               | digits as n { Int(int_of_string n) (* :: main lexbuf *) }
	       | letters as s { Identifier s (* :: main lexbuf *) }
	       | '\n' { incr_linenum lexbuf; token lexbuf }
	       | eof { EOF (* [] *) }
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
