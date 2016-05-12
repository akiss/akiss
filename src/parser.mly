%{

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

open Ast

%}

%token <string> Identifier
%token <int> Int
%token XOR AC
%token Symbols Private Var Rewrite EvRewrite Channels EvChannels Let
%token PrivChannels
%token LeftP RightP LeftB RightB
%token Arrow Equals Dot Slash Comma Semicolon
%token Out In And Zero Plus
%token Not Equivalent Square EvSquare Variants Unifiers Normalize
%token Print PrintTraces
%token InnerSequence InnerInterleave InnerChoice
%token EOF

%left In
%left InnerSequence
%left InnerInterleave
%left InnerChoice
%right Dot

%start main

%type <Ast.cmd list> main

%%

main:
 | commandlist EOF { $1 }

     commandlist:
 | { [] }
 | command Semicolon commandlist { $1 :: $3 }
     
     command:
 | XOR { SetXOR }
 | AC { SetAC }
 | Symbols symbollist { DeclSymbols $2 }
 | Private namelist { DeclPrivate $2 }
 | Channels namelist { DeclChannels $2 }
 | EvChannels namelist { DeclEvChannels $2 }
 | PrivChannels namelist { DeclPrivChannels $2 }
 | Var namelist { DeclVar $2 }
 | Rewrite term Arrow term { DeclRewrite ($2, $4) }
 | EvRewrite term Arrow term { DeclEvRewrite ($2, $4) }
 | Identifier Equals process { DeclProcess ($1, $3) }
 | Print Identifier { QueryPrint $2 }
 | PrintTraces identifierList { QueryPrintTraces $2 }
 | Variants term { QueryVariants $2 }
 | Unifiers term term { QueryUnifiers ($2, $3) }
 | Normalize term { QueryNormalize $2 }     
 | negatable { QueryNegatable (true, $1) }
 | Not negatable { QueryNegatable (false, $2) }

     negatable:
 | Equivalent identifierList And identifierList { NegEquivalent ($2, $4) }
 | Square identifierList And identifierList { NegSquare ($2, $4) }
 | EvSquare identifierList And identifierList { NegEvSquare ($2, $4) }

     identifierList:
 | { [] }
 | neidentifierList { $1 }

     neidentifierList:
 | Identifier { [$1] }
 | Identifier Comma neidentifierList { $1 :: $3 }

     process:
 | Zero { TempEmpty }
 | action { TempAction($1) }
 | action Dot process { TempSequence(TempAction($1), $3) }
 | Let Identifier Equals term In process { TempLet($2, $4, $6) }
 | process InnerSequence process { TempSequence($1, $3) }
 | process InnerInterleave process { TempInterleave($1, $3) }
 | process InnerChoice process { TempChoice($1, $3) }
 | LeftP process RightP { $2 }
 | Identifier { TempProcessRef($1) }

     action:
 | In LeftP Identifier Comma Identifier RightP { TempActionIn($3, $5) }
 | Out LeftP Identifier Comma term RightP { TempActionOut($3, $5) }
 | LeftB term Equals term RightB { TempActionTest ($2, $4) }

     term:
 | Identifier { TempTermCons ($1, []) }
 | Identifier LeftP termlist RightP { TempTermCons ($1, $3) }
 | term Plus term { TempTermCons ("plus", [$1;$3]) }
 | LeftP term Plus term RightP { TempTermCons ("plus", [$2;$4]) }
 | Zero {TempTermCons ("zero",[]) } 

     termlist:
 | { [] }
 | netermlist { $1 }

     netermlist:
 | term { [ $1 ] }
 | term Comma netermlist { $1 :: $3 }

     symbollist:
 | { [] }
 | nesymbollist { $1 }

     nesymbollist:
 | symbol { [ $1 ] }
 | symbol Comma nesymbollist { $1 :: $3 }

     symbol:
 | Identifier Slash Int { ($1, $3) }
 | Identifier Slash Zero { ($1, 0) }

     namelist:
 | { [] }
 | nenamelist { $1 }

     nenamelist:
 | name { [ $1 ] }
 | name Comma nenamelist { $1 :: $3 }

     name:
 | Identifier { $1 }

%%
