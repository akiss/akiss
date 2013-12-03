%{
type tempTerm = TempTermCons of string * (tempTerm list)

type tempAction = TempActionIn of string * string
		  | TempActionOut of string * tempTerm
		  | TempActionTest of tempTerm * tempTerm

type tempProcess = TempSequence of tempProcess * tempProcess
                 | TempAction of tempAction
		 | TempInterleave of tempProcess * tempProcess
		 | TempLet of string * tempTerm * tempProcess
		 | TempEmpty
		 | TempProcessRef of string
		      
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
	    | DeclInterleave of string * (string list)
	    | DeclInterleaveOpt of string * (string list)
	    | DeclRemoveEndTests of string * (string list)
	    | DeclSequence of string * (string list)
	    | QueryEquivalent of (string list) * (string list)
	    | QueryInequivalent of (string list) * (string list)
	    | QuerySquare of (string list) * (string list)
	    | QueryEvSquare of (string list) * (string list)
	    | QueryPrint of string
	    | QueryPrintTraces of string list
(* left out of old grammer: cquery, linquery *)
%}

%token <string> Identifier
%token <int> Int
%token XOR AC
%token Symbols Private Var Rewrite EvRewrite Channels EvChannels Let
%token LeftP RightP LeftB RightB
%token Arrow Equals Dot Slash Comma Semicolon
%token Out In And Zero
%token Equivalent Inequivalent Square EvSquare
%token Print PrintTraces
%token Interleave Sequence InterleaveOpt RemoveEndTests
%token InnerSequence InnerInterleave
%token EOF

%start main

%type <cmd list> main

%%

main:
 | commandlist EOF { $1 }

commandlist:
 | { [] }
 | command Semicolon commandlist { $1 :: $3 }
     
command:
 | XOR { SetXOR }
 | Symbols symbollist { DeclSymbols $2 }
 | Private namelist { DeclPrivate $2 }
 | Channels namelist { DeclChannels $2 }
 | EvChannels namelist { DeclEvChannels $2 }
 | Var namelist { DeclVar $2 }
 | Rewrite term Arrow term { DeclRewrite ($2, $4) }
 | EvRewrite term Arrow term { DeclEvRewrite ($2, $4) }
 | Identifier Equals process { DeclProcess ($1, $3) }
 | Identifier Equals Interleave identifierList { DeclInterleave ($1, $4) }
 | Identifier Equals InterleaveOpt identifierList { DeclInterleaveOpt ($1, $4) }
 | Identifier Equals RemoveEndTests identifierList { DeclRemoveEndTests ($1, $4) }
 | Identifier Equals Sequence identifierList { DeclSequence ($1, $4) }
 | Equivalent identifierList And identifierList { QueryEquivalent ($2, $4) }
 | Inequivalent identifierList And identifierList { QueryInequivalent ($2, $4) }
 | Print Identifier { QueryPrint $2 }
 | PrintTraces identifierList { QueryPrintTraces $2 }
 | Square identifierList And identifierList { QuerySquare ($2, $4) }
 | EvSquare identifierList And identifierList { QueryEvSquare ($2, $4) }

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
 | LeftP process RightP { $2 }
 | Identifier { TempProcessRef($1) }

action:
 | In LeftP Identifier Comma Identifier RightP { TempActionIn($3, $5) }
 | Out LeftP Identifier Comma term RightP { TempActionOut($3, $5) }
 | LeftB term Equals term RightB { TempActionTest ($2, $4) }

term:
 | Identifier { TempTermCons ($1, []) }
 | Identifier LeftP termlist RightP { TempTermCons ($1, $3) }

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
