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
