{
  open Parsemaude
  
    let keyword_table = Hashtbl.create 20

  let _ =
    List.iter (fun (kwd,tok) -> Hashtbl.add keyword_table kwd tok)
      [
   "No" , No;
   "more" , More;
   "unifiers" , Unifiers ;
   "unifier" , Unifier ;
   "match"   , Match ;
   "get" , Get ;
   "variants" , Variants ;
   "Unifier" , Unifier ;
   "unify" , Unify ;
   "match" , Match ;
   "Variant" , Variant ;
   "variant" , Variant ;
   "reduce" , Reduce ;
   "result" , Result ;
   "in" , In ;
   "Solution" , Solution ;
   "Bool" ,Bool;
   "Term" , Term ;
   "cpu" , Cpu ;
   "real" , Real ;
   "second" , Second ;
   "true" , True;
   "false" , False;
   "Bye" , Bye;
       ]
  
  let debug = false

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
  | [' ' '\t'] { token lexbuf } (* Skip blanks *)
  | ['\n' '\r']	{ if debug then Printf.printf "\n" ; incr_linenum lexbuf; token lexbuf } (* New line *)
  | "==========================================" { Line1 }
  | "Maude>" {Maude}
  | ['#' '%'] { Sharp }
  | "rewrites: " digits " in " digits "ms cpu (" digits "ms real) ("
      (digits | "~") " rewrites/second)" { Rewritesline }
  | "Decision time: " digits "ms cpu (" digits "ms real)" { Decisiontimeline }
  | digits "ms" { Ms }
  | "0" | "zero" { Zero }
  | "-->" {Arrow}
  | "/" { Slash }
  | "+" { Plus }
  | "," { Comma }
  | ":" { Colon }
  | ">" { Greater }
  | "=" { Equals }
  | "=?" { EqualUnify }
  | "<=?" { EqualMatch }
  | "(" { if debug then Printf.printf "(";LeftP }
  | ")" { RightP }
  | "." { Dot }
  | 'w' (letters as n) {Func (n)}
  | 'x' (digits as n) {if debug then Printf.printf "x " ;Var({status = ref Types.Master; n = (int_of_string n)})}
  | 'y' (digits as n) {if debug then Printf.printf "y " ;Var({status = ref Types.Slave; n = (int_of_string n)})}
  | "nonce" (digits as n) {if debug then Printf.printf "nonce " ;Nonce (int_of_string n)}
  | "tuple" (digits as n) {if debug then Printf.printf "tuple " ;Tuple (int_of_string n)}
  | "proj" (digits as n1) "o" (digits as n2) {Proj(int_of_string n1,int_of_string n2)}
  | digits as n { Number n }
  | ['A'-'Z' 'a'-'v'] ['a'-'z' 'A'-'Z' '0'-'9']* as id
    {if debug then Printf.printf "%s " id ;
      try Hashtbl.find keyword_table id
      with Not_found ->  Identifier id
    }
  | eof { EOF }
  | _
    {
      let pos = lexbuf.Lexing.lex_curr_p in
      Printf.printf "In Maude, Line %d : Syntax Error\n" (pos.Lexing.pos_lnum);
      exit 0
    }
