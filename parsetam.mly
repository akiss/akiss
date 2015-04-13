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

open Term

(** [freshen sigma] replaces all variables in the range of the substitution
  * [sigma] by fresh variables. *)
let freshen (sigma : subst) =
  let varlist = vars_of_term_list (List.map snd sigma) in
  let fresh_subst =
    List.map (fun x -> (x, Var(Util.fresh_variable ()))) varlist
  in
    List.map (fun (v,t) -> v, (apply_subst t fresh_subst)) sigma

(** Translating symbol names back to Akiss conventions *)
let translate_symbol = function
  | "akisstest" -> "!test!"
  | "akissout" -> "!out!"
  | "akissin" -> "!in!"
  | s -> s

let translate_name x =
  try Scanf.sscanf x "akissn%d" (fun x -> Printf.sprintf "!n!%d" x)
  with Scanf.Scan_failure _ -> x

%}


%token Finished
%token Sharp, Greater, Less
%token Quote
%token EOF
%token Variants, Unify, Match, Norm, With, Pattern
%token Line1
%token Line2
%token Line3
%token FunDecl, EqDecl
%token <string> Identifier
%token <int> Int
%token Equals Dot Slash Comma Colon
%token LeftP RightP LeftCB RightCB
%token Zero
%token Plus

%start main

%type < [ `Variants of (Term.subst list) | `Unify of (Term.subst list) | `Match of (Term.subst list) | `Norm of Term.term ] list > main

%%

main:
 | preamble declarations resultlist EOF { $3 }

preamble:
 | Line1 Line2 Line3 { }

declarations:
 | Sharp Finished { }
 | Sharp FunDecl nesymbollist declarations { }
 | Sharp EqDecl neequationlist declarations { }


resultlist:
 | Greater Finished { [] }
 | result resultlist { $1 :: $2 }

result:
 | Greater Variants term Colon substitutionlist          {`Variants $5}
 | Greater Unify term With term substitutionlist         {`Unify $6}
 | Greater Match term With Pattern term substitutionlist {`Match $7}
 | Greater Norm term term                                {`Norm $4}

term:
 | Identifier {
     let id = translate_symbol $1 in
     if (List.mem id !private_names) || (List.mem (id,0) !fsymbols) then
       Fun(id,[])
     else
       Var id
   }
 | Quote Identifier Quote { Fun(translate_name $2, []) }
 | Identifier LeftP termlist RightP { Fun(translate_symbol $1, $3) }
 | term Plus term { Fun ("plus", [$1; $3]) }
 | LeftP term Plus term RightP { Fun("plus", [$2; $4]) }
 | Less term Comma netermlist Greater {
     let pair item = function
       | None -> Some (item)
       | Some tm -> Some (Fun("pair", [item; tm]))
     in
     match List.fold_right pair ($2::$4) None with
     | Some tm -> tm
     | None -> assert false
   }


termlist:
 | { [] }
 | netermlist { $1 }

netermlist:
 | term { [ $1 ] }
 | term Comma netermlist { $1 :: $3 }


nesymbollist:
 | symbol { [ $1 ] }
 | symbol Comma nesymbollist { $1 :: $3 }

symbol:
 | Identifier Slash Int { ($1, $3) }
 | Identifier Slash Zero { ($1, 0) }


neequationlist:
 | equation { [$1] }
 | equation Comma neequationlist { $1 :: $3 }

equation:
 | term Equals term { ($1,$3) }

substitutionlist:
 | { [] }
 | substitution substitutionlist {$1 :: $2}

substitution:
 | LeftCB assignmentlist RightCB { (freshen $2) }

assignmentlist:
 | { [] }
 | assignment {[$1]}
 | assignment Comma assignmentlist {$1 :: $3}

assignment:
 | term Slash Identifier { ($3, $1) }

%%
