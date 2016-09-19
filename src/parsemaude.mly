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
let freshensubst (sigma : subst) =
  let varlist = vars_of_term_list (List.map snd sigma) in
  let fresh_subst =
    List.map (fun x -> (x, Var(Util.fresh_variable ()))) varlist
  in
  List.map (fun (v,t) -> v, (apply_subst t fresh_subst)) sigma


let freshenvariant ((t, sigma) : (term * subst)) =
  let varlist = vars_of_term_list (t::(List.map snd sigma)) in
  let fresh_subst =
    List.map (fun x -> (x, Var(Util.fresh_variable ()))) varlist
  in
  let fs = List.map (fun (v,t) -> v, (apply_subst t fresh_subst)) sigma in
  let ft = apply_subst t fresh_subst in
  (ft, fs)

    
(** Translating symbol names back to Akiss conventions *)

let translate_symbol = function
  | "akisstest" -> "!test!"
  | "akissout" -> "!out!"
  | "akissin" -> "!in!"
  | s when Util.startswith ~prefix:"akissch" s ->
      String.sub s 7 (String.length s - 7)
  | s when Util.startswith ~prefix:"akiss" s ->
      begin try
        Scanf.sscanf s "akissw%d" (fun d -> "w" ^ string_of_int d)
      with _ ->
        try Scanf.sscanf s "akissn%d" (fun d -> "!n!" ^ string_of_int d)
        with _ -> Scanf.sscanf s "akiss%duple" (fun d -> "!tuple!")
      end
  | s -> s

let translate_name x =
  try Scanf.sscanf x "akissn%d" (fun x -> Printf.sprintf "!n!%d" x)
  with Scanf.Scan_failure _ | End_of_file -> x

%}


%token Sharp, Percent
%token EOF
%token VariantUnify, GetVariants, Reduce
%token In
%token Ms, Cpu, Real, Second
%token Unifier, Variant, Result, Solution
%token Maude, Line1
%token <string> Identifier
%token <string> Number
%token <int> Int
%token Equals, Dot, Slash, Comma, Colon, Arrow
%token EqualUnify, EqualMatch
%token LeftP RightP
%token Zero
%token Plus
%token NoUnifiers
%token NoMoreUnifiers NoMoreVariants
%token Rewritesline
%token Bool True False
%token Greater
%token Term
%token Bye



%start main

%type < [ `Variants of ( (Term.term * Term.subst) list) | `Unify of (Term.subst list) | `Match of (Term.subst list) | `Norm of Term.term | `Equal of bool ] > main

%%
main:
 | firstLine result { $2 }

     firstLine:
 | Line1 { }
 | Identifier Greater Line1 { }
 | Greater Line1 { }
     
     
     result:
 | unifierPreamble unifierList { `Unify $2 }
 | variantPreamble variantList { `Variants $2 }
 | reducePreamble Rewritesline Result resultTerm {`Norm $4 }
 | equalsPreamble Rewritesline Result Bool Colon bool { `Equal $6 }
     
     unifierPreamble:
 | VariantUnify In Identifier Colon term EqualUnify term Dot {}

     unifierList:
 | NoUnifiers Rewritesline {[]}  
 | NoMoreUnifiers Rewritesline {[]}  
 | Unifier Sharp Number Rewritesline substitution unifierList
     {(freshensubst $5)::$6}

     variantPreamble:
 | GetVariants In Identifier Colon term Dot { }

     variantList:
 | NoMoreVariants Rewritesline {[]}  
 | Variant Sharp Number Rewritesline resultTerm substitution
     variantList { freshenvariant($5,$6)::$7 }
     
     resultTerm:
 | Term Colon term { $3 }

     reducePreamble:
 | Reduce In Identifier Colon term Dot { } 

     equalsPreamble:
 | Reduce In Identifier Colon term Equals Equals term Dot { }
     
     term:
 | Identifier
     {
       let id = translate_symbol $1 in
       if (List.mem id !private_names) || (List.mem id !channels) ||
	 (List.mem (id,0) !fsymbols) || (List.mem id ["empty";"!test!"]) then
	 Fun(id,[])
       else
	 Var id
     }
 | Sharp Number Colon Term { Var ("#"^$2) } 
 | Percent Number Colon Term { Var ("%"^$2) } 
 | Identifier LeftP termlist RightP { let t = Fun(translate_symbol
						    $1,$3) in t }
 | term Plus term { Fun ("plus", [$1; $3]) }
 | LeftP term Plus term RightP { Fun("plus", [$2; $4]) }

termlist:
 | { [] }
 | netermlist {	$1 }

netermlist:
 | term { [ $1 ] }
 | term Comma netermlist { $1 :: $3 }

substitution:
 | { [] }
 | assignment substitution { $1 :: $2 }

assignment:
 | Identifier Arrow term  { ($1, $3) }

bool:
 | True  {true}     
 | False {false}     

%%
