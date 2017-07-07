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
open Util
open Types
open Term
open Dag
open Inputs
open Process


type predicate =
  | Knows of term * term
  | Reach
  | Identical of term * term

type body_atom = {
   loc : location option;
   recipe : term ;
   term : term ;
   marked : bool; (* for xor *)
}

(*let null_atom = {loc = None; pred= Reach;marked=false} *)

type raw_statement = {
  binder : statement_role ref;
  nbvars : int ;
  dag : dag ;
  inputs :  inputs ;
  head : predicate ;
  body : body_atom list ;
}

let null_raw_statement = { binder = ref New ; nbvars = 0; dag = empty; inputs= new_inputs; head = Reach;body=[]}

type statement = {
  id : int ;
  vip : bool ;
  st : raw_statement ;
  mutable children : statement list ;
  process : process option;
}

type base = 
{ 
   rules : rewrite_rule list ;
   mutable next_id : int ;
   mutable next_location : int ;
   mutable next_nonce : int;
   solved_deduction : statement ; 
   mutable other_solved :  statement list; 
   not_solved : statement ;
   mutable s_todo : statement list ; 
   mutable ns_todo : statement list ; 
   htable : (raw_statement, statement) Hashtbl.t;
}

(** {3 Printing} *)

let rec show_predicate p = 
(match p with
 | Knows(r,t) ->
      "knows(" ^ (show_term r) ^ "," ^ (show_term t) ^ ")"
 | Identical(r,r') ->
      "identical(" ^ (show_term r) ^ "," ^ (show_term r') ^ ")"
 | Reach -> "reach") 

let show_body_atom a =
  let l = match a.loc with Some l -> string_of_int l.p | None -> "." in
  "knows_"^l^"("^(show_term a.recipe)^","^(show_term a.term)^")"


let rec show_atom_list lst = Format.sprintf "%s" (String.concat ", " (trmap show_body_atom lst))

let show_raw_statement st =
  Format.sprintf
    "(%d%s) %s <== %s \n  %s %s\n" st.nbvars (show_binder !(st.binder)) (show_predicate st.head)(show_atom_list st.body)(show_inputs st.inputs)(show_dag st.dag)

let rec show_statement prefix st =
  (Format.sprintf "%s #%d: %s" 
    prefix st.id (show_raw_statement st.st)) 
  ^ (show_statement_list (prefix ^ "|-" ) st.children)
and show_statement_list prefix lst =
  match lst with 
  | [] -> ""
  | hd :: tl -> (show_statement prefix hd) ^ (show_statement_list prefix tl)

let rec show_statements_id stlst =
  match stlst with 
  | [] -> ""
  | [s] -> string_of_int s.id
  | s::tl -> (string_of_int s.id) ^ ", " ^ show_statements_id tl

let show_kb kb =
  (Format.sprintf 
    "Kb : \n - %d statements \n - %d locations \n - %d nonces \nSolved deduction:\n" 
    kb.next_id kb.next_location kb.next_nonce)
  ^ (show_statement_list " " (kb.solved_deduction.children))
  ^ "Other solved: \n"
  ^ (show_statement_list " " (kb.other_solved))
  ^ "Not solved: \n"
  ^ (show_statement_list " " (kb.not_solved.children))
  ^ "Todo solved: " ^ (show_statements_id kb.s_todo)
  ^ "\nTodo not solved: " ^ (show_statements_id kb.ns_todo)
  ^ "\n"

(** constructor **)
let new_statement () = {id = -1 ; vip = false ; st = null_raw_statement; children = []; process = None}

let new_base rules =
  let kb = 
  {
     rules = rules;
     next_id = 0;
     next_location = 0 ;
     next_nonce = 0 ;
     solved_deduction = new_statement () ;
     other_solved = [] ;
     not_solved = new_statement () ;
     s_todo = [] ;
     ns_todo = [] ;
     htable = Hashtbl.create 10000 ;
  } in
  kb 

(*let new_location kb channel = 
  kb.next_location <- kb.next_location + 1 ;
 { p = kb.next_location; chan=channel}
*)


        



(*
module type T = sig

  type t
  type elt

  val create : unit -> t
  val add : elt -> t -> unit

  val next_not_solved : t -> (elt*elt) option
  val next_solved : t -> (elt*elt) option

  module S : Set.S with type elt = elt

  val solved : t -> S.t
  val not_solved : t -> S.t

  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_solved : (elt -> 'a -> 'a) -> t -> 'a -> 'a

  val only_solved : t -> elt list

end

module type O = sig
  type t
  val compare : t -> t -> int
  val is_solved : t -> bool
end

module Make (M:O) : T with type elt = M.t = struct

  module S = Set.Make(M)

  type elt = M.t

  type t = {
    mutable solved : S.t ;
    mutable not_solved : S.t ;
    s_todo : (elt*elt) Queue.t ;
    ns_todo : (elt*elt) Queue.t
  }

  let create () = {
    solved = S.empty ; not_solved = S.empty ;
    s_todo = Queue.create () ; ns_todo = Queue.create ()
  }

  let new_pair queue pair = Queue.push pair queue

  let next_not_solved kb =
    try Some (Queue.pop kb.ns_todo) with Queue.Empty -> None

  let next_solved kb =
    try Some (Queue.pop kb.s_todo) with Queue.Empty -> None

  let add x kb =
    if M.is_solved x then begin
      kb.solved <- S.add x kb.solved ;
      S.iter (fun y -> new_pair kb.s_todo (x,y)) kb.solved ;
      S.iter (fun y -> new_pair kb.ns_todo (x,y)) kb.not_solved
    end else begin
      kb.not_solved <- S.add x kb.not_solved ;
      S.iter (fun y -> new_pair kb.ns_todo (y,x)) kb.solved
    end

  let fold f kb x =
    S.fold f kb.not_solved (S.fold f kb.solved x)

  let fold_solved f kb x =
    S.fold f kb.solved x

  let only_solved kb = S.elements kb.solved

  let solved kb = kb.solved
  let not_solved kb = kb.not_solved

end
*)