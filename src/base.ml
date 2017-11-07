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
  | Tests of (term * term) list

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
  choices : choices ;
  head : predicate ;
  body : body_atom list ;
  recipes : inputs ;
}

let null_raw_statement = { binder = ref New ; nbvars = 0; dag = empty; inputs= new_inputs; choices= new_choices; head = Reach;body=[];recipes=new_inputs}

type statement = {
  id : int ;
  vip : bool ;
  st : raw_statement ;
  mutable children : statement list ;
  process : process option;
  master_parent : statement;
  slave_parent : statement; 
}

let rec null_statement = { id = -2 ; vip = false ; st = null_raw_statement ; children = [] ; process = None; master_parent = null_statement; slave_parent = null_statement}

type base = 
{ 
   mutable next_id : int ;
   solved_deduction : statement ; (* to preserve structure solved_deduction link to a statement whose children are the actual ones *)
   mutable other_solved :  statement list; 
   not_solved : statement ;
   mutable s_todo : statement Queue.t ; 
   mutable ns_todo : statement Queue.t ; 
   htable : (raw_statement, statement) Hashtbl.t;
}

(** {3 Printing} *)

let rec show_predicate p = 
 match p with
 | Knows(r,t) ->
      "knows(" ^ (show_term r) ^ "," ^ (show_term t) ^ ")"
 | Identical(r,r') ->
      "identical(" ^ (show_term r) ^ "," ^ (show_term r') ^ ")"
 | Reach -> "reach"
 | Tests(l) -> (List.fold_left ( fun str (r,r') -> (if str = "" then "" else str ^ ", ") ^ (show_term r) ^ "=" ^ (show_term r') ) "tests(" l ) ^")"

let show_body_atom a =
  let l = match a.loc with Some l -> string_of_int l.p | None -> "." in
  "knows_"^l^"("^(show_term a.recipe)^","^(show_term a.term)^")"


let rec show_atom_list lst = Format.sprintf "%s" (String.concat ", " (trmap show_body_atom lst))

let show_raw_statement st =
  Format.sprintf
    "(%d%s) %s <== %s \n       %s %s\n       %s\n" st.nbvars (show_binder !(st.binder)) (show_predicate st.head)(show_atom_list st.body)(show_inputs st.inputs)(show_dag st.dag)(show_inputs st.recipes)

let rec show_statement prefix st =
  (Format.sprintf "%s #%d[%d;%d]: %s" 
    prefix st.id (st.master_parent.id)(st.slave_parent.id)(show_raw_statement st.st)) 
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

let rec count_statements st =
  List.fold_left (fun c st -> c + (count_statements st)) 1 st.children

let show_kb kb =
  (Format.sprintf 
    "Kb : \n - %d statements \n - %d solved deduction \n - %d solved identical\n Solved deduction:\n" 
    kb.next_id (count_statements kb.solved_deduction)(List.length kb.other_solved))
  ^ (show_statement_list " " (kb.solved_deduction.children))
  ^ "Other solved: \n"
  ^ (show_statement_list " " (kb.other_solved))
  ^ "Not solved: \n"
  ^ (show_statement_list " " (kb.not_solved.children))
(*  ^ "Todo solved: " ^ (show_statements_id kb.s_todo)
  ^ "\nTodo not solved: " ^ (show_statements_id kb.ns_todo)*)
  ^ "\n"

(** constructor **)
let new_statement () = {id = -1 ; vip = false ; st = null_raw_statement; children = []; process = None; master_parent = null_statement; slave_parent = null_statement }

let new_base () =
  let kb = 
  {
     next_id = 0;
     solved_deduction = new_statement () ;
     other_solved = [] ;
     not_solved = new_statement () ;
     s_todo = Queue.create () ;
     ns_todo = Queue.create() ;
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
