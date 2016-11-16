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

(** Manipulating clauses and saturating knowledge base *)

open Util
open Term

module R = struct

  include Theory.R

  (** Quick non-unifiability test
    * to avoid costly calls to external unification procedure. *)
  let may_be_unifiable t1 t2 =
    match (t1,t2) with
      | (Fun(p,_),Fun(q,_)) when p <> q -> false
	| (Fun(_,[_;_;Fun(f,_)]),Fun(_,[_;_;Fun(g,_)])) when f<>g -> false
      | _ -> true

  let csu u v =
    let sols = if may_be_unifiable u v then unifiers u v [] else [] in
    let n = List.length sols in
      if n>0 then debugOutput "Found %d solution(s)\n" n ;
      sols

  (** If it returns true, terms must be alpha equivalent.
    * It is okay to not return true on all alpha equivalent pairs. *)
  let rough_alpha_equiv ts tt =
    (* Maude.matchers ts tt [] <> [] && Maude.matchers tt ts [] <> [] *)
    try ignore (Rewriting.mgm ts tt) ; ignore (Rewriting.mgm tt ts) ; true with
      | Rewriting.Not_matchable -> false

end

(** {2 Flags} *)

(** Drop "reflexive" statements, i.e. identical and ridentical statements
  * with two equal recipes in their head. This seems harmless but is not
  * justified in the theory. *)
let drop_reflexive = false

(** When dealing with xor, normalize i(R,R') into i(R+R',0) to avoid
  * redundancies. This seems safe but is not yet justified by the theory. *)
let normalize_identical = false

(** In the saturation algorithm with xor, we drop newly generated
  * clauses if their skeleton is not normal, and we renormalize
  * recipes. These options would probably make sense for the regular
  * procedure too. **)
let drop_non_normal_skel = Theory.xor
let renormalize_recipes = Theory.xor

(** [eqrefl_opt] avoids trivial uses of equation that essentially
  * generate reflexive id(R,R) statements. It is not very useful,
  * and is not accounted for in the theory. *)
let eqrefl_opt = false

(** [opti_sort] add additionnal sorting to select the predicate *)
let opti_sort = true

(* Use of Shift rule*)
let apply_shift_rule = Theory.xor

(* Use of Conseq *)
let use_conseq = (not Theory.xor) || true

let use_hardcoded_f0plus = Theory.xor && true

let print_flags () =
  (*assert (not Theory.ac || Theory.xor) ;*)
  if !debug_output then
    Format.printf
      "Parameters:\n\
      \  ac: %b\n\
      \  xor: %b\n\
      \  eqrefl_opt: %b\n\
      \  opti_sort: %b\n\
      \  drop non-normal skel: %b\n\
      \  renormalize_recipes: %b\n\
      \  conseq: %b\n\
      \  hard coded unification f0+: %b\n"
      Theory.ac Theory.xor
      eqrefl_opt opti_sort drop_non_normal_skel renormalize_recipes use_conseq use_hardcoded_f0plus

(** {2 Predicates and clauses, conversions and printing} *)

(* TODO
 * - using a string for predicate names isn't so great (no check
 *   on typos, uselessly costly comparison); a fixed set of variants seems
 *   appropriate, and would solve those issues
 * - the use of startswith x "!n!" to check term types is fragile;
 *   it's even worse now with P variables (and lowercase x variables).. *)

type predicateName = id

(** Possible predicates are
  *   "knows" of arity 3 (world, recipe, term);
  *   "identical" and "ridentical" of arity 3 (world, recipe, recipe);
  *   "reach" of arity 1 (world). *)
type atom =
  | Predicate of predicateName * term list

type statement = {
  id : int ;
  age : int ;
  head : atom ;
  body : atom list ;
  vip : bool
}

let is_deduction_st = function
  | {head=Predicate("knows", _)} -> true
  | _ -> false

let is_equation_st = function
  | {head=Predicate("identical", _)} -> true
  | _ -> false

let is_reach_st = function
  | {head=Predicate("reach", _)} -> true
  | _ -> false

let is_ridentical_st = function
  | {head=Predicate("ridentical", _)} -> true
  | _ -> false

(** A statement is solved if all its premises have a variable as their last
  * argument. *)
let is_solved_body body =
  List.for_all
    (function
       | Predicate("knows", [_; rx; x]) ->
           assert (is_var rx) ;
           is_var x
       | _ -> invalid_arg("is_solved"))
    body
let is_solved {body} = is_solved_body body

let rec vars_of_atom = function
  | Predicate(_, term_list) -> vars_of_term_list term_list

let rec vars_of_horn_clause {head=head;body=body} =
  unique (List.append
	    (List.concat (List.map vars_of_atom body))
            (vars_of_atom head))

let get_world = function
  | Predicate("knows", [w; _; _]) -> w
  | _ -> invalid_arg("get_world")

let get_recipe = function
  | Predicate("knows", [_; r; _]) -> r
  | _ -> invalid_arg("get_recipe")

let get_recipes = function
  | Predicate("knows", [_; r; _]) -> [r]
  | Predicate("identical", [_; r1; r2])
  | Predicate("ridentical", [_; r1; r2]) -> [r1;r2]
  | Predicate("reach",[_]) -> []
  | _ -> assert false

let get_term atom = match atom with
  | Predicate("knows", [_; _; t]) -> t
  | _ -> invalid_arg("get_term")

let size st = List.length st.body

let get_id st = st.id

let get_head st = st.head

let get_body st = st.body

(** {3 Conversions to and from terms} *)

let atom_from_term term = match term with
  | Fun(symbol, termlist) ->
      Predicate(symbol, termlist)
  | _ -> invalid_arg("atom_from_term")

let statement_from_term ~orig term = match term with
  | Fun("!tuple!", head :: body) ->
      { orig with
          head = atom_from_term head ;
          body = trmap atom_from_term body }
  | _ -> invalid_arg "statement_from_term"

let term_from_atom (Predicate(name, al)) =
  Fun(name, al)

let term_from_statement {head=head;body=body} =
  Fun("!tuple!",  (term_from_atom head) :: (trmap term_from_atom body))

(** {3 Printing} *)

let rec show_atom = function
  | Predicate("!equals!", [s;t]) ->
      (show_term s) ^ " = " ^ (show_term t)
  | Predicate(name, term_list) ->
      name ^ "(" ^ (show_term_list term_list) ^ ")"

let rec world_length = function
  | Fun ("world",[_;w]) -> 1 + world_length w
  | Fun ("empty",[]) -> 0
  | Var _ -> 0
  | _ -> raise Not_found

let rec show_atom_body = function
  | Predicate("!equals!", [s;t]) ->
      (show_term s) ^ " = " ^ (show_term t)
  | Predicate(name,[]) -> name ^ "()"
  | Predicate(name, w::term_list) ->
      try
        name ^ "(" ^ (string_of_int (world_length w) ^ "," ^
                      show_term_list term_list) ^ ")"
      with
        | Not_found ->
            name ^ "(" ^ (show_term_list (w::term_list)) ^ ")"

let show_statement st =
  Format.sprintf
    "#%d@@%d(len=%d): %s <== %s"
    st.id st.age
    (List.length st.body)
    (show_atom st.head)
    (String.concat ", " (trmap show_atom_body st.body))

(** {3 Unification and substitutions} *)

let csu_atom a1 a2 =
  R.csu (term_from_atom a1) (term_from_atom a2)

	

let csu_atom_debug dbg a1 a2 =
	let rec explode_term t =
		match t with
		| Fun("plus",[l;r]) -> let (v1,t1) = explode_term l in let (v2,t2) = explode_term r in (v1@v2,t1@t2)
		| Var(x) -> ([x],[])
		| Fun(f,l)-> ([],[Fun(f,l)]) in
	let rec exponential terms sigmalist = 
		match terms with
		| t :: q ->
			let rec addaux term lst =
				match lst with
				| (t11,t12) :: q -> (term::t11,t12)::(t11,term::t12)::(addaux term q)
				| [] -> [] in
			addaux t (exponential q sigmalist)
		| [] -> sigmalist in
	let rec sum_from l =
		match l with
		| [x] -> x
		| x :: m -> Fun("plus",[x ; (sum_from m)])
		| [] -> assert false in
	let rec addvar w world x1 x2 rx x11 x12 x lst =
		let xa = fresh_variable () and xb = fresh_variable () in
		match lst with
		| (t11,t12) :: q ->
			(if t12 = [] then [] else [(w,world);(rx, Fun("plus",[Var(x1);Var(x2)])); (x11 , sum_from (Var(x)::t11)); (x12 , sum_from t12)] )
			:: (if t11 = [] then [] else [(w,world);(rx, Fun("plus",[Var(x1);Var(x2)])); (x11 , sum_from (t11)); (x12 , sum_from (Var(x)::t12))])
			:: [(w,world);(rx, Fun("plus",[Var(x1);Var(x2)])); (x11 , sum_from (Var(xa)::t11)); (x12 , sum_from (Var(xb)::t12));(x,Fun("plus",[Var(xa);Var(xb)]))]
			:: (addvar w world x1 x2 rx x11 x12 x q)
		| [] -> [] in
	if dbg
	then begin (*debugOutput "Unification : %s = %s \n" (show_term (term_from_atom a1)) (show_term (term_from_atom a2));*)
			match (a1,a2) with 
			| (Predicate("knows",[world;Var(rx);t]),Predicate("knows",[Var(w);Fun("plus",[Var(x1);Var(x2)]);Fun("plus",[Var(x11);Var(x12)])])) -> 
				begin List.filter (fun x -> x <> []) (
				match explode_term t with
				| ([],a1::a2::l) -> List.map 
					(fun (l1,l2) -> 
						if l1 = [] || l2 = [] 
						then [] 
						else [(w,world);(rx, Fun("plus",[Var(x1);Var(x2)])); (x11 , sum_from l1 ); (x12 , sum_from l2)])
					(exponential (a2::l) [([a1],[])])
				| ([],l) -> []
				| ([x],a::l) -> 
					if List.mem x ( vars_of_term_list (a::l)) 
					then begin debugOutput "warning \n"; csu_atom  a1 a2 end
					else addvar w world x1 x2 rx x11 x12 x (exponential l [([a],[])])
				| _ ->  csu_atom a1 a2 ) end 
			| _ -> assert(false) end
	else
		csu_atom a1 a2

let apply_subst_atom atom sigma = match atom with
  | Predicate(name, term_list) ->
      Predicate(name, trmap (fun x -> apply_subst x sigma) term_list)

let apply_subst_st st sigma =
  { st with
        head = apply_subst_atom st.head sigma ;
        body = trmap (fun x -> apply_subst_atom x sigma) st.body }

let fresh_statement ~keep_marks f =
  let allv = vars_of_horn_clause f in
  let newv = trmap (fun v ->
                     if not keep_marks then Var (fresh_variable ()) else
                     if v.[0] = 'P' then Var (fresh_string "P") else
                     if v.[0] = 'Q' then Var (fresh_string "Q") else
                       Var (fresh_variable ())) allv in
  let sigma = List.combine allv newv in
    apply_subst_st f sigma

let remove_marking f =
  let f' = fresh_statement ~keep_marks:false f in
    { f' with vip = false }

let fresh_statement f = fresh_statement ~keep_marks:true f

let dotfile =
  match Theory.dotfile with
  | Some f ->
    let dotfile = open_out f in
    Printf.fprintf dotfile "digraph G {\n" ;
    at_exit (fun () -> Printf.fprintf dotfile "}\n") ;
    Some dotfile
  | None -> None

let is_plus_clause = function
  | { head = Predicate ("knows",
               [Var w;
                Fun ("plus",[Var rx; Var ry]);
                Fun ("plus",[Var x; Var y])]) ;

      body = [ Predicate("knows",[Var w1; Var r1; Var x1]) ;
               Predicate("knows",[Var w2; Var r2; Var x2]) ] }
      when (rx <> ry && x <> y) && w = w1 && w = w2 &&
           ((rx,ry) = (r1,r2) || (rx,ry) = (r2,r1)) &&
           ((x,y) = (x1,x2) || (x,y) = (x2,x1))
    -> true
  | _ -> false

let deconstruct_plus_clause = function
  | (Predicate ("knows",
                        [Var w;
                         Fun ("plus",[Var rx; Var ry]);
                         Fun ("plus",[Var x; Var y])]),
      [ Predicate("knows",[Var w'; Var r'; Var x']) ;
        Predicate("knows",[Var w''; Var r''; Var y'']) ])
      when rx <> ry && x <> y && w = w' && w = w'' &&
           ((rx = r' && ry = r'') || (rx = r'' && ry = r')) &&
           ((x = x' && y = y'') || (x = y'' && y = x'))
    ->
      Some (r',r'',x',y'')
  | _ -> None

let is_zero_clause = function
  | { head = Predicate ("knows",[_;Fun("zero",[]);Fun("zero",[])]) ;
      body = [] } -> true
  | _ -> false

let is_plus = function
  | Fun ("plus",_) -> true
  | _ -> false

let isnt_plus x = not (is_plus x)

let is_marked x =  x.[0] = 'P' || x.[0] = 'Q'

let is_dyn_marked x = x.[0] = 'P'

let rec has_rigid = function
  | Fun ("plus",[a;b]) :: l -> has_rigid (a::b::l)
  | Fun (_,_) :: _ -> true
  | Var _ :: l -> has_rigid l
  | [] -> false

let has_rigid t = has_rigid [t]

let rec nb_flexibles n = function
  | Fun ("plus",[a;b]) :: l -> nb_flexibles n (a::b::l)
  | Fun (_,_) :: l -> nb_flexibles n l
  | Var _ :: l -> nb_flexibles (1+n) l
  | [] -> n

let nb_flexibles t = nb_flexibles 0 [t]

(** Create a new clause with unique clause identifier.
  * The clause will be registerd in the DOT output.
  * It would be tempting to automatically refresh the new clause,
  * although it might make logs less readable. *)
let new_clause =
  let compare p q =
    (* We return -1 when p should occur before q in the body,
     * 1 in the opposite case and 0 when it does no matter. *)
    match p,q with
      | Predicate ("knows",[_;Var r1;t1]), Predicate ("knows",[_;Var r2;t2]) ->
		if(opti_sort) then begin
          (* Prioritize terms that pass this test *)
          let check f x1 x2 k =
            match f x1, f x2 with
              | true, true -> 0
              | true, _ -> -1
              | _, true -> 1
              | false, false -> k ()
          in
		check is_dyn_marked r1 r2 (fun () ->
              check is_var t1 t2 (fun () ->
                check isnt_plus t1 t2 (fun () ->
                 (* check has_rigid t1 t2 (fun () -> because two rigid is too much anyway*)
                    compare (nb_flexibles t1) (nb_flexibles t2))))(* ) *) end
		else
			begin
			match is_dyn_marked r1, is_dyn_marked r2 with
			| true, true -> 0
			| true, _ -> -1
			| _, true -> 1
			| false, false -> 0
		end
      | _ -> assert false
  in
  let c = ref 0 in
    fun ?(label="") ?(vip=false) ?(parents=([]:statement list)) (head,body) ->
      let body = List.sort compare body in
      let age =
        List.fold_left
          (fun age {age=a} -> max age (1+a))
          0
          parents
      in
      incr c ;
      let st = { id = !c ; age ; head ; body ; vip } in
      begin match dotfile with
      | Some dotfile ->
        Printf.fprintf dotfile
          "n%d [label=\"%s%d\" parents=%S clause=%S];\n"
          !c
          (match head with
             | Predicate ("knows",_) -> "k"
             | Predicate ("reach",_) -> "r"
             | Predicate ("identical",_) -> "i"
             | Predicate ("ridentical",_) -> "ri"
             | _ -> assert false)
          !c
          (String.concat ","
             (List.map
                (fun st ->
                   "#" ^ string_of_int st.id ^ "@" ^ string_of_int st.age)
                parents))
          (show_statement st) ;
        let parents = match parents with
          | [a;b] -> [max a b]
          | _ -> parents
        in
        List.iter
          (fun {id=id} ->
             Printf.fprintf dotfile "n%d -> n%d [color=%s];\n" id !c
               (match label with "ri" -> "red" | "eq" -> "blue" | _ -> "black"))
          parents ;
      | None -> ()
      end;
      st

(** Create anonymous/temporary statement.
  * This is currently only used in conseq. *)
let anon_statement head body =
  { id = -1 ; age = -1 ; head = head ; body = body ; vip = false }

(** Check that a term is a normal form. *)
let is_normal tm rules =
  R.equals tm (R.normalize tm rules) []

(** {3 Misc} *)

(** Statement equality for set updates
  * This is currently only modulo alpha renaming (and could be written
  * better for that). It may be made modulo AC but this seems too
  * costly.
  * TODO properly treat marked variables! *)
let same_statement s t =
  let ts = term_from_statement s in
  let tt = term_from_statement t in
    R.rough_alpha_equiv ts tt

(** [is_prefix_world w w'] checks whether [w] is a prefix of [w'],
  * assuming the two worlds come from the same statement, so that one
  * is necessarily a prefix of the other. *)
let rec is_prefix_world small_world big_world =
  match (small_world, big_world) with
  | (Fun("empty", []), _) -> true
  | (Fun("world", [h; t]), Fun("world", [hp; tp])) ->
      assert (R.equals h hp []) ;
      is_prefix_world t tp
  | (Fun("world", [_; _]), Fun("empty", [])) -> false
  | (Var(x), Var(y)) ->
      assert (x = y) ;
      true
  | _ ->
      assert false

(** {3 Knowledge bases} *)

module Statements = struct
  type t = statement
  let is_solved = is_solved
  let compare = compare
end

module Base = struct

  include Base.Make(Statements)

  exception Found

  let mem_equiv x kb =
    try
      S.iter
        (fun y ->
           if same_statement x y then begin
             debugOutput "Statement #%d already in kb: #%d.\n"
               (get_id x) (get_id y) ;
             raise Found
           end)
        (if is_solved x then solved kb else not_solved kb) ;
      false
    with Found -> true

  let add ?(needs_check=true) x _ kb =
    assert (needs_check || not (mem_equiv x kb)) ;
    if not (needs_check && mem_equiv x kb) then begin
      debugOutput "Adding clause #%d@@%d.\n" x.id x.age ;
      add x kb
    end

end

let only_knows kb = List.filter is_deduction_st kb

let only_solved kb = Base.only_solved kb

let show_kb kb =
  Base.fold (fun stmt str -> str ^ "\n" ^ show_statement stmt) kb ""

let show_kb_list kb =
  List.fold_left (fun str stmt -> str ^ "\n" ^ show_statement stmt) "" kb

(** {2 Knowledge base update} *)

let rule_rename st =
  (* We need this assertion to justify rename on identical statements.
   * It is guaranteed when we do not use conseq -- TODO cleanup for when
   * we use conseq. *)
  assert (match st.head with
            | Predicate("identical",[_;Var _;Var _]) -> false
            | _ -> true) ;
  let rec attempts = function
    | (Predicate(_, [u; Var bx; Var x]),
       Predicate(_, [uv; Var by; Var y])) :: _
      when is_prefix_world u uv && x = y && bx <> by ->
        apply_subst_st
          { st with body =
              (* Since there must be at most one atom k(_,by,_)
               * in the body, the filter should remove excatly
               * one element. This can easily be optimized. *)
              List.filter
                (function
                   | Predicate(_, [_; Var v; _]) ->
                       v <> by
                   | _ -> assert false)
                st.body }
          [(by, Var bx)]
    | _ :: options -> attempts options
    | [] -> st
  in
    attempts (combine st.body st.body)

let rule_remove = function
  | { head = Predicate("knows", _) as head } as st ->
      let vars_to_keep = vars_of_atom head in
      let body =
        List.filter
          (fun atom -> match atom with
             | Predicate(_, [_; _; Var x]) ->
                 List.mem x vars_to_keep
             | _ -> true)
          st.body
      in
        { st with body = body }
  | st -> st

let rule_shift st = 
  let rec variable_first t =
	match t with 
	| Fun("plus", [Var(x); u]) -> t
	| Fun("plus", [x;Var(y)]) -> Fun( "plus", [Var(y);x])
	| Fun("plus", [x; u])-> 
		begin match variable_first u with
		| Fun("plus", [Var(z); u]) -> Fun( "plus", [Var(z); Fun("plus", [x ; u])])
		| _ -> t
		end
	| _ ->  t in
  let rec get_recipe y l =
	match l with
	| [] -> assert(false)
	| Predicate("knows", [u;rx; Var(x)]) ::q -> if Var(x) = y then rx else get_recipe y q
	| _ -> assert(false) in
  match st.head with
  | Predicate("knows", [w; r ; Fun("plus", [ l ; t ])]) ->
	begin match (variable_first (Fun("plus", [ l ; t ]))) with
		| Fun("plus", [ Var(x); t ]) -> begin let stt = {st with head = Predicate("knows", [w; Fun("plus",[get_recipe (Var(x)) (st.body); r]); t])} in 
			debugOutput "shift + on the statement: %s \n" (show_statement stt); stt;
			 end
		| _ -> st
	end
  | Predicate("knows", [w; r ; Var(x)]) ->
	begin let stt = {st with head = Predicate("knows", [w; Fun("plus",[get_recipe (Var(x)) (st.body); r]); Fun("zero",[])])} in 
			debugOutput "shift 0 on the statement: %s \n" (show_statement stt); stt;
			 end
  | _ -> st


(** For statements that are not canonized we still apply some simplifications
  * to avoid explosions: if a term is derived using several recipes, we can
  * remove derivations for which the recipe does not occur elsewhere in the
  * statement as long as one derivation remains. *)
let simplify_statement st =
  let hvars = vars_of_term_list (get_recipes st.head) in
  let (<--) a a' =
    (* a<<-a' indicates that a can be discarded in favor of a'.
     * By default we use the standard order on strings, but we tweak
     * it so that marked and necessary variables are kept, while making
     * sure that such atoms can be used to justify dropping others. *)
    if List.mem a hvars (*|| is_marked a*) then false else
      if List.mem a' hvars (*|| is_marked a'*) then true else
        a<a'
  in
  let useless,body =
    List.partition
      (fun a ->
         let recipe_var = unbox_var (get_recipe a) in
        (* not (is_marked recipe_var) && *)
         not (List.mem recipe_var hvars) &&
         let t = get_term a in
         let l = world_length (get_world a) in
           List.exists (fun a' ->
                          recipe_var <-- unbox_var (get_recipe a') &&
                          l = world_length (get_world a') &&
                          R.equals t (get_term a') []) st.body)
      st.body
  in
    List.iter
      (fun a -> debugOutput "Removed %s\n" (show_atom a))
      useless ;
    if useless = [] then st else { st with body = body }

let canonical_form statement =
  if is_deduction_st statement && is_solved statement then
    let f = if Theory.xor then 
        iterate rule_shift (simplify_statement statement) 
      else iterate rule_remove (iterate rule_rename statement) in
      debugOutput "Canonized: %s\n" (show_statement f) ;
      f
  else
    simplify_statement statement

(* TODO AC term equality for t and tp? not if conseq stays syntactic in draft
 * not needed for worlds because we don't even need to look at their terms *)
let is_same_t_smaller_w atom1 atom2 = match (atom1, atom2) with
  | (Predicate("knows", [w; _; t]), Predicate("knows", [wp; _; tp])) ->
      (is_prefix_world wp w) && (t = tp)
  | _ -> invalid_arg("is_same_t_smaller_w")

exception Not_a_consequence

(** [first f l e] attempts to call [f] on each element of the list,
  * in order, and returns the result of the first call that succeeds.
  * If all calls fail, re-raise the exception raised by the last call. *)
let rec first f l e =
  match l with
    | [] -> raise e
    | h :: t ->
	try
	  f h
	with e -> first f t e

(** [inst_w_t my_head head_kb exc] attempts to match the world and term
  * arguments of two predicates of arity three, and raises [exc] upon
  * failure. This is used for checking if a clause is in conseq.
  * This version is not modulo AC, used for kb updates (TODO, design choice).
  * Another version, modulo AC, is used for recipizing tests.
  * TODO check that instantiations respect annotations regarding + *)
let inst_w_t my_head head_kb exc =
  match (my_head, head_kb) with
    | (Predicate(_, [myw; _; myt]), Predicate(_, [wkb; _; tkb])) ->
        let t1 = Fun("!tuple!", [myw; myt]) in
        let t2 = Fun("!tuple!", [wkb; tkb]) in
          begin try
            (* debugOutput "Matching %s against %s\n%!" (show_term t1) (show_term t2); *)
            let sigma = Rewriting.mgm t2 t1 in
              (* debugOutput "Result %s\n%!" (show_subst sigma); *)
              sigma
          with
            | Rewriting.Not_matchable -> raise exc
          end
    | _ -> invalid_arg("inst_w_t")

let inst_w_t_ac my_head head_kb =
  match (my_head, head_kb) with
    | (Predicate(_, [myw; _; myt]), Predicate(_, [wkb; _; tkb])) ->
	let t1 = Fun("!tuple!", [myw; myt]) in
	let t2 = Fun("!tuple!", [wkb; tkb]) in
        (* debugOutput "Matching %s against %s\n%!" (show_term t1) (show_term t2); *)
        R.matchers t2 t1 []
        (* debugOutput "Result %s\n%!" (show_subst sigma); *)
    | _ -> invalid_arg("inst_w_t_ac")

let rec factors = function
  | Fun ("plus",[a;b]) -> factors a @ factors b
  | x -> [x]

(** Formatter for printing conseq traces, which are essentially derivations. *)
let rec print_trace chan = function
  | `Public_name ->
      Format.fprintf chan "name"
  | `Axiom ->
      Format.fprintf chan "ax"
  | `Res (st,traces) ->
      Format.fprintf chan "#%d(%a)" st.id (pp_list print_trace ",") traces

(** Check whether a statement is a consequence of a knowledge base, ie.
  * try to find solved statements deriving the same term from the same
  * assumptions.
  * Raise [Not_a_consequence] if there is no such statement.
  * If there is one, return the associated recipe. An identical statement
  * will be added to indicate that the two recipes have the same result,
  * instead of the new useless deduction statement.
  * See Definition 14 and Lemma 2 in the paper. *)
let consequence st kb rules =
  assert (is_solved st) ;
  let rec aux { head = head ; body = body } kb =
    match head with
      | Predicate("knows", [_; _; Fun(name, [])]) when (startswith name "!n!") ->
          `Public_name, Fun(name, [])
      | Predicate("knows", [w; _; t]) ->
          begin try
            (* Base case: Axiom rule of conseq *)
            `Axiom, get_recipe (List.find (is_same_t_smaller_w head) body)
          with
            | Not_found ->
                (* Inductive case: Res rule
                 * Find a (solved, well-formed) statement [x]
                 * whose head is matched by [head] and such that
                 * [aux] succeeds on [y<-body] for each [y] in the
                 * body of [x].
                 *
                 * We need to make sure that we are not finding a conseq
                 * derivation involving non-normal clause instantiations,
                 * as they may not be proper redundancies.
                 * So we require, for each conseq step, that the head of the
                 * instantiated clause [x] is normal. *)
                first
                  (fun x ->
                     (* debugOutput "Checking %s\n%!" *)
                     (*   (show_statement (head, body)); *)
                     (* debugOutput "Against %s\n%!" *)
                     (*   (show_statement x); *)
                     let sigma = inst_w_t head (get_head x) Not_a_consequence in
                     let subresults =
                       List.map
                         (fun y ->
                            let trace,r =
                              aux
                                (anon_statement (apply_subst_atom y sigma) body)
                                kb
                            in
                              trace, (unbox_var (get_recipe y), r))
                         (get_body x)
                     in
                     (* All variables occurring in the head recipe must occur
                      * in the body, so there is no need to apply [sigma] to
                      * [x], it gets done as part of applying the accumulated
                      * substitution [subst]. *)
                     let traces,subst = List.split subresults in
                     let hx_subst =
                       apply_subst (get_recipe (get_head x)) subst
                     in
                       if not (is_normal hx_subst rules) then
                         raise Not_a_consequence ;
                       `Res (x,traces), hx_subst)
                  kb Not_a_consequence
          end
      | _ -> invalid_arg("consequence")
  in
  let trace,r = aux st (only_knows (only_solved kb)) in
    if !debug_output then
      Format.printf "Conseq derivation for #%d: %a\n" st.id print_trace trace ;
    r

(** Detect reflexive identities.
  * Note: even with the simplification of non-solved clauses, there are
  * some cases that we are missing,
  * eg. identical(C[R1],C[R2]) <-- k(R1,T), k(R2,T)
  * and variants of it with one recipe being broken in two parts, etc. *)
let is_reflexive st =
  match st.head with
    | Predicate("knows", _) -> true
    | Predicate("reach", _) -> true
    | Predicate("identical", [_; r; rp])
    | Predicate("ridentical", [_; r; rp]) ->
        if r = rp then begin
          debugOutput "Clause #%d is reflexive, not useful.\n" st.id ;
          false
        end else true
    | _ -> invalid_arg "is_reflexive"

let normalize_identical f =
  if not (Theory.xor && normalize_identical) then f else
    match get_head f with
      | Predicate("identical", [w;r;Fun("zero",[])])
      | Predicate("identical", [w;Fun("zero",[]);r]) ->
          { f with head = Predicate("identical", [w;r;Fun("zero",[])]) }
      | Predicate("identical", [w;r;r']) ->
          { f with head =
              Predicate("identical", [w;Fun("plus",[r;r']);Fun("zero",[])]) }
      | _ -> f

(** Dealing with normalization aspects of newly deduced clauses.
  * This is called before _and_ after canonization, which may be slightly
  * inefficient but allows canonization to use structural equality rather
  * than equality modulo.
  *
  * This version of the function checks that the skeleton of the clause is
  * normal, and drops the clause otherwise. Non-normal recipes are allowed
  * and are re-normalized. *)
let normalize_new_statement rules f =
  let process t =
    if drop_non_normal_skel then
      let t' = R.normalize t rules in
        if not (R.equals t t' []) then begin
          debugOutput "Non-normal term in clause #%d.\n" (get_id f) ;
          None
        end else
          (* Return t' rather than t because it is more canonical. *)
          Some t'
    else
      Some t
  in
  let renorm r = if renormalize_recipes then R.normalize r rules else r in
  let process = function
    | Predicate ("knows",[w;r;t]) ->
        begin match process t, process w with
          | Some t', Some w' -> Some (Predicate ("knows",[w';renorm r;t']))
          | None,_ | _,None -> None
        end
    | Predicate ("reach",[w]) ->
        begin match process w with
          | Some w' -> Some (Predicate ("reach",[w']))
          | None -> None
        end
    | Predicate (id,[w;r;r']) -> (* covers identical and ridentical *)
        begin match process w with
          | Some w' -> Some (Predicate (id,[w';renorm r;renorm r']))
          | None -> None
        end
    | _ -> assert false
  in
  let get_some = function
    | Some x -> x
    | None -> failwith "get_some"
  in
    try
      Some
        { f with
          head = get_some (process f.head) ;
          body = List.map (fun p -> get_some (process p)) f.body }
    with
      | Failure "get_some" -> None

(** Update a knowledge base with a new statement. This involves canonizing
  * the statement, checking whether it already belongs to the consequences
  * of the base, and actually inserting the statement or a variant of it. *)
let update (kb : Base.t) rules (f : statement) : unit =

  (* Do not use [is_normal], in order to replace [f] by its normalization.
   * It is equal modulo AC but will additionnally be normalized wrt some
   * order, which eases reading and gives / may give more power to non-AC
   * tests, eg. in consequence. *)
  let f = normalize_identical f in
  match normalize_new_statement rules f with
    | None -> ()
    | Some f ->

  let vip = f.vip in

  (** Freshen only now to avoid freshening the (many) non-normal clauses
    * that the procedure generates. We don't want to do it too late, though:
    * freshening should come before normalization to preserve the (weak)
    * canonical forms it provides. *)
  let f = fresh_statement f in

  match
    if Theory.xor then let f = canonical_form f in
      Some (if is_solved f then remove_marking f else f)
    else
      (* Canonize, normalize again and keep only normal clauses. *)
      let f = canonical_form f in
        normalize_new_statement rules f
  with None -> () | Some fc ->

  if drop_reflexive && is_reflexive fc then () else
  if is_deduction_st fc && is_solved fc && not vip && use_conseq then
    try
      let recipe = consequence fc kb rules in
      let world = get_world fc.head in
      let newhead =
        Predicate("identical", [world; get_recipe fc.head; recipe])
      in
      let newclause = normalize_identical { fc with head = newhead } in
        (* No need to freshen [newclause], since it has the same variables as
         * [fc] which is fresh. *)
        debugOutput
          "Useless: %s\n\
           Original form: %s\n\
           Replaced by: %s\n\n%!"
          (show_statement fc)
          (show_statement f)
          (show_statement newclause);
        if not (drop_reflexive && is_reflexive newclause) then
          Base.add newclause rules kb
    with Not_a_consequence ->
      (* If we ran conseq, no need to check whether the clause is already
       * in the knowledge base.
       * This optim seems incorrect with xor. TODO make sure why. *)
      Base.add ~needs_check:Theory.xor fc rules kb
  else
    Base.add fc rules kb

(** {2 Initial knowledge base}
  * Seed statements are generated in [Main] and [Process].
  * Here we only take care of creating the initial knowledge base
  * from them. *)

(** Compute the initial knowledge base K_i(S) associated to the
  * seed statements S of a ground trace T. *)
let initial_kb (seed : statement list) rules : Base.t =
  let kb = Base.create () in
  let seed =
    if not Theory.ac then seed else
      let xor_variants,seed =
        List.partition
          (fun f ->
             match get_head f with
               | Predicate("knows",[_;Fun("plus",_);_]) -> true
               | _ -> false)
          seed
      in
        List.iter
          (fun f ->
             debugOutput "Initializing kb with clause %s.\n" (show_statement f) ;
             Base.add f rules kb)
          xor_variants ;
        seed
  in
    List.iter (update kb rules) seed ;
    kb

(** {2 Resolution steps} *)

(* Adapt a substitution to mark one recipe variable as not being a plus.
 * In the case of equation, the recipe variables are not in the substitution. *)
let mark r sigma =
  let r', sigma =
    try
      match List.assoc r sigma with
        | Var r' -> r', sigma
        | _ -> assert false
    with Not_found -> r, (r, Var r) :: sigma
  in
  let r'' = Var (fresh_string "P") in
    List.map (fun (x,t) -> x, apply_subst t [r',r'']) sigma

(** Generate dynamic marking after a Resolution+ rule. *)
let generate_dynamic_marking sigmas ~t ~rx ~x ~ry ~y =

  (* Find the leftmost rigid (non-plus,non-var) subterm *)
  let rec extract_rigid variables = function
    | Fun ("plus",[x;y])::l -> extract_rigid variables (x::y::l)
    | Fun (_,_) as t :: _ -> `Some t
    | Var v :: l -> extract_rigid (v::variables) l
    | [] -> `None variables
  in

  let sigmas =
    (* Dynamic constraint generation *)

    match extract_rigid [] [t] with
      | `None variables ->
          debugOutput
            "rigid subterm: none, size %d\n"
            (List.length variables) ;
          sigmas
      | `Some t ->
          debugOutput "rigid subterm: %s\n" (show_term t) ;
          let rec occurs t = function
            | Var _ :: l -> occurs t l
            | Fun ("plus",args) :: l ->
                occurs t (List.rev_append args l)
            | t' :: l ->
                R.equals t t' [] || occurs t l
            | [] -> false
          in
          let update_sigma sigma =
            let t = apply_subst t sigma in
            let x' = List.assoc x sigma in
            let y' = List.assoc y sigma in
              if occurs t [x'] then
                (* If the rigid term is alone we are not allowed
                 * to mark, and it would not be very useful anyway. *)
                if is_plus x' then mark rx sigma else sigma
              else
                (* We must have [occurs t y'] since the original term
                 * was normal modulo xor, ie. the factor could not occur
                 * twice. *)
                if is_plus y' then mark ry sigma else sigma
          in
            List.map update_sigma sigmas
  in

    if !debug_output then begin
      Format.printf
        "final csu of size %d:\n"
        (List.length sigmas) ;
      List.iter
        (fun s -> Format.printf "* %s\n" (show_subst s))
        sigmas
    end ;
    sigmas

(** Propagate marking on a collection of unifiers. *)
let propagate_marking =
  let propagate sigma =
    let theta =
      List.map
        (function
           | (x, Var y) when x.[0] <> y.[0] ->
               let y' = Var (fresh_string (String.make 1 x.[0])) in
                 [(y,y')]
           | _ -> [])
        sigma
    in
    let theta = List.concat theta in
      List.map (fun (x,t) -> x, apply_subst t theta) sigma
  in
  fun l -> List.map propagate l

(** [resolution d_kb (master,slave)] attempts to perform a resolution step
  * between clauses [master] and [slave] by matching the head of [slave]
  * against the first premise of [master] that is of the form (knows _ _ t)
  * where t is not a variable.
  * This corresponds to the "Resolution" rule in the paper.
  * Return the list of newly generated clauses. *)
let resolution master slave =
  let atom = List.find (fun x -> not (is_var (get_term x))) master.body in

    (* Fail immediately if slave's head isn't a knows statement. *)
    if not (is_deduction_st slave) then [] else

    (* Forbid resolution against f0+ clause if selected atom is marked. *)
    if is_marked (unbox_var (get_recipe atom)) &&
       is_plus_clause slave
    then [] else
    let sigmas = csu_atom_debug (is_plus_clause slave && use_hardcoded_f0plus) atom slave.head in
    let sigmas = propagate_marking sigmas in
    let length = List.length sigmas in
    if !debug_output && length > 0 then begin
      debugOutput "Resolution?\n FROM: %s\n AND : %s\n\n"
        (show_statement master)
        (show_statement slave) ;
      Format.printf "csu of size %d:\n" length ;
      List.iter
        (fun s -> Format.printf "> %s\n" (show_subst s))
        sigmas
    end ;
    let sigmas =
      if sigmas = [] then sigmas else
        match deconstruct_plus_clause (slave.head,slave.body) with
          | None -> sigmas
          | Some (rx,ry,x,y) ->
              generate_dynamic_marking sigmas
                ~t:(get_term atom) ~rx ~x ~ry ~y
    in
    let () =
      if !debug_output && List.length sigmas < length then begin
        Format.printf "filtered csu of size %d:\n" (List.length sigmas) ;
        List.iter
          (fun s -> Format.printf "+ %s\n" (show_subst s))
          sigmas
      end
    in

      (* Create results *)
      List.map
        (fun sigma ->
           let result =
             let head = apply_subst_atom master.head sigma in
             let body =
               List.map (fun x -> apply_subst_atom x sigma)
                 (List.append
                    slave.body
                    (List.filter (fun x -> (x <> atom)) master.body))
             in
               new_clause
                 ~label:"res"
                 ~vip:master.vip
                 ~parents:[master;slave]
                 (head,body)
           in
             debugOutput "RESO: %s\n\n"
               (show_statement result);
             result)
        sigmas

(** [equation fa fb] takes two solved clauses and, when they are solved clauses
  * concluding "knows", attempts to combine them: if the terms and worlds can be
  * unified, generate a clause concluding that the recipes are "identical".
  * This corresponds to the "Equation" rule in the paper.
  * It returns [] if it fails to produce any new clause. *)
let equation fa fb =

  if
    is_deduction_st fa && is_deduction_st fb &&
    (* When dealing with xor, forbid Equation if one clause is f0+. *)
    (not Theory.ac || not (is_plus_clause fa || is_plus_clause fb))
  then

    (* The rule is called only once per (unordered) pair.
     * We have to treat one clause against itself, in which case it needs
     * to be refreshed; such cases were all trivial in the original Akiss
     * but not with xor. *)
    let fa = if fa.id = fb.id then fresh_statement fa else fa in

      match get_head fa, get_head fb with
        | (Predicate("knows", [ul; r; t]),
           Predicate("knows", [upl; rp; tp])) ->

            debugOutput "Equation:\n %s\n %s\n%!"
              (show_statement fa) (show_statement fb) ;
            let t1 = Fun("!tuple!", [t; ul]) in
            let t2 = Fun("!tuple!", [tp; upl]) in
            let sigmas = R.csu t1 t2 in
            let sigmas = propagate_marking sigmas in
            let sigmas =
              (* Performing equation on twice the same clause is useless
               * if the unifier is trivial, ie. when it is essentially a
               * renaming. In those cases the resulting identical atom is
               * an instance of reflexivity.
               * The only non trivial cases should come from the plus clause,
               * but not all of its unifiers are non-trivial. *)
              if eqrefl_opt && fa.id = fb.id then
                let nontrivial sigma =
                  let v1 = vars_of_term t1 in
                  let v2 = vars_of_term t2 in
                  let rec unique = function
                    | x::y::l ->
                        if x=y then unique (y::l) else x :: unique (y::l)
                    | l -> l
                  in
                    try
                      let assoc x sigma =
                        try List.assoc x sigma with Not_found -> Var x
                      in
                      let image v =
                        unique
                          (List.sort String.compare
                             (List.map
                                (fun x -> unbox_var (assoc x sigma))
                                v))
                      in
                      let v'1 = image v1 in
                      let v'2 = image v2 in
                        assert (List.length v1 = List.length v2) ;
                        not (List.length v'1 = List.length v1 && v'1 = v'2)
                    with Invalid_argument "unbox_var" -> true
                in
                let sigmas' = List.filter nontrivial sigmas in
                let l' = List.length sigmas' in
                  if l' < List.length sigmas then
                    debugOutput "Non-trivial solutions: %d\n" l' ;
                  sigmas'
              else
                sigmas
            in
            let newhead = Predicate("identical", [ul; r; rp]) in
            let newbody = List.append (get_body fb) (get_body fa) in
            let clauses =
              List.map
                (fun sigma ->
                   let st =
                     apply_subst_atom newhead sigma,
                     List.map (fun x -> apply_subst_atom x sigma) newbody
                   in
                     new_clause ~label:"eq" ~parents:[fa;fb] st)
                sigmas
            in
              if sigmas <> [] then
                debugOutput "Generated clauses %s.\n"
                  (String.concat ","
                     (List.map (fun st -> "#"^string_of_int st.id) clauses)) ;
              clauses

          | _ -> invalid_arg("equation")
    else
      []

(** [ridentical fa fb] attempts to combine two clauses when one
  * concludes "identical" and the other concludes "reach" and
  * their world params match.
  * This corresponds to the "Test" rule in the paper. *)
let rec ridentical fa fb =
  match fa.head, fb.head with
    | Predicate("identical", [u; r; rp]),
      Predicate("reach", [up]) ->
          assert (is_solved fa && is_solved fb) ;
          debugOutput
            "ridentical trying to combine %s with %s\n%!"
            (show_statement fa) (show_statement fb);
          if(world_length u <> world_length up || r = rp) then [] else begin
          let sigmas = R.csu u up in
            List.map
              (fun sigma ->
                 let newhead = Predicate("ridentical", [u; r; rp]) in
                 let newbody = List.append (get_body fa) (get_body fb) in
                 let result =
                   apply_subst_atom newhead sigma,
                   List.map (fun x -> apply_subst_atom x sigma) newbody
                 in
                 let result = new_clause ~label:"ri" ~parents:[fa;fb] result in
                   debugOutput "\n\nRID FROM: %s\nRID AND : %s\nRID GOT: %s\n\n%!"
                     (show_statement fa)
                     (show_statement fb)
                     (show_statement result);
                   result)
              sigmas
          end
      | Predicate("reach",_),Predicate("identical",_) -> ridentical fb fa
      | _ -> []

(** {2 Saturation procedure} *)

let saturate_step_not_solved rules kb =
  match Base.next_not_solved kb with
    | None -> false
    | Some (solved,not_solved) ->
        let new_statements = resolution not_solved solved in
          List.iter (update kb rules) new_statements ;
          true

let saturate_step_solved rules kb =
  match Base.next_solved kb with
    | None -> false
    | Some (f,g) ->
        List.iter (update kb rules) (equation f g) ;
        List.iter (update kb rules) (ridentical f g) ;
        true

let saturate kb rules =
  assert (if Theory.xor then List.mem ("zero",0) !fsymbols else true) ;
  print_flags () ;
  (* Try not_solved step, otherwise solved step, otherwise stop. *)
  while saturate_step_not_solved rules kb
     || saturate_step_solved rules kb
  do () done

(** {2 Recipe stuff} *)

let namify_subst t =
  let vars = vars_of_term t in
  let names = List.map (fun _ -> Fun(fresh_string "!n!", [])) vars in
  let sigma = List.combine vars names in
  sigma

let namify t =
  let sigma = namify_subst t in
  apply_subst t sigma

(** Using success/failure continuations for backtracking.
  * The success continuation is called on each solution of type 'a,
  * and it is passed a continuation for enumerating more solutions
  * if necessary. Eventually the failure continuation (of type cont)
  * is called to notify that there is no (more) solution. *)
type cont = unit -> unit
type 'a succ = 'a -> cont -> unit

(** [for_some l succ fail f]
  * succeeds if [f] succeeds on some element of [l]. *)
let rec for_some l (succ:'a succ) (fail:cont) f =
  match l with
    | [] -> fail ()
    | hd::tl ->
        f hd succ (fun () -> for_some tl succ fail f)

(** [for_each l succ fail f]
  * succeeds if [f] succeeds on all element of [l],
  * and it returns (through success) the list of returned solutions. *)
let for_each l (succ:'a list succ) (fail:cont) (f:'b -> 'a succ -> cont -> unit) =
  let rec aux prefix fail = function
    | [] -> succ (List.rev prefix) fail
    | hd::tl ->
        f hd (fun x k -> aux (x::prefix) k tl) fail
  in aux [] fail l

let rec find_recipe_h atom kbs (succ:term succ) (fail:cont) =
  match atom with
    | Predicate("knows", [_; _; Fun(name, [])]) when startswith name "!n!" ->
        succ (Fun(name, [])) fail
    | _ ->
        for_some kbs succ fail
          (fun clause succ fail ->
             let sigmas = inst_w_t_ac atom (get_head clause) in
               for_some sigmas succ fail
                 (fun sigma succ fail ->
                    let succ' theta k =
                      succ
                        (apply_subst (get_recipe (get_head clause)) theta)
                        k
                    in
                      for_each (get_body clause) (succ':subst succ) fail
                        (fun atom succ fail ->
                           let rvar = unbox_var (get_recipe atom) in
                           let succ recipe k = succ (rvar,recipe) k in
                             find_recipe_h (apply_subst_atom atom sigma) kbs succ fail)))

exception Recipe_found of term

let find_recipe atom kb =
  let kbsolved = (only_knows (only_solved kb)) in
    try
      find_recipe_h atom kbsolved
        (fun r _ -> raise (Recipe_found r))
        (fun () -> ()) ;
      Format.eprintf "Trying to get %s out of:\n%s\n\n%!"
        (show_atom atom)
        (show_kb_list kbsolved) ;
      assert false
    with Recipe_found r -> r

let rec revworld_h (w : term) (a : term) : term =
  match w with
    | Fun("empty", []) -> a
    | Var(_) -> Fun("world", [w; a])
    | Fun("world", [h; t]) -> revworld_h t (Fun("world", [h; a]))
    | _ -> invalid_arg("rev_worldh")

let revworld w =
  revworld_h w (Fun("empty", []))

let rec recipize_h (tl : term) kb =
  match tl with
    | Fun("empty", []) -> Fun("empty", [])
    | Fun("world", [t; w]) ->
	(
	  match t with
	    | Fun("!in!", [ch; tp]) ->
		let atom = Predicate("knows",
				      [revworld w;
				       Var(fresh_variable ()); tp]) in
		let r = find_recipe atom kb in
		Fun("world", [Fun("!in!", [ch; r]); recipize_h w kb])
	    | Fun("!out!", [ch]) ->
		Fun("world", [t; recipize_h w kb])
	    | Fun("!test!", []) ->
		Fun("world", [t; recipize_h w kb])
	    | _ -> invalid_arg("recipize_h")
	)
    | Var(_) -> invalid_arg("recipize_h with var")
    | _ -> invalid_arg("recipize_h")

let recipize tl kb =
  debugOutput "Recipizing %s\n" (show_term tl);
  let result = recipize_h (revworld tl) kb in
  (
  debugOutput "Result %s\n" (show_term (revworld result));
    result
  )


(** Opti **)
let rec list_find x lst =
	match lst with
	| h::q -> if x = h then List.length q else list_find x q
	| [] -> -1

let rec is_smaller_world small_world big_world =
  match (small_world, big_world) with
  | (Fun("empty", []),Fun("empty", []) ) -> false
  | (Fun("empty", []), _) -> true
  | (Fun("world", [h; t]), Fun("world", [hp; tp])) ->
      if (R.equals h hp []) then
      is_smaller_world t tp else false
  | (Fun("world", [_; _]), Fun("empty", [])) -> false
  | (Var(x), Var(y)) -> x = y
  | _ -> assert false

let is_smaller_reach_test t1 t2 =
	match (t1,t2) with
	| (Fun("check_run",[w1]),Fun("check_run",[w2]))->  is_smaller_world w1 w2 
	| _ -> false

let rec alpha_rename_namified_term term subst =
	match term with
	| Fun(n,[]) when startswith n "!n!" ->
		let i = list_find n subst in 
		if i = -1 
			then (Fun("!n!"^string_of_int (List.length subst),[]), n::subst) 
			else (Fun("!n!"^string_of_int (i),[]),subst)
	| Fun(f,x) -> let (y,s) = List.fold_left (fun  (l,sub) t -> 
		let (rterm,subst) = alpha_rename_namified_term t sub in  (rterm::l,subst)) ([],subst) x in
		(Fun(f,List.rev y),s)
	| Var(x) ->
		let i = list_find x subst in 
		if i = -1 
			then (Var("X"^string_of_int (List.length subst)), x::subst) 
			else (Var("X"^string_of_int (i)),subst)


let alpha_rename_namified_term term =
	let (t,_)=alpha_rename_namified_term term [] in t

(** Extract all successful reachability tests from a knowledge base. *)
let checks_reach kb =
	let solved = Base.only_solved kb in
	List.fold_left
    (fun checks x ->
       match (get_head x) with
         | Predicate("reach", [w]) ->
		let new_check = alpha_rename_namified_term(Fun ("check_run", [revworld (recipize (namify w) kb)])) in 
		begin             
			debugOutput "TESTER: %s \n" (show_term new_check); 
			new_check  :: checks end 
         | _ -> checks)
    [] solved

(** Extract all successful identity tests from a knowledge base. *)
let checks_ridentical kb =
  Base.fold_solved
    (fun x checks -> 
       match (get_head x) with
         | Predicate("ridentical", [w; r; rp]) ->
             let sigma = namify_subst w in
             let new_w = revworld (recipize (apply_subst w sigma) kb) in
             let omega =
               List.map
                 (function
                    | Predicate("knows", [_; Var(vX); Var(vx)]) ->
                        (vX, apply_subst (Var(vx)) sigma)
                    | _ -> invalid_arg("checks_ridentical"))
                 (get_body x)
             in
             let resulting_test = alpha_rename_namified_term(Fun("check_identity", [new_w;
                                                         apply_subst r omega;
                                                         apply_subst rp omega])) in
             begin debugOutput "TESTER: %s\n" (show_term resulting_test) ; 
             resulting_test :: checks end 
         | _ -> checks)
    kb []
    
(** Extract all successful tests from a (saturated) knowledge base. *)
let checks  kb =
  List.append (checks_reach kb) (checks_ridentical kb)

let show_tests tests =
  String.concat "\n" (trmap show_term tests)

let show_rew_rules rules =
  String.concat "\n" (trmap
    (
      fun x ->
	match x with
	| (l, r) -> (show_term l)^" -> "^(show_term r);
    )
    rules)

	
