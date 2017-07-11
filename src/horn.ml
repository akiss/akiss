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
open Types
open Util
open Term
open Base
open Process


(** {2 Flags} *)

let use_ac =  false
let use_xor =  false

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
let drop_non_normal_skel = use_xor
let renormalize_recipes = use_xor

(** [eqrefl_opt] avoids trivial uses of equation that essentially
  * generate reflexive id(R,R) statements. It is not very useful,
  * and is not accounted for in the theory. *)
let eqrefl_opt = false

(** [opti_sort] add additionnal sorting to select the predicate *)
let opti_sort = true

(* Use of Shift rule*)
let apply_shift_rule = use_xor

(* Use of Conseq *)
let use_conseq = (not use_xor) || true

let print_flags () =
  (*assert (not use_ac || use_xor) ;*)
  if !debug_output then
    Format.printf
      "Parameters:\n\
      \  ac: %b\n\
      \  xor: %b\n\
      \  eqrefl_opt: %b\n\
      \  opti_sort: %b\n\
      \  drop non-normal skel: %b\n\
      \  renormalize_recipes: %b\n\
      \  conseq: %b\n"
      use_ac use_xor
      eqrefl_opt opti_sort drop_non_normal_skel renormalize_recipes use_conseq 

(** {2 Predicates and clauses, conversions and printing} *)

(** Possible predicates are
  *   "knows" of arity 3 (world, recipe, term);
  *   "identical" and "ridentical" of arity 3 (world, recipe, recipe);
  *   "reach" of arity 1 (world). *)


let is_deduction_st st = 
  match st.head with 
  | Knows(_,_) -> true
  | _ -> false

let is_equation_st st = 
  match st.head with
  | Identical(_, _) -> true
  | _ -> false

let is_reach_st st = 
  match st.head with
  | Reach -> true
  | _ -> false


(** A statement is solved if all its premises have a variable as their last
  * argument. *)

let is_solved st = 
  List.for_all
    (fun a -> assert (is_var a.recipe) ; is_var a.term)
    st.body

let rec vars_of_atom = function
  | Knows( r , t) -> vars_of_term_list [r;t]
  | Reach -> []
  | Identical(r1,r2) -> vars_of_term_list [r1;r2]

let get_head_recipe = function 
  | Knows( r, _) -> r
  | _ -> assert(false)


let get_recipes = function
  | Knows( r, _) -> [r]
  | Identical( r1, r2) -> [r1;r2]
  | Reach -> []

let get_term atom = atom.term

let get_head_term = function 
  | Knows(  _, t) -> t
  | _ -> assert(false)

let size st = List.length st.body

let get_id st = st.id

let get_head st = st.head

let get_body st = st.body



(** {3 Unification and substitutions} *)

(*let csu_atom a1 a2 =
  Rewriting.csu (term_from_atom a1) (term_from_atom a2)*)


let apply_subst_pred pred sigma  = 
match pred with
  | Knows(r,t) -> 
     Knows(Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term t sigma)
  | Identical(r,r') -> 
     Identical(Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term r' sigma)
  | Reach -> Reach

let apply_subst_statement st (sigma : substitution)=
  {
      binder = sigma.binder;
      nbvars = sigma.nbvars;
      dag = st.dag;
      inputs = Inputs.map (fun t -> Rewriting.apply_subst_term t sigma) st.inputs;
      head = apply_subst_pred st.head sigma ;
      body = trmap (fun x -> {x with recipe= Rewriting.apply_subst_term x.recipe sigma; term=Rewriting.apply_subst_term x.term sigma}) st.body 
  }




(*let fresh_statement f = fresh_statement ~keep_marks:true f*)

(*let dotfile =
  match Theory.dotfile with
  | Some f ->
    let dotfile = open_out f in
    Printf.fprintf dotfile "digraph G {\n" ;
    at_exit (fun () -> Printf.fprintf dotfile "}\n") ;
    Some dotfile
  | None -> None *)

(*let is_plus = function
  | Fun ("plus",_) -> true
  | _ -> false

let isnt_plus x = not (is_plus x)

let rec has_rigid = function
  | Fun ("plus",[a;b]) :: l -> has_rigid (a::b::l)
  | Fun (_,_) :: _ -> true
  | Var _ :: l -> has_rigid l
  | [] -> false

let has_rigid t = has_rigid [t]*)

(*let rec nb_flexibles n = function
  | Fun ("plus",[a;b]) :: l -> nb_flexibles n (a::b::l)
  | Fun (_,_) :: l -> nb_flexibles n l
  | Var _ :: l -> nb_flexibles (1+n) l
  | [] -> n

let nb_flexibles t = nb_flexibles 0 [t]*)

(** Create a new clause with unique clause identifier.
  * The clause will be registerd in the DOT output.
  * It would be tempting to automatically refresh the new clause,
  * although it might make logs less readable. *)
(*let new_clause =
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
      let st = { id = !c ; age ; head ; body ; ineq; vip } in
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

*)




(** {2 Knowledge base update} *)
exception TODO
let rule_rename st = (*
  let sorted_body = List.sort (fun x y -> 
   if x.loc = y.loc then 0 else 
   if Dag.is_before st.dag x.loc y.loc then 1 else -1 )
   st.body in
  let rec rule_rename atom remaining_body =
     match atom.pred with 
     | Knows (bx ,x) -> begin
       try
         let a' =  List.find (fun a -> 
         match a.pred with 
         | Knows(by,y) -> x = y) remaining_body in
         raise TODO
       with
       | Not_found -> 
         match remaining_body with
         | [] -> raise TODO
         | h::q -> rule_rename atom q
       end
     | _ -> assert(false) in
  (* We need this assertion to justify rename on identical statements.
   * It is guaranteed when we do not use conseq -- TODO cleanup for when
   * we use conseq. *)
  assert (match st.head.pred with
            | Identical(Var _,Var _) -> false
            | _ -> true) ;
  (*rule_rename atom*)*)
  st

let rule_remove st = st
  (*match st.head with
  |  Knows( _, _) ->
      let vars_to_keep = vars_of_atom st.head  in (* + world *)
      let body =
        List.filter
          (fun atom -> match atom.term with
             |  Var x ->
                 List.mem x vars_to_keep
             | _ -> true)
          st.body
      in
        { st with body = body }
  | _ -> st*)

let rule_shift st = 
  let rec variable_first t =
	match t with 
	| Fun({ id = Plus}, [Var(x); u]) -> t
	| Fun({ id = Plus} as f, [x;Var(y)]) -> Fun(f , [Var(y);x])
	| Fun({ id = Plus} as f, [x; u])-> 
		begin match variable_first u with
		| Fun({ id = Plus} as g, [Var(z); u]) -> 
              Fun( g, [Var(z); Fun(f, [x ; u])])
		| _ -> t
		end
	| _ ->  t in
  let rec get_recipe y l =
	match l with
	| [] -> assert(false)
	| { term=Var(x)} as atom ::q -> if Var(x) = y then atom.recipe else get_recipe y q
	| _ -> assert(false) in
  match st.head with
  | Knows( r , (Fun({ id = Plus} as f, [ l ; t ]) as pl)) ->
	begin match (variable_first pl) with
		| Fun({ id = Plus}, [ Var(x); t ]) -> begin 
              let stt = {st with head = Knows( Fun(f,[get_recipe (Var(x)) (st.body); r]), t)} in 
			if !debug_output 
                  then Format.printf "shift + on the statement: %s \n" (show_raw_statement stt); 
                  stt
			 end
		| _ -> st
	end
  | Knows( r , Var(x)) ->
    begin let stt = {st with head = 
      Knows(Fun({ id = Plus; has_variables = true},[get_recipe (Var(x)) (st.body); r]), 
        Fun({ id = Zero; has_variables = false},[]))} in 
      if !debug_output 
      then Format.printf "shift 0 on the statement: %s \n" (show_raw_statement stt); 
      stt
    end
  | _ -> st


(** For statements that are not canonized we still apply some simplifications
  * to avoid explosions: if a term is derived using several recipes, we can
  * remove derivations for which the recipe does not occur elsewhere in the
  * statement as long as one derivation remains. *)
let simplify_statement st =
  let hvars = vars_of_term_list (get_recipes st.head) in
  let useless,body =
    List.partition
      (fun a ->
         let recipe_var = unbox_var a.recipe in
         not (List.mem recipe_var hvars) &&
         let t = a.term in
         let l = a.loc in
           List.exists (fun a' ->
                          let recipe_var' = unbox_var a'.recipe in
                          recipe_var.n < recipe_var'.n &&
                          Dag.is_before (st.dag) l (a'.loc) &&
                          Rewriting.equals_ac t (a'.term) ) st.body)
      st.body
  in
  if !about_canonization then
    List.iter (fun a -> Format.printf "Removed %s\n" (show_body_atom a)) useless ;
  if useless = [] then st else { st with body = body }

let canonical_form statement =
  if is_deduction_st statement && is_solved statement then
    let f = if use_xor then 
        iterate rule_shift (simplify_statement statement) 
      else iterate rule_remove (iterate rule_rename statement) in
      if !about_canonization then Format.printf "Canonized: %s\n" (show_raw_statement f) ;
      f
  else
    simplify_statement statement


(** [first f l e] attempts to call [f] on each element of the list,
  * in order, and returns the result of the first call that succeeds.
  * If all calls fail, re-raise the exception raised by the last call. *)

	
(* for conseq: try all statement until one fit*)
exception Not_a_consequence
exception Bad_World
exception Bad_case

let  first kb f =
   let rec first_node st f =
     try f st.st with 
     Bad_case -> first_list st.children f  
   and first_list sts f =
     match sts with 
     | [] -> raise Bad_World
     | h::q -> begin 
        try first_node h f with
        Bad_World -> first_list q f 
     end in
   try
   first_list kb.solved_deduction.children f
   with
   | Bad_World -> raise Not_a_consequence

(** [inst_w_t my_head head_kb exc] attempts to match the world and term
  * arguments of two predicates of arity three, and raises [exc] upon
  * failure. This is used for checking if a clause is in conseq.
  * This version is not modulo AC, used for kb updates (TODO, design choice).
  * Another version, modulo AC, is used for recipizing tests.
  * TODO check that instantiations respect annotations regarding + *)
let inst_w_t my_st kb_st =
  match (my_st.head, kb_st.head) with
    | (Knows( _, myt), Knows(  _, tkb)) ->
          begin 
            (* debugOutput "Matching %s against %s\n%!" (show_term t1) (show_term t2); *)
            if not (Dag.subset kb_st.dag my_st.dag) then raise Bad_World else
            match Inputs.csm kb_st.inputs my_st.inputs with
            | sigma :: q -> begin
              try
                let (hard,sigma) = Rewriting.match_ac [] [(myt, tkb)] sigma in
              (* debugOutput "Result %s\n%!" (show_subst sigma); *)
                if hard <> [] then raise Bad_case;
                sigma
              with
              | Rewriting.Not_matchable -> raise Bad_case 
              end
            | [] -> raise Bad_World
          end
    | _ -> invalid_arg("inst_w_t "^(show_raw_statement my_st) ^(show_raw_statement kb_st))

(*let inst_w_t_ac my_head head_kb =
  match (my_head, head_kb) with
    | (Predicate(_, [myw; _; myt]), Predicate(_, [wkb; _; tkb])) ->
	let t1 = Fun("!tuple!", [myw; myt]) in
	let t2 = Fun("!tuple!", [wkb; tkb]) in
        (*extraOutput about_else "Matching %s against %s\n%!" (show_term t1) (show_term t2); *)
        R.matchers t2 t1 [] 
        (*List.iter (fun sigma -> extraOutput about_else "Result %s\n%!" (show_subst sigma)) s;*)
    | _ -> invalid_arg("inst_w_t_ac")
    *)


(** Formatter for printing conseq traces, which are essentially derivations. *)
let rec print_trace chan = function
(*  | `Public_name ->
      Format.fprintf chan "name"*)
  | `Axiom ->
      Format.fprintf chan "ax"
  | `Res (st,traces) ->
      Format.fprintf chan "#%s(%a)" (show_raw_statement st) (pp_list print_trace ",") traces

(** Check whether a statement is a consequence of a knowledge base, ie.
  * try to find solved statements deriving the same term from the same
  * assumptions.
  * Raise [Not_a_consequence] if there is no such statement.
  * If there is one, return the associated recipe. An identical statement
  * will be added to indicate that the two recipes have the same result,
  * instead of the new useless deduction statement.
  * See Definition 14 and Lemma 2 in the paper. *)
let consequence st kb rules =
  (*Printf.printf "Conseq of %s \non %s" (show_raw_statement st) (show_kb kb);*)
  let apply_subst_list_atom atom sigma  = 
   Knows(apply_subst atom.recipe sigma, apply_subst atom.term sigma) in
  assert (is_solved st) ;
  let rec aux st kb =
    match st.head with
(*      | Knows(  _ , Fun({ id=FreshName(_)} as name, [])) ->
          `Public_name, Fun(name, [])*)
      | Knows( _, t) ->
          begin try
            (* Base case: Axiom rule of conseq *)
            `Axiom, (List.find (
			fun a -> t = a.term ) st.body).recipe
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
                first kb
                  (fun x ->
                     let sigma = inst_w_t st x in
                     let subresults =
                       List.map
                         (fun y ->
                            let trace,r =
                              aux
                                {x with head=(apply_subst_list_atom y sigma) }
                                kb
                            in
                              trace, (unbox_var (y.recipe), r))
                         (x.body)
                     in
                     (* All variables occurring in the head recipe must occur
                      * in the body, so there is no need to apply [sigma] to
                      * [x], it gets done as part of applying the accumulated
                      * substitution [subst]. *)
                     let traces,subst = List.split subresults in
                     let hx_subst =
                       apply_subst (get_head_recipe (get_head x)) subst
                     in
                     (** Check that a term is a normal form. *)
                     let is_normal tm rules =
                       Rewriting.equals_ac tm (Rewriting.normalize tm rules)  in
                       if not (is_normal hx_subst rules) then
                         raise Not_a_consequence ;
                       `Res (x,traces), hx_subst)
          end
      | _ -> invalid_arg("consequence")
  in
  let trace,r = aux st kb in
    if !about_canonization then
      Format.printf "Conseq derivation for #%s: %a\n" (show_raw_statement st) print_trace trace ;
    r

(** Detect reflexive identities.
  * Note: even with the simplification of non-solved clauses, there are
  * some cases that we are missing,
  * eg. identical(C[R1],C[R2]) <-- k(R1,T), k(R2,T)
  * and variants of it with one recipe being broken in two parts, etc. *)
let is_reflexive st =
  match st.head with
    | Knows( _) -> true
    | Reach -> true
    | Identical( r, rp) ->
        if r = rp then begin
          if !debug_output then Format.printf "Clause #%s is reflexive, not useful.\n" (show_raw_statement st) ;
          false
        end else true

let normalize_identical f = f (*
  if not (use_xor && normalize_identical) then f else
    match get_head f with
      | Predicate("identical", [w;r;Fun("zero",[])])
      | Predicate("identical", [w;Fun("zero",[]);r]) ->
          { f with head = Predicate("identical", [w;r;Fun("zero",[])]) }
      | Predicate("identical", [w;r;r']) ->
          { f with head =
              Predicate("identical", [w;Fun("plus",[r;r']);Fun("zero",[])]) }
      | _ -> f
*)
(** Dealing with normalization aspects of newly deduced clauses.
  * This is called before _and_ after canonization, which may be slightly
  * inefficient but allows canonization to use structural equality rather
  * than equality modulo.
  *
  * This version of the function checks that the skeleton of the clause is
  * normal, and drops the clause otherwise. Non-normal recipes are allowed
  * and are re-normalized. *)
let normalize_new_statement rules f = Some f
(*  let process t =
    if drop_non_normal_skel then
      let t' = Rewriting.normalize t rules in
        if not (Rewriting.equals_ac t t') then begin
          (*if !debug_output then*) Format.printf "Non-normal term in clause #%d.\n" (get_id f) ;
          None
        end else
          (* Return t' rather than t because it is more canonical. *)
          Some t'
    else
      Some t
  in
  let renorm r = if renormalize_recipes then Rewriting.normalize r rules else r in
  let process = function
    | Knows,[w;r;t]) ->
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
*)
let remove_marking f = {f with body = List.map (fun a -> {a with marked = false}) f.body }

(** Update a knowledge base with a new statement. This involves canonizing
  * the statement, checking whether it already belongs to the consequences
  * of the base, and actually inserting the statement or a variant of it. *)
let update kb vip f =
  let rules = kb.rules in
  (* Do not use [is_normal], in order to replace [f] by its normalization.
   * It is equal modulo AC but will additionnally be normalized wrt some
   * order, which eases reading and gives / may give more power to non-AC
   * tests, eg. in consequence. *)
  let f = normalize_identical f in
  match normalize_new_statement rules f with
    | None -> None
    | Some f ->

  (** Freshen only now to avoid freshening the (many) non-normal clauses
    * that the procedure generates. We don't want to do it too late, though:
    * freshening should come before normalization to preserve the (weak)
    * canonical forms it provides. *)
  (*let f = fresh_statement f in*)

  match
    if use_xor then let f = canonical_form f in
      Some (if is_solved f then remove_marking f else f)
    else
      (* Canonize, normalize again and keep only normal clauses. *)
      let f = canonical_form f in
        normalize_new_statement rules f
  with None -> None | Some fc ->

  if drop_reflexive && is_reflexive fc then None else
  if is_deduction_st fc && is_solved fc && not vip && use_conseq then
    try
      let recipe = consequence fc kb rules in
      let newhead =
        Identical(get_head_recipe fc.head, recipe)
      in
      let newclause = normalize_identical { fc with head = newhead } in
        (* No need to freshen [newclause], since it has the same variables as
         * [fc] which is fresh. *)
        if !about_canonization then Format.printf 
          "Useless: %s\n Original form: %s\n Replaced by: %s\n\n%!"
          (show_raw_statement fc)(show_raw_statement f)(show_raw_statement newclause);
        if not (drop_reflexive && is_reflexive newclause) then
          Some newclause
        else None
    with Not_a_consequence ->
      (* If we ran conseq, no need to check whether the clause is already
       * in the knowledge base.
       * This optim seems incorrect with xor. TODO make sure why. *)
      Some fc
  else
    Some fc



(** {2 Resolution steps} *)

(** [resolution d_kb (master,slave)] attempts to perform a resolution step
  * between clauses [master] and [slave] by matching the head of [slave]
  * against the first premise of [master] that is of the form (knows _ _ t)
  * where t is not a variable.
  * This corresponds to the "Resolution" rule in the paper.
  * Return the list of newly generated clauses. *)
exception Impossible
(*
let resolution_plus master =
   let atom = List.find (fun x -> not (is_var (get_term x.pred))) master.body in
    (* Forbid resolution against f0+ clause if selected atom is marked. *)
   if atom.marked then [] else
	(* Do all unifications in the rule *)
	let x1 = { n = 1 ; status = ref Slave; canonized = false} in
	let x2 = { n = 2 ; status = ref Slave; canonized = false} in
	let x11 = { n = 3 ; status = ref Slave; canonized = false} in
	let x12 = { n = 4 ; status = ref Slave; canonized = false} in
	(* split a plus into a varaibles' list and a rigid factors' list *)
	let rec explode_term t =
		match t with
		| Fun({id = Plus},[l;r]) -> 
			let (v1,t1) = explode_term l in 
			let (v2,t2) = explode_term r in 
			(v1@v2,t1@t2)
		| Var(x) -> ([x],[])
		| Fun(f,l)-> ([],[Fun(f,l)]) in
	(* assume that lst contains all combination for terms except term then do all combinations with term *)
	let rec addaux term lst =
		match lst with
		| (t11,t12) :: q -> (term::t11,t12)::(t11,term::t12)::(addaux term q)
		| [] -> [] in
	(* generate all combinations *)
	let rec exponential terms sigmalist = 
		match terms with
		| t :: q ->
			addaux t (exponential q sigmalist)
		| [] -> sigmalist in
	(* Create a sum from a terms' list *)
	let rec sum_from l =
		match l with
		| [x] -> x
		| x :: m -> Fun({id = Plus; has_variables = true},[x ; (sum_from m)])
		| [] -> assert false in
	(* when the atom contains a variable, special case where the variable can be split*)
	let rec addvar x1 x2 rx x11 x12 x lst =
		let xa = fresh_variable () and xb = fresh_variable () in
		match lst with
		| (t11,t12) :: q ->
			(if t12 = [] then [] 
			else [(x11 , sum_from (Var(x)::t11)); (x12 , sum_from t12)] )
			:: (if t11 = [] then [] 
			else [(x11 , sum_from (t11)); (x12 , sum_from (Var(x)::t12))])
			:: [ (x11 , sum_from (Var(xa)::t11)); (x12 , sum_from (Var(xb)::t12));(x,Fun({id = Plus; has_variables = true},[Var(xa);Var(xb)]))]
			:: (addvar  x1 x2 rx x11 x12 x q)
		| [] -> [] in
	(* apply a substitution in our local formatting *) 
	let rec apply_subst binder x t' t =
		match t with 
		| Fun (f, args) -> Fun( f, List.map (fun t -> apply_subst binder x t' t ) args)
		| Var (x') -> if x' = x then t' else Var({n = x.n ; status = binder; canonized = false}) in
	let apply_pred binder x t' rx rt a =
		match a with
		| Knows(r,t) -> Knows(apply_subst binder rx rt r, apply_subst binder x t' t)
		| Identical(r,r') -> Identical(apply_subst binder rx rt r,apply_subst binder rx rt r')
		| Reach -> Reach in
	(* build a list of all possible cases of unification *)
	let sigmas =
		match atom.pred with 
		| Knows(Var(rx),t) ->
		(*Predicate("knows",[Var(w);Fun("plus",[Var(x1);Var(x2)]);Fun("plus",[Var(x11);Var(x12)])]))*)
			begin List.filter (fun x -> x <> []) (
			match explode_term t with
			| ([],a1::a2::l) -> List.fold_left 
				(fun statements (l1,l2) -> 
					if l1 = [] || l2 = [] 
					then statements
					else [(x11 , sum_from l1 );(x12 , sum_from l2)]::statements)
				[] (exponential (a2::l) [([a1],[])])
			| ([],l) -> []
			| ([x],a::l) -> 
				if List.mem x ( vars_of_term_list (a::l)) 
				then failwith "Unexpected term (TODO)"
				else addvar x1 x2 rx x11 x12 x (exponential l [([a],[])])
			| _ ->  failwith "loop" ) end 
		| _ -> assert(false) 
	in
      (* Create results *)
      List.map
        (fun sigma ->
           let binder = ref Slave in
           let sigma = Rewriting.process sigma in
           let result =
           {
           binder = binder ;
           nbvars = master.nbvars + 2 ; (*TODO*)
           dag = master.dag ;
           inputs = Inputs.map (fun t -> apply_pred binder ) inputs;
           head = { master.head with pred = apply_pred binder };
           body = {loc = x.loc ; marked = true ; pred = apply_pred binder }
               :: {loc = x.loc ; marked = false ; pred = apply_pred binder }
               :: (List.map (fun x -> { x with pred = apply_pred binder} )
                 (List.filter (fun x -> (x <> atom)) master.body))
           }
           in
             if !debug_output then Format.printf "RESO+: %s\n\n"
               (show_raw_statement result);
             result)
        sigmas
*)
let resolution sigma dag master slave =
   try begin
   let atom = List.find (fun x -> not (is_var ( x.term))) master.body in
   let dag =
     match (atom.loc) with
     | (Some l) -> let new_dag = Dag.merge dag (Dag.final slave.dag l) in
       (*Printf.printf "new dag %s\n" (Dag.show_dag new_dag);*)
       if Dag.is_cyclic new_dag 
       then begin (*Printf.printf "cyclic dag \n";*) raise Impossible end;
       new_dag
     | _ -> dag in
   let sigmas =
    Rewriting.csu [
      (atom.term, get_head_term slave.head);
      (atom.recipe, get_head_recipe slave.head)] sigma
    in
      (* Create results *)
    List.map
      (fun sigma ->
          let sigma = Rewriting.pack sigma in
          if !about_saturation then Printf.printf "Found: %s\n" (show_substitution sigma);
          let result =
             let body =
               List.map (fun x -> {
               loc = begin match x.loc with 
                     | None -> atom.loc
                     | Some l -> Some l end ; 
               recipe = Rewriting.apply_subst_term x.recipe sigma;
               term = Rewriting.apply_subst_term x.term sigma ;
               marked = x.marked }
                 )
                 (slave.body @
                    (List.filter (fun x -> (x <> atom)) master.body))
             in 
          {
           binder = sigma.binder ;
           nbvars = sigma.nbvars ;
           dag = dag ;
           inputs = Inputs.merge sigma master.inputs slave.inputs;
           head = (apply_subst_pred master.head sigma) ;
           body = body }
           in 
           if !about_saturation then Format.printf "RESO: %s\n\n"
               (show_raw_statement result);
           result)
        sigmas 
    end
    with Impossible -> []

(** [equation fa fb] takes two solved clauses and, when they are solved clauses
  * concluding "knows", attempts to combine them: if the terms and worlds can be
  * unified, generate a clause concluding that the recipes are "identical".
  * This corresponds to the "Equation" rule in the paper.
  * It returns [] if it fails to produce any new clause. *)
let equation sigma dag fa fb =

 (* if
    is_deduction_st fa && is_deduction_st fb &&
    (* When dealing with xor, forbid Equation if one clause is f0+. *)
    (not use_ac || not (is_plus_clause fa || is_plus_clause fb))
  then *)

    (* The rule is called only once per (unordered) pair.
     * We have to treat one clause against itself, in which case it needs
     * to be refreshed; such cases were all trivial in the original Akiss
     * but not with xor. *)
    (*let fa = if fa.id = fb.id then fresh_statement fa else fa in*)

  match fa.head, fb.head with
    | (Knows( r, t), Knows( rp, tp)) -> begin
      if !about_saturation then Format.printf "Equation:\n %s\n %s\n%!"
         (show_raw_statement fa) (show_raw_statement fb) ;
      let sigmas = Rewriting.csu [(t,tp)] sigma in
            (*let sigmas =
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
                    if !debug_output then Format.printf "Non-trivial solutions: %d\n" l' ;
                  sigmas'
              else
                sigmas
            in*)
    List.map
      (fun sigma ->
          let sigma = Rewriting.pack sigma in
          if !about_saturation then Printf.printf "Found: %s\n" (show_substitution sigma);
          let result =
             let body =
               List.map (fun x -> {
               loc =  x.loc ; 
               recipe = Rewriting.apply_subst_term x.recipe sigma ;
               term = Rewriting.apply_subst_term x.term sigma ;
               marked = false }
                 )
                 (fa.body @ fb.body) 
             in
          {
           binder = sigma.binder ;
           nbvars = sigma.nbvars ;
           dag = dag ;
           inputs = Inputs.merge sigma fa.inputs fb.inputs;
           head = Identical(Rewriting.apply_subst_term r sigma,Rewriting.apply_subst_term rp sigma);
           body = body }
           in
           if !about_saturation then Format.printf "RESO: %s\n\n"
               (show_raw_statement result);
           result)
        sigmas 
      end
          | _ -> invalid_arg("equation")

(** {2 Saturation procedure} *)


(** Core statements without variant computations *)



let rec concretize inputs term =
   match term with
   | Fun({id=Input(l)},[]) -> Inputs.get l inputs
   | Fun(f,args) -> Fun(f,List.map (concretize inputs) args)
   | _ -> term  

let expand_call kb (procId : procId) args chans=
  if !about_seed then Format.printf "Expansion of %s (%d;%d)\nwhich is %s \n%!"
     (show_procId procId)(Array.length args)(Array.length chans) (show_bounded_process procId.process);
  let location = kb.next_location in
  let nonce = kb.next_nonce in
  kb.next_location <- location + procId.nbloc ;
  kb.next_nonce <- nonce + procId.nbnonces ;
  convert_pr (procId, location, nonce, (Array.make procId.nbloc null_location),(Array.make procId.nbnonces null_nonce), args, chans) procId.process
   
let rec trace_statements kb solved_parent unsolved_parent process st =
  if !about_seed then 
    Format.printf "Computing seed statement for {%s}\n with %s \n%!"  
        (show_process process)(show_raw_statement st);
  match process with
    | EmptyP -> ()
    | ParallelP(plist) -> 
      List.iter (fun p -> trace_statements kb solved_parent unsolved_parent  p st) plist
    | SeqP(Output(loc, t), pr) ->
      let next_dag = Dag.put_at_end st.dag loc in
      let identity_sigma = Rewriting.identity_subst st.nbvars in
      let term = concretize st.inputs t in
      let binder = identity_sigma.binder in
      st.binder := Master;
      let st = apply_subst_statement st identity_sigma in
      let next_head = Knows(Fun({id= Frame(loc); has_variables = false},[]), term) in
      let st = {
        binder = binder; 
        nbvars = st.nbvars; 
        dag = next_dag;
        inputs = st.inputs;
        head = next_head;
        body = st.body} in
      let v = Rewriting.variants st.nbvars term kb.rules in
      List.iter (fun (_,sigma) -> 
        if !about_seed then Format.printf "- variant %s\n" (show_substitution sigma);
        add_statement kb solved_parent unsolved_parent (Some pr)
          (apply_subst_statement st sigma)) v
    | SeqP(Input(loc), pr) ->
      let next_dag = Dag.put_at_end st.dag loc in
      let identity_sigma = Rewriting.identity_subst st.nbvars in
      let binder = identity_sigma.binder in
      st.binder := Master;
      let st = apply_subst_statement st identity_sigma in
      let new_var = {n = st.nbvars; status = binder} in
      let next_inputs = Inputs.add_input binder loc new_var st.inputs in
      let premisse = {
        loc = Some loc; 
        recipe = Var({n = st.nbvars + 1; status = binder}) ;
        term = Var(new_var); 
        marked = false} in
      let next_body = premisse :: st.body in
      (if is_solved st 
      then add_statement kb solved_parent unsolved_parent (Some pr)
      else add_statement kb solved_parent unsolved_parent (Some pr))
       (
       {
        binder = binder; 
        nbvars = st.nbvars + 2 ; 
        dag = next_dag;
        inputs = next_inputs;
        head = Reach ;
        body = next_body}) 
    | SeqP(Test(s, t), pr) ->
      st.binder := Master;
      let sterm = concretize st.inputs s in
      let tterm = concretize st.inputs t in 
      List.iter (fun subst -> trace_statements kb solved_parent unsolved_parent pr (apply_subst_statement st subst)) (Rewriting.unifiers st.nbvars sterm tterm kb.rules)
    | SeqP(TestInequal(s, t), pr) ->
       trace_statements kb solved_parent unsolved_parent pr st
    | CallP(_, procId, args, chans) -> 
      let args = Array.map (concretize st.inputs) args in
      trace_statements kb solved_parent unsolved_parent (expand_call kb procId args chans) st
   (* | _ -> invalid_arg ("todo")*)


and add_statement kb solved_parent unsolved_parent process st = 
  if !about_saturation then Format.printf "Adding statement %s \n%!" (show_raw_statement st);
  let is_solved_st = is_solved st in
  match update kb (unsolved_parent.vip) st with
  | None -> ()
  | Some new_st -> begin
     if try ignore (Hashtbl.find kb.htable new_st);true with | Not_found -> false then () else 
     kb.next_id <- 1 + kb.next_id ;
     let st = {
       id = kb.next_id ; 
       vip = unsolved_parent.vip ;
       st = new_st ;
       children = [] ;
       process = if is_solved_st then None else process} in 
     if !about_saturation then Printf.printf "Addition of %s " (show_statement "" st);
     if is_solved_st 
     then 
         begin
         if is_deduction_st st.st 
         then begin
           kb.s_todo <- st :: kb.s_todo;
           solved_parent.children <- st :: solved_parent.children;
           match process with 
           | None -> ()
           | Some process -> trace_statements kb st unsolved_parent process st.st end
         else begin
           kb.other_solved <- st :: kb.other_solved;
           match process with 
           | None -> ()
           | Some process -> trace_statements kb solved_parent unsolved_parent process st.st end
         end 
     else begin
       kb.ns_todo <- st :: kb.ns_todo;
       unsolved_parent.children <- st :: unsolved_parent.children end
    end

let context_statements kb (f:funId) =
   let binder = ref Master in
   let rec generate_variables nb =
     if nb=0 then []
     else (Var({n=nb * 2 - 1; status = binder}),Var({n=nb * 2 - 2; status = binder}))::generate_variables (nb-1)
   in
   let variables = generate_variables f.arity in
   let rv,tv = List.split variables in
   let term_head = Fun({id=Regular(f);has_variables=true},tv) in
   let statement =
     { binder=binder; nbvars=2*f.arity; dag= Dag.empty; inputs = Inputs.new_inputs; 
       head=Knows(Fun({id=Regular(f);has_variables=true},rv),term_head);
       body=List.map (function (r,t) -> {loc=None;recipe = r; term = t; marked=false}) variables;
     } in
   let v = Rewriting.variants (2*f.arity) term_head kb.rules in
      List.iter (fun (_,sigma) -> 
        let st = apply_subst_statement statement sigma in
        let head = match st.head with
        | Knows(r,t) -> Knows(r, Rewriting.normalize t kb.rules)
        | _ -> assert false  in
        if !about_seed then Format.printf "- variant %s\n%!" (show_substitution sigma);
        add_statement kb kb.solved_deduction kb.not_solved None
        {st with head = head} ) v

let tuple_statements kb i =
   let binder = ref Master in
   let rec generate_variables nb =
     if nb=0 then []
     else (Var({n=nb * 2 - 1; status = binder}),Var({n=nb * 2 - 2; status = binder}))::generate_variables (nb-1)
   in
   let variables = generate_variables i in
   let rv,tv = List.split variables in
   let term_head = Fun({id=Tuple(i);has_variables=true},tv) in
   let statement =
     { binder=binder; nbvars=2*i; dag= Dag.empty; inputs = Inputs.new_inputs; 
       head=Knows(Fun({id=Tuple(i);has_variables=true},rv),term_head);
       body=List.map (function (r,t) -> {loc=None;recipe = r; term = t; marked=false}) variables;
     } in
   let v = Rewriting.variants (2*i) term_head kb.rules in
      List.iter (fun (_,sigma) -> 
        let st = apply_subst_statement statement sigma in
        let head = match st.head with
        | Knows(r,t) -> Knows(r, Rewriting.normalize t kb.rules)
        | _ -> assert false  in
        if !about_seed then Format.printf "- variant %s\n%!" (show_substitution sigma);
        add_statement kb kb.solved_deduction kb.not_solved None
        {st with head = head} ) v

let proj_statements kb i j=
   let binder = ref Master in
   let rec generate_variables nb =
     if nb=0 then []
     else (Var({n=nb * 2 - 1; status = binder}),Var({n=nb * 2 - 2; status = binder}))::generate_variables (nb-1)
   in
   let variables = generate_variables 1 in
   let rv,tv = List.split variables in
   let term_head = Fun({id=Projection(i,j);has_variables=true},tv) in
   let statement =
     { binder=binder; nbvars=2; dag= Dag.empty; inputs = Inputs.new_inputs; 
       head=Knows(Fun({id=Projection(i,j);has_variables=true},rv),term_head);
       body=List.map (function (r,t) -> {loc=None;recipe = r; term = t; marked=false}) variables;
     } in
   let v = Rewriting.variants (2) term_head kb.rules in
      List.iter (fun (_,sigma) -> 
        let st = apply_subst_statement statement sigma in
        let head = match st.head with
        | Knows(r,t) -> Knows(r, Rewriting.normalize t kb.rules)
        | _ -> assert false  in
        if !about_seed then Format.printf "- variant %s\n%!" (show_substitution sigma);
        add_statement kb kb.solved_deduction kb.not_solved None
        {st with head = head} ) v



let extra_resolution kb solved unsolved =
  if !about_saturation then Printf.printf "Try resolution between #%d and #%d\n" solved.id unsolved.id;
  (* Printf.printf "%s \n %s\n" (show_raw_statement solved.st) (show_raw_statement unsolved.st); *)
  let merged_dag = Dag.merge unsolved.st.dag solved.st.dag in
  if Dag.is_cyclic merged_dag then false else
  let sigma = ((Array.make unsolved.st.nbvars None),(Array.make solved.st.nbvars None)) in
  solved.st.binder:= Slave;
  unsolved.st.binder:= Master;
  let sigmas = Inputs.csu sigma solved.st.inputs unsolved.st.inputs in
  if sigmas = [] then false
  else begin 
    List.iter (fun sigma -> List.iter 
      (fun st -> add_statement kb solved unsolved unsolved.process st )
       (resolution sigma merged_dag unsolved.st solved.st)) sigmas;
    true end

let extra_equation kb solved1 solved2 =
  if !about_saturation then Printf.printf "Try equation between #%d and #%d\n" solved1.id solved2.id;
  (*Printf.printf "%s \n %s\n" (show_raw_statement solved.st) (show_raw_statement unsolved.st);*)
  let merged_dag = Dag.merge solved1.st.dag solved2.st.dag in
  if Dag.is_cyclic merged_dag then false else
  let sigma = ((Array.make solved1.st.nbvars None),(Array.make solved2.st.nbvars None)) in
  solved2.st.binder:= Slave;
  solved1.st.binder:= Master;
  let sigmas = Inputs.csu sigma solved1.st.inputs solved2.st.inputs in
  if sigmas = [] then false
  else begin 
    List.iter (fun sigma -> List.iter 
      (fun st -> add_statement kb solved1 kb.not_solved None st )
       (equation sigma merged_dag solved1.st solved2.st)) sigmas;
    true end



let rec process_resolution_new_solved kb solved unsolved =
  if unsolved.id > solved.id then () 
  else
    if extra_resolution kb solved unsolved
    then 
      List.iter (fun st -> process_resolution_new_solved kb solved st) unsolved.children

let rec process_resolution_new_unsolved kb solved unsolved =
  if unsolved.id < solved.id then () 
  else
    if extra_resolution kb solved unsolved
    then 
      List.iter (fun st -> process_resolution_new_unsolved kb st unsolved) solved.children

let rec process_equation kb new_solved old_solved =
  if old_solved.id >= new_solved.id then ()
  else
    if extra_equation kb new_solved old_solved
    then 
      List.iter (fun st -> process_equation kb new_solved st) old_solved.children


let saturate rules procId  =
  let kb = Base.new_base rules in
  List.iter (fun f -> context_statements kb f) !Parser_functions.functions_list;
  List.iter (fun i -> tuple_statements kb i; for j = 0 to i - 1 do proj_statements kb j i done ) !Parser_functions.tuple_arity;
  trace_statements kb kb.solved_deduction kb.not_solved (CallP({p = -1;io=Call;chan=null_chan;name="main"},procId,Array.make 0 zero,Array.make 0 null_chan)) null_raw_statement;
  while kb.s_todo <> [] || kb.ns_todo <> [] do
    if !about_progress then 
      begin 
      Printf.printf "%d statements to process / %d in total \n"
        ((List.length kb.s_todo)+(List.length kb.ns_todo)) kb.next_id;
      if kb.next_id mod 1000 = 0 then Printf.printf "%s\n" (show_kb kb)
      end ;
    match kb.ns_todo with
    | [] -> begin 
      match kb.s_todo with
      | [] -> assert false
      | solved :: q -> kb.s_todo <- q ;
        if !about_saturation then Printf.printf "Start equations with #%d\n" solved.id;
        List.iter (fun solved2 -> process_equation kb solved solved2) kb.solved_deduction.children;
        if !about_saturation then Printf.printf "Start resolutions with #%d\n" solved.id;
        List.iter (fun unsolved -> process_resolution_new_solved kb solved unsolved) kb.not_solved.children
      end
    | unsolved :: q -> kb.ns_todo <- q ;
      if !about_saturation then Printf.printf "Start resolutions of #%d\n" unsolved.id;
      List.iter (fun solved -> process_resolution_new_unsolved kb solved unsolved) kb.solved_deduction.children
  done ;
  Printf.printf "Saturation is done %s\n" (show_kb kb);
    
(*
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
      Format.eprintf "Trying to get %s\n out of:\n%s\n\n%!"
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
  if !debug_output then Format.printf  "Recipizing %s\n%!" (show_term tl);
  let result = recipize_h (revworld tl) kb in
  (
  if !debug_output then Format.printf  "Result %s\n%!" (show_term (revworld result));
    result
  )


(** Optimizations **)
(* Avoid tests on traces with different input output scenarios and alpha rename  tests to avoid identical ones *)

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

let rec list_find x lst =
	match lst with
	| h::q -> if x = h then List.length q else list_find x q
	| [] -> -1

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

(*let rec satisfiable lst rules =
	match lst with
	| [] -> true
	| Predicate("ineq",[w;s;t]) :: q -> 
		if R.equals s t rules then 
			begin extraOutput about_else "The predicate %s is not satisfiable.\n%!" (show_atom (Predicate("ineq",[w;s;t]))); false end
		else satisfiable q rules
	| _ -> assert false*)

(** Extract all successful reachability tests from a knowledge base. *)
let checks_reach kb rules =
	let solved = Base.only_solved kb in
	List.fold_left
    (fun checks x -> 
       match (get_head x) with
         | Predicate("reach", [w]) -> 
		(*extraOutput about_else "========> %s\n" (show_statement x);*)
		let sigma = namify_subst w in
		(*extraOutput about_else "========< %s\n" (show_subst sigma);*)
		let new_check = alpha_rename_namified_term(
			Fun ("check_run", [revworld (recipize (apply_subst w sigma) kb )])) in 
		begin             
			if !debug_output then Format.printf "TESTER: %s \n%!" (show_term new_check); 
			new_check  :: checks end 
         | _ -> checks)
    [] solved

(** Extract all successful identity tests from a knowledge base. *)
let checks_ridentical kb rules =
  Base.fold_solved
    (fun x checks -> 
       match (get_head x) with
         | Predicate("ridentical", [w; r; rp]) ->
             let sigma = namify_subst w in
             let new_w = revworld (recipize (apply_subst w sigma) kb ) in
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
             begin if !debug_output then Format.printf  "TESTER: %s\n" (show_term resulting_test) ; 
             resulting_test :: checks end 
         | _ -> checks)
    kb []
    
(** Extract all successful tests from a (saturated) knowledge base. *)
let checks kb rules =
  List.append (checks_reach kb rules) (checks_ridentical kb rules)

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

	*)
