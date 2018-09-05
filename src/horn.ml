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
  | Tests(_) -> assert false
  | Unreachable -> []

let get_head_recipe = function 
  | Knows( r, _) -> r
  | _ -> assert(false)

let get_term atom = atom.term

let get_head_term = function 
  | Knows(  _, t) -> t
  | _ -> assert(false)

let size st = List.length st.body

let get_id st = st.id

let get_head st = st.head

let get_body st = st.body

let compare_loc_opt l1 l2 =
  match l1,l2 with
  | None , Some l1 -> 1
  | Some l1,Some l2 -> Pervasives.compare l1.p l2.p
  | Some _ , None -> -1
  | None, None -> 0

(** {3 Unification and substitutions} *)

(*let csu_atom a1 a2 =
  Rewriting.csu (term_from_atom a1) (term_from_atom a2)*)





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
  | Knows( r , Var(x)) -> st (* (*Bugguy when no xor*)
    begin let stt = {st with head = 
      Knows(Fun({ id = Plus; has_variables = true},[get_recipe (Var(x)) (st.body); r]), 
        Fun({ id = Zero; has_variables = false},[]))} in 
      if !debug_output 
      then Format.printf "shift 0 on the statement: %s \n" (show_raw_statement stt); 
      stt
    end *)
  | _ -> st


(** For statements that are not canonized we still apply some simplifications
  * to avoid explosions: if a term is derived using several recipes, we can
  * remove derivations for which the recipe does not occur elsewhere in the
  * statement as long as one derivation remains. *)
let simplify_statement st =
  (*let hvars = vars_of_atom st.head (*vars_of_term_list (get_recipes st.head)*) in
  st.binder := Master;
  let master_final = Array.make (st.nbvars) None in
  let binder = ref New in
  let nbv = ref 0 in
  let (useless,body) =
    List.partition
      (fun a ->
        let recipe_var = unbox_var a.recipe in
        List.iter (fun (x : varId) -> 
          if master_final.(x.n) = None
          then (master_final.(x.n) <- Some(Var({n = !nbv ; status = binder})) ;incr nbv);
        ) (vars_of_term a.term);
        let t = a.term in
        try
        let smallest_recipe =  List.fold_left 
           (fun best current -> 
              if not (Rewriting.equals_ac t current.term)
              then best
              else
              let recipe_current = Term.unbox_var current.recipe in
              let recipe_best = Term.unbox_var best.recipe in
              if recipe_best.n > recipe_current.n 
              then current else best 
           ) a st.body in
        let smallest_recipe_var = Term.unbox_var smallest_recipe.recipe in 
        if master_final.(smallest_recipe_var.n) = None
        then
          (master_final.(smallest_recipe_var.n) <- Some(Var({n = !nbv ; status = binder})) ;incr nbv);
        if smallest_recipe != a 
        then 
          master_final.(recipe_var.n) <- master_final.(smallest_recipe_var.n);
         (* sigma_repl.(recipe_var.n) <- Some smallest_recipe.recipe ;*)
        List.exists (fun a' -> 
              if a'.term <> t
              then false
              else Dag.can_be_replaced_by st.dag a.loc a'.loc) st.body 
         with Not_found -> false
         )
       (List.sort (fun x y -> Pervasives.compare (x.loc,(Term.unbox_var x.recipe).n) (y.loc,(Term.unbox_var y.recipe).n)) st.body)
  in
  let body = List.sort_uniq (fun x y -> Pervasives.compare (x.loc,(Term.unbox_var x.recipe).n) (y.loc,(Term.unbox_var y.recipe).n)) body in
  if t then
    List.iter (fun a -> Format.printf "Removed %s\n" (show_body_atom a)) useless ;
(*  if useless = [] then st 
  else *)
  let sigma = { 
    binder = binder; 
    master =  Array.map get_opt master_final;
    slave = Array.make 0 zero;(* Array.map get_opt slave_final;*)
    nbvars = !nbv;
  } in
  let r = apply_subst_statement { st with body = body; } sigma in
   Printf.printf "result: %s\n" (show_raw_statement r); 
  (*st.binder := New;*)
  r*)
  
  try 
  let hvars = vars_of_atom st.head (*vars_of_term_list (get_recipes st.head)*) in
  (*Printf.printf "simplification of %s\n" (show_raw_statement st);*)
  let sigma_repl = Array.make st.nbvars None in
  st.binder := Master;
  let binder = ref New in
  let nbv = ref 0 in
  let (useless,body) =
    List.partition
      (fun a ->
        List.iter (fun (x : varId) -> 
          if sigma_repl.(x.n) = None
          then (sigma_repl.(x.n) <- Some(Var({n = !nbv ; status = binder})) ;incr nbv);
        ) (vars_of_term a.term);
        let recipe_var = unbox_var a.recipe in
        if sigma_repl.(recipe_var.n) = None then (
           sigma_repl.(recipe_var.n) <- Some(Var({n = !nbv ; status = binder})) ;incr nbv);
        not (List.mem recipe_var hvars) &&
        let t = a.term in
        let l = a.loc in
        match List.find_opt 
            (fun a' ->
              let recipe_var' = unbox_var a'.recipe in
              (( recipe_var.n < recipe_var'.n && l = a'.loc)
                  || Dag.should_be_before (st.dag) (a'.loc) l)
                  && Rewriting.equals_ac t (a'.term) ) st.body with
        | Some is_better ->
          let better = (unbox_var is_better.recipe).n in
          if !about_canonization then
              Printf.printf "Atom %s removed due to %s\n" (show_body_atom a) (show_body_atom is_better);
          if sigma_repl.(better) = None then 
            sigma_repl.(better) <- sigma_repl.(recipe_var.n)
          else 
            (sigma_repl.(recipe_var.n) <- sigma_repl.(better); decr nbv); 
          true
         | None -> false
         )
       (List.sort (fun x y -> compare_loc_opt x.loc y.loc) st.body)
  in
  let sigma = { 
    binder = binder; 
    master =  Array.map (function Some x -> x | None -> zero) sigma_repl;
    slave = Array.make 0 zero;
    nbvars = !nbv;
  } in
  let r = apply_subst_statement { st with body = body; } sigma in
  (* Printf.printf "result: %s\n" (show_raw_statement r); *)
  (*st.binder := New;*)
  r
  with 
    Invalid_argument _ -> 
      Printf.eprintf "Error when simplify_statement %s \n" (show_raw_statement st);exit 6 
  (*if !about_canonization then
    List.iter (fun a -> Format.printf "Simplify statement removes %s\n" (show_body_atom a)) useless ;*)
  (*if useless = [] then st 
  else 
    let sigma = Rewriting.pack sigma in
    apply_subst_statement { st with body = body;} sigma*)
    
    

let canonical_form statement =
  if is_deduction_st statement && is_solved statement then
    let f = if true || use_xor then 
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
      (* Printf.printf "T%d " st.id; *)
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
            if not (Dag.subset kb_st.dag my_st.dag) || not (Inputs.subset_choices kb_st.choices my_st.choices)
            then begin (*Printf.printf "@";*) raise Bad_World end else
            match Inputs.csm kb_st.inputs my_st.inputs with
            | sigma :: q -> begin
              try
                let (hard,sigma) = Rewriting.match_ac [] [(tkb, myt)] sigma in
              (* debugOutput "Result %s\n%!" (show_subst sigma); *)
                if hard <> [] then raise Bad_case; (*warning: not possible to find recipes *)
                sigma
              with
              | Rewriting.Not_matchable -> (*Printf.printf "-";*) raise Bad_case 
              end
            | [] -> (*Printf.printf "&";*) raise Bad_World
          end
    | _ -> invalid_arg("inst_w_t "^(show_raw_statement my_st) ^(show_raw_statement kb_st))

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
  if !about_canonization then Printf.printf "Conseq of %s" (show_raw_statement st) ;
  (*st.binder := Rule;*)
  let apply_subst_list_atom atom sigma  = 
   Knows(apply_subst atom.recipe sigma, apply_subst atom.term sigma) in
  assert (is_solved st) ;
  let rec aux st kb =
    (*Printf.printf "___%s\n" (show_raw_statement st);*)
    (*st.binder := New;*)
    match st.head with
(*      | Knows(  _ , Fun({ id=FreshName(_)} as name, [])) ->
          `Public_name, Fun(name, [])*)
      | Knows( _, t) ->
          begin try
            (* Base case: Axiom rule of conseq *)
            `Axiom, (List.find (fun a -> t = a.term ) st.body).recipe
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
                    (*Printf.printf "\nst: %s\n sigma = %s\n" (show_raw_statement x)(show_subst sigma); *)
                     let subresults =
                       List.map
                         (fun y ->
                            let trace,r =
                              aux
                                {st with head=(apply_subst_list_atom y sigma) }
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
      Format.printf "Kb %s\nConseq derivation for #%s:\nrecipe %s\ntrace %a\n" (show_kb kb)(show_raw_statement st) (show_term r) print_trace trace ;
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
    | Unreachable -> true
    | Identical( r, rp) ->
        if r = rp then begin
          if !debug_output then Format.printf "Clause #%s is reflexive, not useful.\n" (show_raw_statement st) ;
          false
        end else true
    | Tests(_) -> assert false

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
let normalize_new_statement f = (* This opti slow down the algo a bit much*)
  if not (Inputs.are_normal f.inputs) 
  then begin (*Printf.printf "input: %s\n" (show_raw_statement f);*) None end
  else
  if not (List.for_all 
    (fun a -> let t' = Rewriting.normalize a.term (!Parser_functions.rewrite_rules) in Rewriting.equals_ac a.term t')
    f.body)
  then begin (*Printf.printf "terms: %s\n" (show_raw_statement f);*) None end
  else 
  match f.head with 
  | Reach -> Some f
  | Unreachable -> Some f
  | Knows(r,t) -> 
    let t' = Rewriting.normalize t (!Parser_functions.rewrite_rules) in 
    if not (Rewriting.equals_ac t t')
    then begin (*Printf.printf "hea: %s\n" (show_raw_statement f); *)
      None (*Some {f with head = Reach}*) end (* A knows is also a reach statement but the reach statement has already been processed *)
    else Some {f with head = Knows(Rewriting.normalize r (!Parser_functions.rewrite_rules),t)}
  | Identical(r,r') -> Some {f with 
      head = Identical(Rewriting.normalize r (!Parser_functions.rewrite_rules),
            Rewriting.normalize r' (!Parser_functions.rewrite_rules))}
  | Tests(_) -> assert false (*Some {f with 
      head = Tests(EqualitiesSet.map (fun (r,r') -> Rewriting.normalize r (!Parser_functions.rewrite_rules),
            Rewriting.normalize r' (!Parser_functions.rewrite_rules))equal,
            EqualitiesSet.map (fun (r,r') -> Rewriting.normalize r (!Parser_functions.rewrite_rules),
            Rewriting.normalize r' (!Parser_functions.rewrite_rules))diseq) }*) (* this case is not used *)



let remove_marking f = {f with body = List.map (fun a -> {a with marked = false}) f.body }

(** Update a knowledge base with a new statement. This involves canonizing
  * the statement, checking whether it already belongs to the consequences
  * of the base, and actually inserting the statement or a variant of it. *)
let update kb vip f =
  let rules = ! Parser_functions.rewrite_rules in
  (* Do not use [is_normal], in order to replace [f] by its normalization.
   * It is equal modulo AC but will additionnally be normalized wrt some
   * order, which eases reading and gives / may give more power to non-AC
   * tests, eg. in consequence. *)
  let f = normalize_identical f in
  (* A bit expensive to do twice: there is no that many non normal statement*)
  (*match normalize_new_statement f with
    | None ->  None
    | Some f ->*)
  match
    if use_xor then let f = canonical_form f in
      Some (if is_solved f then remove_marking f else f)
    else
      (* Canonize, normalize again and keep only normal clauses. *)
      let f = canonical_form f in
        normalize_new_statement f
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
let is_tuple term =
  match term with
  | Fun ({id = Tuple _},_) -> true
  | _ -> false

let resolution sigma choices dag master slave =
   try begin
   let atom = List.find (fun x -> not (is_var ( x.term))) master.body in
   if atom.loc != None && is_tuple atom.term && not (is_tuple (get_head_recipe slave.head)) then [] else 
   let dag =
     match (atom.loc) with
     | (Some l) -> let new_dag = Dag.merge dag (Dag.final slave.dag l) in
       (*Printf.printf "new dag %s\n" (Dag.show_dag new_dag);*)
       if Dag.is_cyclic new_dag 
       then begin (*Printf.printf "cyclic dag \n";*) raise Dag.Impossible end;
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
          if !debug_saturation then Printf.printf "Found: %s\n" (show_substitution sigma);
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
           choices = choices ;
           inputs = Inputs.merge sigma master.inputs slave.inputs;
           recipes = Inputs.merge(*_recipes*) sigma master.recipes slave.recipes;
           head = (apply_subst_pred master.head sigma) ;
           body = body ;
           involved_copies = BangSet.union master.involved_copies slave.involved_copies ; }
           in 
           if !debug_saturation then Format.printf "RESO: %s\n\n"
               (show_raw_statement result);
           result)
        sigmas 
    end
    with Dag.Impossible -> []

(** [equation fa fb] takes two solved clauses and, when they are solved clauses
  * concluding "knows", attempts to combine them: if the terms and worlds can be
  * unified, generate a clause concluding that the recipes are "identical".
  * This corresponds to the "Equation" rule in the paper.
  * It returns [] if it fails to produce any new clause. *)
let equation sigma choices dag fa fb =

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
      if !debug_saturation then Format.printf "Equation:\n %s\n %s\n%!"
         (show_raw_statement fa) (show_raw_statement fb) ;
      if (Rewriting.equals_ac r rp) then [] else
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
          if !debug_saturation then Printf.printf "Found: %s\n" (show_substitution sigma);
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
           choices = choices ;
           inputs = Inputs.merge sigma fa.inputs fb.inputs;
           recipes = Inputs.merge(*_recipes*) sigma fa.recipes fb.recipes;
           head = Identical(Rewriting.apply_subst_term r sigma,Rewriting.apply_subst_term rp sigma);
           body = body ;
           involved_copies = BangSet.union fa.involved_copies fb.involved_copies ; }
           in
           if !debug_saturation then Format.printf "RESO: %s\n\n"
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


 
let rec hidden_chan_statement kb  (loc_input , term_input ,ineq_input,st_input,pr_input) (loc_output,  term_output,ineq_output,st_output,pr_output) solved_parent unsolved_parent test_parent  =
  match term_input,term_output with
  | None, Some term_output -> (
  match Inputs.merge_choices_add_link st_output.choices st_input.choices loc_output loc_input with
    None -> ()
  | Some choices ->
  let dag = Dag.merge st_output.dag st_input.dag in
  if Dag.is_cyclic dag then () 
  else (
  st_input.binder := Slave;
  st_output.binder := Master;
  if !about_seed then Printf.printf "Computing hiden_chan_statement\n -link %d <-> %d\n -input %s \n -output %s\n%!" loc_input.p loc_output.p (show_raw_statement st_input)(show_raw_statement st_output);
  if st_input.binder = st_output.binder then (
    (*Printf.printf "same statement %s and %s\n" (show_raw_statement st_input)(show_raw_statement st_output);*)
    let sig_id = Rewriting.identity_subst st_output.nbvars in
    let st = apply_subst_statement { st_output with choices = choices ; dag = dag } sig_id in
    let ineqs = (ineq_output @  ineq_input) in
    trace_statements kb ineqs solved_parent unsolved_parent test_parent pr_output st ;
    let process_input = Process.apply_subst_process loc_input term_output pr_input in
    (*Printf.printf "subst %d by %s process : %s\n" loc_input.p (show_term term_output) (show_process_start 3 process_input);*)
    trace_statements kb ineqs solved_parent unsolved_parent test_parent process_input st 
  )
  else
  let sigma = ((Array.make st_output.nbvars None),(Array.make st_input.nbvars None)) in
   (*Printf.printf "Computing hiden_chan_statement\n -link %d <-> %d\n" loc_input.p loc_output.p;*)
  let sigmas = Inputs.csu sigma st_output.inputs st_input.inputs in
  if sigmas = [] then ()
  else (
  let dag = Dag.put_at_end (Dag.put_at_end dag loc_input) loc_output in
  List.iter (fun sigma -> 
    let sigma = Rewriting.pack sigma in
    (*Printf.printf "subst %s\n" (show_substitution sigma);*)
    let st =
      let body =
        List.map (fun x -> {
        loc =  x.loc ; 
        recipe = Rewriting.apply_subst_term x.recipe sigma ;
        term = Rewriting.apply_subst_term x.term sigma ;
        marked = false }
          )
          (st_output.body @ st_input.body) 
        in
      {
      binder = sigma.binder ;
      nbvars = sigma.nbvars ;
      dag = dag ;
      choices = choices ;
      inputs = Inputs.merge sigma st_output.inputs st_input.inputs;
      recipes = Inputs.merge sigma st_output.recipes st_input.recipes;
      head = Reach;
      body = body ;
      involved_copies = BangSet.union st_output.involved_copies st_input.involved_copies ; }
    in
    let ineqs = List.map (fun (s,t) -> (Rewriting.apply_subst_term s sigma,Rewriting.apply_subst_term t sigma)) (ineq_output @  ineq_input) in
    trace_statements kb ineqs solved_parent unsolved_parent test_parent pr_output st ;
    let process_input = Process.apply_subst_process loc_input term_output pr_input in
    (*Printf.printf "subst %d by %s process : %s\n" loc_input.p (show_term term_output) (show_process_start 3 process_input);*)
    trace_statements kb ineqs solved_parent unsolved_parent test_parent process_input st 
  ) sigmas ))
  )
  | _ -> assert false
 
and trace_statements kb ineqs solved_parent unsolved_parent test_parent process st =
  let rec add_ineqs_statements ineqs idsigma st =
  match ineqs with
  | [] -> ()
  | (s,t)::q -> 
    let st = apply_subst_statement {st with head = Unreachable} idsigma in
    st.binder := Master;
    let sterm = concretize st.inputs s in
    let tterm = concretize st.inputs t in 
    let unifiers = Rewriting.unifiers st.nbvars sterm tterm (! Parser_functions.rewrite_rules) in 
      List.iter (fun subst -> add_statement kb solved_parent unsolved_parent test_parent None (apply_subst_statement st subst)) unifiers
  in
  if !about_seed then 
    Format.printf "Computing seed statement for {%s}\n with %s \n%!"  
        (show_process process)(show_raw_statement st);
  match process with
    | EmptyP -> ()
    | ParallelP(plist) -> 
      List.iter (fun p -> trace_statements kb ineqs solved_parent unsolved_parent test_parent p st) plist
    | ChoiceP(l,plist) -> 
      List.iter (fun (i,p) -> 
        let choices = Inputs.add_choice l i st.choices in
        let st = {st with choices = choices} in
        trace_statements kb ineqs solved_parent unsolved_parent test_parent p st) plist
    | SeqP(OutputA(loc, t), pr) -> (* the reach statement has been solved, computing variants *)
      (*let next_dag = Dag.put_at_end st.dag loc in*)
      let identity_sigma = Rewriting.identity_subst st.nbvars in
      let term = Rewriting.normalize (concretize st.inputs t) (! Parser_functions.rewrite_rules)in
      let binder = identity_sigma.binder in
      st.binder := Master;
      let st = apply_subst_statement st identity_sigma in
      let next_head = Knows(Fun({id= Frame(loc); has_variables = false},[]), term) in
      let st = { st with
        binder = binder; 
        head = next_head;
        } in
      let v = Rewriting.variants st.nbvars term (! Parser_functions.rewrite_rules) in
      List.iter (fun (_,sigma) -> 
        if !about_seed then Format.printf "- variant for output: %s\n" (show_substitution sigma);
        let new_st = apply_subst_statement st sigma in
        let new_head = match new_st.head with Knows(r,t) -> Knows(r,Rewriting.normalize t !Parser_functions.rewrite_rules) | _ -> assert false in
        add_statement kb solved_parent unsolved_parent test_parent (Some EmptyP)
          ({new_st with head = new_head})) v 
     | SeqP(Output({observable = Public} as loc, t), pr) -> (* the reach part of the output *)
      let next_dag = Dag.put_at_end st.dag loc in
      let identity_sigma = Rewriting.identity_subst st.nbvars in
      let binder = identity_sigma.binder in
      st.binder := Master;
      let st = apply_subst_statement st identity_sigma in
      let st = { st with
        binder = binder; 
        dag = next_dag ;
        head = Reach;
        } in
      begin 
      add_ineqs_statements ineqs identity_sigma st ;
      add_statement kb solved_parent unsolved_parent test_parent (Some (ParallelP([SeqP(OutputA(loc, t), pr);pr]))) st
      end
    | SeqP(Input({observable = Public} as loc), pr) -> 
      let next_dag = Dag.put_at_end st.dag loc in
      let identity_sigma = Rewriting.identity_subst (st.nbvars + 2) in
      let binder = identity_sigma.binder in
      st.binder := Master;
      let st = apply_subst_statement st identity_sigma in
      let new_var = {n = st.nbvars - 2; status = binder} in
      let new_recipe = {n = st.nbvars - 1; status = binder} in
      let next_inputs = Inputs.add_input loc new_var st.inputs in
      let next_recipes = Inputs.add_input loc new_recipe st.recipes in
      let premisse = {
        loc = Some loc; 
        recipe = Var(new_recipe) ;
        term = Var(new_var); 
        marked = false} in
      let next_body = premisse :: st.body in
      let st = {
        binder = binder; 
        nbvars = st.nbvars; 
        dag = next_dag;
        choices = st.choices ;
        inputs = next_inputs;
        recipes = next_recipes;
        head = Reach ;
        body = next_body;
        involved_copies = st.involved_copies} in
      begin
      add_ineqs_statements ineqs identity_sigma st ;
      add_statement kb solved_parent unsolved_parent test_parent (Some pr) st end
    | SeqP(Input({io = Input({visibility = Hidden} as chan)} as loc), pr) -> (
      match ChanMap.find_opt { c= chan; io = Out; ph =loc.phase} kb.hidden_chans with
      | None -> ()
      | Some chans -> 
        List.iter (fun stout -> 
          hidden_chan_statement kb (loc,None,ineqs,st,pr) stout solved_parent unsolved_parent test_parent) chans);
      kb.hidden_chans <- ChanMap.add { c = chan; io = In; ph = loc.phase} 
        ((loc,None,ineqs,st,pr):: ( try 
          ChanMap.find { c= chan; io = In; ph =loc.phase} kb.hidden_chans 
          with Not_found -> []))
        kb.hidden_chans 
    | SeqP(Output({io = Output({visibility = Hidden} as chan)} as loc, t), pr) -> (
      match ChanMap.find_opt { c= chan; io = In; ph =loc.phase} kb.hidden_chans with
      | None -> ()
      | Some chans -> 
        List.iter (fun stin -> 
          hidden_chan_statement kb stin (loc,Some t,ineqs,st,pr) solved_parent unsolved_parent test_parent) chans);
      kb.hidden_chans <- ChanMap.add { c = chan; io = Out; ph = loc.phase} 
        ((loc,Some t,ineqs,st,pr):: ( try 
          ChanMap.find { c= chan; io = Out; ph =loc.phase} kb.hidden_chans 
          with Not_found -> []))
        kb.hidden_chans 
    | SeqP(Input(loc), pr)
    | SeqP(Output(loc,_), pr) ->
      assert false
    | SeqP(Test(s, t), pr) ->
      st.binder := Master;
      let sterm = concretize st.inputs s in
      let tterm = concretize st.inputs t in 
      (*Printf.printf "comparing %s == %s\n" (show_term sterm) (show_term tterm);*)
      let unifiers = Rewriting.unifiers st.nbvars sterm tterm (! Parser_functions.rewrite_rules) in 
      List.iter (fun subst -> trace_statements kb ineqs solved_parent unsolved_parent test_parent pr (apply_subst_statement st subst)) unifiers
    | SeqP(TestInequal(s, t), pr) ->
      (*Printf.printf "inequal %s %s\n" (show_term s)(show_term t);*)
      if s <> t then 
       trace_statements kb ((s,t)::ineqs) solved_parent unsolved_parent test_parent pr st
    | CallP(loc, j, procId, args, chans) -> 
      (*let args = Array.map (concretize st.inputs) args in*)
      for i = 1 to j do
      (*Format.printf "Adding %d-th copy of %s \n%!" i procId.name;*)
      let pr = expand_call loc i procId args chans in
      trace_statements kb ineqs solved_parent unsolved_parent test_parent pr {st with involved_copies = BangSet.add (loc,i) st.involved_copies}
      done
   (* | _ -> invalid_arg ("todo")*)


and add_statement kb solved_parent unsolved_parent test_parent process st = 
  if !debug_saturation then Format.printf "Adding statement %s \n%!" (show_raw_statement st);
  let is_solved_st = is_solved st in
  match update kb (unsolved_parent.vip) st with
  | None -> ()
  | Some new_st -> begin 
     let new_st = canonize_statement new_st in
     let hash_st = raw_to_hash_statement new_st in
     new_st.binder:=if is_solved_st then Slave else Master;
     if Hashtbl.mem kb.htable hash_st then () else begin 
     kb.next_id <- 1 + kb.next_id ;
     let st = {
       id = kb.next_id ; 
       vip = unsolved_parent.vip ;
       st = new_st ;
       children = [] ;
       process = if is_solved_st then None else process ;
       master_parent = unsolved_parent;
       slave_parent = solved_parent;
       test_parent = test_parent;
       } in 
     (if !debug_saturation 
     then Printf.printf "Addition of %s \n unsolved: %s solved: %s test: %s process: %s\n\n %!" 
      (show_statement "" st)(show_raw_statement unsolved_parent.st)(show_raw_statement solved_parent.st)(show_raw_statement test_parent.st)
      (match process with None -> "none" | Some pr -> show_process_start 3 pr)
     else if !about_progress && kb.next_id mod 500 = 0 then Printf.printf "Addition of %s \n%!" (show_statement "" st));
     Hashtbl.add kb.htable hash_st st;
     if is_solved_st 
     then 
         begin
         match st.st.head with
         | Knows(_) -> 
           begin
           Queue.add st kb.s_todo;
           solved_parent.children <- st :: solved_parent.children;
           match process with 
           | None -> ()
           | Some process -> trace_statements kb [] st unsolved_parent test_parent process st.st end
         | Unreachable -> kb.unreachable_solved <- st :: kb.unreachable_solved
         | Reach
         | Identical(_,_) -> begin
            test_parent.children <- st :: test_parent.children;
            match process with 
           | None -> ()
           | Some process -> trace_statements kb [] solved_parent unsolved_parent st process st.st end
         | Tests(_) -> assert false
        (* begin
           kb.reachable_solved <- st :: kb.reachable_solved;
           match process with 
           | None -> ()
           | Some process -> trace_statements kb [] solved_parent unsolved_parent process st.st end
         | Identical(_,_) -> begin
           kb.identity_solved <- st :: kb.identity_solved;
           match process with 
           | None -> ()
           | Some process -> trace_statements kb [] solved_parent unsolved_parent process st.st end*)
         end 
     else begin
       Queue.add st kb.ns_todo;
       unsolved_parent.children <- st :: unsolved_parent.children end
    end
   end

let theory_statements kb fname arity =
   let binder = ref Master in
   let rec generate_variables nb =
     if nb=0 then []
     else (Var({n=nb * 2 - 1; status = binder}),Var({n=nb * 2 - 2; status = binder}))::generate_variables (nb-1)
   in
   let variables = generate_variables arity in
   let rv,tv = List.split variables in
   let term_head = Fun({id=fname;has_variables=true},tv) in
   let statement =
     { 
       binder = binder; 
       nbvars = 2*arity; 
       dag = Dag.empty; 
       choices = Inputs.new_choices; 
       inputs = Inputs.new_inputs; 
       recipes = Inputs.new_inputs; 
       head=Knows(Fun({id=fname;has_variables=true},rv),term_head);
       body=List.map (function (r,t) -> {loc=None;recipe = r; term = t; marked=false}) variables;
       involved_copies = BangSet.empty;
     } in
   let v = Rewriting.variants (2*arity) term_head (! Parser_functions.rewrite_rules) in
      List.iter (fun (_,sigma) -> 
        let st = apply_subst_statement statement sigma in
        let head = match st.head with
        | Knows(r,t) -> Knows(r, Rewriting.normalize t (! Parser_functions.rewrite_rules))
        | _ -> assert false  in
        if !about_seed then Format.printf "- variant for theory  of %s %s\n%!" (show_term (Fun({id=fname;has_variables=true},[]))) (show_substitution sigma);
        add_statement kb kb.solved_deduction kb.not_solved kb.rid_solved None
        {st with head = head} ) v


let extra_resolution kb solved unsolved =
  if !debug_saturation then Printf.printf "Try resolution between #%d and #%d\n%!" solved.id unsolved.id;
  (* Printf.printf "%s \n %s\n" (show_raw_statement solved.st) (show_raw_statement unsolved.st); *)
  match Inputs.merge_choices unsolved.st.choices solved.st.choices with
    None -> false
  | Some merged_choice ->
  let merged_dag = Dag.merge unsolved.st.dag solved.st.dag in
  if Dag.is_cyclic merged_dag then false else
  let sigma = ((Array.make unsolved.st.nbvars None),(Array.make solved.st.nbvars None)) in
  solved.st.binder:= Slave;
  unsolved.st.binder:= Master;
  let sigmas = Inputs.csu sigma solved.st.inputs unsolved.st.inputs in
  if sigmas = [] then false
  else begin 
    List.iter (fun sigma -> List.iter 
      (fun st -> add_statement kb solved unsolved (if unsolved.test_parent == kb.rid_solved then solved.test_parent else unsolved.test_parent) unsolved.process st )
       (resolution sigma merged_choice merged_dag unsolved.st solved.st)) sigmas;
    true end

let extra_equation kb solved1 solved2 =
  if !debug_saturation then Printf.printf "Try equation between #%d and #%d\n%!" solved1.id solved2.id;
  (*Printf.printf "%s \n %s\n" (show_raw_statement solved.st) (show_raw_statement unsolved.st);*)
  match Inputs.merge_choices solved1.st.choices solved2.st.choices with
    None -> false
  | Some merged_choice ->
  let merged_dag = Dag.merge solved1.st.dag solved2.st.dag in
  if Dag.is_cyclic merged_dag then false else
  let sigma = ((Array.make solved1.st.nbvars None),(Array.make solved2.st.nbvars None)) in
  solved2.st.binder:= Slave;
  solved1.st.binder:= Master;
  let sigmas = Inputs.csu sigma solved1.st.inputs solved2.st.inputs in
  if sigmas = [] then false
  else begin 
    List.iter (fun sigma -> List.iter 
      (fun st -> add_statement kb solved1 kb.not_solved 
          (if solved1.test_parent == kb.rid_solved then solved2.test_parent else solved1.test_parent )  
        None st )
       (equation sigma merged_choice merged_dag solved1.st solved2.st)) sigmas; (*TODO :  duplicate sigma to handle several unifiers *)
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


let saturate procId  =
  let kb = Base.new_base () in
  List.iter (fun f -> theory_statements kb (Regular(f)) f.arity) !Parser_functions.functions_list;
  List.iter (fun i -> theory_statements kb (Tuple(i)) i; for j = 0 to i - 1 do theory_statements kb (Projection(j,i)) 1 done ) !Parser_functions.tuple_arity;
  let ind = processes_infos.next_location in
  processes_infos.next_location <- processes_infos.next_location + 1 ;
  trace_statements kb [] kb.solved_deduction kb.not_solved kb.rid_solved
    (CallP(root_location ind,1,procId,Array.make 0 zero,Array.make 0 null_chan))
    null_raw_statement;
  while not (Queue.is_empty(kb.s_todo)) || not (Queue.is_empty(kb.ns_todo)) do
    if false && !about_progress then 
      begin 
      Printf.printf "%d statements to process / %d in total \n"
        ((Queue.length kb.s_todo)+(Queue.length kb.ns_todo)) kb.next_id
      end ;
    if (Queue.is_empty(kb.ns_todo)) then
      begin 
        let solved =  Queue.take(kb.s_todo) in
        if !debug_saturation then Printf.printf "Start equations with #%d\n" solved.id;
        List.iter (fun solved2 -> process_equation kb solved solved2) kb.solved_deduction.children;
        if !debug_saturation then Printf.printf "Start resolutions with #%d\n" solved.id;
        List.iter (fun unsolved -> process_resolution_new_solved kb solved unsolved) kb.not_solved.children
      end
    else begin let unsolved = Queue.take(kb.ns_todo) in
      if !debug_saturation then Printf.printf "Start resolutions of #%d\n" unsolved.id;
      List.iter (fun solved -> process_resolution_new_unsolved kb solved unsolved) kb.solved_deduction.children end
  done ;
  (ind,kb)  

(** {2 Recipe stuff} *)

(** Using success/failure continuations for backtracking.
  * The success continuation is called on each solution of type 'a,
  * and it is passed a continuation for enumerating more solutions
  * if necessary. Eventually the failure continuation (of type cont)
  * is called to notify that there is no (more) solution. *)
  (*
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

*)
