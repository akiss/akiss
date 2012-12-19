(** Manipulating clauses and saturating knowledge base *)

open Util
open Term
open Variants

(** Wrapper around Term to perform unification through Cime *)
module Term = struct
  include Term
  let mgu = Cime.mgu
  let csu = Cime.csu
  let csu u v =
    let sols = csu u v in
    let n = List.length sols in
      if n > 0 then debugOutput "Found %d solution(s)\n" n ;
      sols
end

(** {2 Predicates and clauses, conversions and printing} *)

(* TODO
 * - lists as sets is bad, at least stop caring about their order
 * - using a string for predicate names isn't so great (no check
 *   on typos, uselessly costly comparison); a fixed set of variants seems
 *   appropriate, and would solve those issues
 * - the use of startswith x "!n!" to check term types is fragile *)

type predicateName = id

(** Possible predicates are
  *   "knows" of arity 3 (world, recipe, term);
  *   "identical" and "ridentical" of arity 3 (world, recipe, recipe);
  *   "reach" of arity 1 (world). *)
type atom = 
  | Predicate of predicateName * term list

type hornClause =
    atom * atom list

type statement = hornClause

let is_deduction_st (head, _) = match head with
  | Predicate("knows", _) -> true
  | _ -> false

let is_equation_st (head, _) = match head with
  | Predicate("identical", _) -> true
  | _ -> false

let is_reach_st (head, _) = match head with
  | Predicate("reach", _) -> true
  | _ -> false

let is_ridentical_st (head, _) = match head with
  | Predicate("ridentical", _) -> true
  | _ -> false

(** A statement is solved if all its premises have a variable as their last
  * argument.
  * TODO there seems to be an assumption that this is never called
  *   on a "reach" statement, which also seems invalid in the [ridentical]
  *   step *)
let is_solved (_, body) =
  List.for_all (fun atom ->
		  match atom with
		    | Predicate(_, [_; _; x]) -> is_var x
		    | _ -> invalid_arg("is_solved")) body

let only_knows kb =
  List.filter is_deduction_st kb

let only_solved kb =
  List.filter is_solved kb

let rec vars_of_atom = function
  | Predicate(_, term_list) -> vars_of_term_list term_list

let rec vars_of_horn_clause (head, body) =
  unique (List.append
	    (trconcat (trmap vars_of_atom body))
            (vars_of_atom head))

let get_world atom = match atom with
  | Predicate("knows", [w; _; _]) -> w
  | _ -> invalid_arg("get_world")

let get_recipe atom = match atom with
  | Predicate("knows", [_; r; _]) -> r
  | _ -> invalid_arg("get_recipe")

let get_term atom = match atom with
  | Predicate("knows", [_; _; t]) -> t
  | _ -> invalid_arg("get_term")

let size (_,body) = List.length body

let get_head ((head, body) : statement) : atom =
  head

let get_body ((head, body) : statement) : atom list =
  body

(** {3 Conversions to and from terms} *)

let atom_from_term term = match term with
  | Fun(symbol, termlist) ->
      Predicate(symbol, termlist)
  | _ -> invalid_arg("atom_from_term")

let statement_from_term term = match term with 
  | Fun("implies", head :: body) ->
      (atom_from_term head, trmap atom_from_term body)
  | _ -> invalid_arg("statement_from_term")

let term_from_atom (Predicate(name, al)) =
  Fun(name, al)

let term_from_statement (head, body) =
  Fun("implies",  (term_from_atom head) :: (trmap term_from_atom body))

(** {3 Printing} *)

let rec show_atom = function
  | Predicate("!equals!", [s;t]) ->
      (show_term s) ^ " = " ^ (show_term t)
  | Predicate(name, term_list) ->
      name ^ "(" ^ (show_term_list term_list) ^ ")"

let show_statement ((head, body) : hornClause) =
(*  debugOutput "Statement of length %d\n%!" (List.length body); *)
  (show_atom head) ^ "  <==  " ^ (String.concat ", " (trmap show_atom body))

let show_kb kb =
  String.concat "\n" (trmap show_statement kb)

(** {3 Unification and substitutions} *)

let csu_atom a1 a2 = 
  Term.csu (term_from_atom a1) (term_from_atom a2)

let apply_subst_atom atom sigma = match atom with
  | Predicate(name, term_list) ->
      Predicate(name, trmap (fun x -> apply_subst x sigma) term_list)

let apply_subst_st (head, body) sigma =
  (apply_subst_atom head sigma, trmap (fun x -> apply_subst_atom x sigma) body)

(** {3 Misc} *)

(** Statement equality, modulo alpha renaming and TODO AC *)
let same_statement s t = 
  let ts = term_from_statement s in
  let tt = term_from_statement t in
  try
    let _ = mgm ts tt in
    let _ = mgm tt ts in
    true
  with Not_matchable -> false

let fresh_statement f =
  let allv = vars_of_horn_clause f in
  let newv = trmap (fun _ -> (Var(fresh_variable ()))) allv in
  let sigma = List.combine allv newv in
    apply_subst_st f sigma

(** [is_prefix_world w w'] checks whether [w] is a prefix of [w'],
  * assuming that worlds are compatible.
  * TODO use assert rather than invalid_arg to allow optimizations *)
let rec is_prefix_world small_world big_world = 
  match (small_world, big_world) with
  | (Fun("empty", []), _) -> true
  | (Fun("world", [h; t]), Fun("world", [hp; tp])) ->
      if h = hp then
        is_prefix_world t tp
      else
        invalid_arg "assertion failure is_prefix_world"
  | (Fun("world", [_; _]), Fun("empty", [])) -> false
  | (Var(x), Var(y)) ->
      if x = y then true else
        invalid_arg "assertion failure is_prefix_world"
  | _ ->
      invalid_arg
        (Printf.sprintf
           "is_prefix_world %s %s"
           (show_term small_world) (show_term big_world))

(* DB this is dead code, all its uses are commented out *)
(******************************)
(* testing some optimization *)
let solved_reach_subsumes r1 r2 =
  (* does r1 subsume r2? *)
  match r1 with 
  | (Predicate("reach", [w1]), _) ->
    (
      match r2 with 
      | (Predicate("reach", [w2]),_) -> is_prefix_world w2 w1
(*	let res = is_prefix_world w2 w1 in if res then (Printf.printf "\n %s \n subsumes \n %s \n" (show_statement r1) (show_statement r2); res) else res *)
      | _ -> false
    )
  | _ -> false
(******************************)

(** {2 Knowledge base update} *)

let rule_rename statement = match statement with
  | (Predicate("knows", _) as head, body) ->
      let options = trconcat (
	trmap 
	  (fun (atom1, atom2) -> match (atom1, atom2) with
	     | (Predicate("knows", [u; bx; x]), Predicate("knows", [v; by; y])) ->
		 (if (is_prefix_world u v) 
		    && (is_var x) 
		    && (is_var y) 
		    && ((unbox_var x) = (unbox_var y))
		    && ((unbox_var bx) <> (unbox_var by)) then
		      [(unbox_var by, (Var(unbox_var bx)))]
		  else
		    [])
	     | _ -> invalid_arg("rule_rename"))
	  (combine body body)) in (
	match options with
	  | (by, tbx) :: _ -> 
	      apply_subst_st 
		(head, 
		 (List.filter
		    (fun atom -> match atom with
		       | Predicate("knows", [_; testy; _]) -> (unbox_var testy) <> by
		       | _ -> invalid_arg("rule_rename"))
		    body))
		[(by, tbx)]
	  | _ -> statement
      )
  | _ -> statement

let rule_remove statement = match statement with
  | (Predicate("knows", _) as head, body) ->
      let vars_to_keep = vars_of_atom head in
      (head, List.filter 
	 (fun atom -> match atom with
	    | Predicate(_, [_; _; x]) -> 
		(not (is_var x)) || 
		  (List.mem (unbox_var x) vars_to_keep)
	    | _ -> invalid_arg("rule_remove"))
	 body)
  | _ -> statement

let canonical_form statement = 
  if is_solved statement then
    iterate rule_remove (iterate rule_rename statement)
  else
    statement

let is_same_t_smaller_w atom1 atom2 = match (atom1, atom2) with
  | (Predicate("knows", [w; _; t]), Predicate("knows", [wp; _; tp])) ->
      (is_prefix_world wp w) && (t = tp) (* TODO term equality *)
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
  * failure.
  * TODO mgm inside: update for AC *)
let inst_w_t my_head head_kb exc =
  match (my_head, head_kb) with
    | (Predicate(_, [myw; _; myt]), Predicate(_, [wkb; _; tkb])) -> (
	let t1 = Fun("!tuple!", [myw; myt]) in
	let t2 = Fun("!tuple!", [wkb; tkb]) in
	try
          (* debugOutput "Maching %s against %s\n%!" (show_term t1) (show_term t2); *)
          let sigma = mgm t2 t1 in
            (* debugOutput "Result %s\n%!" (show_subst sigma); *)
            sigma
	with Not_matchable -> raise exc
      )
    | _ -> invalid_arg("inst_w_t")

(** Check whether a statement is a consequence of a knowledge base, ie.
  * try to find a statement deriving the same "knows" atoms up to the recipe
  * from the same "knows" assumptions, among the solved statements of the base.
  * Raise [Not_a_consequence] if there is no such statement. If there is one,
  * return the associated recipe.
  * See Definition 14 and Lemma 2 in the paper. *)
let consequence st kb =
  assert (is_solved st) ;
  let rec aux (head, body) kb = 
    match head with
      | Predicate("knows", [_; _; Fun(name, [])]) when (startswith name "!n!") ->
          Fun(name, [])
      | Predicate("knows", [w; _; t]) ->
          begin try
            (* Base case: Axiom rule of conseq *)
            get_recipe (List.find (is_same_t_smaller_w head) body)
          with
            | Not_found ->
                (* Inductive case: Res rule
                 * Find a (solved, well-formed) statement [x]
                 * whose head is matched by [head] and such that
                 * [aux] succeeds on [y<-body] for each [y] in the
                 * body of [x]. *)
                first
                  (fun x ->
                     (* debugOutput "Checking %s\n%!" *)
                     (*   (show_statement (head, body)); *)
                     (* debugOutput "Against %s\n%!" *)
                     (*   (show_statement x); *)
                     let sigma = inst_w_t head (get_head x) Not_a_consequence in
                       (* debugOutput "Sigma: %s\n\n%!" (show_subst sigma); *)
                       apply_subst 
                         (get_recipe (get_head x))
                         (List.map
                            (fun y ->
                               unbox_var (get_recipe y),
                               aux (apply_subst_atom y sigma, body) kb)
                            (get_body x)))
                  kb Not_a_consequence
          end
      | _ -> invalid_arg("consequence")
  in
    aux st (only_knows (only_solved kb))

let set_insert f kb =
  if (List.exists (fun x -> same_statement f x) kb) then
    []
  else
    (
      (* debugOutput "Adding %s\n%!" (show_statement f); *)
      [fresh_statement f]
    )

(** Update a knowledge base with a new statement. This involves canonizing
  * the statement, checking whether it already belongs to the consequences
  * of the base, and actually inserting the statement or a variant of it. *)
let update (kb : statement list) (f : statement) : statement list =
  let (head, body) as fc = canonical_form f in
  if ((is_deduction_st f) && (is_solved f)) then
    try
      let recipe = consequence fc kb in
      let world = get_world head in
      let newhead = Predicate("identical", [world; get_recipe head; recipe]) in
      (
	debugOutput "USELESS: %s\nCF:%s\nINSTEAD:%s\n\n%!" (show_statement f) (show_statement fc)
	  (show_statement (newhead, body)); 
	let result = set_insert (newhead, body) kb in
	(
	  debugOutput "STATEMENTS INSERTED: %d\n%!" (List.length result);
	  result
	)
      )
    with Not_a_consequence -> 
      set_insert fc kb
(*  else if ( (is_reach_st fc) && (is_solved fc) ) then
    
    if (List.exists (fun x -> (solved_reach_subsumes x fc)) kb) then
      kb
    else (* set_insert fc kb *)
      (set_insert fc (List.filter (fun x ->  (not (is_reach_st fc)) || (solved_reach_subsumes fc x)) kb)) *)
  else
    set_insert fc kb

(** {2 Initial knowledge base}
  * TODO seed stuff should be here *)

(** Compute the initial knowledge base K_i(S) associated to the
  * seed statements S of a ground trace T. *)
let initial_kb (seed : statement list) : statement list =
  snd(
    iterate
      (
	fun (x : (statement list) * (statement list)) ->
	  match x with
	    | (s :: r, kb) -> (r, (List.append (update kb s) kb))
	    | ([], kb) -> ([], kb)
      )
      (seed, [])
  )

(** {2 Resolution steps} *)

(** [resolution d_kb master slave] attempts to perform a resolution step
  * between clauses [master] and [slave] by matching the head of [slave]
  * against the first premise of [master] that is of the form (knows _ _ t)
  * where t is not a variable.
  * This corresponds to the "Resolution" rule in the paper.
  * Return the list of newly generated clauses, of length at most 1.
  * The parameter [d_kb] is useless. *)
let resolution d_kb ((master_head, master_body), (slave_head, slave_body)) =
  match (List.filter (fun x -> not (is_var (get_term x))) master_body) with
  | atom :: _ ->
        (* let is_ground_w_t atom = *)
        (*   match atom with *)
        (*     | Predicate(_, [w; _; t]) -> ((is_ground w) && (is_ground t)) *)
        (*     | _ -> invalid_arg("is_ground_w_t") *)
	(* if is_ground_w_t atom then *)
	(*   try *)
	(*     let recipe = consequence (atom, []) d_kb in *)
	(*     let sigma = [(unbox_var (get_recipe atom), recipe)] in *)
	(*     let result = apply_subst_st  *)
	(*       (master_head, (List.filter (fun x -> (x <> atom)) master_body)) *)
	(*       sigma in *)
	(*     [result] *)
	(*   with *)
	(*     | Not_a_consequence -> [] *)
	(* else *)
    let sigmas = csu_atom atom slave_head in
      List.map
        (fun sigma ->
           let result =
             apply_subst_st
               (master_head,
                List.append
                  (List.filter (fun x -> (x <> atom)) master_body)
                  slave_body)
               sigma
           in
             debugOutput "Resolution:\n FROM: %s\n AND : %s\n RESO: %s\n\n%!"
               (show_statement (master_head, master_body))
               (show_statement (slave_head, slave_body))
               (show_statement result);
             result)
        sigmas
  | [] -> []

(** [equation (fa,fb)] takes two clauses and, when they are solved clauses
  * concluding "knows", attempts to combine them: if the terms and worlds can be
  * unified, generate a clause concluding that the recipes are "identical".
  * This corresponds to the "Equation" rule in the paper.
  * TODO in my example this runs on knows(...,w1,plus(...)); plus isn't a var?!
  * TODO that function seems to be ran on twice the same clause, and also ran on
  *   both (a,b) and (b,a); there might be faster ways of getting a reflexive
  *   symmetric "identical" predicate
  * It returns [] if it fails to produce any new clause. *)
let equation (fa, fb) =
  (
    if (is_solved fa) && (is_solved fb) &&
      (is_deduction_st fa) && (is_deduction_st fb) then (
        debugOutput "Equation:\n %s\n %s\n%!" (show_statement fa) (show_statement fb);
        match ((get_head fa), (get_head fb)) with
          | (Predicate("knows", [ul; r; t]),
             Predicate("knows", [upl; rp; tp])) ->
              let t1 = Fun("!tuple!", [t; ul]) in
              let t2 = Fun("!tuple!", [tp; upl]) in
        let sigmas = Term.csu t1 t2 in
          List.map
            (fun sigma ->
               let newhead = Predicate("identical", [ul; r; rp]) in
               let newbody = List.append (get_body fa) (get_body fb) in
                 apply_subst_st (newhead, newbody) sigma)
            sigmas
          | _ -> invalid_arg("equation")
      )
    else
      []
  )

(** [ridentical (fa,fb)] attempts to combine the two clauses when [fa]
  * concludes "identical" and [fb] concludes "reach" and their world params
  * match. This corresponds to the "Test" rule in the paper. *)
let ridentical (fa, fb) =
  (* debugOutput "entering ridentical\n%!";  *)
  if not (is_solved fa && is_solved fb) then [] else
    match ((get_head fa), (get_head fb)) with
      | (Predicate("identical", [u; r; rp]),
         Predicate("reach", [up])) ->
          debugOutput
            "ridentical trying to combine %s with %s\n%!"
            (show_statement fa) (show_statement fb);
          let sigmas = Term.csu u up in
            List.map
              (fun sigma ->
                 let newhead = Predicate("ridentical", [u; r; rp]) in
                 let newbody = List.append (get_body fa) (get_body fb) in
                 let result = apply_subst_st (newhead, newbody) sigma in
                   debugOutput "\n\nRID FROM: %s\nRID AND : %s\nRID GOT: %s\n\n%!" 
                     (show_statement fa)
                     (show_statement fb)
                     (show_statement result);
                   result)
              sigmas
      | _ -> []

(** {2 Saturation procedure} *)

(* let resolution_step d_un d_so o_kb = *)
(*   debugOutput "Performing resolution step\n%!"; *)
(*   let n_kb = trconcat (trmap (fun x -> resolution d_so x) (combine d_un d_so)) in *)
(*   let (n_d_kb, n_o_kb_aux) = List.partition is_deduction_st n_kb in *)
(*   let (n_d_so_aux, n_d_un_aux) = List.partition is_solved n_d_kb in *)
(*   let n_d_so = trconcat (trmap (fun x -> update d_so x) n_d_so_aux) in *)
(*   let n_d_un = trconcat (trmap (fun x -> update d_un x) n_d_un_aux) in *)
(*   let n_o_kb = trconcat (trmap (fun x -> update o_kb x) n_o_kb_aux) in *)
(*   (n_d_so, n_d_un, n_o_kb) *)

(* let empty_list = function *)
(*  | [] -> true *)
(*  | _ -> false *)
(* let rec saturate_aux d_un d_so o_kb = *)
(*   let (n_d_so, n_d_un, n_o_kb) = resolution_step d_un d_so o_kb in *)
(*   if empty_list n_d_so && empty_list n_d_un && empty_list n_o_kb then *)
(*     (d_un, d_so, o_kb) *)
(*   else *)
(*     saturate_aux (List.rev_append d_un n_d_un) *)
(*       (List.rev_append d_so n_d_so) *)
(*       (List.rev_append o_kb n_o_kb) *)

let useful (head, body) rules = (* TODO normalize and equality *)
  match head with
    | Predicate("knows", _) -> true
    | Predicate("reach", _) -> true
    | Predicate("identical", [_; r; rp])
    | Predicate("ridentical", [_; r; rp]) ->
        normalize r rules <> normalize rp rules
    | _ -> invalid_arg("useful")

(* let rec second_step_aux er_kb_any d_so a rules =  *)
(*   let er_kb = List.filter (fun x -> useful x rules) er_kb_any in *)
(*   let new_generation_aux = trconcat (trmap (fun x -> resolution d_so x) *)
(* 				       (combine er_kb d_so)) in *)
(*   ( *)
(*     debugOutput "Updating by new generation of %d statements... %!"  *)
(*       (List.length new_generation_aux); *)
(*     let new_generation = trconcat (trmap (fun x -> update a x) new_generation_aux) in *)
(*     ( *)
(*       debugOutput "added %d statements\n%!" (List.length new_generation); *)
(*       if List.length new_generation = 0 then *)
(* 	a *)
(*       else *)
(* 	second_step_aux new_generation d_so (List.rev_append new_generation a) rules *)
(*     ) *)
(*   ) *)

let resolution_step_new unsolved_s solved_ks =
  trconcat (trmap (fun x -> resolution solved_ks x) (combine unsolved_s solved_ks))

let saturate_class_one_step kb ff =
  let solved_ks = only_solved (only_knows kb) in
  let to_solve = List.filter ff kb in
  let new_statements = resolution_step_new to_solve solved_ks in
  List.append kb (trconcat (trmap (fun x -> update kb x) new_statements))

let saturate_class kb ff =
  iterate (fun x -> saturate_class_one_step x ff) kb

let saturate_equation_one_step kb =
  let solved_ks = only_solved (only_knows kb) in
  let other = List.filter (fun x -> is_equation_st x) kb in
  let new_statements = resolution_step_new other solved_ks in
  List.append kb (trconcat (trmap (fun x -> update kb x) new_statements))

let saturate kb rules =
  let kb_p = saturate_class kb is_deduction_st in
  let solved_ks = only_knows (only_solved kb_p) in
  let new_es = trconcat (trmap equation (combine solved_ks solved_ks)) in
  let new_es_useful = List.filter (fun x -> useful x rules) new_es in
  let kb_q = saturate_class (List.append kb_p new_es_useful) is_equation_st in
  let kb_r = saturate_class kb_q is_reach_st in
  let solved_es = List.filter is_equation_st kb_r in
  let solved_rs = List.filter is_reach_st kb_r in
  let new_ri = trconcat (trmap ridentical (combine solved_es solved_rs)) in
  let kb_s = List.append kb_r new_ri in
  saturate_class kb_s is_ridentical_st

(* let saturate_old kb rules = *)
(*   debugOutput "Equational statements already in initial kb: %s\n%!" (show_kb (List.filter is_equation_st kb)); *)
(*   let (d_kb, o_kb) = List.partition is_deduction_st kb in *)
(*   let (d_so, d_un) = List.partition is_solved d_kb in *)
(*   let (d_un, d_so, o_kb) = saturate_aux d_un d_so o_kb in *)
(*   ( *)
(*     debugOutput "The equational statements added during first phase: %s\n%!" (show_kb o_kb); *)
(*   let e_kb = trconcat (trmap equation (combine d_so d_so)) in *)
(*   let temp = List.append (List.append o_kb e_kb) (List.filter is_equation_st kb) in *)
(*   let er_kb = second_step_aux temp d_so temp rules in *)
(*   let er_so = List.filter is_solved er_kb in *)
(*   let e_so = List.filter is_equation_st er_so in *)
(*   let r_so = List.filter is_reach_st er_so in *)
(*   ( *)
(*     let e_so_useful = (List.filter (fun x -> useful x rules) e_so) in *)
(*     debugOutput "I have %d (%d) solved equational statements and %d solved reach statements" (List.length e_so) (List.length e_so_useful) (List.length r_so); *)
(*     let temp2 = trconcat (trmap ridentical (combine e_so_useful r_so)) in *)
(*     let ri_kb = second_step_aux temp2 d_so temp2 rules in *)
(*     trconcat [d_so; d_un; er_kb; ri_kb] *)
(*   ) *)
(*   ) *)

(** {2 Recipe stuff} *)

let namify_subst t =
  let vars = vars_of_term t in
  let names = trmap (fun _ -> Fun(fresh_string "!n!", [])) vars in
  let sigma = List.combine vars names in
  sigma

let namify t =
  let sigma = namify_subst t in
  apply_subst t sigma

exception Algorithm_error
exception Find_recipe_h_error

exception No_recipe_found

let rec find_recipe_h atom kbs all = 
  match atom with
  | Predicate("knows", [_; _; Fun(name, [])]) when (startswith name "!n!") ->
	Fun(name, [])
    | _ ->
	(
	  match kbs with
	    | (((Predicate("knows", [wp; rp; tp])) as head), body) :: rest -> 
		(
		  try
		    let sigma = inst_w_t atom head No_recipe_found in
		    (
		      (* debugOutput "Sigma: %s\n\n%!" (show_subst sigma); *)
		      apply_subst 
			(get_recipe head)
			(List.combine
			   (trmap 
			      (fun y -> unbox_var (get_recipe y))
			      body)
			   (trmap 
			      (fun y -> find_recipe_h
				 (apply_subst_atom y sigma) 
				 all
				 all)
			      body))
		    )
		  with
		    | No_recipe_found -> find_recipe_h atom rest all
		)
	    | [] -> raise No_recipe_found;
	    | _ -> raise Find_recipe_h_error;
	)

let find_recipe atom kb =
  let kbsolved = (only_knows (only_solved kb)) in
  try
    find_recipe_h atom kbsolved kbsolved
  with No_recipe_found -> (
    Printf.eprintf "Trying to get %s out of:\n%s\n\n%!" 
      (show_atom atom)
      (show_kb kbsolved);
    raise Algorithm_error
  )

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

let checks_reach kb = 
  trconcat (
    trmap
      (fun x ->
	(
	  (* debugOutput "TESTER: %s\n" (show_statement x); *)
  	  match (get_head x) with
  	    | Predicate("reach", [w]) when is_solved x ->
  	      [Fun("check_run", [revworld (recipize (namify w) kb)])]
  	    | _ -> []))
      kb)

let checks_ridentical kb =
  trconcat (
    trmap
      (fun x ->
	(
	  (* debugOutput "TESTER: %s\n" (show_statement x); *)
  	  match (get_head x) with
   	    | Predicate("ridentical", [w; r; rp]) when is_solved x ->
		let sigma = namify_subst w in
		let new_w = revworld (recipize (apply_subst w sigma) kb) in
		let omega = trmap (function arg -> match arg with
				     | Predicate("knows", [_; Var(vX); Var(vx)]) -> 
					 (vX, apply_subst (Var(vx)) sigma)
				     | _ -> invalid_arg("checks_ridentical"))
		  (get_body x) in
		let resulting_test = Fun("check_identity", [new_w; 
							    apply_subst r omega;
							    apply_subst rp omega]) in
		(
		  (* debugOutput "FROM: %s\nGOT:%s\n\n%!" (show_statement x) (show_term resulting_test); *)
  		  [resulting_test]
		)
  	    | _ -> []))
      kb)


let checks kb  =
  let kb_solved = List.filter is_solved kb in
  List.append (checks_reach kb_solved) (checks_ridentical kb_solved)

let show_tests tests =
  String.concat "\n\n" (trmap show_term tests)


let show_rew_rules rules =
  String.concat "\n" (trmap 
    (
      fun x ->
	match x with
	| (l, r) -> (show_term l)^" -> "^(show_term r);
    ) 
    rules)
