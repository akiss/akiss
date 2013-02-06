(** Manipulating clauses and saturating knowledge base *)

open Util
open Term

(** Wrapper around Term to perform unification through Cime *)
module Term = struct
  include Term
  let mgu = Cime.mgu
  let mgm = Cime.mgm
  let csu = Cime.csu
  let csu u v =
    let sols = csu u v in
    let n = List.length sols in
      if n>0 then debugOutput "Found %d solution(s)\n" n ;
      sols
end

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

type hornClause =
    int * atom * atom list

type statement = hornClause

let is_deduction_st (_, head, _) = match head with
  | Predicate("knows", _) -> true
  | _ -> false

let is_equation_st (_, head, _) = match head with
  | Predicate("identical", _) -> true
  | _ -> false

let is_reach_st (_, head, _) = match head with
  | Predicate("reach", _) -> true
  | _ -> false

let is_ridentical_st (_, head, _) = match head with
  | Predicate("ridentical", _) -> true
  | _ -> false

(** A statement is solved if all its premises have a variable as their last
  * argument. *)
let is_solved (_,_,body) =
  List.for_all
    (function
       | Predicate("knows", [_; rx; x]) ->
           assert (is_var rx) ;
           is_var x
       | _ -> invalid_arg("is_solved"))
    body

let rec vars_of_atom = function
  | Predicate(_, term_list) -> vars_of_term_list term_list

let rec vars_of_horn_clause (_, head, body) =
  unique (List.append
	    (trconcat (trmap vars_of_atom body))
            (vars_of_atom head))

let get_world atom = match atom with
  | Predicate("knows", [w; _; _]) -> w
  | _ -> invalid_arg("get_world")

let get_recipe atom = match atom with
  | Predicate("knows", [_; r; _]) -> r
  | _ -> invalid_arg("get_recipe")

let get_recipes atom = match atom with
  | Predicate("knows", [_; r; _]) -> [r]
  | Predicate("identical", [_; r1; r2])
  | Predicate("ridentical", [_; r1; r2]) -> [r1;r2]
  | Predicate("reach",[_]) -> []
  | _ -> assert false

let get_term atom = match atom with
  | Predicate("knows", [_; _; t]) -> t
  | _ -> invalid_arg("get_term")

let size (_,_,body) = List.length body

let get_id ((id, _, _) : statement) : int =
  id

let get_head ((_, head, body) : statement) : atom =
  head

let get_body ((_, head, body) : statement) : atom list =
  body

(** {3 Conversions to and from terms} *)

let atom_from_term term = match term with
  | Fun(symbol, termlist) ->
      Predicate(symbol, termlist)
  | _ -> invalid_arg("atom_from_term")

let statement_from_term id term = match term with 
  | Fun("!tuple!", head :: body) ->
      (id, atom_from_term head, trmap atom_from_term body)
  | _ -> invalid_arg("statement_from_term")

let term_from_atom (Predicate(name, al)) =
  Fun(name, al)

let term_from_statement (_, head, body) =
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

let show_statement ((id, head, body) : hornClause) =
  Printf.sprintf
    "#%d(len=%d): %s <== %s"
    id
    (List.length body)
    (show_atom head)
    (String.concat ", " (trmap show_atom_body body))

(** {3 Unification and substitutions} *)

let csu_atom a1 a2 = 
  Term.csu (term_from_atom a1) (term_from_atom a2)

let apply_subst_atom atom sigma = match atom with
  | Predicate(name, term_list) ->
      Predicate(name, trmap (fun x -> apply_subst x sigma) term_list)

let apply_subst_st (id, head, body) sigma =
  (id,
   apply_subst_atom head sigma,
   trmap (fun x -> apply_subst_atom x sigma) body)

let fresh_statement f =
  let allv = vars_of_horn_clause f in
  let newv = trmap (fun v ->
                     if v.[0] = 'P' then Var (fresh_string "P") else
                       Var (fresh_variable ())) allv in
  let sigma = List.combine allv newv in
    apply_subst_st f sigma

let dotfile =
  let dotfile = open_out "akiss.dot" in
    Printf.fprintf dotfile "digraph G {\n" ;
    at_exit (fun () -> Printf.fprintf dotfile "}\n") ;
    dotfile

let is_plus = function
  | Fun ("plus",_) -> true
  | _ -> false

let isnt_plus x = not (is_plus x)

let is_marked x = x.[0] = 'P'

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
          (* Prioritize terms that pass this test *)
          let check f x1 x2 k =
            match f x1, f x2 with
              | true, true -> 0
              | true, _ -> -1
              | _, true -> 1
              | false, false -> k ()
          in
            check is_var t1 t2 (fun () ->
              check isnt_plus t1 t2 (fun () ->
                check is_marked r1 r2 (fun () ->
                  check has_rigid t1 t2 (fun () ->
                    compare (nb_flexibles t1) (nb_flexibles t2)))))
      | _ -> assert false
  in
  let c = ref 0 in
    fun ?(label="") ?(parents=([]:statement list)) (head,body) ->
      let body = List.sort compare body in
        incr c ;
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
             (List.map (fun (i,_,_) -> "#" ^ string_of_int i) parents))
          (show_statement (!c,head,body)) ;
        let parents = match parents with
          | [a;b] -> [max a b]
          | _ -> parents
        in
        List.iter
          (fun (id,_,_) ->
             Printf.fprintf dotfile "n%d -> n%d [color=%s];\n" id !c
               (match label with "ri" -> "red" | "eq" -> "blue" | _ -> "black"))
          parents ;
        !c,head,body

(** {3 Misc} *)

(** Statement equality for set updates
  * This is currently only modulo alpha renaming (and could be written
  * better for that). It may be made modulo AC but this seems too
  * costly.
  * TODO properly treat marked variables! *)
let same_statement s t =
  let ts = term_from_statement s in
  let tt = term_from_statement t in
    (* Maude.matchers ts tt [] <> [] && Maude.matchers tt ts [] <> [] *)
    try ignore (mgm ts tt) ; ignore (mgm tt ts) ; true with Not_matchable ->
    false

(** [is_prefix_world w w'] checks whether [w] is a prefix of [w'],
  * assuming the two worlds come from the same statement, so that one
  * is necessarily a prefix of the other. *)
let rec is_prefix_world small_world big_world = 
  match (small_world, big_world) with
  | (Fun("empty", []), _) -> true
  | (Fun("world", [h; t]), Fun("world", [hp; tp])) ->
      assert (Maude.equals h hp []) ;
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

  let add ?(needs_check=true) x rules kb =
    assert (needs_check || not (mem_equiv x kb)) ;
    if not (needs_check && mem_equiv x kb) then begin
      debugOutput "Adding clause #%d.\n" (get_id x) ;
      add (fresh_statement x) kb
    end

end

let only_knows kb = List.filter is_deduction_st kb

let only_solved kb = Base.only_solved kb

let show_kb kb =
  Base.fold (fun stmt str -> str ^ "\n" ^ show_statement stmt) kb ""

let show_kb_list kb =
  List.fold_left (fun str stmt -> str ^ "\n" ^ show_statement stmt) "" kb

(** {2 Knowledge base update} *)

let rule_rename statement = match statement with
  | (id, (Predicate("knows", _) as head), body) ->
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
		(id, head, 
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
  | (id, (Predicate("knows", _) as head), body) ->
      let vars_to_keep = vars_of_atom head in
      (id, head, List.filter 
	 (fun atom -> match atom with
	    | Predicate(_, [_; _; x]) -> 
		(not (is_var x)) || 
		  (List.mem (unbox_var x) vars_to_keep)
	    | _ -> invalid_arg("rule_remove"))
	 body)
  | _ -> statement

(** For statements that are not canonized we still apply some simplifications
  * to avoid explosions: if a term is derived using several recipes, we can
  * remove derivations for which the recipe does not occur elsewhere in the
  * statement. *)
let simplify_statement (id,head,body) =
  let hvars = vars_of_term_list (get_recipes head) in
  let rec update body =
    let useless,body =
      List.partition
        (fun a ->
           not (List.mem (unbox_var (get_recipe a)) hvars) &&
           let t = get_term a in
           let l = world_length (get_world a) in
             List.exists (fun a' ->
                            a != a' &&
                            l = world_length (get_world a') &&
                            Maude.equals t (get_term a') []) body)
        body
    in
      List.iter
        (fun a -> debugOutput "Removed %s\n" (show_atom a))
        useless ;
      if useless <> [] then update body else body
  in
    (id,head,update body)

let canonical_form statement = 
  if is_solved statement then
    let f = iterate rule_remove (iterate rule_rename statement) in
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
  * failure.
  * This is used for checking if a clause is in conseq, which is done
  * in kb updates and when recipizing tests. In the first case we may
  * or may not want AC (TODO). In the second case we need AC.
  * TODO check that instantiations respect annotations regarding + *)
let inst_w_t ?(ac=false) my_head head_kb exc =
  match (my_head, head_kb) with
    | (Predicate(_, [myw; _; myt]), Predicate(_, [wkb; _; tkb])) -> (
	let t1 = Fun("!tuple!", [myw; myt]) in
	let t2 = Fun("!tuple!", [wkb; tkb]) in
	try
          (* debugOutput "Maching %s against %s\n%!" (show_term t1) (show_term t2); *)
          let sigma = (if ac then Term.mgm else mgm) t2 t1 in
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
  let rec aux (_, head, body) kb = 
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
                               aux (-1, apply_subst_atom y sigma, body) kb)
                            (get_body x)))
                  kb Not_a_consequence
          end
      | _ -> invalid_arg("consequence")
  in
    aux st (only_knows (only_solved kb))

(** Avoid reflexive identities.
  * Note: even with the simplification of non-solved clauses, there are
  * some cases that we are missing,
  * eg. identical(C[R1],C[R2]) <-- k(R1,T), k(R2,T)
  * and variants of it with one recipe being broken in two parts, etc. *)
let useful (id, head, body) =
  match head with
    | Predicate("knows", _) -> true
    | Predicate("reach", _) -> true
    | Predicate("identical", [_; r; rp])
    | Predicate("ridentical", [_; r; rp]) ->
        if r = rp then begin
          debugOutput "Clause #%d is not useful.\n" id ;
          false
        end else true
    | _ -> invalid_arg("useful")

(** Update a knowledge base with a new statement. This involves canonizing
  * the statement, checking whether it already belongs to the consequences
  * of the base, and actually inserting the statement or a variant of it. *)
let update (kb : Base.t) rules (f : statement) : unit =

  let tf_orig = term_from_statement f in
  let tf = Maude.normalize tf_orig rules in
  let f = statement_from_term (get_id f) tf in
  if not (Maude.equals tf_orig tf []) then
    debugOutput "Clause #%d is not normal.\n" (get_id f)
  else

  let (id, head, body) as fc = canonical_form f in
  if useful fc then
  if is_deduction_st f && is_solved f then
    try
      (* TODO can we really run consequence before freshening the clause? *)
      let recipe = consequence fc kb in
      let world = get_world head in
      let newhead = Predicate("identical", [world; get_recipe head; recipe]) in
        debugOutput
          "USELESS: %s\nCF:%s\nINSTEAD:%s\n\n%!"
          (show_statement f) (show_statement fc)
          (show_statement (id, newhead, body)); 
        if useful (id,newhead,body) then
          Base.add (id, newhead, body) rules kb
    with Not_a_consequence ->
      Base.add ~needs_check:false fc rules kb
  else
    Base.add fc rules kb

(** {2 Initial knowledge base}
  * TODO seed stuff should be here *)

(** Compute the initial knowledge base K_i(S) associated to the
  * seed statements S of a ground trace T. *)
let initial_kb (seed : statement list) : Base.t =
  let kb = Base.create () in
    List.iter (update kb []) seed ;
    kb

(** {2 Resolution steps} *)

(** Restrict a csu based on plus-constraints *)
let plus_restrict sigmas ~t ~rx ~x ~ry ~y =

  (* Find the leftmost rigid (non-plus,non-var) subterm *)
  let rec extract_rigid = function
    | Fun ("plus",[x;y])::l -> extract_rigid (x::y::l)
    | Fun (_,_) as t :: _ -> Some t
    | Var _ :: l -> extract_rigid l
    | [] -> None
  in

  (* Adapt a substitution to mark one recipe variable as not being a plus.
   * In the case of equation, the recipe variables are not in the substitution. *)
  let update r sigma =
    let sigma =
      if List.mem_assoc r sigma then begin
        assert (Var r = List.assoc r sigma) ;
        sigma
      end else
        (r, Var r) :: sigma
    in
    let r' = Var (fresh_string "P") in
      List.map (fun (x,t) -> x, apply_subst t [r,r']) sigma
  in

  let sigmas =
    (* Recipe renaming strategy *)

    (* When there is a rigid (non-plus) subterm a in t:
     * do nothing unless [static_rigid];
     * if it occurs in a single subterm on the other side, mark the corresponding
     * recipe;
     * if it does not occur in a single subterm, always mark on the left, unless
     * [dynamic_nooccur] in which case the most convenient choice is made for
     * each solution. *)
    let static_rigid = true in
    let dynamic_nooccur = false in

    (* When there is no rigid subterm: do nothing unless [static_norigid];
     * mark the left recipe, unless [dynamic_norigid] in which case the most
     * convenient marking is made for each solution. *)
    let static_norigid = false in
    let dynamic_norigid = false in

    match extract_rigid [t] with
      | None ->
          debugOutput "rigid subterm: none (%s)\n" (show_term t) ;
          if not static_norigid then sigmas else
          List.map
            (fun sigma ->
               if dynamic_norigid && is_var (List.assoc x sigma) then
                 update ry sigma
               else
                 update rx sigma)
            sigmas
      | Some t ->
          debugOutput "rigid subterm: %s\n" (show_term t) ;
          let rec occurs = function
            | Var _ :: l -> occurs l
            | Fun (s,args) as t' :: l ->
                t = t' || occurs (List.rev_append args l)
            | [] -> false
          in
          let update_sigma sigma =
            let ox = occurs [List.assoc x sigma] in
            let oy = occurs [List.assoc y sigma] in
              if (ox && oy) || not (ox || oy) then
                if dynamic_nooccur && is_var (List.assoc x sigma) then
                  update ry sigma
                else
                  update rx sigma
              else
                if ox then update rx sigma else update ry sigma
          in
            if not static_rigid then sigmas else
              List.map update_sigma sigmas
  in

    if !debug_output then begin
      Printf.printf
        "final csu of size %d:\n"
        (List.length sigmas) ;
      List.iter
        (fun s -> Printf.printf "* %s\n" (show_subst s))
        sigmas
    end ;
    sigmas

let mark_flexible_plus_2 ~a ~b ~rx ~ry ~x ~y sigmas =

  (* Adapt a substitution to mark one recipe variable as not being a plus.
   * In the case of equation, the recipe variables are not in the substitution. *)
  let update r sigma =
    let sigma =
      if List.mem_assoc r sigma then begin
        assert (Var r = List.assoc r sigma) ;
        sigma
      end else
        (r, Var r) :: sigma
    in
    let r' = Var (fresh_string "P") in
      List.map (fun (x,t) -> x, apply_subst t [r,r']) sigma
  in

    assert (List.length sigmas <= 7) ;
    List.map
      (fun (sigma:subst) ->
         let x' = List.assoc x sigma in
         let y' = List.assoc y sigma in
         let a' = List.assoc a sigma in
         let b' = List.assoc b sigma in
           if (x',y') = (a',b') || (x',y') = (b',a') then
             sigma
           else
             match a',b' with
               | Fun ("plus",[Var _;Var _]), Fun ("plus",[Var _; Var _]) ->
                   update rx sigma
               | Fun ("plus",[Var _; Var _]), Var w
               | Var w, Fun ("plus",[Var _; Var _]) ->
                   begin match x' with
                     | Fun ("plus",[Var x'1; Var x'2]) ->
                         assert (w = x'1 || w = x'2) ;
                         assert (is_var y') ;
                         update rx sigma
                     | Var o ->
                         begin match y' with
                           | Fun ("plus",[Var y'1; Var y'2]) ->
                               assert (w = y'1 || w = y'2) ;
                               update ry sigma
                           | _ -> assert false
                         end
                     | _ -> assert false
                   end
               | _ -> assert false)
      sigmas

let mark_flexible_plus_3 ~a ~b ~c ~rx ~ry ~x ~y sigmas =

  (* TODO factorize this *)
  (* Adapt a substitution to mark one recipe variable as not being a plus.
   * In the case of equation, the recipe variables are not in the substitution. *)
  let update r sigma =
    let sigma =
      if List.mem_assoc r sigma then begin
        assert (Var r = List.assoc r sigma) ;
        sigma
      end else
        (r, Var r) :: sigma
    in
    let r' = Var (fresh_string "P") in
      List.map (fun (x,t) -> x, apply_subst t [r,r']) sigma
  in
  let is_split = function
    | Var _ -> false
    | Fun (f,_) -> assert (f = "plus") ; true
  in
    assert (List.length sigmas <= 25) ;
    List.map
      (fun (sigma:subst) ->
         let x' = List.assoc x sigma in
         let a' = List.assoc a sigma in
         let b' = List.assoc b sigma in
         let c' = List.assoc c sigma in
           (* Mark recipe associated with something of the form
            *   a1+b1+c1, a1+b1, a+b+c1. *)
         let split, whole = List.partition is_split [a';b';c'] in
           match split,whole with
             | [_;_;_],_ -> update rx sigma
             | [_],_ ->
                 begin match x' with
                   | Var _ -> update ry sigma
                   | _ -> update rx sigma
                 end
             | _,[_] ->
                 begin match x' with
                   | Fun ("plus",[Var _;Var _]) -> update rx sigma
                   | _ -> update ry sigma
                 end
             | [],_ -> sigma
             | _ -> assert false)
      sigmas

let plus_restrict ~t (slave_head,slave_body) sigmas =
  match slave_head,slave_body with
    | _ when sigmas = [] -> sigmas
    | Predicate ("knows",
                 [Var w;
                  Fun ("plus",[Var rx; Var ry]);
                  Fun ("plus",[Var x; Var y])]),
      [ Predicate("knows",[Var w'; Var r'; Var x']) ;
        Predicate("knows",[Var w''; Var r''; Var y'']) ]
      when rx <> ry && x <> y && w = w' && w = w'' &&
           ((rx,x,ry,y) = (r',x',r'',y'') ||
            (rx,x,ry,y) = (r'',y'',r',x'))
      ->
        begin match t with
          | Fun ("plus",[Var a; Var b]) when a <> b ->
              let sigmas = mark_flexible_plus_2 ~a ~b ~rx ~ry ~x ~y sigmas in
                debugOutput "flexible 2-2 equation, csu becomes:\n" ;
                List.iter
                  (fun s ->
                     debugOutput "> %s/%s, %s/%s -- %s\n"
                       (show_term (List.assoc rx s))
                       (show_term (List.assoc x s))
                       (show_term (List.assoc ry s))
                       (show_term (List.assoc y s))
                       (show_subst s))
                  sigmas ;
                sigmas
          | Fun ("plus",[Var a; Fun ("plus",[Var b; Var c])])
          | Fun ("plus",[Fun ("plus",[Var a; Var b]); Var c])
            when a <> b && a <> c && b <> c ->
              let sigmas = mark_flexible_plus_3 ~a ~b ~c ~rx ~ry ~x ~y sigmas in
                debugOutput "flexible 3-2 equation, csu becomes:\n" ;
                List.iter
                  (fun s ->
                     debugOutput "> %s/%s, %s/%s -- %s\n"
                       (show_term (List.assoc rx s))
                       (show_term (List.assoc x s))
                       (show_term (List.assoc ry s))
                       (show_term (List.assoc y s))
                       (show_subst s))
                  sigmas ;
                sigmas
          | _ ->
              plus_restrict sigmas ~t ~rx ~x ~ry ~y
        end
  | _ -> sigmas

(** [resolution d_kb (master,slave)] attempts to perform a resolution step
  * between clauses [master] and [slave] by matching the head of [slave]
  * against the first premise of [master] that is of the form (knows _ _ t)
  * where t is not a variable.
  * This corresponds to the "Resolution" rule in the paper.
  * Return the list of newly generated clauses. *)
let resolution master slave =
  let (mid, master_head, master_body) = master in
  let (sid, slave_head, slave_body) = slave in
  let atom = List.find (fun x -> not (is_var (get_term x))) master_body in

    (* Fail immediately if slave's head isn't a knows statement. *)
    if not (is_deduction_st slave) then [] else

    (* Fail immediately if solutions would violate marking. *)
    if is_marked (unbox_var (get_recipe atom)) &&
       is_plus (get_recipe slave_head)
    then [] else

    let sigmas = csu_atom atom slave_head in
    let length = List.length sigmas in
    if !debug_output && length > 0 then begin
      debugOutput "Resolution?\n FROM: %s\n AND : %s\n\n"
        (show_statement (mid, master_head, master_body))
        (show_statement (sid, slave_head, slave_body)) ;
      Printf.printf "csu of size %d:\n" length ;
      List.iter
        (fun s -> Printf.printf "> %s\n" (show_subst s))
        sigmas
    end ;
    let sigmas =
      plus_restrict ~t:(get_term atom) (slave_head,slave_body) sigmas
    in
    let () =
      if !debug_output && List.length sigmas < length then begin
        Printf.printf "filtered csu of size %d:\n" (List.length sigmas) ;
        List.iter
          (fun s -> Printf.printf "+ %s\n" (show_subst s))
          sigmas
      end
    in

      (* Create results *)
      List.map
        (fun sigma ->
           let result =
             let head = apply_subst_atom master_head sigma in
             let body =
               List.map (fun x -> apply_subst_atom x sigma)
                 (List.append
                    slave_body
                    (List.filter (fun x -> (x <> atom)) master_body))
             in
               new_clause ~label:"res"
                 ~parents:[master;slave] (head,body)
           in
             debugOutput "RESO: %s\n\n"
               (show_statement result);
             result)
        sigmas

(** [equation fa fb] takes two clauses and, when they are solved clauses
  * concluding "knows", attempts to combine them: if the terms and worlds can be
  * unified, generate a clause concluding that the recipes are "identical".
  * This corresponds to the "Equation" rule in the paper.
  * It returns [] if it fails to produce any new clause. *)
let equation fa fb =
  let (a,_,_),(b,_,_) = fa,fb in
    (* Avoid reflexivity and symmetry, and order so that the plus context
     * statement will be second (the latter needs to be made more solid). *)
    if a<=b then [] else
    if (is_solved fa) && (is_solved fb) &&
      (is_deduction_st fa) && (is_deduction_st fb) then (
        debugOutput "Equation:\n %s\n %s\n%!" (show_statement fa) (show_statement fb);
        match ((get_head fa), (get_head fb)) with
          | (Predicate("knows", [ul; r; t]),
             Predicate("knows", [upl; rp; tp])) ->
              let t1 = Fun("!tuple!", [t; ul]) in
              let t2 = Fun("!tuple!", [tp; upl]) in
              let sigmas = Term.csu t1 t2 in
              let sigmas = plus_restrict ~t (get_head fb, get_body fb) sigmas in
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
                       (List.map (fun (id,_,_) -> "#"^string_of_int id) clauses)) ;
                clauses
          | _ -> invalid_arg("equation")
      )
    else
      []

(** [ridentical fa fb] attempts to combine the two clauses when [fa]
  * concludes "identical" and [fb] concludes "reach" and their world params
  * match. This corresponds to the "Test" rule in the paper. *)
let ridentical fa fb =
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
        let ids = equation f g @ equation g f in
        (* let ids = List.filter (fun x -> useful x rules) ids in *)
          List.iter (update kb rules) ids ;
          List.iter (update kb rules) (ridentical f g @ ridentical g f) ;
          true

let saturate kb rules =
  (* Try not_solved step, otherwise solved step, otherwise stop. *)
  while saturate_step_not_solved rules kb
     || saturate_step_solved rules kb
  do () done

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
	    | (_, ((Predicate("knows", [wp; rp; tp])) as head), body) :: rest -> 
		(
		  try
		    let sigma = inst_w_t ~ac:true atom head No_recipe_found in
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
      (show_kb_list kbsolved);
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

(** Extract all successful reachability tests from a knowledge base. *)
let checks_reach kb = 
  Base.fold_solved
    (fun x checks ->
       (* debugOutput "TESTER: %s\n" (show_statement x); *)
       match (get_head x) with
         | Predicate("reach", [w]) when is_solved x ->
             Fun ("check_run", [revworld (recipize (namify w) kb)]) :: checks
         | _ -> checks)
    kb []

(** Extract all successful identity tests from a knowledge base. *)
let checks_ridentical kb =
  Base.fold_solved
    (fun x checks ->
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
               (* debugOutput "FROM: %s\nGOT:%s\n\n%!"
                *   (show_statement x) (show_term resulting_test); *)
               resulting_test :: checks
  	    | _ -> checks)
    kb []

(** Extract all successful tests from a (saturated) knowledge base. *)
let checks kb  =
  List.append (checks_reach kb) (checks_ridentical kb)

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
