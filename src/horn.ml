(** Manipulating clauses and saturating knowledge base *)
open Types
open Util
open Term
open Base
open Process
open Dag

(** {1 Saturation procedure}*)

(** {2 Basic functions on statements }*)

let statement_f0 =
  let binder = ref Master in
  let rx1 = Var({status=binder;n=0}) in
  let rx2 = Var({status=binder;n=1}) in
  let tx1 = Var({status=binder;n=2}) in
  let tx2 = Var({status=binder;n=3}) in
     { null_raw_statement with
       binder = binder; 
       nbvars = 4; 
       head=Knows(Fun({id=Plus;has_variables=true},[rx1;rx2]),Fun({id=Plus;has_variables=true},[tx1;tx2]));
       body=[ {loc=empty_loc;recipe = rx1; term = tx1; marked = false};
              {loc=empty_loc;recipe = rx2; term = tx2; marked = false }];
     }

let statement_f1 =
  let binder = ref Master in
  let rx1 = Var({status=binder;n=0}) in
  let rx2 = Var({status=binder;n=1}) in
  let tx1 = Var({status=binder;n=2}) in
  let tx2 = Var({status=binder;n=3}) in
     { null_raw_statement with
       binder = binder; 
       nbvars = 4; 
       head=Knows(Fun({id=Plus;has_variables=true},[rx1;rx2]),tx2);
       body=[ {loc=empty_loc;recipe = rx1; term = tx1; marked=true};
              {loc=empty_loc;recipe = rx2; term = Fun({id=Plus;has_variables=true},[tx1;tx2]); marked = true }];
     }

let statement_f2 =
  let binder = ref Master in
  let rx1 = Var({status=binder;n=0}) in
  let rx2 = Var({status=binder;n=1}) in
  let tx1 = Var({status=binder;n=2}) in
  let tx2 = Var({status=binder;n=3}) in
  let tx3 = Var({status=binder;n=4}) in
     { null_raw_statement with
       binder = binder; 
       nbvars = 5; 
       head=Knows(Fun({id=Plus;has_variables=true},[rx1;rx2]),Fun({id=Plus;has_variables=true},[tx1;tx2]));
       body=[ {loc=empty_loc;recipe = rx1; term = Fun({id=Plus;has_variables=true},[tx1;tx3]); marked=true};
              {loc=empty_loc;recipe = rx2; term = Fun({id=Plus;has_variables=true},[tx3;tx2]); marked =true}];
     }
 
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
  
let is_test_st st = 
  match st.head with
  | Tests(_) -> true
  | _ -> false
  
let is_solved_atom a =
  if not (is_var a.recipe) then false else ( 
  if a.marked 
  then is_var a.term 
  else is_sum_term a.term )

let is_solved st = 
  List.for_all
    is_solved_atom st.body
    
(*let find_unsolved st = 
  match List.find_opt (fun a -> not (is_solved_atom a)) st.body  with
  | Some a -> a
  | None -> Printf.printf "%s" (show_raw_statement st); assert false*)
  
(* Extract an unsolved atom from a statement, if possible without a plus or at least a marked one *)  
let rec find_unsolved best body =
  match body with
  | [] -> (match best with
    | None -> Printf.printf "Looking for unsolved atom of a solved statement\n"; assert false
    | Some a -> a)
  | a :: body -> if is_solved_atom a then find_unsolved best body else 
    (match a.term with
    | Fun({id = Plus},[l;r]) -> find_unsolved (if a.marked || best = None then Some a else best) body
    | _ -> a)
    
let find_unsolved st = find_unsolved None st.body
  
let rec explode_term t =
    match t with
    | Fun({id = Plus},[l;r]) -> 
      let (v1,t1) = explode_term l in 
      let (v2,t2) = explode_term r in 
      (v1@v2,t1@t2)
    | Var(x) -> ([t],[])
    | Fun(f,l)-> ([],[Fun(f,l)])

let rec vars_of_atom = function
  | Knows( r , t) -> vars_of_term_list [r;t]
  | Reach | ReachTest _ -> []
  | Identical(r1,r2) -> vars_of_term_list [r1;r2]
  | Tests(_) -> assert false
  | Unreachable -> []

let get_head_recipe = function 
  | Knows( r, _) -> r
  | _ -> assert(false)

let get_head_term = function 
  | Knows(  _, t) -> t
  | _ -> assert(false)


(** {2  Decompose a sum of variables into sum of body term } *)

exception Not_a_linear_combination

let xor_var v1 v2 = list_diff (v1 @ v2) (list_intersect v1 v2)
  
let remove_rows var recip vars rows =
  List.fold_right (fun (x,recipe,var_lst) (var,recipe',vars') -> 
    if List.mem x vars 
    then (var,xor_var recipe' recipe, xor_var vars' var_lst )
    else (var,recipe',vars')
    ) rows (var,recip,vars)

let rec find_var x body rows  =
  match body with
  | [] -> raise Not_a_linear_combination
  | b :: body -> let vars = vars_of_term b.term in
    if List.mem x vars 
    then 
      let row = (remove_rows x [b.recipe] vars rows)  in
      (row,b)
    else
      find_var x body rows 
  
let rec find_xor_sum vars body rows =
  (*Printf.printf "\nvars: ";
  List.iter (fun v -> Printf.printf "%s" (show_varId v)) vars;*)
  match vars with
  | [] -> []
  | x :: _ -> 
    let (v,r,vs), b = find_var x body rows in
    (*Printf.printf "new row : %s=%s,%s, " (show_varId v)(show_term_list r)"";
    List.iter (fun x -> Printf.printf "%s " (show_varId x))vs;*)
    xor_var r (find_xor_sum (xor_var vars vs) (List.filter (fun b' -> b != b') body) ((v,r,vs)::rows))
    
let get_recipe_for_sum sum_var st =
  let var = List.map (fun x -> unbox_var x) sum_var in
  Rewriting.recompose_term (find_xor_sum var st.body [])


(** {2 Replacing deduction statements by simpler ones }*)  
  
(* for conseq: try all statement until one fit*)
exception Not_a_consequence
exception Bad_World
exception Restricted_World
exception Bad_case

(** [first f l e] attempts to call [f] on each element of the list,
    in order, and returns the result of the first call that succeeds.
    If all calls fail, re-raise the exception raised by the last call. *)
let first kb f =
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
   first_list kb.children f
   with
   | Bad_World -> (
      try f statement_f0 with
      Bad_case -> raise Not_a_consequence)
      
let rec first_sigma sigma_lst f =
  match sigma_lst with
  | [] -> raise Bad_case
  | s :: ss -> ( try f s with Bad_case | Bad_World -> first_sigma ss f)

(** [inst_w_t my_head head_kb exc] attempts to match the world and term
  * arguments of two predicates of arity three, and raises [exc] upon
  * failure. This is used for checking if a clause is in conseq. *)
let inst_w_t my_st kb_st =
  let myt = get_head_term my_st.head in
  let tkb = get_head_term kb_st.head in
  (* debugOutput "Matching %s against %s\n%!" (show_term t1) (show_term t2); *)
  if not (strict_subset kb_st.dag my_st.dag) 
    || not (Inputs.subset_choices kb_st.choices my_st.choices)
  then begin (*Printf.printf "@";*) raise Bad_World end 
  else
    let sigmas = Inputs.csm true my_st.binder kb_st.inputs my_st.inputs in
    if sigmas = [] then raise Bad_World;
    List.concat (List.map (fun sigma -> Rewriting.csm true my_st.binder [(tkb, myt)] sigma 
     (* try
        let (hard,sigma) = Rewriting.match_ac false [] [(tkb, myt)] sigma in
        (* debugOutput "Result %s\n%!" (show_subst sigma); *)
        if hard <> [] 
        then (
          if be_complete 
          then Maude.acmatchers my_st.binder hard sigma
          else raise Bad_case)
        else
          [ sigma ]
      with
      | Term.Not_matchable -> (*Printf.printf "-";*) raise Bad_case *)
    ) sigmas)


(** Formatter for printing conseq traces, which are essentially derivations. *)
let rec print_trace chan = function
  | `Axiom ->
      Format.fprintf chan "ax"
  | `Res (st,traces) ->
      Format.fprintf chan "#%s(%a)" (show_raw_statement st) (pp_list print_trace ",") traces

(** Check whether a statement is a consequence of a knowledge base, ie.
    try to find solved statements deriving the same term from the same
    assumptions.
    Raise [Not_a_consequence] if there is no such statement.
    If there is one, return the associated recipe. An identical statement
    will be added to indicate that the two recipes have the same result,
    instead of the new useless deduction statement. *)
let consequence st kb rules = 
  (*if !about_canonization then Printf.printf "Conseq of %s" (show_raw_statement st) ;*)
  (*st.binder := Rule;*)
  let apply_subst_list_atom atom sigma  = 
   Knows(zero, apply_subst atom.term sigma) in
  assert (is_solved st) ;
  let rec aux st kb =
    (*Printf.printf "___%s\n" (show_raw_statement st);*)
    (*st.binder := New;*)
    let t = get_head_term st.head in
    try
          let (var,cst) = explode_term t in
          if cst != [] then raise Not_a_linear_combination
          else
            (* Base case: Axiom rule of conseq *)
          `Axiom, get_recipe_for_sum var st
    with
    | Not_a_linear_combination ->
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
            let sigmas = inst_w_t st x in
            first_sigma sigmas 
              (fun sigma ->
                (*Printf.printf "\nst: %s\n sigma = %s\n" (show_raw_statement x)(show_subst sigma); *)
                let subresults =
                  List.map
                    (fun y ->
                      let trace,r = aux {st with head=(apply_subst_list_atom y sigma) } kb in
                      trace, (unbox_var (y.recipe), r))
                    (x.body)
                in
                (* All variables occurring in the head recipe must occur
                 * in the body, so there is no need to apply [sigma] to
                 * [x], it gets done as part of applying the accumulated
                 * substitution [subst]. *)
                let traces,subst = List.split subresults in
                let hx_subst = apply_subst (get_head_recipe (x.head)) subst in
                (** Check that a term is a normal form. *)
                let is_normal tm rules = Rewriting.equals_ac tm (Rewriting.normalize tm rules) in
                if not (is_normal hx_subst rules) then raise Bad_case ;
                `Res (x,traces), hx_subst
              )
          )
  in
  let trace,r = aux st kb in
    if !about_canonization then
      Format.printf "Conseq derivation for #%s:\nrecipe %s\ntrace %a\n" 
      (show_raw_statement st) (show_term r) print_trace trace ;
    r



(** {2 Knowledge base canonization rules } *)

let rule_shift st = 
  match st.head with
  | Knows( r , (Fun({ id = Plus}, [ l ; t ]) as pl)) -> (
    let var,cst = explode_term pl in
    try
    if var = [] then st else begin
    if !about_canonization then Printf.printf "shift on: %s\n"(show_raw_statement st);
    let recipe = get_recipe_for_sum var st in
    let stt = {st with head = Knows( Fun({id=Plus;has_variables=true},[r;recipe]), Rewriting.recompose_term cst)} in 
    if !about_canonization then Format.printf "shift + on the statement: %s \n" (show_raw_statement stt); 
    stt end
    with
    | Not_a_consequence -> assert false)
  | Knows( r , Var(x)) -> st (* (*Bugguy when no xor*)
    begin let stt = {st with head = 
      Knows(Fun({ id = Plus; has_variables = true},[get_recipe (Var(x)) (st.body); r]), 
        Fun({ id = Zero; has_variables = false},[]))} in 
      if !debug_output 
      then Format.printf "shift 0 on the statement: %s \n" (show_raw_statement stt); 
      stt
    end *)
  | _ -> st 

exception No_Eval
exception Unsound_Statement (* Statement with a premisse which is unsatisfiable *)
  
let rec eval_recipe choices inputs solved_atom term =
  match term with
  | Fun({id=Frame({io = Output(_,t)})},[]) -> eval_recipe choices inputs solved_atom t 
  | Fun({id=InputVar({observable = Public} as l)},[]) -> Inputs.get l inputs
  | Fun({id=InputVar({observable = Hidden} as l)},[]) -> 
    eval_recipe choices inputs solved_atom (
      match (Inputs.get_output_of_input choices l).io with 
      Output(_,t)-> t 
      | _ -> assert false) 
  | Fun(f,args) -> Fun(f,List.map (eval_recipe choices inputs solved_atom) args)
  | Var(x) -> (try 
     (List.find (fun a -> a.recipe = term) solved_atom).term 
    with Not_found -> raise No_Eval )

let simplify_statement st =
  try 
  (*Printf.printf "simplification of %s\n" (show_raw_statement st);*)
  let sigma_repl = Array.make st.nbvars None in
  st.binder := Master;
  let binder = ref New in
  let nbv = ref 0 in
  let body_maker = ref [] in
  let var_recipe_body,other_body = List.partition (fun b -> is_var b.recipe) st.body in
  let other_body = List.filter (fun b -> 
    if LocationSet.cardinal b.loc > 1 then true else 
    try 
    let t = eval_recipe st.choices st.inputs var_recipe_body b.recipe in
    if Rewriting.equals_ac (Rewriting.normalize t (!Parser_functions.rewrite_rules))  b.term then
      false
    else (
      (*Printf.printf "\n%s = %s \n %s%!" (show_term t)(show_term b.term) (show_raw_statement st);*)
      raise Unsound_Statement )
    with
    No_Eval -> true 
  ) other_body in 
    List.iter
      (fun a ->
        List.iter (fun (x : varId) -> 
          if sigma_repl.(x.n) = None
          then (sigma_repl.(x.n) <- Some(Var({n = !nbv ; status = binder})) ;incr nbv);
        ) (vars_of_term a.term);
        let recipe_var = unbox_var a.recipe in
        let t = a.term in
        match List.find_opt (fun (a',lset) -> Rewriting.equals_ac t (a'.term)) !body_maker with
        | Some (b,locs) -> 
          let better = (unbox_var b.recipe).n in
          if !about_canonization then
              Printf.printf "Atom %s removed due to %s\n" (show_body_atom a) (show_body_atom b);
          assert (sigma_repl.(better) <> None) ; 
          sigma_repl.(recipe_var.n) <- sigma_repl.(better); 
          locs := first_actions_among st.dag (LocationSet.union !locs a.loc) 
        | None ->
            if sigma_repl.(recipe_var.n) = None 
            then (
              sigma_repl.(recipe_var.n) <- Some(Var({n = !nbv ; status = binder})) ;incr nbv) 
            else assert false;
            body_maker := (a , ref a.loc ) :: !body_maker
         )
       (List.sort (fun x y -> compare_loc_set x.loc y.loc) var_recipe_body)
  ;
  let body = other_body @ List.map (fun (b,locset) -> {b with loc = !locset}) !body_maker in
  let sigma = { 
    binder = binder; 
    master =  Array.map (function Some x -> x | None -> zero) sigma_repl;
    slave = Array.make 0 zero;
    nbvars = !nbv;
  } in
  let r = apply_subst_statement { st with body = body; } sigma in
  (* Printf.printf "result: %s\n" (show_raw_statement r); *)
  (*st.binder := New;*)
  (sigma,r)
  with 
    Invalid_argument _ -> 
      Printf.eprintf "Error when simplify_statement %s \n" (show_raw_statement st);
      exit 6
    

let canonical_form statement =
  let _,statement = simplify_statement statement in
  let statement = 
    if is_deduction_st statement && is_solved statement 
    then
        rule_shift statement
    else 
        statement in
  (*if !about_canonization then Format.printf "Canonized: %s\n" (show_raw_statement statement) ;*)
  statement


let is_identity_of_theory st =
  match st.head with
  | Identical(s,t) -> Dag.is_empty st.dag.rel || (!Parser_functions.use_xor && s = t) (* Slow down too much *) 
  | _ -> false


let normalize_identical f = 
  if not !Parser_functions.use_xor then f else
    match f.head with
      | Identical(t1, (Fun({id=Plus},_) as t2)) 
      | Identical((Fun({id=Plus},_) as t1), t2) -> {f with head = Identical(Rewriting.normalize (Fun({id=Plus;has_variables=true},[t1;t2])) [],zero)}
      | Identical(z,t) when z = zero -> {f with head = Identical(t,zero)}
      | _ -> f

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
  let f = {f with recipes = Inputs.renormalize f.recipes; inputs = (if !Parser_functions.use_xor then Inputs.renormalize f.inputs else f.inputs)} in
  match f.head with 
  | Reach | ReachTest _ | Unreachable -> Some f
  | Knows(r,t) -> 
    let t' = Rewriting.normalize t (!Parser_functions.rewrite_rules) in 
    if not (Rewriting.equals_ac t t')
    then begin (*Printf.printf "hea: %s\n" (show_raw_statement f); *)
      None (*Some {f with head = Reach}*) end (* A knows is also a reach statement but the reach statement has already been processed *)
    else Some {f with head = Knows(Rewriting.normalize r (!Parser_functions.rewrite_rules),t)}
  | Identical(r,r') -> Some {f with 
      head = Identical(Rewriting.normalize r (!Parser_functions.rewrite_rules),
            Rewriting.normalize r' (!Parser_functions.rewrite_rules))}
  | Tests(hd) -> Some {f with 
      head = Tests({
        hd with 
        equalities= 
          EqualitiesSet.map (fun (r,r') -> Rewriting.normalize r (!Parser_functions.rewrite_rules),
            Rewriting.normalize r' (!Parser_functions.rewrite_rules))hd.equalities;
        disequalities = EqualitiesSet.map (fun (r,r') -> Rewriting.normalize r (!Parser_functions.rewrite_rules),
            Rewriting.normalize r' (!Parser_functions.rewrite_rules)) hd.disequalities })}


(*let remove_marking f = {f with body = List.map (fun a -> {a with marked = false}) f.body }*)

(** Update a knowledge base with a new statement. This involves canonizing
  * the statement, checking whether it already belongs to the consequences
  * of the base, and actually inserting the statement or a variant of it. *)
let update kb f =
  let rules = ! Parser_functions.rewrite_rules in
  (* Do not use [is_normal], in order to replace [f] by its normalization.
   * It is equal modulo AC but will additionnally be normalized wrt some
   * order, which eases reading and gives / may give more power to non-AC
   * tests, eg. in consequence. *)
  let f = normalize_identical f in (* do nothing *)
  try
  let f = canonical_form f in
  match normalize_new_statement f
  with 
    None -> None 
  | Some fc ->
  if is_identity_of_theory fc then None else
  if is_deduction_st fc && is_solved fc then
    try
      let recipe = consequence fc kb.solved_deduction rules in
      let newhead =
        Identical(get_head_recipe fc.head, recipe)
      in
      let newclause = normalize_identical { fc with head = newhead } in
        if !about_canonization then Format.printf 
          "Useless: %s\n Original form: %s\n Replaced by: %s\n\n%!"
          (show_raw_statement fc)(show_raw_statement f)(show_raw_statement newclause);
        if not (is_identity_of_theory newclause) then
          Some newclause
        else None
    with Not_a_consequence ->
      Some fc
  else
    Some fc
  with Unsound_Statement -> None


    

(** {2 Resolution steps} *)
    
    

let resolution_plus master =
  let atom = find_unsolved master in
  (* Forbid resolution against f0+ clause if selected atom is marked. *)
  if atom.marked then [] else
  (* Do all unifications in the rule *)
  let binder = ref Slave in
  let rx1 = { n = 0 ; status = binder; } in
  let rx2 = { n = 1 ; status = binder; } in
  let tx1 = { n = 2 ; status = binder; } in
  let tx2 = { n = 3 ; status = binder; } in
  let sigma = sigma_maker_init master.nbvars 4 in
  match explode_term atom.term with
  | _, rigid :: _ -> 
 (* (* split a plus into a variables' list and a rigid factors' list *)
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
	(* build a list of all possible cases of unification *)
	let sigmas =
		(*Predicate("knows",[Var(w);Fun("plus",[Var(x1);Var(x2)]);Fun("plus",[Var(x11);Var(x12)])]))*)
			List.filter (fun x -> x <> []) (
			match explode_term t with
			| ([],a1::a2::l) -> List.fold_left 
				(fun sig_mini (l1,l2) -> 
					if l1 = [] || l2 = [] 
					then sig_mini
					else [(x11 , sum_from l1 );(x12 , sum_from l2)]::sig_mini)
				[] (exponential (a2::l) [([a1],[])])
			| ([],l) -> []
			| ([x],a::l) -> 
				if List.mem x ( vars_of_term_list (a::l)) 
				then failwith "Unexpected term (TODO)"
				else addvar x1 x2 rx x11 x12 x (exponential l [([a],[])])
			| _ ->  failwith "loop" )
  in *)
  let sigmas = List.concat 
      (List.map (fun sigm -> Rewriting.csu_ac [(atom.term,Fun({id = Plus; has_variables = true},[Var(tx1);Var(tx2)]) )] sigm) 
        (Rewriting.csu_xor [(atom.recipe, Fun({id = Plus; has_variables = true},[Var(rx1);Var(rx2)]))] sigma))
   (* Rewriting.csu [
      (atom.term,Fun({id = Plus; has_variables = true},[Var(tx1);Var(tx2)]) );
      (atom.recipe, Fun({id = Plus; has_variables = true},[Var(rx1);Var(rx2)]))] sigma *)
  in
      (* Create results *)
      List.map
        (fun sigma ->
           let sigma = Rewriting.pack sigma in
           let t1 = Rewriting.apply_subst_term (Var (tx1)) sigma in
           let t2 = Rewriting.apply_subst_term (Var (tx2)) sigma in
           let _, t1s = explode_term t1 in
           let rigid = Rewriting.apply_subst_term rigid sigma in
           let t1_rigid = List.exists (fun t -> t = rigid) t1s (* not (is_sum_term t1)*) in
           let result =
           {
           binder = sigma.binder ;
           nbvars = sigma.nbvars ;
           dag = master.dag ;
           inputs = Inputs.map (fun t -> Rewriting.apply_subst_term t sigma) master.inputs;
           recipes = Inputs.map (fun t -> Rewriting.apply_subst_term t sigma) master.recipes;
           head = apply_subst_pred master.head sigma ;
           body = {loc = atom.loc ; marked = t1_rigid ; recipe = Rewriting.apply_subst_term (Var (rx1)) sigma ; term = t1 }
               :: {loc = atom.loc ; marked = not (t1_rigid) ; recipe = Rewriting.apply_subst_term (Var (rx2)) sigma ; term = t2}
               :: (List.map (fun x -> { x with recipe = Rewriting.apply_subst_term x.recipe sigma; term = Rewriting.apply_subst_term x.term sigma} )
                 (List.filter (fun x -> (x <> atom)) master.body));
           choices = master.choices;
           involved_copies = master.involved_copies;
           }
           in (*
             if !debug_output then Format.printf "RESO+: %s\n\n"
               (show_raw_statement result);*)
           result)
        sigmas
  | _ -> assert false

let is_tuple term =
  match term with
  | Fun ({id = Tuple _},_) -> true
  | _ -> false
  
(** [resolution sigma choices dag master slave] attempts to perform a resolution step
    between clauses [master] and [slave] by matching the head of [slave]
    against the first premise of [master] which is not solved.
    sigma is the partial unification of the recipes/inputs only, 
    choices the merge of choices and dag the merge of dags 
    which have been computed in extra_resolution
    This corresponds to the "Resolution" rule in the paper.
    Return the list of newly generated clauses. *)
let resolution sigma choices dag master slave =
   let atom = find_unsolved master in
   (* Printf.printf "Slave: %s\n Selected atom %s\n" (show_raw_statement slave)(show_body_atom atom);*)
   if atom.loc != empty_loc && is_tuple atom.term && not (is_tuple (get_head_recipe slave.head)) then [] else 
   begin try
   let dag =
     if atom.loc != empty_loc 
     then (
      let new_dag = merge dag (put_set_at_end slave.dag atom.loc) in
       (*Printf.printf "new dag %s\n" (show_dag new_dag);*)
       if is_cyclic new_dag 
       then begin (*Printf.printf "cyclic dag \n";*) raise Impossible end;
       new_dag )
     else dag in
   let sigmas = List.concat 
      (List.map (fun sigm -> Rewriting.csu_ac [(atom.term, get_head_term slave.head)] sigm) 
        (Rewriting.csu_xor [(atom.recipe, get_head_recipe slave.head)] sigma))
   (* Rewriting.csu [
      (atom.term, get_head_term slave.head);
      (atom.recipe, get_head_recipe slave.head)] sigma *)(*recipes should be modulo xor*)
    in
   (* Printf.printf "Unifiers %d\n" (List.length sigmas);*)
      (* Create results *)
    List.map
      (fun sigma ->
          let sigma = Rewriting.pack sigma in
          if !debug_saturation then Printf.printf "Found: %s\n" (show_substitution sigma);
          let result =
             let body =
               List.map (fun x -> {
               loc = 
                if empty_loc = x.loc 
                then atom.loc 
                else x.loc ; 
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
           recipes = Inputs.merge_recipes sigma master.recipes slave.recipes;
           head = (apply_subst_pred master.head sigma) ;
           body = body ;
           involved_copies = BangSet.union master.involved_copies slave.involved_copies ; }
           in 
           if !debug_saturation then Format.printf "RESO: %s\n\n"
               (show_raw_statement result);
           result)
        sigmas 
  with Impossible -> []
  end
 
(** [equation sigma choices dag fa fb] takes two solved clauses and, when they are solved clauses
  * concluding "knows", attempts to combine them: if the terms and worlds can be
  * unified, generate a clause concluding that the recipes are "identical".
  * This corresponds to the "Equation" rule in the paper.
  * It returns [] if it fails to produce any new clause. *)
let equation sigma choices dag fa fb =
  match fa.head, fb.head with
    | (Knows( r, t), Knows( rp, tp)) -> begin
      if !debug_saturation then Format.printf "Equation:\n %s\n %s\n%!"
         (show_raw_statement fa) (show_raw_statement fb) ;
      if (Rewriting.equals_ac r rp) then [] else
      let sigmas = Rewriting.csu_ac [(t,tp)] sigma in
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
           recipes = Inputs.merge_recipes sigma fa.recipes fb.recipes;
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

          
          
(** {2 Trace generation} *)



let rec concretize inputs term =
   match term with
   | Fun({id=InputVar(l)},[]) -> Inputs.get l inputs
   | Fun(f,args) -> Fun(f,List.map (concretize inputs) args)
   | _ -> term  

(** Compute statements which express private chan communication from two statments ending at a private input and output *) 
let rec hidden_chan_statement kb  (loc_input , term_input ,ineq_input,st_input,pr_input) (loc_output,  term_output,ineq_output,st_output,pr_output) solved_parent unsolved_parent test_parent  = 
  if !about_seed then Printf.printf "Computing hidden_chan_statement\n -link %d <-> %d\n -input %s \n -output %s\n%!" loc_input.p loc_output.p (show_raw_statement st_input)(show_raw_statement st_output);
  match term_input,term_output with
  | None, Some term_output -> 
  (
  match Inputs.merge_choices_add_link st_output.choices st_input.choices loc_output loc_input with
    None -> if !about_seed then Printf.printf "incompatible choices\n"; ()
  | Some choices ->
  let dag = merge st_output.dag st_input.dag in
  if is_cyclic dag then (if !about_seed then Printf.printf "incompatible dag\n"; () )
  else (
  st_input.binder := Slave;
  st_output.binder := Master;
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
  else (
  let sigma = sigma_maker_init st_output.nbvars st_input.nbvars in
  (* Printf.printf "Computing hiden_chan_statement\n -link %d <-> %d\n" loc_input.p loc_output.p; *)
  let sigmas = List.concat (List.map 
      (fun sigm -> Inputs.csu sigm st_output.inputs st_input.inputs) 
      (Inputs.csu_recipes sigma st_output.recipes st_input.recipes))
   (* Inputs.csu sigma st_output.inputs st_input.inputs *) in
  if sigmas = [] then ()
  else (
  let dag = put_at_end (put_at_end dag loc_input) loc_output in
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
      recipes = Inputs.merge_recipes sigma st_output.recipes st_input.recipes;
      head = Reach;
      body = body ;
      involved_copies = BangSet.union st_output.involved_copies st_input.involved_copies ; }
    in
    let ineqs = List.map (fun (s,t) -> (Rewriting.apply_subst_term s sigma,Rewriting.apply_subst_term t sigma)) (ineq_output @  ineq_input) in
    trace_statements kb ineqs solved_parent unsolved_parent test_parent pr_output st ;
    let process_input = Process.apply_subst_process loc_input term_output pr_input in
    (*Printf.printf "subst %d by %s process : %s\n" loc_input.p (show_term term_output) (show_process_start 3 process_input);*)
    trace_statements kb ineqs solved_parent unsolved_parent test_parent process_input st 
  ) sigmas )))
  )
  | _ -> assert false
 
(** The seed is computed incrementally: this function compute new statements from the trace ([process]) *) 
and trace_statements kb ineqs solved_parent unsolved_parent test_parent process st =
  let rec add_ineqs_statements ineqs idsigma st =
  match ineqs with
  | [] -> true
  | (s,t)::q -> begin
    let st = apply_subst_statement {st with head = Unreachable} idsigma in
    st.binder := Master;
    let sterm = concretize st.inputs s in
    let tterm = concretize st.inputs t in 
    let unifiers = Rewriting.unifiers st.nbvars sterm tterm (! Parser_functions.rewrite_rules) in 
    (* match unifiers with
    | [subst ] -> 
        if Rewriting.is_identity_master subst  st.nbvars
        then false (* This reach is unconditionally unreachable: just remove it and don't add unreach predicate *)
        else (add_statement kb solved_parent unsolved_parent test_parent None (apply_subst_statement st subst);true)
    | _ ->*)
    List.iter (fun subst -> add_statement kb solved_parent unsolved_parent test_parent None (apply_subst_statement st subst)) unifiers; true
    end
  in
  if !about_seed then 
    Format.printf "\nComputing seed statement for {%s}\n with %s \n%!"  
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
      (*let next_dag = put_at_end st.dag loc in*)
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
      let next_dag = put_at_end st.dag loc in
      let identity_sigma = Rewriting.identity_subst st.nbvars in
      (*let binder = identity_sigma.binder in*)
      st.binder := Master;
      let st = apply_subst_statement st identity_sigma in
      let st = { st with
        (*binder = binder; *)
        dag = next_dag ;
        head = Reach;
        } in
      begin 
      if add_ineqs_statements ineqs identity_sigma st 
      then add_statement kb solved_parent unsolved_parent test_parent (Some (ParallelP([SeqP(OutputA(loc, t), pr);pr]))) st
      end
    | SeqP(Input({observable = Public} as loc), pr) -> 
      let next_dag = put_at_end st.dag loc in
      let identity_sigma = Rewriting.identity_subst (st.nbvars + 2) in
      let binder = identity_sigma.binder in
      st.binder := Master;
      let st = apply_subst_statement st identity_sigma in
      let new_var = {n = st.nbvars - 2; status = binder} in
      let new_recipe = {n = st.nbvars - 1; status = binder} in
      let next_inputs = Inputs.add_input loc new_var st.inputs in
      let next_recipes = Inputs.add_input loc new_recipe st.recipes in
      let premisse = {
        loc = LocationSet.singleton loc; 
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
      if add_ineqs_statements ineqs identity_sigma st ;
      then add_statement kb solved_parent unsolved_parent test_parent (Some pr) st end
    | SeqP(Input({io = Input({visibility = Hidden} as chan)} as loc), pr) -> (
      begin match ChanMap.find_opt { c= chan; io = Out; ph =loc.phase} kb.hidden_chans with
      | None -> ()
      | Some chans -> 
        List.iter (fun stout -> 
          hidden_chan_statement kb (loc,None,ineqs,st,pr) stout solved_parent unsolved_parent test_parent) chans end;
      let ckey = { c = chan; io = In; ph = loc.phase} in
      if ! about_seed then Printf.printf "Inserting %s for %d\n" (show_chan_key ckey)loc.p;
      kb.hidden_chans <- ChanMap.add ckey
        ((loc,None,ineqs,st,pr):: ( try 
          ChanMap.find ckey kb.hidden_chans 
          with Not_found -> []))
        kb.hidden_chans )
    | SeqP(Output({io = Output({visibility = Hidden} as chan, _)} as loc, t), pr) -> ( 
      begin match ChanMap.find_opt { c= chan; io = In; ph =loc.phase} kb.hidden_chans with
        | None -> ()
        | Some chans ->
          List.iter (fun stin -> 
            hidden_chan_statement kb stin (loc,Some t,ineqs,st,pr) solved_parent unsolved_parent test_parent) chans end;
      let ckey = { c = chan; io = Out; ph = loc.phase} in
      if ! about_seed then Printf.printf "Inserting %s for %d\n" (show_chan_key ckey) loc.p;
      kb.hidden_chans <- ChanMap.add  ckey
        ((loc,Some t,ineqs,st,pr):: ( try 
          ChanMap.find ckey kb.hidden_chans 
          with Not_found -> []))
        kb.hidden_chans )
    | SeqP(Input(loc), pr)
    | SeqP(Output(loc,_), pr) ->
      assert false
    | SeqP(Test(s, t), pr) ->
      st.binder := Master;
      let sterm = concretize st.inputs s in
      let tterm = concretize st.inputs t in 
      if !about_seed then Printf.printf "Test:  %s == %s\n" (show_term sterm) (show_term tterm);
      let unifiers = Rewriting.unifiers st.nbvars sterm tterm (! Parser_functions.rewrite_rules) in 
      List.iter (fun subst -> st.binder := Master; 
        let new_st = { (apply_subst_statement st subst) with head = ReachTest(ineqs)} in
        add_statement kb solved_parent unsolved_parent test_parent (Some pr) new_st
        (*trace_statements kb ineqs solved_parent unsolved_parent test_parent pr new_st*)) unifiers
    | SeqP(TestInequal(s, t), pr) ->
      (*Printf.printf "inequal %s %s\n" (show_term s)(show_term t);*)
      if s <> t then 
       trace_statements kb ((s,t)::ineqs) solved_parent unsolved_parent test_parent pr st
    | CallP(loc, j, procId, args, chans) -> 
      (*let args = Array.map (concretize st.inputs) args in*)
      for i = 1 to j do
      (* if !about_seed then Format.printf "Adding %d-th copy of %s \n%!" i procId.name; *)
      let pr = expand_call loc i procId args chans in
      trace_statements kb ineqs solved_parent unsolved_parent test_parent pr {st with involved_copies = BangSet.add (loc,i) st.involved_copies}
      done
   (* | _ -> invalid_arg ("todo")*)

(** Take a solved statement and update the knowledge base with it *)
and add_statement kb solved_parent unsolved_parent test_parent process st = 
  if !debug_saturation || ! about_canonization then Format.printf "Adding statement %s \n%!" (show_raw_statement st);
  match update kb st with
  | None -> if ! about_canonization then Printf.printf "Statement is dropped\n";()
  | Some new_st -> begin 
     if ! about_canonization then Printf.printf "Normalized statement: %s\n" (show_raw_statement new_st);
     let is_solved_st = is_solved new_st in
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
     then Printf.printf "Addition of %s \n unsolved: %d solved: %d test: %d process: %s\n\n %!" 
      (show_statement "" st)(unsolved_parent.id)(solved_parent.id)(test_parent.id)
      (match process with None -> "none" | Some pr -> show_process_start 3 pr)
     else if !about_progress && kb.next_id mod (match st.st.head with Tests(_) -> 5000 | _ -> 500) = 0 then Printf.printf "Addition of %s \n%!" (show_statement "" st));
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
         | ReachTest(ineqs) -> begin
            match process with 
            | None -> assert false
            | Some process -> trace_statements kb ineqs solved_parent unsolved_parent test_parent process st.st end
         | Tests(_) -> kb.temporary_merge_test_result <- st :: kb.temporary_merge_test_result
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
       dag = empty; 
       choices = Inputs.new_choices; 
       inputs = Inputs.new_inputs; 
       recipes = Inputs.new_inputs; 
       head=Knows(Fun({id=fname;has_variables=true},rv),term_head);
       body=List.map (function (r,t) -> {loc=empty_loc;recipe = r; term = t; marked=false}) variables;
       involved_copies = BangSet.empty;
     } in
   let v = Rewriting.variants (2*arity) term_head (! Parser_functions.rewrite_rules) in
      List.iter (fun (_,sigma) -> 
        let st = apply_subst_statement statement sigma in
        let head = match st.head with
        | Knows(r,t) -> Knows(r, Rewriting.normalize t (! Parser_functions.rewrite_rules))
        | _ -> assert false  in
        if !about_seed then 
          Format.printf "- variant for theory of function %s : %s\n%!" 
            (show_term (Fun({id=fname;has_variables=true},[]))) (show_substitution sigma);
        add_statement kb kb.solved_deduction kb.not_solved kb.rid_solved None
        {st with head = head} ) v

(** {2 Saturation exploration}*)    

let extra_resolution kb solved unsolved =
  if !debug_saturation then Printf.printf "Try resolution between #%d and #%d : " solved.id unsolved.id;
  (* Printf.printf "%s \n %s\n" (show_raw_statement solved.st) (show_raw_statement unsolved.st); *)
  match Inputs.merge_choices unsolved.st.choices solved.st.choices with
    None -> if !debug_saturation then Printf.printf " incompatible choices\n"; false
  | Some merged_choice ->
  let merged_dag = merge unsolved.st.dag solved.st.dag in
  if is_cyclic merged_dag then (if !debug_saturation then Printf.printf " cyclic dag\n"; false) else
  let sigma = sigma_maker_init unsolved.st.nbvars solved.st.nbvars in
  solved.st.binder:= Slave;
  unsolved.st.binder:= Master;
  let sigmas = match Inputs.csu_recipes sigma solved.st.recipes unsolved.st.recipes with
  | [] -> []
  | [s] -> Inputs.csu s solved.st.inputs unsolved.st.inputs
  | lst -> List.concat(List.rev_map (fun s -> Inputs.csu s solved.st.inputs unsolved.st.inputs) lst) in 
  if sigmas = [] then (if !debug_saturation then Printf.printf " recipes cannot be unified \n"; false )
  else begin 
    if !debug_saturation then Printf.printf " compatible worlds\n";
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
  let merged_dag = merge solved1.st.dag solved2.st.dag in
  if is_cyclic merged_dag then false else
  let sigma = sigma_maker_init solved1.st.nbvars solved2.st.nbvars in
  solved2.st.binder:= Slave;
  solved1.st.binder:= Master;
  let sigmas = match Inputs.csu_recipes sigma solved1.st.recipes solved2.st.recipes with
  | [] -> []
  | [s] -> Inputs.csu s solved1.st.inputs solved2.st.inputs
  | lst -> (* List.iter (fun s -> Printf.printf "%s\n" (show_subst_maker s)) lst; *)
     assert false in 
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

(** [merge_sat kb] performs the saturation of kb where an unsolved test have been added, used during the algorithm in tests.ml *)      
let merge_sat kb = 
  while not (Queue.is_empty(kb.ns_todo)) do
    let unsolved = Queue.take(kb.ns_todo) in
    unsolved.st.binder := Master;
    if !debug_saturation then Printf.printf "Start merge resolutions of #%d\n" unsolved.id;
    if !Parser_functions.use_xor then 
    List.iter 
      (fun st -> add_statement kb kb.solved_deduction unsolved 
          unsolved.test_parent unsolved.process st )
      (resolution_plus unsolved.st);
    List.iter (fun solved -> process_resolution_new_unsolved kb solved unsolved) kb.solved_deduction.children
  done
   
(** The big saturation algorithm on [procId] *)   
let saturate procId  =
  let kb = Base.new_base () in
  List.iter (fun f -> theory_statements kb (Regular(f)) f.arity) !Parser_functions.functions_list;
  List.iter (fun i -> 
    theory_statements kb (Tuple(i)) i; 
    for j = 0 to i - 1 do theory_statements kb (Projection(j,i)) 1 done ) !Parser_functions.tuple_arity;
  theory_statements kb Zero 0;
  add_statement kb kb.solved_deduction kb.not_solved kb.rid_solved None statement_f1;
  add_statement kb kb.solved_deduction kb.not_solved kb.rid_solved None statement_f2;
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
    else begin 
      let unsolved = Queue.take(kb.ns_todo) in
      if !debug_saturation then Printf.printf "Start resolutions of #%d\n%!" unsolved.id;
      if !Parser_functions.use_xor then
      List.iter 
        (fun st -> add_statement kb kb.solved_deduction unsolved 
          unsolved.test_parent unsolved.process st )
        (resolution_plus unsolved.st);
      List.iter (fun solved -> process_resolution_new_unsolved kb solved unsolved) kb.solved_deduction.children
    end
  done ;
  (ind,kb)  
