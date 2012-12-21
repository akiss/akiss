(** Variants and unification modulo R
  *
  * Variants modulo AC are not computed. This will eventually be done by Maude.
  *
  * Unification modulo R is also provided in this module and used when
  * building seed statements. We need this even for basic tests so it has been
  * adapted in a naive (maybe incomplete) way by replacing syntactic unification
  * with AC unification everywhere. *)

open Util;;
open Term;;

let mgu = Cime.mgu;;

type position = int list;;

type mask =
  | VarMask
  | FunMask of mask list
;;

let rec mask_of = function
  | Var(_) -> VarMask
  | Fun(_, tl) -> FunMask (trmap mask_of tl)
;;

let rec prepend n pl =
  trmap (function x -> n :: x) pl
;;

let rec init_pos = function
  | Var(_) -> []
  | Fun(_, tl) -> [] :: (trconcat (List.map2 prepend 
				  (create_consecutive 0 (List.length tl))
				  (trmap init_pos tl)))
;;

let rec at_position t p =
  match p with
    | [] -> t
    | i :: rp -> (
	match t with
	  | Var(_) -> invalid_arg("at_position")
	  | Fun(f, tl) -> at_position (List.nth tl i) rp
      )
;;

let rec repl_position t p s =
  match p with
    | [] -> s
    | i :: rp -> (
	match t with
	  | Var(_) -> invalid_arg("at_position")
	  | Fun(f, tl) -> Fun(f, List.map2
				(function x -> function y ->
				   if x == i then
				     repl_position y rp s
				   else
				     y)
				(create_consecutive 0 (List.length tl))
				tl)
      )
;;

let fresh_copy (l, r) =
  let vars = vars_of_term_list [l; r] in
  let new_vars = trmap (function x -> fresh_variable ()) vars in
  let sigma = List.combine vars (trmap (function x -> (Var(x))) new_vars) in
  (apply_subst l sigma, apply_subst r sigma)
;;

let rec one_rule old_sigma t p (lhs, rhs) = 
  let (l, r) = fresh_copy (lhs, rhs) in
  try
    let sigma = mgu (at_position t p) l in
    [(apply_subst (repl_position t p r) sigma, compose old_sigma sigma)]
  with Not_unifiable -> []
;;

let rec all_rules old_sigma t p rules =
    trconcat (trmap (function x -> one_rule old_sigma t p x) rules)
;;

let rec is_prefix small big =
  match (small, big) with
    | ([], _) -> true
    | (x :: rs, y :: rb) when x = y -> is_prefix rs rb
    | _ -> false
;;

let rec down positions p =
  List.filter (function x -> not (is_prefix p x)) positions
;;

(* let rec is_strict_prefix small big = *)
(*   match (small, big) with *)
(*   | ([], []) -> false *)
(*   | ([], _) -> true *)
(*   | (x :: rs, y :: rb) when x = y -> is_strict_prefix rs rb *)
(*   | _ -> false *)
(* ;; *)

(* let has_strict_suffix p positions = *)
(*   List.exists (function x -> is_strict_prefix p x) positions *)
(* ;; *)

(* let downmost positions =  *)
(*   List.filter (function x -> not (has_strict_suffix x positions)) positions *)
(* ;; *)

let one_step (t, sigma, positions) rules =
  trconcat (trmap (function x -> 
			   trmap (function (z, y) -> (z, y, (down positions x)))
			     (all_rules sigma t x rules))
		 positions)
;;

let iterate_once configuration rules =
  trconcat (trmap (function x -> one_step x rules) configuration)
;;

let is_renaming sigma = 
  if List.exists (
    function (x, y) ->
      match y with
      | (Var _) -> false
      | _ -> true) sigma then
    false
  else
    let n = List.length sigma in
    let m = List.length (unique (trmap (function (_, y) -> y) sigma)) in
    if n = m then
      true
    else
      false
;;

let rec feed n positions = 
  trconcat (trmap
	      (function p ->
		match p with
		| x :: y ->
		  if x = n then
		    [y]
		  else 
		    []
		|  [] -> []
	      )
	      positions)
;;

let rec normalize_under term_t positions rules =
  match term_t with
  | Var(_) -> term_t
  | Fun(name, arg_list) ->
    match positions with
    | [] -> 
      normalize term_t rules
    | _ ->
      let numbers = create_consecutive 0 (List.length arg_list) in
      Fun(name, 
	  List.map2
	    (function term_s ->
	      function n ->
		normalize_under term_s (feed n positions) rules)
	    arg_list numbers)
;;

let simplify_2 term_t vars_t (t1, sigma1, p1) (t2, sigma2, p2) rules = 
  let s1 = Fun("!tuple!",
	       trmap (function x -> apply_subst (Var x) sigma1) vars_t) in
  let s2 = Fun("!tuple!",
	       trmap (function x -> apply_subst (Var x) sigma2) vars_t) in
  try
    let sigma = mgu s1 s2 in
    if is_renaming sigma then
      let pr = list_intersect p1 p2 in
      Some (normalize_under (apply_subst term_t sigma1) pr rules, sigma1, pr)
    else
      None
  with Not_unifiable -> None
;;

let rec simplify_dumb term_t vars_t dumb rules =
  match dumb with
  | hd1 :: hd2 :: tl ->
    (
      match simplify_2 term_t vars_t hd1 hd2 rules with
      | Some next_hd -> simplify_dumb term_t vars_t (next_hd :: tl) rules
      | None -> hd1 :: (simplify_dumb term_t vars_t (hd2 :: tl) rules)
    )
  | _ -> dumb
;;

let simplify term_t vars_t next_dumb configuration rules =
  simplify_dumb term_t vars_t next_dumb rules
;;

let show_position (p : position) : string =
  String.concat ""
    (trmap string_of_int p)
;;

let show_positions positions =
  String.concat " " (trmap show_position positions)
;;

let show_configuration (t, sigma, positions) =
  (show_term t) ^ ", " ^ (show_subst sigma) ^ ", " ^ (show_positions positions)
;;

let rec show_configurations c =
  "[" ^ (String.concat ";\n" (trmap show_configuration c)) ^ "]"
;;

let rec iterate_all term_t vars_t configuration rules =
  let next_dumb = iterate_once configuration rules in
  let next_simpl  = simplify term_t vars_t next_dumb configuration rules in
  (
    (* Printf.printf "Dumb: %s\n%!" (show_configurations next_dumb); *)
    (* Printf.printf "Simpl: %s\n%!" (show_configurations next_simpl); *)
    List.append configuration 
      (if next_simpl = [] then 
	  []
       else 
	  (iterate_all term_t vars_t next_simpl rules))
  )
;;

let variants t rules =
  let vars_t = vars_of_term t in
  iterate_all t vars_t [(t, [], init_pos t)] rules
;;

let one_unifier ssigma sigmas tsigma sigmat svars tvars : subst list = 
  let vinter = list_intersect svars tvars in
  let tpis = trmap (function x -> apply_subst (Var(x)) sigmas) vinter in
  let vpis = vars_of_term_list tpis in
  let tpit = trmap (function x -> apply_subst (Var(x)) sigmat) vinter in
  let vpit = vars_of_term_list tpit in
  let xs = trmap (function x -> Var(fresh_variable ())) vpis in
  let ys = trmap (function x -> Var(fresh_variable ())) vpit in
  let pis = List.map2 (fun x y -> (x, y)) vpis xs in
  let pit = List.map2 (fun x y -> (x, y)) vpit ys in
  let t1 = Fun("!tuple!", (apply_subst ssigma pis) ::
		 (trmap (fun x -> apply_subst x pis) tpis)) in
  let t2 = Fun("!tuple!", (apply_subst tsigma pit) ::
		 (trmap (fun x -> apply_subst x pit) tpit)) in
  try
    let sigma = mgu t1 t2 in
    [List.append
       (restrict (compose (compose sigmas pis) sigma) svars)
       (restrict (compose (compose sigmat pit) sigma) 
	  (list_diff tvars svars))]
  with Not_unifiable -> []
;;

let unifiers s t rules =
  let svars = vars_of_term s in
  let tvars = vars_of_term t in
  let vs = variants s rules in
  let vt = variants t rules in
  let w = combine vs vt in
  trconcat (trmap (fun ((x, y, _), (z, t, _)) ->
			   one_unifier x y z t svars tvars) w)
;;
