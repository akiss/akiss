(** Unification and matching *)

open Types
open Term
open Util
open Maude


(*let list_diff big small = 
  List.filter (function x -> not (List.mem x small))  big*)




exception Not_unifiable
exception Call_Maude


(*let rec subst_one x small = function
  | Var({ link = l}) as v -> if x = l then small else v
  | Fun(f, list) ->
      Fun(f, List.map (function y -> subst_one x small y) list)

let subst_one_in_list x small list =
  List.map (function y -> subst_one x small y) list

let subst_one_in_subst x small sigma =
  List.map (function (v, t) -> (v, (subst_one x small t))) sigma *)

(* given a sum split the sum in three parts: variables, constants functions, all functions *)
(*let rec explode_term t =
	let rec is_constant f =
		match f with
		| Var(x) -> false
		| Fun(f,l)-> List.fold_left (fun x t -> x && is_constant t) true l in
	match t with
	| Fun({id = Plus; has_variables = true},[l;r]) -> let (v1,t1,c1) = explode_term l in let (v2,t2,c2) = explode_term r in (v1@v2,t1@t2,c1@c2)
	| Var(x) -> ([x],[],[])
	| Fun(f,l)-> if is_constant (Fun(f,l)) then ([],[f],[Fun(f,l)]) else ([],[f],[])
*)

(** Equality modulo pure AC *)
let rec sum_to_list t =
	match t with
	| Fun({id=Plus},[l;r]) -> (sum_to_list l)@(sum_to_list r)
	| x -> [x]

  
let rec compare_ac s t =
  (*Printf.printf "%s ? %s \n%!" (show_term s) (show_term t);*)
	match (s,t) with
	| (Var(x),Var(y)) when x=y -> 0
	| (Var(x),Var(y)) -> let r = compare x.status y.status in if r = 0 then compare x.n y.n else r
	| (Fun({id=Plus},a1),Fun({id=Plus},a2)) -> list_compare_ac (List.sort compare_ac (sum_to_list s)) (List.sort compare_ac (sum_to_list t))
	| (Fun(f,a),Fun(g,b)) -> let r = compare f.id g.id in if r != 0 then r else 
      List.fold_left2 (fun x t1 t2 -> if x != 0 then x else (compare_ac t1 t2)) 0 a b
	| (Var(_),Fun(_)) -> 1
	| (Fun(_),Var(_)) -> -1
	
and list_compare_ac l1 l2 =
	match l1,l2 with
	| t1 :: q1, t2 :: q2 -> let r = compare_ac t1 t2 in if r != 0 then r else list_compare_ac q1 q2
	| [] , [] -> 0
	| [] , _  -> 1
	| _ , [] -> -1
	
let rec list_reduce l =
  match l with
	| z :: q when z = zero -> list_reduce q
	| t1 :: t2 :: q when compare_ac t1 t2 = 0 -> list_reduce q
	| t :: q -> t :: (list_reduce q)
	| [] -> []
  
let order_plus s =
  (*Printf.printf "list   ";
  List.iter (fun x -> Printf.printf "%s; " (show_term x) ) s;
  Printf.printf "\nsorted ";*)
  let lst = List.sort compare_ac s in
  (*List.iter (fun x -> Printf.printf "%s; " (show_term x) ) lst;
  Printf.printf "\n";*)
  list_reduce lst


module TermSum = Map.Make(struct
    type t = term 
    let compare x y = compare_ac x y
  end)

let equals_ac s t = let r = (compare_ac s t) in (*Printf.printf "%d\n" r;*) r = 0

(** {2 Get unifiers} *)

let rec recompose_term_set ts =
  TermSum.fold (fun t nb term -> if term = zero then t else Fun({id = Plus; has_variables = true},[t;term])) ts zero
(*	match lst with
	| t1 :: t2 :: q -> Fun({id = Plus; has_variables = true},[t1;recompose_term (t2 ::q)])
	| t1 :: [] -> t1
	| [] -> Fun({id = Zero; has_variables = false},[])*)
	
let term_sum_union xor ms1 ms2 =
  TermSum.union (fun t nb1 nb2 -> if xor then if nb1 + nb2 mod 2 = 0 then None else Some 1 else Some (nb1 + nb2)) ms1 ms2
  
(** given a term t provide Fct(t)  *)
let rec explode_term xor t sigma =
  let rec has_var f =
    match f with
    | Var(x) -> let sub = find_sub x sigma in begin
          match sub.(x.n) with
          | None -> (true,f)
          | Some t -> has_var t
          end
    | Fun(f,l)-> 
        let (x,lst) = List.fold_right (fun t (x,lst) -> 
          let (has_v,t') = has_var t in 
          (x || has_v, t' :: lst)) l (false,[])  in 
        (x,Fun({f with has_variables = x},lst)) in
   match t with
   | Fun({id = Plus; },[l;r]) ->
          let ts1 = explode_term xor l sigma in 
          let ts2 = explode_term xor r sigma in 
          term_sum_union xor ts1 ts2
          (*TermSum.diff
          (TermSum.union ts1 ts2)
          (TermSum.inter ts1 ts2)*)
   | Var(x) -> let sub = find_sub x sigma in begin
          match sub.(x.n) with
          | None -> TermSum.singleton t 1
          | Some t -> explode_term xor t sigma
          end 
   | Fun(f,l)-> let (x,t) = has_var (Fun(f,l)) in TermSum.singleton t 1
   
let diff_sum_term mset1 mset2 = 
  TermSum.merge (fun t nb1 nb2 ->
    match nb1,nb2 with
    | Some nb1, Some nb2 -> if nb1 > nb2 then Some (nb1-nb2) else None 
    | Some nb1, None -> Some nb1
    | None , _ -> None ) mset1 mset2
    
let mset_cardinal mset =
  TermSum.fold (fun t nb nbtot -> nb + nbtot) mset 0

let rec is x t sigma = 
    match t with 
    | Fun(f, args) -> false
    | Var(y) when x = y -> true
    | Var(y) -> let sub = find_sub y sigma in begin
        match sub.(y.n) with
          | None -> false 
          | Some t -> is x t sigma
        end
   
let rec occurs x t sigma = 
    match t with 
    | Fun(f, args) -> occurs_list x args sigma
    | Var(y) when x = y -> true
    | Var(y) -> let sub = find_sub y sigma in begin
        match sub.(y.n) with
          | None -> false 
          | Some t -> occurs x t sigma
        end
and occurs_list x l sigma =
    match l with 
    | [] -> false
    | h::q -> occurs x h sigma || occurs_list x q sigma

let rec unify xor hard pairlst sigma =
  (*Printf.printf "Subst%s,%s \n%!" (show_subst_array sigma.m) (show_subst_array sigma.s);*)
  let rec combine l1 l2 l =
    match (l1,l2) with
    | (h1::q1,h2::q2) -> (h1,h2)::(combine q1 q2 l)
    | ([],[]) -> l
    | _ -> raise Not_unifiable in
  match pairlst with
    | [] -> hard
    | (Var(x), Var(y))::q when x = y -> unify xor hard q sigma
    | (Var(x), t)::q -> (*Printf.printf "With term %s\n" (show_term t);*)
          let sub = find_sub x sigma in begin
          match sub.(x.n) with
          | None -> 
               if occurs x t sigma
               then ( 
                if not (is x t sigma) 
                then raise Not_unifiable
               )
               else sub.(x.n)<- Some t; 
               unify xor hard q sigma
          | Some t' -> unify xor hard ((t',t)::q) sigma
          end
    | (t, (Var(y) as s))::q -> unify xor hard ((s,t)::q) sigma
    | ((Fun({id = Plus}, _) as sa), (Fun({id=Plus}, _) as ta))::q -> may_unify_plus xor hard sa ta q sigma
    | (Fun({id = f}, sa), Fun({id = g}, ta))::q when f = g -> unify xor hard (combine sa ta q) sigma
    | _ ->  raise Not_unifiable
    
and may_unify_plus xor hard sa ta pairlst sigma =
  (*Printf.printf "unify xor plus\nsa %s | ta : %s  \n" (show_term sa)(show_term ta);*)
	let exp_sa' = explode_term xor sa sigma in 
	let exp_ta' = explode_term xor ta sigma in
	(* remove terms that appears both in sa and ta *)
	let exp_sa = diff_sum_term exp_sa' exp_ta' in
	let exp_ta = diff_sum_term exp_ta' exp_sa' in
	(* if now one term is not a + switch to the standard unification *)
  if mset_cardinal exp_sa < 2 then unify xor hard ((recompose_term_set exp_sa,recompose_term_set exp_ta)::pairlst) sigma
	else if mset_cardinal exp_ta < 2 then unify xor hard ((recompose_term_set exp_ta,recompose_term_set exp_sa)::pairlst) sigma
	else if xor then unify xor ((sa,ta)::hard) pairlst sigma 
	else
    let (nbv_sa,ws) = TermSum.fold (fun t nb'(nb,w) -> match t with Var(_) -> (nb+nb',w) | _ -> (nb,t)) exp_sa (0,zero) in
    let (nbv_ta,wt) = TermSum.fold (fun t nb'(nb,w) -> match t with Var(_) -> (nb+nb',w) | _ -> (nb,t)) exp_ta (0,zero) in
    if nbv_sa + nbv_ta > 1 then unify xor ((sa,ta)::hard) pairlst sigma (* if there is more than 1 variable ask Maude *)
    else if nbv_sa = 0 then 
      remove_one_factor_both_side hard wt exp_ta exp_sa sa ta pairlst sigma
    else if nbv_ta = 0 then
      remove_one_factor_both_side hard ws exp_sa exp_ta sa ta pairlst sigma
    else assert false
    
and remove_one_factor_both_side hard wt exp_ta exp_sa sa ta pairlst sigma =    
        match wt with 
        | Fun({id = f; has_variables = hvf}, _) -> 
          let unifiable =
            TermSum.filter (fun sa' nb -> 
              match sa' with 
              Fun({id = g; has_variables = hvg}, _) when f = g -> if hvf && hvg then equals_ac wt sa' else true | _ -> false) exp_sa in
           let nbunif =  mset_cardinal unifiable in
           if nbunif = 0 then raise Not_unifiable else
           if nbunif = 1 
           then (
              let sa', one = TermSum.choose unifiable in
              assert (one = 1);
              let slimmed_sa = recompose_term_set (TermSum.remove sa' exp_sa) in
              let slimmed_ta = recompose_term_set (TermSum.remove wt exp_ta) in
              (*Printf.printf "reduction+ sa %s -> %s | ta : %s -> %s \n" (show_term sa)(show_term slimmed_sa)(show_term ta)(show_term slimmed_ta);*)
              unify true hard ((sa',wt)::((slimmed_sa,slimmed_ta)::pairlst)) sigma
          )
          else unify true ((sa,ta)::hard) pairlst sigma
        | _ -> assert false
        
(*	if (List.length xs) + (List.length ys) > 1
	then unify ((sa,ta)::hard) pairlst sigma
	else let (ab_t1,co_t1,ab_t2,co_t2) = if xs = [] then (us,ds,ts,cs) else (ts,cs,us,ds) in
		if List.length ts = List.length cs && List.length us = List.length ds 
		then begin
			let c_t2=list_diff co_t2 co_t1 in
			let c_t1=list_diff co_t1 co_t2 in
			if c_t1 <> [] 
			then raise Not_unifiable
			else 
			if  xs = [] && ys = [] 
			then begin
				if c_t2 <> [] 
				then raise Not_unifiable 
				else unify hard pairlst sigma end
			else
			if c_t2 = [] then raise Not_unifiable  else
			let t=recompose_term c_t2 in
			let x = if xs = [] then List.hd ys else List.hd xs in
			let sub = find_sub x sigma in
			sub.(x.n)<-Some t ;
			unify hard pairlst sigma
		end
		else 
			if sa = ta then unify hard pairlst sigma else (* in the lucky case where all terms coincide *)
			if List.exists (function x -> not (List.mem x ab_t2)) ab_t1 
			then raise Not_unifiable 
			else 
			if (xs <> [] ||  ys <> [])  
			then unify ((sa,ta)::hard) pairlst sigma 
			else if List.exists (function x -> not (List.mem x ab_t1)) ab_t2 
			then raise Not_unifiable 
			else unify ((sa,ta)::hard) pairlst sigma 
*)
(*let rec mgu nbs nbt s t = unify [(s,t)] (Array.make nbs None,Array.make nbt None) *)

let csu xor pairlst sigma = 
  (*Printf.printf "%s \n%!" (show_subst_maker sigma);*)
  let pairlst = ref pairlst in
  let old_length = ref 1000000 in
  try
    while !old_length > 0 && List.length !pairlst < !old_length do
      (*Printf.printf "--%s%!" (
      List.fold_left (fun  str (t1,t2) -> str ^
        (show_term t1)^" =? "^(show_term t2) ^"\n")"" !pairlst);*)
      old_length := List.length !pairlst;
      pairlst := unify xor [] !pairlst sigma ;
    done ;
    if !old_length = 0 then [sigma]
    else
      let maude_xor = if xor then XOR else AC in
      acunifiers maude_xor !pairlst sigma (*Call Maude on hard with sigma *)
  with 
  | Not_unifiable ->  (*Printf.printf "no unif\n";*)[]
  
let csu_ac pairlst sigma = csu false pairlst sigma
  
let csu_xor pairlst sigma = csu true pairlst sigma
(*  try ignore(unify true [] pairlst sigma);
  [sigma] 
  with 
  | Not_unifiable -> []*)
  
(** {2 Use of unifiers to perform substitutions}*)

let get_option = function None -> assert false | Some t -> t

(** From a susbt obtained from unification generates a substitution which can be applied to term *)
let pack sigma =
  let master_final = Array.make (Array.length(sigma.m)) None in
  let slave_final = Array.make (Array.length(sigma.s)) None in
  let extra_final = List.map (fun e -> Array.make (e.nb_extra)  None) sigma.e in
  let binder = ref New in
  let nbv = ref 0 in
  (* Build a new term from a term an a processed substitution *)
  let rec put_term_of arr i init_i  =
    match init_i with 
      | None -> arr.(i) <- Some(Var({n = !nbv ; status = binder})) ;
        incr nbv
      | Some t -> arr.(i) <- Some(apply_subst_term t)
  and apply_subst_term t =
    match t with
    | Fun(f,args) -> Fun(f, List.map (fun t -> apply_subst_term t) args )
    | Var(x) -> begin
      let indexes = 
        match !(x.status) with 
        Master -> master_final 
        | Slave | Rule -> slave_final 
        | Extra n -> (List.nth extra_final n) 
        | _ -> assert false in
      match indexes.(x.n) with 
       | Some(t) -> t
       | None -> 
         let sub = find_sub x sigma in 
         put_term_of indexes x.n sub.(x.n);
         get_option (indexes.(x.n))
       end
  in
  let doit final init  = 
    for i = 0 to Array.length(init) - 1 do 
      match final.(i) with
      | Some _ -> ()
      | None -> put_term_of final i init.(i)
    done    
  in
  doit master_final (sigma.m);
  doit slave_final (sigma.s);
  { 
    binder = binder; 
    master =  Array.map get_option master_final;
    slave = Array.map get_option slave_final;
    nbvars = !nbv;
  }

let rec apply_subst_term term sigma =
  try
   match term with
  | Fun(f,args) -> Fun(f, List.map (fun t -> apply_subst_term t sigma) args )
  | Var(x) -> let the_sigma = if !(x.status) = Master then sigma.master else sigma.slave in
     the_sigma.(x.n)
  with
  | Invalid_argument a -> Printf.eprintf "Error when subst of %s with %s \n" (show_term term)(show_substitution sigma);
    raise (Invalid_argument a)

let rec compose_master sigma tau =
  Array.iteri (fun i term -> sigma.master.(i)<- apply_subst_term term tau)sigma.master ;
  (*Array.iteri (fun i term -> sigma.slave.(i)<- apply_subst_term term tau)sigma.slave ;*)
  { 
    binder = tau.binder; 
    nbvars = tau.nbvars;
    master = sigma.master;
    slave  = sigma.slave;
  }

let rec compose sigma tau =
  Array.iteri (fun i term -> sigma.master.(i)<- apply_subst_term term tau)sigma.master ;
  Array.iteri (fun i term -> sigma.slave.(i) <- apply_subst_term term tau)sigma.slave ;
  { 
    binder = tau.binder; 
    nbvars = tau.nbvars;
    master = sigma.master;
    slave  = sigma.slave;
  }

let rec compose_with_subst_lst sigma subst =
  let nbvars = ref 0 in
  let binder = ref New in
  let rec repl = function
    | Var(x) -> let v = Var({n = !nbvars; status = binder}) in incr nbvars; v
    | Fun(symbol, args ) -> Fun(symbol, List.map repl args ) in
  let subst = List.map (fun (x,t) -> (x,repl t)) subst in
  Array.iteri (fun i term -> sigma.master.(i) <- apply_subst term subst) sigma.master ;
  Array.iteri (fun i term -> sigma.slave.(i) <- apply_subst term subst) sigma.slave ;
  { 
    binder = binder; 
    nbvars = !nbvars;
    master = sigma.master;
    slave  = sigma.slave;
  }

let identity_subst nbv =
  let binder = ref Master in
  let master = Array.make nbv (Var({status=binder; n=0})) in
  { binder = binder ;
    nbvars = nbv ;
    master = Array.mapi (fun i _ -> Var({status=binder; n=i})) master ; 
    slave = Array.make 0 (Var({status=binder; n=0}))
  }
  
(** In test.ml to merge test heads *)
let merging_subst nbv binder =
  let master = Array.make nbv (Var({status=binder; n=0})) in
  { binder = binder ;
    nbvars = nbv ;
    master = Array.mapi (fun i _ -> Var({status=binder; n=i})) master ; 
    slave = Array.make 0 (Var({status=binder; n=0}))
  } 
  
let is_identity_master sigma nb =
  assert (Array.length sigma.slave = 0);
  if sigma.nbvars <> nb then false
  else Array.for_all (fun t -> is_var t) sigma.master



(** {2 Most general matcher} *)

let rec explode_term_matcher xor t sigma =
   match t with
   | Fun({id = Plus; },[l;r]) ->
          let ts1 = explode_term_matcher xor l sigma in 
          let ts2 = explode_term_matcher xor r sigma in 
          term_sum_union xor ts1 ts2
   | Var(x) -> 
      if List.mem_assoc x sigma then
      explode_term_matcher xor (List.assoc x sigma) sigma
      else TermSum.singleton t 1
   | Fun(f,l)-> TermSum.singleton t 1




let rec match_ac xor hard pattern_model_list sigma =
  let rec combine l1 l2 l =
    match (l1,l2) with
    | (h1::q1,h2::q2) -> (h1,h2)::(combine q1 q2 l)
    | ([],[]) -> l
    | _ -> raise Not_matchable in
  match pattern_model_list with
    | [] -> (hard,sigma)
    | (Var(x), t)::q -> match_ac xor hard q (new_or_same x t sigma)
    | ((Fun({id=Plus},pa)as pattern), (Fun({id=Plus},ma) as model))::q -> may_match_plus xor hard pattern model q sigma
    | (Fun(f, pa), Fun(g, ma))::q when (f.id = g.id) ->
	match_ac xor hard (combine pa ma q) sigma
    | (_, _)::q -> raise Not_matchable

and may_match_plus xor hard pattern model pairlst sigma =
  (*Printf.printf "match plus\npattern %s | model : %s  \n" (show_term pattern)(show_term model);*)
  let exp_pattern' = explode_term_matcher xor pattern sigma in 
  let exp_model' = explode_term_matcher xor model sigma in
  (* remove terms that appears both in pattern and model *)
  let exp_pattern = diff_sum_term exp_pattern' exp_model' in
  let exp_model = diff_sum_term exp_model' exp_pattern' in
  (* if now one term is not a + switch to the standard unification *)
  if TermSum.cardinal exp_pattern < 2 then match_ac xor hard ((recompose_term_set exp_pattern,recompose_term_set exp_model)::pairlst) sigma
  else 
    match_ac xor ((pattern,model)::hard) pairlst sigma (* if there is more than 1 variable ask Maude *)
    


(*	let (xs,ts,cs)= explode_term pattern in 
	if xs = [] && List.length ts = List.length cs then
		begin if equals_ac pattern model then
			match_ac hard lst sigma
		else raise Not_matchable end
	else match_ac ((pattern,model)::hard) lst sigma *)

(** Most general matcher modulo AC *)
let rec csm be_lazy binder pmlst sigma = 
  (*Printf.printf "matching %s against pattern %s \n%!" (show_term m) (show_term p);*)
  try 
    let (hard,sigma) = match_ac false [] pmlst sigma in
    if hard = [] then [sigma]
    else 
      if be_lazy 
      then []  
      else Maude.acmatchers binder hard sigma 
  with Not_matchable -> []

let rec csm_xor be_lazy binder pmlst sigma = 
  (*Printf.printf "matching %s against pattern %s \n%!" (show_term m) (show_term p);*)
  try 
    let (hard,sigma) = match_ac true [] pmlst sigma in
    if hard = [] then [sigma]
    else 
      if be_lazy 
      then []
      else Maude.xormatchers binder hard sigma 
  with Not_matchable -> []




(** {2 Normalization} *)
let rec recompose_term lst =
	match lst with
	| t1 :: t2 :: q -> Fun({id = Plus; has_variables = true},[t1;recompose_term (t2 ::q)])
	| t1 :: [] -> t1
	| [] -> Fun({id = Zero; has_variables = false},[])

let rec top_rewrite t rule =
  (*Printf.printf "top rewrite %s \n%!" (show_rewrite_rule rule);*)
    match csm false rule.binder_rule [(rule.lhs, t)] [] with
    | [sigma] -> [apply_subst rule.rhs sigma]
    | [] -> []
    | sigma :: q -> Printf.printf "> ?/? \n%!"; [apply_subst rule.rhs sigma] (* is it ok ? *)

let rec compare_term t1 t2 =
	match (t1,t2) with
	| (Fun(f,a),Var(x)) -> 1
	| Var(x),(Fun(f,a)) -> -1
	| (Var(x),Var(y)) -> compare x y
	| (Fun(f,a),Fun(g,b)) -> let c = compare f g in
		if c <> 0 then c
		else compare_term_list a b 
and compare_term_list l1 l2 =
	match (l1,l2) with
	| (t1::q1,t2::q2) -> let c = compare_term t1 t2 in
		if c <> 0 then c
		else compare_term_list q1 q2
	| ([],[]) -> 0
	| (_,[])  -> 1
	| ([],_) -> -1

let rec remove_duplicate lst =
	match lst with
	| Fun({id=Zero},[])::q -> remove_duplicate q 
	| a::b::q -> 
	if equals_ac a b then remove_duplicate q else a :: (remove_duplicate (b ::q))
	| [x] -> [x]
	| [] -> []

(* top normalize assumes that all strict subterms are in normal form *)
let rec top_normalize t rules all_rules=
  (*Printf.printf "top normalize %s \n%!" (show_term t);*)
  match rules with
  | [] -> t
  | rule :: rules -> begin
    match top_rewrite t rule with
    | [] -> top_normalize t rules all_rules
    | s :: _ -> normalize s all_rules
    end
(* call this function to find the normal form of any term *)
and normalize t rules =
  (*Printf.printf "normalize %s \n%!" (show_term t);*)
  match t with
    | Fun({id=Plus},_) -> 
        let lst = order_plus (List.fold_left (fun lst x -> (sum_to_list (normalize x rules)) @ lst ) [] (sum_to_list t)) in
        let r = recompose_term lst in
(*    let r = recompose_term
	(remove_duplicate (List.sort compare_term 
	(List.concat(List.map (fun x -> sum_to_list (normalize x rules)) (List.concat (List.map sum_to_list ta)))))) in
*)  
        (*Printf.printf "normalize %s into %s \n%!" (show_term t)(show_term r); *) r
    | Fun(f, ta) ->
	top_normalize (Fun(f, List.map (fun x -> normalize x rules) ta)) rules rules
    | Var(x) -> t

let equals_r s t rules =
  let s = normalize s rules in
  let t = normalize t rules in
  equals_ac s t

(** {2 Variants and unification modulo R} *)
(*                                        *)
(*       ==================               *)
(*                                        *)
(*              TODO                      *)
(*                                        *)
(******************************************)


open Util
let trconcat = List.concat

type position = int list;;

let show_position (p : position) : string =
  String.concat ""
    (trmap string_of_int p)


let show_positions positions =
  String.concat " " (trmap show_position positions)


let show_configuration (t, sigma, positions) =
  (show_term t) ^ ", sig: " ^ (show_substitution sigma) ^ ", pos : " ^ (show_positions positions)


let rec show_configurations c =
  "\n[\n" ^ (String.concat ";\n" (trmap show_configuration c)) ^ "\n]"



(*type mask =
  | VarMask
  | FunMask of mask list
;;*)

(*let rec mask_of = function
  | Var(_) -> VarMask
  | Fun(_, tl) -> FunMask (trmap mask_of tl)
;;*)

let rec prepend n pl =
  trmap (function x -> n :: x) pl


let rec init_pos = function
  | Var(_) -> []
  | Fun(_, tl) -> [] :: (trconcat (List.map2 prepend 
				  (create_consecutive 0 (List.length tl))
				  (trmap init_pos tl)))


let rec at_position t p =
  match p with
    | [] -> t
    | i :: rp -> (
	match t with
	  | Var(_) -> invalid_arg("at_position")
	  | Fun(f, tl) -> at_position (List.nth tl i) rp
      )


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


(* TODO change it *)
(*let fresh_copy rule =
  let vars = vars_of_term_list [rule.lhs; rule.rhs] in
  let new_vars = trmap (function x -> fresh_variable ()) vars in
  let sigma = List.combine vars (trmap (function x -> (Var(x))) new_vars) in
  (apply_subst rule.lhs sigma, apply_subst rule.rhs sigma)
;;*)

let rec one_rule old_sigma t p rule = 
  let identity = identity_subst old_sigma.nbvars in
  let (l, r) = (*fresh_copy*) (rule.lhs, rule.rhs) in
  let sigma = {m= (Array.make old_sigma.nbvars None); s=(Array.make rule.nbvars_rule None); e=[]} in
    match csu_ac [((at_position t p),l)] sigma with
    | [sigma] ->  let sigma = pack sigma in 
      sigma.binder := Master;
      let t'= repl_position t p r in
     (* Printf.printf "<one rule>t= %s; sigma= %s\n give: %s\n" (show_term t)(show_substitution sigma)(show_term t');*)
    [(apply_subst_term t' sigma, 
      compose_master ({old_sigma with 
          master=Array.map (fun t -> apply_subst_term t identity) old_sigma.master})
        sigma)]
    | [] ->  []
    | _ -> raise Call_Maude


let all_rules old_sigma t p rules =
    trconcat (trmap (function x -> one_rule old_sigma t p x) rules)


let rec is_prefix small big =
  match (small, big) with
    | ([], _) -> true
    | (x :: rs, y :: rb) when x = y -> is_prefix rs rb
    | _ -> false


let rec down positions p =
  List.filter (function x -> not (is_prefix p x)) positions

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
  (*sigma.binder:=New;
  Printf.printf "one step %s\n" (show_configuration (t, sigma, positions));
  sigma.binder:=Master;*)
  trconcat (trmap (function x -> 
			   trmap (function (z, y) -> (z, y, (down positions x)))
			     (all_rules sigma t x rules))
		 positions)
;;

let iterate_once configuration rules =
  trconcat (trmap (function x -> one_step x rules) configuration)


let is_renaming sigma1 sigma2 = 
  let r = sigma1 = sigma2 in
  (*Printf.printf ">> %b : %s %s \n"r (show_substitution sigma1)(show_substitution sigma2);*)
  r(*todo*)(*
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
;;*)

let rec feed n positions = 
  trconcat (trmap
      (function p ->
		match p with
		| x :: y ->
		  if x = n then [y] else []
		|  [] -> []
      )
      positions)


let rec normalize_under term_t positions rules =
  (*Printf.printf "[normalization of %s \n" (show_term term_t);
  let r =*)
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
   (* in
    Printf.printf " got %s ]\n" (show_term r);
    r*)

let simplify_2 term_t (t1, sigma1, p1) (t2, sigma2, p2) rules =
  (*let s1 = Fun("!tuple!",
	       trmap (function x -> apply_subst (Var x) sigma1) vars_t) in
  let s2 = Fun("!tuple!",
	       trmap (function x -> apply_subst (Var x) sigma2) vars_t) in
  match csu s1 s2 with
  | [sigma] -> 
    if is_renaming sigma then
      let pr = list_intersect p1 p2 in
      Some (normalize_under (apply_subst term_t sigma1) pr rules, sigma1, pr)
    else
      None
  | [] -> None
  | _ -> assert(false)*)
  if is_renaming sigma1 sigma2 then
      let pr = list_intersect p1 p2 in
      Some (normalize_under (apply_subst_term term_t sigma1) pr rules, sigma1, pr)
    else
      None


(* let rec simplify_dumb term_t vars_t dumb rules = *)
(*   match dumb with *)
(*   | hd1 :: hd2 :: tl -> *)
(*     ( *)
(*       match simplify_2 term_t vars_t hd1 hd2 rules with *)
(*       | Some next_hd -> simplify_dumb term_t vars_t (next_hd :: tl) rules *)
(*       | None -> hd1 :: (simplify_dumb term_t vars_t (hd2 :: tl) rules) *)
(*     ) *)
(*   | _ -> dumb *)
(* ;; *)

(* let simplify term_t vars_t next_dumb configuration rules = *)
(*   simplify_dumb term_t vars_t next_dumb rules *)
(* ;; *)


let rec simplify_1 c clist term_t rules =
(* simplify configuration each element of the configuration list clist *)
(*  with the configuration c *)
     match clist with
     | hd :: tl ->
       (
         match simplify_2 term_t c hd rules with
	 | Some simpc -> (simplify_1 simpc tl term_t rules)
	 | None -> let (sc, sl) = (simplify_1 c tl term_t rules) in
		   (sc, hd :: sl)
       )
     | _ -> (c, clist)


let rec simplify term_t config_list rules =
  (*Printf.printf "simplify %s :: %s <<end\n" (show_term term_t) (show_configurations config_list);*)
    match config_list with
    | hd :: tl -> 
      let (simphd, simptl) = (simplify_1 hd tl term_t rules) in simphd :: (simplify term_t simptl rules)
    | _ -> config_list


(* let simplify term_t vars_t next_dumb configuration rules = *)
(*   simplify_0 term_t vars_t next_dumb rules *)
(* ;; *)



let rec iterate_all term_t configuration rules =
  (*Printf.printf "Term %s\n Configurations : %s\n" (show_term term_t)(show_configurations configuration); *)
  let next_dumb = iterate_once configuration rules in
  let next_simpl  = simplify term_t next_dumb rules in
  (
      (*Printf.printf "Dumb:%s\n%!" (show_configurations next_dumb); 
      Printf.printf "Simpl:%s\n%!" (show_configurations next_simpl); *)
    List.append configuration 
      (if next_simpl = [] then 
	  []
       else 
	  (iterate_all term_t next_simpl rules))
  )


let rec max_var maxi t =
  match t with
  | Var(x) -> max maxi x.n
  | Fun(f,args) -> List.fold_left (fun m arg -> max m (max_var m arg)) maxi args



let variants nbv t rules =
  (* Printf.printf "\nCompute variants of : %s\n" (show_term t); *)
  (*let vars_t = vars_of_term t in*)
  let sigma = identity_subst nbv in
  iterate_all t [(apply_subst_term t sigma, sigma, init_pos t)] rules

let one_unifier ssigma sigmas tsigma sigmat = 
  let sigmas = { binder = sigmas.binder; nbvars = sigmas.nbvars; master = Array.copy sigmas.master; slave = Array.copy sigmas.slave} in
  let sigma_init = { m=Array.make sigmas.nbvars None; s=Array.make sigmat.nbvars None; e=[]} in
  sigmas.binder := Master;
  sigmat.binder := Slave ;
  (*Printf.printf "terms with variants %s -+- %s \n corresponding substitution\n sigma s =  %s \nsigma t = %s\n%!" 
    (show_term ssigma)(show_term tsigma)(show_substitution sigmas)(show_substitution sigmat);*)
  let t1t2 = (ssigma,tsigma) ::Array.to_list( Array.map2 (fun x y -> (x,y)) sigmas.master sigmat.master) in
  match csu_ac t1t2 sigma_init with
  | [sigma] -> let sigma = pack sigma in [ compose sigmas sigma ]
  | [] -> (*Printf.printf "no unif\n\n" ;*)[]
  | _ -> raise Call_Maude


let unifiers nbv s t rules =
  try
  let s = normalize s rules in
  let t = normalize t rules in
  let vs = variants nbv s rules in
  (*Printf.printf "______\n\nresult s: %s\n variants of %s\n" (show_configurations vs)(show_term t);*)
  let vt = variants nbv t rules in
  (*Printf.printf "______\n\nresult t: %s\n"(show_configurations vt);*)
  let w = combine vs vt in
  trconcat (trmap (fun ((x, y, _), (z, t, _)) ->
       one_unifier x y z t) w)
  with Call_Maude -> List.map pack (Maude.acunifiers E [(s,t)] (sigma_maker_init nbv 0))


let variants nbv t rules =
  try
  List.map (fun (a,b,_) -> a,b) (variants nbv t rules)
  with Call_Maude -> maude_current_nbv := nbv; Maude.variants t
  
let rec explode_term t =
	let rec is_constant f =
		match f with
		| Var(x) -> false
		| Fun(f,l)-> List.fold_left (fun x t -> x && is_constant t) true l in
	match t with
	| Fun({id=Plus},[l;r]) -> let (v1,t1,c1) = explode_term l in let (v2,t2,c2) = explode_term r in (v1@v2,t1@t2,c1@c2)
	| Var(x) -> ([x],[],[])
	| Fun(f,l)-> if is_constant (Fun(f,l)) then ([],[f],[Fun(f,l)]) else ([],[f],[])



