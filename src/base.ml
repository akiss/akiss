(** Declaration of statement types, printers and basic functions *)
open Util
open Types
open Term
open Dag
open Inputs
open Process

type body_atom = {
   loc : LocationSet.t;
   recipe : term ;
   term : term ;
   marked : bool; (* for xor *)
}

module EqualitiesSet = Set.Make(struct
    type t = (body_atom list) * term * term
    let compare x y = let b1,x1,x2 = x in let b2,y1,y2 = y in compare (x1,x2) (y1,y2)
  end)
  
type test_head = {
  head_binder : statement_role ref;
  mutable equalities : EqualitiesSet.t;
  mutable disequalities : EqualitiesSet.t ;
}

type predicate =
  | Knows of term * term
  | Reach
  | ReachTest of action *  (term * term) list (** action is to avoid overwriting for hashes *)
  | Identical of term * term
  | Tests of test_head
  | Unreachable



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
  involved_copies : BangSet.t ;
}




let null_raw_statement = {
  binder = ref New ;
  nbvars = 0; 
  dag = empty; 
  inputs= new_inputs; 
  choices= new_choices; 
  head = Reach;
  body=[];
  recipes=new_inputs;
  involved_copies=BangSet.empty}

type statement = {
  id : int ;
  st : raw_statement ;
  mutable children : statement list ; (* deduction statement: statements derived from rules, other: statements more complex *)
  process : process option; (** Process to unfold when a solved statement is derived from it *)
  master_parent : statement; (** the solved statement from which this statement has been derived *)
  slave_parent : statement; 
  test_parent : statement; (** the solved reach statement from which the unsolved statement comes from *)
}

let rec null_statement = { 
  id = -2 ; st = null_raw_statement ; children = [] ; process = None; 
  master_parent = null_statement; slave_parent = null_statement; test_parent = null_statement}

type i_o = In | Out

type chankey = { 
  ph : int ;
  c : chanId ; 
  io : i_o ; 
}

let switch_io = function In -> Out | Out -> In

module ChanMap = Map.Make(struct
    type t = chankey
      let compare x y = compare x y
  end)
  
(** {3 Hash types} *)

type hash_predicate = 
  | HKnows of hash_term * hash_term
  | HReach
  | HReachTest of action 
  | HIdentical of hash_term * hash_term
  | HTests (** In Bijection tests with different equalities are merged *)
  | HUnreachable

type hash_body = (hash_locset * hash_term * hash_term * bool) list
  
type hash_statement = {
  hnbvars : int ;
  hchoices : hash_choices ;
(*  hinputs :  hash_inputs ;*)
  hrecipes : hash_inputs ;
  hdag : hash_dag ;
  hhead : hash_predicate ;
  hbody : hash_body ;
}

let predicate_to_hash p = 
  match p with
 | Knows(r,t) -> HKnows(term_to_hash r,term_to_hash t)
 | Identical(r,r') -> HIdentical(term_to_hash r,term_to_hash r')
 | Reach -> HReach
 | ReachTest(a,_) -> HReachTest(a)
 | Unreachable -> HUnreachable
 | Tests(h) -> HTests
 
let body_to_hash body = 
  List.map (fun atom -> (locset_to_hash atom.loc,term_to_hash atom.recipe,term_to_hash atom.term,atom.marked)) body

let statement_to_hash st = {
  hnbvars = st.nbvars ;
  hchoices = choices_to_hash st.choices ;
  hdag = dag_to_hash st.dag;
  hhead = predicate_to_hash st.head ;
  hrecipes = inputs_to_hash st.recipes ;
(*  hinputs =  inputs_to_hash st.inputs ;*)
  hbody = body_to_hash st.body ;
}

let test_to_hash = statement_to_hash

let get_hash_choices hst = hst.hchoices 
  
(** {2 The type of the knowledge base}*)
  
type base = 
{ 
   mutable next_id : int ;
   solved_deduction : statement ; (** to preserve structure solved_deduction link to a statement whose children are the actual ones *)
   rid_solved : statement ; (** to have a tree structure for the tests *)
   mutable unreachable_solved : statement list; 
   not_solved : statement ;
   temporary_merge_test : statement ; (** to merge two tests put the unsolved test as its child *)
   mutable temporary_merge_test_result : statement list; (** get the corresponding solved statement here *)
   mutable s_todo : statement Queue.t ; (** the solved statements which have not been saturated *)
   mutable ns_todo : statement Queue.t ; 
   mutable hidden_chans : ((location * (term option) * ((term*term)list) * raw_statement * process) list) ChanMap.t ;
   (** "statements" waiting to be merged with another "statement" relative to private communication  *)
   htable : (hash_statement, statement) Hashtbl.t; (** To avoid adding twice the same statement *)
}

(** {2 Assert that all variables of a statement are binded with its binder }*)


let rec check_binder_term binder good_vars bad_vars term =
  match term with
  | Var(x) -> 
    if x.status == binder 
    then (
      if List.mem x !bad_vars 
      then (Printf.printf "\nType ERROR at %s\n" (show_term term);false)
      else ((
        if not (List.mem x !good_vars)
        then good_vars := x :: !good_vars);
        true)
    )
    else (Printf.printf "\nBINDER ERROR at %s\n" (show_term term);false)
  | x when x = fun_error -> Printf.printf "\nFUN ERROR at %s\n" (show_term term); false
  | Fun(_,lst) -> List.for_all (check_binder_term binder good_vars bad_vars) lst
  
let check_binder_head binder rec_var term_var head = 
  match head with
  | Tests({equalities= e;disequalities = d;head_binder = b}) -> b == binder && EqualitiesSet.for_all (fun (_,s,t) -> check_binder_term binder rec_var term_var s && check_binder_term binder rec_var term_var t) e && EqualitiesSet.for_all (fun (_,s,t) -> check_binder_term binder rec_var term_var s && check_binder_term binder rec_var term_var t) d
  | Identical(s,t)-> check_binder_term binder rec_var term_var s && check_binder_term binder rec_var term_var t
  | Knows(s,t) -> check_binder_term binder rec_var term_var s && check_binder_term binder term_var rec_var t
  | _ -> true
  
let check_binder_st st =
  let rec_var = ref [] in
  let term_var = ref [] in
  let binder = st.binder in
  Dag.for_all (fun _ t -> check_binder_term binder term_var rec_var t) st.inputs.i
  && Dag.for_all (fun _ t -> check_binder_term binder rec_var term_var t) st.recipes.i
  && List.for_all (fun x -> check_binder_term binder term_var rec_var x.term && check_binder_term binder rec_var term_var x.recipe) st.body
  && check_binder_head binder rec_var term_var st.head

(** {2 Printing} *)

let show_test_head h =
  (EqualitiesSet.fold ( fun (b,r,r') str -> (if str = "" then "" else str ^ "  ~  ") ^ (show_term r) ^ " = " ^ (show_term r') ) h.equalities "" ) 
     ^ (EqualitiesSet.fold ( fun (b,r,r') str -> (if str = "" then " | " else str ^ " ~ ") ^ (show_term r) ^ " != " ^ (show_term r') ) h.disequalities "")

let show_predicate p = 
 match p with
 | Knows(r,t) -> if !use_xml then "<pred>K(<rec>"^ (show_term r) ^ "</rec>,<term>" ^ (show_term t) ^ "</term>)</pred>" else
      "knows(" ^ (show_term r) ^ "," ^ (show_term t) ^ ")"
 | Identical(r,r') ->
     (if !use_xml then "<i>identical</i>(" else "identical(" )^ (show_term r) ^ "," ^ (show_term r') ^ ")"
 | Reach -> if !use_xml then "<r>reach</r>" else "reach"
 | ReachTest _ -> if !use_xml then "<r>reachT</r>" else "reachT"
 | Unreachable -> if !use_xml then "<u>unreach</u>" else "unreach"
 | Tests(h) -> 
    "tests(" ^ (show_test_head h) ^ ")"

let show_body_atom a =
  (*let l = match a.loc with Some l -> string_of_int l.p | None -> "." in*)
  if !use_xml then 
  "<pred>"^(if a.marked then "K+" else "K")^"<loc>"^(show_loc_set a.loc)^"</loc>(<rec>"^(show_term a.recipe)^"</rec>,<term>"^(show_term a.term)^"</term>)</pred>"
  else
   (if a.marked then "KnOwS_" else "knows_")^(show_loc_set a.loc)^"("^(show_term a.recipe)^","^(show_term a.term)^")"


let rec show_atom_list lst = List.fold_left (fun str b -> (if str = "" then "" else str ^ ",") ^ (show_body_atom b)) "" lst

let show_raw_statement st =
  let string = 
  if !use_xml then
  Format.sprintf
    "<raw_st><nbvars>%d</nbvars>\n<statement> %s%s &lt;== %s </statement>%s %s %s\n<recipes>%s</recipes></raw_st>\n" 
    st.nbvars 
    (show_predicate st.head)
    (match st.head with Reach | Unreachable | ReachTest(_) -> "("^(show_loc_set (last_actions st.dag))^")" | _ -> "")
    (show_atom_list st.body)
    (show_inputs st.inputs)
    (show_dag st.dag)
    (show_choices st.choices)
    (show_inputs st.recipes)
  else
  Format.sprintf
    "(%d%s) %s <== %s \n       %s %s %s\n       %s\n" st.nbvars (show_binder !(st.binder)) (show_predicate st.head)(show_atom_list st.body)(show_inputs st.inputs)(show_dag st.dag)(show_choices st.choices)(show_inputs st.recipes) in 
  string ^ if not (check_binder_st st) then (Printf.printf "BINDER ERROR: \n%s\n" string; assert false; st.binder := Rule;  " BINDER ERROR " ) else ""
  
let show_chan_key chkey =
   if !use_xml then 
      Format.sprintf "<ckey>%s %s %s</ckey>\n" chkey.c.name (match chkey.io with In -> "in" | Out -> "out") 
      (if chkey.ph <> 0 then "<phase>"^ (string_of_int chkey.ph) ^ "</phase>" else "")
    else
      Format.sprintf "[%s]%s-%d" chkey.c.name (match chkey.io with In -> "in" | Out -> "out") chkey.ph
  
let show_chan_statements chmap =
  if !use_xml then 
    ChanMap.fold ( fun key lst str -> str ^ "\n<chanset>" ^ (show_chan_key key) ^ (List.fold_left (fun str (l,t,terms,st,pr) -> 
    str ^
      Format.sprintf "<hidden>%d%s %s</hidden>\n" l.p (match t with None -> "" | Some t -> " ("^(show_term t)^")") (show_raw_statement st)
  ) "" lst) ^ "</chanset>") chmap ""
  else
  ChanMap.fold ( fun key lst str -> str ^ "\n" ^ (show_chan_key key) ^ (List.fold_left (fun str (l,t,terms,st,pr) -> 
    str ^ Format.sprintf "loc %d%s, %s\n" l.p (match t with None -> "" | Some t -> " ("^(show_term t)^")")(show_raw_statement st)
  ) ": \n" lst) ^ "\n") chmap ""


let rec show_statement prefix st =
  if !use_xml then
  (Format.sprintf "<st><id>%d</id><parents>[%d;%d]</parents>\n %s" 
    st.id (st.master_parent.id)(st.slave_parent.id)(show_raw_statement st.st)) 
  ^ "<children>"^(show_statement_list "" st.children) ^ "</children></st>"
 else
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
  if !use_xml then
   "<base><deductions>"^(show_statement_list " " (kb.solved_deduction.children))
   ^"</deductions><tests>"^ (show_statement_list " " (kb.rid_solved.children))
   ^"</tests><unreachables>"^(show_statement_list " " (kb.unreachable_solved))
   ^"</unreachables><unsolved>"^(show_statement_list " " (kb.not_solved.children))
   ^"</unsolved><hiddenchans>"^(show_chan_statements kb.hidden_chans)^"</hiddenchans></base>\n"  
  else
  (Format.sprintf 
    "Kb : \n - %d statements \n - %d solved deduction \n - %d solved reach and identities \n - %d solved unreach\n\nSolved deduction:\n" 
    kb.next_id (count_statements kb.solved_deduction)(count_statements kb.rid_solved)(List.length kb.unreachable_solved))
  ^ (show_statement_list " " (kb.solved_deduction.children))
  ^ "Solved reach and identities: \n"
  ^ (show_statement_list " " (kb.rid_solved.children))
  ^ "Unreachable solved: \n"
  ^ (show_statement_list " " (kb.unreachable_solved))
  ^ "Not solved: \n"
  ^ (show_statement_list " " (kb.not_solved.children))
  ^ "hidden chan statement: " ^ (show_chan_statements kb.hidden_chans)
 (* ^ "\nTodo not solved: " ^ (show_statements_id kb.ns_todo)*)
  ^ "\n"

  
(** get the test_head strucutre from the head statement of a test *)
let get_test_head head = 
  match head with
  | Tests(eq) -> eq
  | _ -> assert false

(** {2 Substitutions}*)

let apply_subst_test_head head (sigma : substitution) = 
  {
    head_binder = sigma.binder;
    equalities=EqualitiesSet.map (fun (b,r,r') -> (b,Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term r' sigma)) head.equalities;
    disequalities=EqualitiesSet.map (fun (b,r,r') -> (b,Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term r' sigma)) head.disequalities
  }
     
let apply_subst_pred pred sigma  = 
match pred with
  | Knows(r,t) -> 
     Knows(Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term t sigma)
  | Identical(r,r') -> 
     Identical(Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term r' sigma)
  | Reach -> Reach
  | ReachTest(tid,ineqs) -> ReachTest(tid, (*List.map (fun (s,t) -> (Rewriting.apply_subst_term s sigma,Rewriting.apply_subst_term t sigma))*) ineqs)
  | Unreachable -> Unreachable
  | Tests(head) -> Tests(apply_subst_test_head head sigma)

let apply_subst_statement st (sigma : substitution) = 
  try
  {
      binder = sigma.binder;
      nbvars = sigma.nbvars;
      dag = st.dag;
      choices = st.choices;
      inputs = Inputs.map (fun t -> Rewriting.apply_subst_term t sigma) st.inputs;
      recipes = Inputs.map (fun t -> Rewriting.apply_subst_term t sigma) st.recipes;
      head = apply_subst_pred st.head sigma ;
      body = trmap (fun x -> {x with recipe= Rewriting.apply_subst_term x.recipe sigma; term=Rewriting.apply_subst_term x.term sigma}) st.body ;
      involved_copies = st.involved_copies ;
  }
  with Invalid_argument a -> 
    Printf.eprintf "Error with substitution on %s \n" (show_raw_statement st); 
    raise (Invalid_argument a)
  
(**  constructor *)
let new_statement () = {
  id = -1 ; st = null_raw_statement; children = []; process = None;
  master_parent = null_statement; slave_parent = null_statement;test_parent = null_statement
  }

(** create an empty base *)
let new_base () =
  let kb = 
  {
     next_id = 0;
     solved_deduction = new_statement () ;
     rid_solved = new_statement ();
     unreachable_solved = [] ;
     not_solved = new_statement () ;
     temporary_merge_test = new_statement () ;
     temporary_merge_test_result = [] ;
     hidden_chans = ChanMap.empty;
     s_todo = Queue.create () ;
     ns_todo = Queue.create() ;
     htable = Hashtbl.create 10000 ;
  } in
  kb
