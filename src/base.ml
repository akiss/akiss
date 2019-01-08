open Util
open Types
open Term
open Dag
open Inputs
open Process
  
module EqualitiesSet = Set.Make(struct
    type t = term * term
      let compare x y = compare x y
  end)
  
type test_head = {
  head_binder : statement_role ref;
  mutable equalities : EqualitiesSet.t;
  mutable disequalities : EqualitiesSet.t ;
}

type predicate =
  | Knows of term * term
  | Reach
  | Identical of term * term
  | Tests of test_head
  | Unreachable

type body_atom = {
   loc : LocationSet.t;
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
  involved_copies : BangSet.t ;
}

(*for hash table *)
type hash_statement = {
  hbinder : statement_role ref;
  hnbvars : int ;
  hdag : dag ;
  hinputs :  inputs ;
  hrecipes : inputs ;
  hchoices : choices ;
  hhead : predicate ;
  hbody : body_atom list ;
}

type hash_test = {
  htbinder : statement_role ref;
  htnbvars : int ;
  htdag : dag ;
  htinputs :  inputs ;
  htrecipes : inputs ;
  htchoices : choices ;
  htbody : body_atom list ;
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
  vip : bool ;
  st : raw_statement ;
  mutable children : statement list ; (* deduction statement: statements derived from rules, other: statements more complex *)
  process : process option;
  master_parent : statement;
  slave_parent : statement; 
  test_parent : statement; (*the solved statement from which the unsolved statement comes from *)
}

let rec null_statement = { 
  id = -2 ; vip = false ; st = null_raw_statement ; children = [] ; process = None; 
  master_parent = null_statement; slave_parent = null_statement; test_parent = null_statement}

type i_o = In | Out

type chankey = { 
  c : chanId ; 
  io : i_o ; 
  ph : int
}

let switch_io = function In -> Out | Out -> In

module ChanMap = Map.Make(struct
    type t = chankey
      let compare x y = compare x y
  end)
  
  

type base = 
{ 
   mutable next_id : int ;
   solved_deduction : statement ; (* to preserve structure solved_deduction link to a statement whose children are the actual ones *)
   rid_solved : statement ; (* to have a tree structure for the tests *)
   (*mutable identity_solved :  statement list; 
   mutable reachable_solved : statement list ;*)
   mutable unreachable_solved : statement list; 
   not_solved : statement ;
   temporary_merge_test : statement ;
   mutable temporary_merge_test_result : statement list;
   mutable s_todo : statement Queue.t ; 
   mutable ns_todo : statement Queue.t ; 
   mutable hidden_chans : ((location * (term option) * ((term*term)list) * raw_statement * process) list) ChanMap.t ;
   htable : (hash_statement, statement) Hashtbl.t;
}


let rec check_binder_term binder term =
  match term with
  | Var(x) -> if x.status == binder then true else (Printf.printf "\nBINDER ERROR at %s\n" (show_term term);true)
  | Fun(_,lst) -> List.for_all (check_binder_term binder) lst
  
let check_binder_head binder head = 
  match head with
  | Tests({equalities= e;disequalities = d;head_binder = b}) -> b == binder && EqualitiesSet.for_all (fun (s,t) -> check_binder_term binder s && check_binder_term binder t) e && EqualitiesSet.for_all (fun (s,t) -> check_binder_term binder s && check_binder_term binder t) d
  | Identical(s,t)
  | Knows(s,t) -> check_binder_term binder s && check_binder_term binder t
  | _ -> true
  
let check_binder_st st =
  let binder = st.binder in
  Dag.for_all (fun _ t -> check_binder_term binder t) st.inputs.i
  && Dag.for_all (fun _ t -> check_binder_term binder t) st.recipes.i
  && List.for_all (fun x -> check_binder_term binder x.term && check_binder_term binder x.recipe) st.body
  && check_binder_head binder st.head

(** {3 Printing} *)
let show_test_head h =
  (EqualitiesSet.fold ( fun (r,r') str -> (if str = "" then "" else str ^ "  °  ") ^ (show_term r) ^ " = " ^ (show_term r') ) h.equalities "" ) 
     ^ (EqualitiesSet.fold ( fun (r,r') str -> (if str = "" then " | " else str ^ ", ") ^ (show_term r) ^ " != " ^ (show_term r') ) h.disequalities "")

let show_predicate p = 
 match p with
 | Knows(r,t) -> if !use_xml then "<pred>K(<rec>"^ (show_term r) ^ "</rec>,<term>" ^ (show_term t) ^ "</term>)</pred>" else
      "knows(" ^ (show_term r) ^ "," ^ (show_term t) ^ ")"
 | Identical(r,r') ->
     (if !use_xml then "<i>identical</i>(" else "identical(" )^ (show_term r) ^ "," ^ (show_term r') ^ ")"
 | Reach -> if !use_xml then "<r>reach</r>" else "reach"
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
    "<raw_st><nbvars>%d</nbvars>\n<statement> %s &lt;== %s </statement>%s %s %s\n<recipes>%s</recipes></raw_st>\n" st.nbvars (show_predicate st.head)(show_atom_list st.body)(show_inputs st.inputs)(show_dag st.dag)(show_choices st.choices)(show_inputs st.recipes)
  else
  Format.sprintf
    "(%d%s) %s <== %s \n       %s %s %s\n       %s\n" st.nbvars (show_binder !(st.binder)) (show_predicate st.head)(show_atom_list st.body)(show_inputs st.inputs)(show_dag st.dag)(show_choices st.choices)(show_inputs st.recipes) in 
  string ^ if not (check_binder_st st) then (st.binder := Rule;  " BINDER ERROR " ) else ""
  
let show_chan_key chkey =
   if !use_xml then 
      Format.sprintf "<ckey>%s %s %d</ckey>\n" chkey.c.name (match chkey.io with In -> "in" | Out -> "out") chkey.ph
    else
      Format.sprintf "[%s]%s-%d" chkey.c.name (match chkey.io with In -> "in" | Out -> "out") chkey.ph
  
let show_chan_statements chmap =
  ChanMap.fold ( fun key lst str -> str ^ "\n<chanset>" ^ (show_chan_key key) ^(List.fold_left (fun str (l,t,terms,st,pr) -> 
    str ^
    if !use_xml then 
      Format.sprintf "<hidden>%d %s</hidden>\n" l.p (show_raw_statement st)
    else
      Format.sprintf "loc %d, %s\n" l.p (show_raw_statement st)
  ) ": " lst) ^ "</chanset>") chmap ""

let show_hash_test st =
  let string = 
  Format.sprintf
    "(%d%s) T <== %s \n       %s %s %s\n" st.htnbvars (show_binder !(st.htbinder)) (show_atom_list st.htbody)(show_inputs st.htinputs)(show_dag st.htdag)(show_choices st.htchoices) in 
  string

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

  
(** Getters **)

let get_test_head head = 
  match head with
  | Tests(eq) -> eq
  | _ -> assert false

(** Substitutions **)

let apply_subst_test_head head (sigma : substitution) = 
  {
    head_binder = sigma.binder;
    equalities=EqualitiesSet.map (fun (r,r') -> (Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term r' sigma)) head.equalities;
    disequalities=EqualitiesSet.map (fun (r,r') -> (Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term r' sigma)) head.disequalities
  }
     
let apply_subst_pred pred sigma  = 
match pred with
  | Knows(r,t) -> 
     Knows(Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term t sigma)
  | Identical(r,r') -> 
     Identical(Rewriting.apply_subst_term r sigma, Rewriting.apply_subst_term r' sigma)
  | Reach -> Reach
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
  
(** constructor **)
let new_statement () = {
  id = -1 ; vip = false ; st = null_raw_statement; children = []; process = None;
  master_parent = null_statement; slave_parent = null_statement;test_parent = null_statement
  }

let new_base () =
  let kb = 
  {
     next_id = 0;
     solved_deduction = new_statement () ;
     rid_solved = new_statement ();
     (*identity_solved = [] ;
     reachable_solved = [];*)
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

  
let canonize_statement st = 
  { st with (*either the head is not a test or the head is a test and hash_test does not consider it *)
    dag = canonize_dag st.dag;
    inputs = canonize_inputs st.inputs;
    recipes = canonize_inputs st.recipes;
    choices = canonize_choices st.choices
  }

let raw_to_hash_statement st = { hbinder = st.binder ; hnbvars = st.nbvars; hdag = st.dag; hinputs= st.inputs; hrecipes=st.recipes; hchoices= st.choices; hhead = st.head;hbody=st.body}

let raw_to_hash_test st = { htbinder = st.binder ; htnbvars = st.nbvars; htdag = st.dag; htinputs= st.inputs; htrecipes=st.recipes; htchoices= st.choices; htbody=st.body}
