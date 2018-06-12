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

type predicate =
  | Knows of term * term
  | Reach
  | Identical of term * term
  | Tests of (EqualitiesSet.t * EqualitiesSet.t)
  | Unreachable

type body_atom = {
   loc : location option;
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
}

(*for hash table *)
type hash_statement = {
  hbinder : statement_role ref;
  hnbvars : int ;
  hdag : dag ;
  hinputs :  inputs ;
  hchoices : choices ;
  hhead : predicate ;
  hbody : body_atom list ;
}

let null_raw_statement = { binder = ref New ; nbvars = 0; dag = empty; inputs= new_inputs; choices= new_choices; head = Reach;body=[];recipes=new_inputs}

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

type base = 
{ 
   mutable next_id : int ;
   solved_deduction : statement ; (* to preserve structure solved_deduction link to a statement whose children are the actual ones *)
   rid_solved : statement ; (* to have a tree structure for the tests *)
   (*mutable identity_solved :  statement list; 
   mutable reachable_solved : statement list ;*)
   mutable unreachable_solved : statement list; 
   not_solved : statement ;
   mutable s_todo : statement Queue.t ; 
   mutable ns_todo : statement Queue.t ; 
   htable : (hash_statement, statement) Hashtbl.t;
}


let rec check_binder_term binder term =
  match term with
  | Var(x) -> x.status == binder
  | Fun(_,lst) -> List.for_all (check_binder_term binder) lst
  
let check_binder_st st =
  let binder = st.binder in
  Dag.for_all (fun _ t -> check_binder_term binder t) st.inputs.i
  && Dag.for_all (fun _ t -> check_binder_term binder t) st.recipes.i
  && List.for_all (fun x -> check_binder_term binder x.term && check_binder_term binder x.recipe) st.body

(** {3 Printing} *)

let rec show_predicate p = 
 match p with
 | Knows(r,t) -> if !use_xml then "<pred>K(<rec>"^ (show_term r) ^ "</rec>,<term>" ^ (show_term t) ^ "</term>)</pred>" else
      "knows(" ^ (show_term r) ^ "," ^ (show_term t) ^ ")"
 | Identical(r,r') ->
      "identical(" ^ (show_term r) ^ "," ^ (show_term r') ^ ")"
 | Reach -> "reach"
 | Unreachable -> "unreach"
 | Tests(equal,diseq) -> 
    "tests(" ^ (EqualitiesSet.fold ( fun (r,r') str -> (if str = "" then "" else str ^ ", ") ^ (show_term r) ^ "=" ^ (show_term r') ) equal "" ) 
    ^  ";" ^ (EqualitiesSet.fold ( fun (r,r') str -> (if str = "" then "" else str ^ ", ") ^ (show_term r) ^ "!=" ^ (show_term r') ) diseq "")^ ")"

let show_body_atom a =
  let l = match a.loc with Some l -> string_of_int l.p | None -> "." in
  if !use_xml then 
  "<pred>K<loc>"^l^"</loc>(<rec>"^(show_term a.recipe)^"</rec>,<term>"^(show_term a.term)^"</term>)</pred>"
  else
  "knows_"^l^"("^(show_term a.recipe)^","^(show_term a.term)^")"


let rec show_atom_list lst = Format.sprintf "%s" (String.concat ", " (trmap show_body_atom lst))

let show_raw_statement st =
  let string = 
  if !use_xml then
  Format.sprintf
    "<raw_st><nbvars>%d</nbvars>\n<statement> %s &lt;== %s </statement>%s %s %s\n<recipes>%s</recipes></raw_st>\n" st.nbvars (show_predicate st.head)(show_atom_list st.body)(show_inputs st.inputs)(show_dag st.dag)(show_choices st.choices)(show_inputs st.recipes)
  else
  Format.sprintf
    "(%d%s) %s <== %s \n       %s %s %s\n       %s\n" st.nbvars (show_binder !(st.binder)) (show_predicate st.head)(show_atom_list st.body)(show_inputs st.inputs)(show_dag st.dag)(show_choices st.choices)(show_inputs st.recipes) in 
  assert (check_binder_st st);
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
   ^"</tests><unreachables>"^(show_statement_list " " (kb.unreachable_solved))^"</unreachables></base>\n"  
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
(*  ^ "Todo solved: " ^ (show_statements_id kb.s_todo)
  ^ "\nTodo not solved: " ^ (show_statements_id kb.ns_todo)*)
  ^ "\n"

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
     s_todo = Queue.create () ;
     ns_todo = Queue.create() ;
     htable = Hashtbl.create 10000 ;
  } in
  kb 

let canonize_head head =
  match head with
  | Tests(eq,diseq) -> Tests(EqualitiesSet.of_list (EqualitiesSet.elements eq),EqualitiesSet.of_list (EqualitiesSet.elements diseq))
  | _ -> head
  
let canonize_statement st = 
  { st with
    head = canonize_head st.head;
    dag = canonize_dag st.dag;
    inputs = canonize_inputs st.inputs;
    recipes = canonize_inputs st.recipes;
    choices = canonize_choices st.choices
  }

let raw_to_hash_statement st = { hbinder = st.binder ; hnbvars = st.nbvars; hdag = st.dag; hinputs= st.inputs; hchoices= st.choices; hhead = st.head;hbody=st.body}
