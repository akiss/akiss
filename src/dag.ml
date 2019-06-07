(** partial ordered sets of locations *)

open Types

module Location =
       struct
         type t = location
         let compare x y =
           compare (x.p:int) (y.p:int)
       end

module LocationSet = Set.Make(Location)

module Dag = Map.Make(Location)

type dag = {
  rel : LocationSet.t Dag.t ;
}

let empty_loc = LocationSet.empty

(**  {2 Printers} *)

let show_loc_set ls =
  LocationSet.fold (fun l str -> (if str = "" then "" else str ^ "," ) ^ (string_of_int l.p)) ls "" 

let show_dag dag =
  if !Util.use_xml then 
  (Dag.fold (fun l ls str -> str ^(if LocationSet.is_empty ls 
    then (Format.sprintf "<findex>%d</findex>" l.p) 
    else ((Format.sprintf "<index>%d</index><succ>" l.p) ^ (show_loc_set ls) ^ "</succ>")
    )) dag.rel "<dag>")^"</dag>"
  else
  (Dag.fold (fun l ls str -> str ^(Format.sprintf " %d<" l.p) ^ (show_loc_set ls)) dag.rel "{")^"}"


  



(** {2 for hash tables} *)
type hash_locset = int list
type hash_dag = (int * hash_locset) list 

let locset_to_hash ls = List.map (fun l' -> l'.p) (LocationSet.elements ls)
let dag_to_hash dag = List.map (fun (l,ls) -> (l.p, (locset_to_hash ls))) (Dag.bindings dag.rel)

(** {2 Dag functions}*)
let empty = {rel = Dag.empty}

let is_empty dag = Dag.is_empty dag.rel

let singleton l1 l2 =
  { rel = Dag.add l2 LocationSet.empty (Dag.singleton l1 (LocationSet.singleton l2))}

let put_at_end dag loc =
  {rel = Dag.add loc (LocationSet.empty)(Dag.map (fun set -> LocationSet.add loc set) dag.rel)}

 
let subset dag1 dag2 =
  let exception E in 
  try ignore (Dag.merge (fun loc set1 set2 -> 
    match (set1,set2) with
    | (Some set1, Some set2) -> if not (LocationSet.subset set1 set2) then raise E else None
    | (Some set1, None) -> raise E
    | (None,  _) -> None) dag1.rel dag2.rel); true
  with E -> false

(** Used in conseq: check that dag1 is included in dag2 and do not contain final indexes *)  
let strict_subset dag1 dag2 =
  let exception E in 
  try ignore (Dag.merge (fun loc set1 set2 -> 
    match (set1,set2) with
    | (Some set1, Some set2) -> if not (LocationSet.subset set1 set2) || LocationSet.is_empty set2 then raise E else None
    | (Some set1, None) -> raise E
    | (None,  _) -> None) dag1.rel dag2.rel); true
  with E -> false

let order_from_recipes_and_inputs recipe_locs input_locs =  
  {rel= LocationSet.fold (fun l dag -> Dag.add l input_locs dag) recipe_locs Dag.empty}
  
let merge dag1 dag2 =
   let one_side dag1 dag2 =
   Dag.fold (fun o seti newdag -> 
     Dag.add
     o (LocationSet.fold (fun i dag'  -> 
       try let dests = Dag.find i dag2.rel in 
         LocationSet.union dag' dests
       with 
       | Not_found -> dag' ) seti seti ) newdag
    ) dag1.rel Dag.empty in    
   let map1 = one_side dag1 dag2 in
   let map2 = one_side dag2 dag1 in
   {rel= Dag.union (fun loc set1 set2 -> Some (LocationSet.union set1 set2)) map1 map2}
   
let merge dag1 dag2 =
  merge dag1 (merge (merge dag1 dag2) dag2)

let is_before_all dag l locs =
  try
    LocationSet.is_empty (LocationSet.diff locs (Dag.find l dag.rel))
  with 
  | Not_found -> assert false

(** For [truncconj] *)
let restr_set dag dag1 locs2 =
  Dag.fold (fun l1 _ locset ->
  if (List.mem l1 locs2) ||
   ( List.exists 
    (fun l2 -> LocationSet.mem l2 (try Dag.find l1 dag.rel with Not_found -> assert false)) locs2)
  then
    LocationSet.add l1 locset
  else locset 
  ) dag1.rel LocationSet.empty
  
(** for recipize *)  
let before_dag dag locs =
 { rel=  Dag.filter (fun l after ->  (LocationSet.subset locs after)) dag.rel}

(** for [merge_test] *)
let is_cyclic dag =
  Dag.exists (fun l ls -> LocationSet.exists (fun l' -> l=l') ls) dag.rel
  
  

exception Impossible

(* create the dag where the last location of dag are before l, check that phases of dag are before l too  *)  
(*let final dag l=
  let final = Dag.filter (fun k set -> 
    if LocationSet.is_empty set then 
      if k.phase > l.phase then raise Impossible else true else false) dag.rel in
  {rel = Dag.map (fun _ -> LocationSet.singleton l) final}*)
  
(** for [resolution] *)  
let put_set_at_end dag locset =
  let minphase= LocationSet.fold (fun l minphase -> min minphase l.phase) locset 1000000 in
  {rel = Dag.mapi (fun loc lset -> if minphase < loc.phase then raise Impossible else LocationSet.union lset locset) dag.rel}

(** For execution *)
let dag_with_one_action_at_end locs action =
  let set_a = LocationSet.singleton action in 
  { rel = LocationSet.fold (fun l dag -> Dag.add l set_a dag) locs (Dag.singleton action LocationSet.empty)}
  
  
let first_actions_among dag locs =
  let first = LocationSet.filter 
    (fun k -> Dag.for_all 
      (fun k' locset -> 
           not (LocationSet.mem k' locs) 
        || not (LocationSet.mem k locset)) dag.rel) locs in
  first
  
let only_observable dag = dag
  (*{rel = Dag.fold (fun l lset dag -> if l.observable = Public then Dag.add l (LocationSet.filter (fun l -> l.observable = Public) lset) dag else dag) dag.rel Dag.empty}*)

(** For execution and completions *)  
let last_actions_among dag locs =
  let last = LocationSet.filter ( fun k -> LocationSet.equal (LocationSet.diff locs (Dag.find k dag.rel) ) locs) locs in
  last

let locations_of_dag dag =   
  Dag.fold (fun loc _ locset -> LocationSet.add loc locset) dag.rel LocationSet.empty
  
let pick_last_or_null dag locs =
  let last = last_actions_among dag locs in
  try 
    LocationSet.choose last
  with Not_found -> null_location
  
(* For finding recipes in test.ml, merge_tests*)
(*let expurge_dag_after dag locs =
  {rel= Dag.filter (fun l lset -> not (LocationSet.is_empty (LocationSet.inter locs lset))) dag.rel}*)
  
(* The <. operator from the theory *)  
(*let preceding_dag dag locs =
  {rel= Dag.filter (fun l lset ->  (LocationSet.is_empty (LocationSet.diff locs lset))) dag.rel}*)
  
(*let dag_with_actions_at_end locs lset = 
  { rel = LocationSet.fold (fun l dag -> Dag.add l lset dag) locs (Dag.empty)}*)

(** For printing traces *)
let last_actions dag =
 Dag.fold ( fun k  locs result -> if LocationSet.is_empty locs then LocationSet.add k result else result) dag.rel LocationSet.empty
