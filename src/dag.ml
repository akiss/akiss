
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



(**
  Printers
**)

let show_loc_set ls =
  (*let l_save = ref null_location in
  let first = ref true in
  
  LocationSet.iter (fun l ->
    if !first 
    then (l_save := l; first := false)
    else (assert (Location.compare !l_save l <= 0); l_save := l)
  ) ls;*)
  
  (*print_string "\n\nshow_loc\n";
  LocationSet.iter (fun l -> Printf.printf "%d," l.p) ls;
  print_string "\n";
  *)
  let r = LocationSet.fold (fun l str -> (if str = "" then "" else str ^ "," ) ^ (string_of_int l.p)) ls "" in
  (* Printf.printf "Version with Fold : %s\nend of show_loc\n\n" r;*)
  r;;

let show_dag dag =
  if !Util.use_xml then 
  (Dag.fold (fun l ls str -> str ^(if LocationSet.is_empty ls 
    then (Format.sprintf "<findex>%d</findex>" l.p) 
    else ((Format.sprintf "<index>%d</index><succ>" l.p) ^ (show_loc_set ls) ^ "</succ>")
    )) dag.rel "<dag>")^"</dag>"
  else
  (Dag.fold (fun l ls str -> str ^(Format.sprintf " %d<" l.p) ^ (show_loc_set ls)) dag.rel "{")^"}"


(**
  Dag stuff
**)

(* for hash tables *)
let canonize_dag dag = {rel = List.fold_left (fun dag' (l,ls) -> Dag.add l (LocationSet.of_list (LocationSet.elements ls)) dag') Dag.empty (Dag.bindings dag.rel)}

let empty = {rel = Dag.empty}

let is_empty dag = Dag.is_empty dag.rel

let singleton l1 l2 =
  { rel = Dag.add l2 LocationSet.empty (Dag.singleton l1 (LocationSet.singleton l2))}

let put_at_end dag loc =
  {rel = Dag.add loc (LocationSet.empty)(Dag.map (fun set -> LocationSet.add loc set) dag.rel)}

 exception E
let subset dag1 dag2 =
  (*let exception E in *)
  try ignore (Dag.merge (fun loc set1 set2 -> 
    match (set1,set2) with
    | (Some set1, Some set2) -> if not (LocationSet.subset set1 set2) then raise E else None
    | (Some set1, None) -> raise E
    | (None,  _) -> None) dag1.rel dag2.rel); true
  with E -> false

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

let is_before dag l1 l2 =
  match l1, l2 with 
  | Some l1, Some l2 -> begin
   try
   LocationSet.mem l2 (Dag.find l1 dag.rel)
   with 
   | Not_found -> false end 
  | None , Some _ -> true
  | _ -> false

(* To replace a recipe by a one that should be created before *)
let should_be_before dag l1 l2 =
  match l1, l2 with 
  | Some l1, Some l2 -> begin
   try
   LocationSet.mem l2 (Dag.find l1 dag.rel)
   with 
   | Not_found -> false end 
  | None , Some _ -> false
  | Some _, None -> true
  | None,None -> false (* in this case the recipe number matter *)

let is_cyclic dag =
  Dag.exists (fun l ls -> LocationSet.exists (fun l' -> l=l') ls) dag.rel

exception Impossible

(* create the dag where the last location of dag are before l, check that phases of dag are before l too  *)  
let final dag l=
  let final = Dag.filter (fun k set -> 
    if LocationSet.is_empty set then 
      if k.phase > l.phase then raise Impossible else true else false) dag.rel in
  {rel = Dag.map (fun _ -> LocationSet.singleton l) final}

(* For execution *)

let dag_with_one_action_at_end locs action =
  let set_a = LocationSet.singleton action in 
  { rel = LocationSet.fold (fun l dag -> Dag.add l set_a dag) locs (Dag.singleton action LocationSet.empty)}
  
  
let first_actions_among dag locs =
  let first = LocationSet.filter (fun k -> Dag.for_all (fun k' locset -> 
  not (LocationSet.mem k' locs) || not (LocationSet.mem k locset)) dag.rel) locs in
  first

(* For execution and completions *)  
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
let expurge_dag_after dag loc =
  {rel= Dag.filter (fun l lset -> not (LocationSet.mem l (Dag.find loc dag.rel))) dag.rel}
  
let preceding_dag dag loc =
  {rel= Dag.filter (fun l lset ->  (LocationSet.mem loc (Dag.find l dag.rel))) dag.rel}
  
let dag_with_actions_at_end locs lset = 
  { rel = LocationSet.fold (fun l dag -> Dag.add l lset dag) locs (Dag.empty)}

(* let () =
   let ch : Parser_functions.chanId= {name="c";id=0}  in
   let l1 = {p= 1; chan=ch} in
   let l2 = {p= 2; chan=ch} in
   let l3 = {p=3; chan=ch} in
   let l4 ={p=4; chan=ch} in
   let dag12 = singleton l1 l2 in
   let dag23 = singleton l2 l3 in
   let dag = merge dag12 dag23 in
   let dag24 = singleton l2 l4 in
   let dagc = merge dag dag24 in
   if not (is_cyclic dagc) then
   print_dag dagc
   *)
