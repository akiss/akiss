
open Types

module Location =
       struct
         type t = location
         let compare x y =
           compare x.p y.p
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
  LocationSet.fold (fun l str -> (if str = "" then "" else str ^ "," ) ^ (string_of_int l.p)) ls "";;

let show_dag dag =
  (Dag.fold (fun l ls str -> str ^(Format.sprintf " %d<" l.p) ^ (show_loc_set ls)) dag.rel "{")^"}"


(**
  Dag stuff
**)

let empty = {rel = Dag.empty}

let singleton l1 l2 =
  { rel = Dag.singleton l1 (LocationSet.singleton l2)}

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

let is_before dag l1 l2 =
  match l1, l2 with 
  | Some l1, Some l2 -> begin
   try
   LocationSet.mem l2 (Dag.find l1 dag.rel)
   with 
   | Not_found -> false end 
  | None , Some _ -> true
  | _ -> false

let is_cyclic dag =
  Dag.exists (fun l ls -> LocationSet.exists (fun l' -> l=l') ls) dag.rel

let final dag l=
  let final = Dag.filter (fun k set -> LocationSet.is_empty set) dag.rel in
  {rel = Dag.map (fun _ -> LocationSet.singleton l) final}

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