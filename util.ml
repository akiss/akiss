let debug_output = ref false;;

let verbose_output = ref false;;

let verboseOutput a =
  if !verbose_output then
    Printf.printf a
  else
    Printf.ifprintf stdout a
;;

let debugOutput a =
  if !debug_output then
    Printf.printf a
  else
    Printf.ifprintf stdout a
;;

(* TODO use the standard library:
 *  - List.rev is already tailrec
 *  - trmap_aux is List.rev (List.rev_map ..) *)

let rec trmap_aux f l a =
  match l with
    | [] -> List.rev a
    | h :: t ->
	trmap_aux f t ((f h) :: a)
;;

let trmap f l =
  trmap_aux f l []
;;

let rec trreverse_h l a =
  match l with
    | [] -> a
    | hd :: tl ->
	trreverse_h tl (hd :: a)
;;

let trreverse l =
  trreverse_h l []
;;


let rec trfoldmap_h f a l res =
  match l with
    | [] -> trreverse res
    | hd :: tl ->
	let next = f hd a in
	trfoldmap_h f next tl (next :: res)
;;

let rec trconcat_aux ll a =
  match ll with
    | [] -> a
    | h :: t ->
	trconcat_aux t (List.rev_append h a)
;;

let trconcat ll =
  trconcat_aux ll []
;;

let f res e = 
  if List.mem e res then 
    res 
  else 
    e::res;;

(* return a list without duplicates *)
let unique list = List.fold_left f [] list;;

(* create a list containing no times the element elem *)
let rec create_list elem no = 
  if no = 0 then
    []
  else
    elem :: (create_list elem (no - 1))
;;

let rec create_consecutive start no =
  if no = 0 then
    []
  else
    start :: (create_consecutive (start + 1) (no - 1))
;;

let counter = ref 0;;

let fresh_string prefix =
  let result = prefix ^ (string_of_int !counter) in
  (
    counter := !counter + 1;
    result
  )
;;

let fresh_variable () =
  fresh_string "X"
;;

let fresh_axiom () = 
  fresh_string "axiom"
;;

let combine list1 list2 =
  trconcat (trmap (function x ->
			   (trmap (function y -> (x, y)) list2)) list1)
;;

let list_diff big small = 
  List.filter (function x -> not (List.mem x small))  big
;;

let list_intersect list1 list2 = 
  List.filter (function x -> List.mem x list2) list1
;;

let rec is_prefix small big = match (small, big) with
  | ([], _) -> true
  | (s :: sr, b :: br) when s = b -> (is_prefix sr br)
  | _ -> false
;;

(* iterate f on a until a fixpoint is reached *)
let rec iterate f a =
  let next = f a in
  if next = a then
    a
  else
    iterate f next
;;

(* iterate "f" on "a" "n" times  *)
let rec iterate_n n f a =
  if n = 0 then
    a
  else
    iterate_n (n - 1) f (f a)
;;

let rec take n list =
  if n = 0 then
    []
  else
    match list with
      | hd :: tl -> hd :: take (n - 1) tl
      | [] -> []
;;

let rec all_prefixes = function
  | [] -> []
  | h :: t -> [] :: (trmap (fun x -> h :: x) (all_prefixes t))
;;

let show_string_list list =
  String.concat ", " list
;;
