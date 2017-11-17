
exception Bug

let bench = ref 0.
let bench_cur = ref 0.
let bench_start () = bench_cur := Sys.time ()
let bench_stop () = bench := !bench +. Sys.time () -. !bench_cur

let debug_output = ref false
let verbose_output = ref false
let about_seed = ref false
let debug_seed = ref false
let about_saturation = ref false
let debug_saturation = ref false
let about_tests = ref false
let debug_tests = ref false
let about_else = ref false
let debug_else = ref false
let about_execution = ref false
let debug_execution = ref false
let about_theory = ref false
let debug_theory = false
let about_traces = ref false
let about_maude = ref false
let about_canonization = ref false
let about_progress = ref false

(*let verboseOutput a =
  if !verbose_output || about_verbose then
    Format.printf a
  else
    Format.ifprintf Format.std_formatter a

let debugOutput a =
  if !debug_output || !about_debug then
    Format.printf a
  else
    Format.ifprintf Format.std_formatter a*)

let normalOutput a =
  if !verbose_output || !debug_output then
    Format.ifprintf Format.std_formatter a
  else
    Format.printf a

(* TODO use the standard library:
 *  - List.rev is already tailrec
 *  - is many places, trmap is useless, reversing would be harmless
 *  - stop using lists as sets *)

let trmap f l = List.rev (List.rev_map f l)

(** When using lists as sets List.concat is uselessly costly (not
  * tail-recursive) and the following union function is preferable.
  * It does not preserve the order. *)

let rec union acc = function
  | [] -> acc
  | traces :: l -> union (List.rev_append traces acc) l

let union l = union [] l

(** Return a list without duplicates, for structural equality. *)
let unique =
  let f res e = 
    if List.mem e res then 
      res 
    else 
      e::res
  in
    fun l -> List.fold_left f [] l

(** [create_list elem no]
  * creates a list containing [no] times the element [elem]. *)
let rec create_list elem no = 
  if no = 0 then
    []
  else
    elem :: (create_list elem (no - 1))

(** [create_consecutive start no] returns the list
  * [start;start+1;...;start+no-1] of length [no]. *)
let rec create_consecutive start no =
  if no = 0 then
    []
  else
    start :: (create_consecutive (start + 1) (no - 1))



let combine l1 l2 =
  List.fold_left
    (fun c e1 ->
       List.fold_left (fun c e2 -> (e1,e2)::c) c l2)
    []
    l1

let list_diff big small = 
  List.filter (function x -> not (List.mem x small))  big

let list_intersect list1 list2 = 
  List.filter (function x -> List.mem x list2) list1

let rec is_prefix small big = match (small, big) with
  | ([], _) -> true
  | (s :: sr, b :: br) when s = b -> (is_prefix sr br)
  | _ -> false

(* iterate f on a until a fixpoint is reached *)
let rec iterate f a =
  let next = f a in
  if next = a then
    a
  else
    iterate f next

(* iterate "f" on "a" "n" times  *)
let rec iterate_n n f a =
  if n = 0 then
    a
  else
    iterate_n (n - 1) f (f a)

let rec take n list =
  if n = 0 then
    []
  else
    match list with
      | hd :: tl -> hd :: take (n - 1) tl
      | [] -> []

let rec all_prefixes = function
  | [] -> []
  | h :: t -> [] :: (trmap (fun x -> h :: x) (all_prefixes t))

let show_string_list list =
  String.concat ", " list


let output_string ch s = Format.fprintf ch "%s" s

let rec pp_list pp sep chan = function
  | [] -> ()
  | [x] -> pp chan x
  | x::tl ->
      pp chan x ;
      output_string chan sep ;
      pp_list pp sep chan tl
