module BangLocation :
  sig
    type t = Types.location * int
    val compare : Types.location * 'a -> Types.location * 'a -> int
  end
module BangDag :
  sig
    type key = BangLocation.t
    type 'a t = 'a Map.Make(BangLocation).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  end
type action =
    Input of Types.location
  | Output of Types.location * Types.term
  | OutputA of Types.location * Types.term
  | Test of Types.term * Types.term
  | TestInequal of Types.term * Types.term
type process =
    EmptyP
  | ParallelP of process list
  | SeqP of action * process
  | ChoiceP of Types.location * (int * process) list
  | CallP of Types.location * int * Types.procId * Types.term array *
      Types.chanId array
type process_infos = {
  first_location : int;
  first_nonce : int;
  process : process;
}
type processes_infos = {
  mutable next_location : int;
  mutable next_nonce : int;
  mutable processes : process_infos BangDag.t;
  mutable location_list : Types.location list;
}
val processes_infos : processes_infos
val show_action : action -> string
val show_process : process -> string
val show_process_start : int -> process -> string
val count_type_nb : Types.typ -> Types.procId -> int -> int
val convert_term :
  Types.procId ->
  Types.location array ->
  Types.nonceId array ->
  Types.term array -> Types.relative_temp_term -> Types.term
val convert_chan :
  Types.procId ->
  Types.chanId array -> Types.relative_temp_term -> Types.chanId
val new_location :
  Types.procId ->
  int -> Types.io -> string -> Types.location option -> Types.location
val convert_pr :
  Types.procId * int * int * Types.location array * Types.nonceId array *
  Types.term array * Types.chanId array ->
  Types.bounded_process -> Types.location option -> process
val expand_call :
  Types.location ->
  int -> Types.procId -> Types.term array -> Types.chanId array -> process
