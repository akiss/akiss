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
(*    val mem : key -> 'a t -> bool
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
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) Seq.t -> 'a t *)
  end
module BangSet :
  sig
    type elt = BangLocation.t
    type t = Set.Make(BangLocation).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
(*    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
    val to_seq_from : elt -> t -> elt Seq.t
    val to_seq : t -> elt Seq.t
    val add_seq : elt Seq.t -> t -> t
    val of_seq : elt Seq.t -> t *)
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
type process_infos = { first_location : int; first_nonce : int; }
type processes_infos = {
  mutable next_location : int;
  mutable next_nonce : int;
  mutable processes : process_infos BangDag.t;
  mutable location_list : Types.location list;
  mutable nonce_list : Types.nonceId list;
  mutable max_phase : int;
}
val processes_infos : processes_infos
val show_action : action -> string
val show_process : process -> string
val show_process_start : int -> process -> string
(*val count_type_nb : Types.typ -> Types.procId -> int -> int
val convert_term :
  Types.procId ->
  Types.location array ->
  Types.nonceId array ->
  Types.term array -> Types.relative_temp_term -> Types.term
val convert_chan :
  Types.procId ->
  Types.chanId array -> Types.relative_temp_term -> Types.chanId
val new_nonce : string -> int -> Types.nonceId
val new_location :
  Types.procId ->
  int -> Types.io -> string -> Types.location option -> int -> Types.location*)
val convert_pr :
  Types.procId * int * int * Types.location array * Types.nonceId array *
  Types.term array * Types.chanId array ->
  Types.bounded_process -> Types.location option -> int -> process
val memoize_call: (Types.location * int * Types.term array * Types.chanId array,process) Hashtbl.t
val expand_call :
  Types.location ->
  int -> Types.procId -> Types.term array -> Types.chanId array -> process
val repl_hidden_loc :
  Types.location -> Types.term -> Types.term -> Types.term
val apply_subst_action : Types.location -> Types.term -> action -> action
val apply_subst_process : Types.location -> Types.term -> process -> process
