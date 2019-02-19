module Location :
  sig
    type t = Types.location
    val compare : Types.location -> Types.location -> int
  end
module LocationSet :
  sig
    type elt = Location.t
    type t = Set.Make(Location).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t 
    val union : t -> t -> t
    val inter : t -> t -> t
(*    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool*)
    val iter : (elt -> unit) -> t -> unit
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
(*    val for_all : (elt -> bool) -> t -> bool *)
    val exists : (elt -> bool) -> t -> bool 
    val filter : (elt -> bool) -> t -> t
(*    val partition : (elt -> bool) -> t -> t * t *)
    val cardinal : t -> int
    val elements : t -> elt list
(*    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option *)
    val choose : t -> elt
(*    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t *)
    val find : elt -> t -> elt
(*    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option*)
    val of_list : elt list -> t 
  end
module Dag :
  sig
    type key = Location.t
    type 'a t = 'a Map.Make(Location).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
(*    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t *)
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
(*    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
    val iter : (key -> 'a -> unit) -> 'a t -> unit 
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
(*    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
    val cardinal : 'a t -> int 
    val bindings : 'a t -> (key * 'a) list
(*    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option *)
    val choose : 'a t -> key * 'a
(*    val choose_opt : 'a t -> (key * 'a) option
    val split : key -> 'a t -> 'a t * 'a option * 'a t *)
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option 
    val find_first : (key -> bool) -> 'a t -> key * 'a
(*    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option *)
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
(*    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) Seq.t -> 'a t *)
  end
type dag = { rel : LocationSet.t Dag.t; }
val empty_loc : LocationSet.t
val show_loc_set : LocationSet.t -> string
val show_dag : dag -> string
val canonize_dag : dag -> dag
val empty : dag
val is_empty : dag -> bool
val singleton : Dag.key -> Dag.key -> dag
val put_at_end : dag -> Dag.key -> dag
(*exception E*)
val subset : dag -> dag -> bool
val strict_subset : dag -> dag -> bool
val merge : dag -> dag -> dag
val is_before_all : dag -> Dag.key -> LocationSet.t -> bool
val restr_set : dag -> dag -> LocationSet.elt list -> LocationSet.t
val is_cyclic : dag -> bool
exception Impossible
val put_set_at_end : dag -> LocationSet.t -> dag
val dag_with_one_action_at_end : LocationSet.t -> LocationSet.elt -> dag
val first_actions_among : dag -> LocationSet.t -> LocationSet.t
val only_observable : dag -> dag
val last_actions_among : dag -> LocationSet.t -> LocationSet.t
val locations_of_dag : dag -> LocationSet.t
val pick_last_or_null : dag -> LocationSet.t -> LocationSet.elt
val last_actions : dag -> LocationSet.t
