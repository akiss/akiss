module VarAux : sig type t = Types.varId val compare : 'a -> 'a -> int end
module VariableSet :
  sig
    type elt = VarAux.t
    type t = Set.Make(VarAux).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
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
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val of_list : elt list -> t
  end
module VarMap :
  sig
    type key = VarAux.t
    type 'a t = 'a Map.Make(VarAux).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
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
    val max_binding : 'a t -> key * 'a
    val choose : 'a t -> key * 'a
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  end
val var_set_of_term_list : VariableSet.t -> Types.term list -> VariableSet.t
val var_set_of_term : VariableSet.t -> Types.term -> VariableSet.t
val is_var : Types.term -> bool
val unbox_var : Types.term -> Types.varId
val vars_of_term_list : Types.term list -> Types.varId list
val vars_of_term : Types.term -> Types.varId list
val apply_var_set_subst : Types.term -> Types.term VarMap.t -> Types.term
val is_ground : Types.term -> bool
val occurs : Types.varId -> Types.term -> bool
val apply_subst : Types.term -> Types.subst_lst -> Types.term
val bound : 'a -> ('a * 'b) list -> bool
val apply_subst_term_list :
  Types.term list -> Types.subst_lst -> Types.term list
val show_subst : (Types.varId * Types.term) list -> string
val show_subst_list : (Types.varId * Types.term) list list -> string
val show_variant : Types.term * (Types.varId * Types.term) list -> string
val show_variant_list :
  (Types.term * (Types.varId * Types.term) list) list -> string
val compose :
  Types.subst_lst -> Types.subst_lst -> (Types.varId * Types.term) list
val restrict :
  Types.subst_lst -> Types.varId list -> (Types.varId * Types.term) list
