module EqualitiesSet :
  sig
    type elt = Types.term * Types.term
    type t
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
(*    val exists : (elt -> bool) -> t -> bool
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
    val of_seq : elt Seq.t -> t*)
  end
type test_head = {
  head_binder : Types.statement_role ref;
  mutable equalities : EqualitiesSet.t;
  mutable disequalities : EqualitiesSet.t;
}
type predicate =
    Knows of Types.term * Types.term
  | Reach
  | Identical of Types.term * Types.term
  | Tests of test_head
  | Unreachable
type body_atom = {
  loc : Dag.LocationSet.t;
  recipe : Types.term;
  term : Types.term;
  marked : bool;
}
type raw_statement = {
  binder : Types.statement_role ref;
  nbvars : int;
  dag : Dag.dag;
  inputs : Inputs.inputs;
  choices : Inputs.choices;
  head : predicate;
  body : body_atom list;
  recipes : Inputs.inputs;
  involved_copies : Process.BangSet.t;
}
type hash_statement = {
  hbinder : Types.statement_role ref;
  hnbvars : int;
  hdag : Dag.dag;
  hinputs : Inputs.inputs;
  hrecipes : Inputs.inputs;
  hchoices : Inputs.choices;
  hhead : predicate;
  hbody : body_atom list;
}
type hash_test = {
  htbinder : Types.statement_role ref;
  htnbvars : int;
  htdag : Dag.dag;
  htinputs : Inputs.inputs;
  htrecipes : Inputs.inputs;
  htchoices : Inputs.choices;
  htbody : body_atom list;
}
val null_raw_statement : raw_statement
type statement = {
  id : int;
  vip : bool;
  st : raw_statement;
  mutable children : statement list;
  process : Process.process option;
  master_parent : statement;
  slave_parent : statement;
  test_parent : statement;
}
val null_statement : statement
type i_o = In | Out
type chankey = { c : Types.chanId; io : i_o; ph : int; }
val switch_io : i_o -> i_o
module ChanMap :
  sig
    type key = chankey
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
(*    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
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
    val split : key -> 'a t -> 'a t * 'a option * 'a t*)
    val find : key -> 'a t -> 'a 
    val find_opt : key -> 'a t -> 'a option
(*    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) Seq.t -> 'a t*)
  end
type base = {
  mutable next_id : int;
  solved_deduction : statement;
  rid_solved : statement;
  mutable unreachable_solved : statement list;
  not_solved : statement;
  temporary_merge_test : statement;
  mutable temporary_merge_test_result : statement list;
  mutable s_todo : statement Queue.t;
  mutable ns_todo : statement Queue.t;
  mutable hidden_chans :
    (Types.location * Types.term option * (Types.term * Types.term) list *
     raw_statement * Process.process)
    list ChanMap.t;
  htable : (hash_statement, statement) Hashtbl.t;
}
(*val check_binder_term : Types.statement_role ref -> Types.term -> bool
val check_binder_head : Types.statement_role ref -> predicate -> bool
val check_binder_st : raw_statement -> bool*)
val show_test_head : test_head -> string
val show_predicate : predicate -> string
val show_body_atom : body_atom -> string
val show_atom_list : body_atom list -> string
val show_raw_statement : raw_statement -> string
val show_hash_test : hash_test -> string
val show_statement : string -> statement -> string
val show_statement_list : string -> statement list -> string
val show_statements_id : statement list -> string
val count_statements : statement -> int
val show_kb : base -> string
val get_test_head : predicate -> test_head
val apply_subst_test_head : test_head -> Types.substitution -> test_head
val apply_subst_pred : predicate -> Types.substitution -> predicate
val apply_subst_statement :
  raw_statement -> Types.substitution -> raw_statement
val new_statement : unit -> statement
val new_base : unit -> base
val canonize_statement : raw_statement -> raw_statement
val raw_to_hash_statement : raw_statement -> hash_statement
val raw_to_hash_test : raw_statement -> hash_test
