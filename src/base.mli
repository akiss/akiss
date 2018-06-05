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
type predicate =
    Knows of Types.term * Types.term
  | Reach
  | Identical of Types.term * Types.term
  | Tests of (EqualitiesSet.t * EqualitiesSet.t)
  | Unreachable
type body_atom = {
  loc : Types.location option;
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
}
type hash_statement = {
  hbinder : Types.statement_role ref;
  hnbvars : int;
  hdag : Dag.dag;
  hinputs : Inputs.inputs;
  hchoices : Inputs.choices;
  hhead : predicate;
  hbody : body_atom list;
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
type base = {
  mutable next_id : int;
  solved_deduction : statement;
  rid_solved : statement;
  mutable unreachable_solved : statement list;
  not_solved : statement;
  mutable s_todo : statement Queue.t;
  mutable ns_todo : statement Queue.t;
  htable : (hash_statement, statement) Hashtbl.t;
}
val show_predicate : predicate -> string
val show_body_atom : body_atom -> string
val show_atom_list : body_atom list -> string
val show_raw_statement : raw_statement -> string
val show_statement : string -> statement -> string
val show_statement_list : string -> statement list -> string
val show_statements_id : statement list -> string
val count_statements : statement -> int
val show_kb : base -> string
val new_statement : unit -> statement
val new_base : unit -> base
val canonize_statement : raw_statement -> raw_statement
val raw_to_hash_statement : raw_statement -> hash_statement
