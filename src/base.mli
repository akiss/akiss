type predicate =
    Knows of Types.term * Types.term
  | Reach
  | Identical of Types.term * Types.term
  | Tests of
      ((Types.term * Types.term) list * (Types.term * Types.term) list)
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
