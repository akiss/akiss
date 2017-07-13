type predicate =
    Knows of Types.term * Types.term
  | Reach
  | Identical of Types.term * Types.term
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
  head : predicate;
  body : body_atom list;
}
val null_raw_statement : raw_statement
type statement = {
  id : int;
  vip : bool;
  st : raw_statement;
  mutable children : statement list;
  process : Process.process option;
}
type base = {
  rules : Types.rewrite_rule list;
  mutable next_id : int;
  mutable next_location : int;
  mutable next_nonce : int;
  solved_deduction : statement;
  mutable other_solved : statement list;
  not_solved : statement;
  mutable s_todo : statement list;
  mutable ns_todo : statement list;
  htable : (raw_statement, statement) Hashtbl.t;
}
val show_predicate : predicate -> string
val show_body_atom : body_atom -> string
val show_atom_list : body_atom list -> string
val show_raw_statement : raw_statement -> string
val show_statement : string -> statement -> string
val show_statement_list : string -> statement list -> string
val show_statements_id : statement list -> string
val show_kb : base -> string
val new_statement : unit -> statement
val new_base : Types.rewrite_rule list -> base