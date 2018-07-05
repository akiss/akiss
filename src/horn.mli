val use_ac : bool
val use_xor : bool
val drop_reflexive : bool
val drop_non_normal_skel : bool
val renormalize_recipes : bool
val eqrefl_opt : bool
val opti_sort : bool
val apply_shift_rule : bool
val use_conseq : bool
val print_flags : unit -> unit
val is_deduction_st : Base.raw_statement -> bool
val is_equation_st : Base.raw_statement -> bool
val is_reach_st : Base.raw_statement -> bool
val is_solved : Base.raw_statement -> bool
val vars_of_atom : Base.predicate -> Types.varId list
val get_head_recipe : Base.predicate -> Types.term
val get_term : Base.body_atom -> Types.term
val get_head_term : Base.predicate -> Types.term
val size : Base.raw_statement -> int
val get_id : Base.statement -> int
val get_head : Base.raw_statement -> Base.predicate
val get_body : Base.raw_statement -> Base.body_atom list
val rule_rename : 'a -> 'a
val rule_remove : 'a -> 'a
val rule_shift : Base.raw_statement -> Base.raw_statement
val simplify_statement : Base.raw_statement -> Base.raw_statement
val canonical_form : Base.raw_statement -> Base.raw_statement
exception Not_a_consequence
exception Bad_World
exception Bad_case
val first : Base.base -> (Base.raw_statement -> 'a) -> 'a
val inst_w_t :
  Base.raw_statement -> Base.raw_statement -> (Types.varId * Types.term) list
val print_trace :
  Format.formatter ->
  ([< `Axiom | `Res of Base.raw_statement * 'a list ] as 'a) -> unit
val consequence :
  Base.raw_statement -> Base.base -> Types.rewrite_rule list -> Types.term
val is_reflexive : Base.raw_statement -> bool
val normalize_identical : 'a -> 'a
val normalize_new_statement : Base.raw_statement -> Base.raw_statement option
val remove_marking : Base.raw_statement -> Base.raw_statement
val update :
  Base.base -> bool -> Base.raw_statement -> Base.raw_statement option
val resolution :
  Types.term option array * Types.term option array ->
  Inputs.choices ->
  Dag.dag ->
  Base.raw_statement -> Base.raw_statement -> Base.raw_statement list
val equation :
  Types.term option array * Types.term option array ->
  Inputs.choices ->
  Dag.dag ->
  Base.raw_statement -> Base.raw_statement -> Base.raw_statement list
val concretize : Inputs.inputs -> Types.term -> Types.term
val hidden_chan_statement :
  Base.base ->
  Dag.Dag.key * Types.term option * (Types.term * Types.term) list *
  Base.raw_statement * Process.process ->
  Dag.Dag.key * Types.term option * (Types.term * Types.term) list *
  Base.raw_statement * Process.process ->
  Base.statement -> Base.statement -> Base.statement -> unit
val trace_statements :
  Base.base ->
  (Types.term * Types.term) list ->
  Base.statement ->
  Base.statement ->
  Base.statement -> Process.process -> Base.raw_statement -> unit
val add_statement :
  Base.base ->
  Base.statement ->
  Base.statement ->
  Base.statement -> Process.process option -> Base.raw_statement -> unit
val theory_statements : Base.base -> Types.funName -> int -> unit
val extra_resolution : Base.base -> Base.statement -> Base.statement -> bool
val extra_equation : Base.base -> Base.statement -> Base.statement -> bool
val process_resolution_new_solved :
  Base.base -> Base.statement -> Base.statement -> unit
val process_resolution_new_unsolved :
  Base.base -> Base.statement -> Base.statement -> unit
val process_equation : Base.base -> Base.statement -> Base.statement -> unit
val saturate : Types.procId -> int * Base.base
