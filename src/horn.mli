val statement_f0 : Base.raw_statement
val statement_f1 : Base.raw_statement
val statement_f2 : Base.raw_statement
val is_deduction_st : Base.raw_statement -> bool
val is_equation_st : Base.raw_statement -> bool
val is_reach_st : Base.raw_statement -> bool
val is_test_st : Base.raw_statement -> bool
val is_solved_atom : Base.body_atom -> bool
val is_solved : Base.raw_statement -> bool
val find_unsolved : Base.raw_statement -> Base.body_atom
val explode_term : Types.term -> Types.term list * Types.term list
val vars_of_atom : Base.predicate -> Types.varId list
val get_head_recipe : Base.predicate -> Types.term
val get_head_term : Base.predicate -> Types.term
exception Not_a_linear_combination
val xor_var : 'a list -> 'a list -> 'a list
(*val remove_rows :
  'a ->
  'b list ->
  'c list -> ('c * 'b list * 'c list) list -> 'a * 'b list * 'c list
val find_var :
  Types.varId ->
  Base.body_atom list ->
  (Types.varId * Types.term list * Types.varId list) list ->
  (Types.varId * Types.term list * Types.varId list) * Base.body_atom
val find_xor_sum :
  Types.varId list ->
  Base.body_atom list ->
  (Types.varId * Types.term list * Types.varId list) list -> Types.term list
val get_recipe_for_sum : Types.term list -> Base.raw_statement -> Types.term*)
exception Not_a_consequence
(*exception Bad_World
exception Restricted_World
exception Bad_case
val first : Base.statement -> (Base.raw_statement -> 'a) -> 'a
val first_sigma : 'a list -> ('a -> 'b) -> 'b
val inst_w_t :
  bool -> Base.raw_statement -> Base.raw_statement -> Types.subst_lst list
val print_trace :
  Format.formatter ->
  ([< `Axiom | `Res of Base.raw_statement * 'a list ] as 'a) -> unit
val consequence :
  bool ->
  Base.raw_statement ->
  Base.statement -> Types.rewrite_rule list -> Types.term
val rule_shift : Base.raw_statement -> Base.raw_statement *)
exception No_Eval
exception Unsound_Statement
(*val eval_recipe :
  Inputs.choices ->
  Inputs.inputs -> Base.body_atom list -> Types.term -> Types.term*)
val simplify_statement :
  Base.raw_statement -> Types.substitution * Base.raw_statement
val canonical_form : Base.statement -> Base.raw_statement -> (Types.substitution * Base.raw_statement) list
val is_identity_of_theory : Base.raw_statement -> bool
(*val normalize_identical : 'a -> 'a*)
val normalize_new_statement : Base.raw_statement -> Base.raw_statement option
(*val update : Base.base -> Base.raw_statement -> Base.raw_statement option
val resolution_plus : Base.raw_statement -> Base.raw_statement list
val is_tuple : Types.term -> bool
val resolution :
  Types.subst_maker ->
  Inputs.choices ->
  Dag.dag ->
  Base.raw_statement -> Base.raw_statement -> Base.raw_statement list
val equation :
  Types.subst_maker ->
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
val process_equation : Base.base -> Base.statement -> Base.statement -> unit*)
val merge_sat : Base.base -> unit
val saturate : Types.procId -> int * Base.base
val clean_recipe_variable : Base.raw_statement -> Base.raw_statement
val filter_map: ('a -> 'b option) -> 'a list -> 'b list
