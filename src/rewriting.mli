val show_subst_array : Types.term option array -> string
val copy_subst : 'a array * 'b array -> 'a array * 'b array
exception Not_unifiable
exception Not_matchable
val recompose_term : Types.term list -> Types.term
val find_sub : Types.varId -> 'a * 'a -> 'a
val is :
  Types.varId ->
  Types.term -> Types.term option array * Types.term option array -> bool
val occurs :
  Types.varId ->
  Types.term -> Types.term option array * Types.term option array -> bool
val occurs_list :
  Types.varId ->
  Types.term list ->
  Types.term option array * Types.term option array -> bool
val unify :
  (Types.term * Types.term) list ->
  (Types.term * Types.term) list ->
  Types.term option array * Types.term option array ->
  (Types.term * Types.term) list
val may_unify_plus :
  (Types.term * Types.term) list ->
  Types.term ->
  Types.term ->
  (Types.term * Types.term) list ->
  Types.term option array * Types.term option array ->
  (Types.term * Types.term) list
val csu :
  (Types.term * Types.term) list ->
  Types.term option array * Types.term option array ->
  (Types.term option array * Types.term option array) list
val get_option : 'a option -> 'a
val pack :
  Types.term option array * Types.term option array -> Types.substitution
val apply_subst_term : Types.term -> Types.substitution -> Types.term
val compose_master :
  Types.substitution -> Types.substitution -> Types.substitution
val compose : Types.substitution -> Types.substitution -> Types.substitution
val identity_subst : int -> Types.substitution
val merging_subst : int -> Types.statement_role ref -> Types.substitution
val sum_to_list : Types.term -> Types.term list
val equals_ac : Types.term -> Types.term -> bool
val list_equals_ac : Types.term list -> Types.term list -> bool
val new_or_same : 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
val explode_term :
  Types.term -> Types.varId list * Types.funInfos list * Types.term list
val match_ac :
  (Types.term * Types.term) list ->
  (Types.term * Types.term) list ->
  (Types.varId * Types.term) list ->
  (Types.term * Types.term) list * (Types.varId * Types.term) list
val may_match_plus :
  (Types.term * Types.term) list ->
  Types.term ->
  Types.term ->
  (Types.term * Types.term) list ->
  (Types.varId * Types.term) list ->
  (Types.term * Types.term) list * (Types.varId * Types.term) list
val csm : Types.term -> Types.term -> (Types.varId * Types.term) list list
val top_rewrite : Types.term -> Types.rewrite_rule -> Types.term list
val compare_term : Types.term -> Types.term -> int
val compare_term_list : Types.term list -> Types.term list -> int
val remove_duplicate : Types.term list -> Types.term list
val top_normalize :
  Types.term ->
  Types.rewrite_rule list -> Types.rewrite_rule list -> Types.term
val normalize : Types.term -> Types.rewrite_rule list -> Types.term
val equals_r : Types.term -> Types.term -> Types.rewrite_rule list -> bool
val trconcat : 'a list list -> 'a list
type position = int list
val show_position : position -> string
val show_positions : position list -> string
val show_configuration :
  Types.term * Types.substitution * position list -> string
val show_configurations :
  (Types.term * Types.substitution * position list) list -> string
val prepend : 'a -> 'a list list -> 'a list list
val init_pos : Types.term -> int list list
val at_position : Types.term -> int list -> Types.term
val repl_position : Types.term -> int list -> Types.term -> Types.term
val one_rule :
  Types.substitution ->
  Types.term ->
  int list -> Types.rewrite_rule -> (Types.term * Types.substitution) list
val all_rules :
  Types.substitution ->
  Types.term ->
  int list ->
  Types.rewrite_rule list -> (Types.term * Types.substitution) list
val is_prefix : 'a list -> 'a list -> bool
val down : 'a list list -> 'a list -> 'a list list
val one_step :
  Types.term * Types.substitution * int list list ->
  Types.rewrite_rule list ->
  (Types.term * Types.substitution * int list list) list
val iterate_once :
  (Types.term * Types.substitution * int list list) list ->
  Types.rewrite_rule list ->
  (Types.term * Types.substitution * int list list) list
val is_renaming : 'a -> 'a -> bool
val feed : 'a -> 'a list list -> 'a list list
val normalize_under :
  Types.term -> int list list -> Types.rewrite_rule list -> Types.term
val simplify_2 :
  Types.term ->
  'a * Types.substitution * int list list ->
  'b * Types.substitution * int list list ->
  Types.rewrite_rule list ->
  (Types.term * Types.substitution * int list list) option
val simplify_1 :
  Types.term * Types.substitution * int list list ->
  ('a * Types.substitution * int list list) list ->
  Types.term ->
  Types.rewrite_rule list ->
  (Types.term * Types.substitution * int list list) *
  ('a * Types.substitution * int list list) list
val simplify :
  Types.term ->
  (Types.term * Types.substitution * int list list) list ->
  Types.rewrite_rule list ->
  (Types.term * Types.substitution * int list list) list
val iterate_all :
  Types.term ->
  (Types.term * Types.substitution * int list list) list ->
  Types.rewrite_rule list ->
  (Types.term * Types.substitution * int list list) list
val max_var : int -> Types.term -> int
val one_unifier :
  Types.term ->
  Types.substitution ->
  Types.term -> Types.substitution -> Types.substitution list
val unifiers :
  int ->
  Types.term ->
  Types.term -> Types.rewrite_rule list -> Types.substitution list
val variants :
  int ->
  Types.term ->
  Types.rewrite_rule list -> (Types.term * Types.substitution) list
