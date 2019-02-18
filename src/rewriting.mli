exception Not_unifiable
exception Call_Maude
val csu_ac :
  (Types.term * Types.term) list ->
  Types.subst_maker -> Types.subst_maker list
val csu_xor :
  (Types.term * Types.term) list ->
  Types.subst_maker -> Types.subst_maker list
val get_option : 'a option -> 'a
val pack : Types.subst_maker -> Types.substitution
val apply_subst_term : Types.term -> Types.substitution -> Types.term
(*val compose_master :
  Types.substitution -> Types.substitution -> Types.substitution*)
val compose : Types.substitution -> Types.substitution -> Types.substitution
val compose_with_subst_lst :
  Types.substitution -> (Types.varId * Types.term) list -> Types.substitution
val identity_subst : int -> Types.substitution
val merging_subst : int -> Types.statement_role ref -> Types.substitution
val is_identity_master : Types.substitution -> int -> bool
val equals_ac : Types.term -> Types.term -> bool
(*val list_equals_ac : Types.term list -> Types.term list -> bool*)
val recompose_term : Types.term list -> Types.term
(*val match_ac : bool ->
  (Types.term * Types.term) list ->
  (Types.term * Types.term) list ->
  (Types.varId * Types.term) list ->
  (Types.term * Types.term) list * (Types.varId * Types.term) list*)
val csm : bool ->
  Types.statement_role ref ->
  (Types.term * Types.term) list -> Types.subst_lst -> Types.subst_lst list
val csm_xor : bool ->
  Types.statement_role ref ->
  (Types.term * Types.term) list -> Types.subst_lst -> Types.subst_lst list
val normalize : Types.term -> Types.rewrite_rule list -> Types.term
val equals_r : Types.term -> Types.term -> Types.rewrite_rule list -> bool
val trconcat : 'a list list -> 'a list
val unifiers :
  int ->
  Types.term ->
  Types.term -> Types.rewrite_rule list -> Types.substitution list
val variants :
  int ->
  Types.term ->
  Types.rewrite_rule list -> (Types.term * Types.substitution) list
