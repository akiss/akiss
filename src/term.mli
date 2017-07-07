val is_var : Types.term -> bool
val unbox_var : Types.term -> Types.varId
val vars_of_term_list : Types.term list -> Types.varId list
val vars_of_term : Types.term -> Types.varId list
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
