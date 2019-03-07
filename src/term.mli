module VarAux : sig type t = Types.varId val compare : 'a -> 'a -> int end
module VariableSet :
  sig
    type elt = VarAux.t
    type t = Set.Make(VarAux).t
  end
module VarMap :
  sig
    type key = VarAux.t
    type 'a t = 'a Map.Make(VarAux).t
  end
exception Not_matchable
val var_set_of_term_list : VariableSet.t -> Types.term list -> VariableSet.t
val var_set_of_term : VariableSet.t -> Types.term -> VariableSet.t
val is_var : Types.term -> bool
val unbox_var : Types.term -> Types.varId
val is_sum_term : Types.term -> bool
val vars_of_term_list : Types.term list -> Types.varId list
val vars_of_term : Types.term -> Types.varId list
val apply_var_set_subst : Types.term -> Types.term VarMap.t -> Types.term
(*val is_ground : Types.term -> bool
val occurs : Types.varId -> Types.term -> bool*)
val new_or_same : 'a -> Types.term -> ('a * Types.term) list -> ('a * Types.term) list
val apply_subst : Types.term -> Types.subst_lst -> Types.term
(*val bound : 'a -> ('a * 'b) list -> bool*)
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
val sigma_maker_init : int -> int -> Types.subst_maker
val copy_subst : Types.subst_maker -> Types.subst_maker
val copy_subst_add_extra :
  Types.subst_maker -> int -> Types.statement_role ref -> Types.subst_maker
val find_sub : Types.varId -> Types.subst_maker -> Types.subst_array
val maude_current_sigma : Types.subst_maker ref
val maude_current_binder : Types.statement_role ref ref
val maude_current_nbv : int ref
