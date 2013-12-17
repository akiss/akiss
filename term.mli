exception Parse_error_semantic of string
exception Invalid_term
exception Not_unifiable
exception Not_matchable

val vars : string list ref
val channels : string list ref
val fsymbols : (string * int) list ref
val private_names : string list ref

type id = string
type varName = id
type funName = id
type term = Fun of funName * term list | Var of varName
type subst = (varName * term) list

val is_var : term -> bool
val unbox_var : term -> varName
val vars_of_term_list : term list -> varName list
val vars_of_term : term -> varName list
type extrasig =
  { vars : string list ;
    names : int list ;
    params : int list ;
    tuples : int list }
val sig_of_term_list : term list -> extrasig

val is_ground : term -> bool
val occurs : varName -> term -> bool

val parse_term : Ast.tempTerm -> term
val show_term : term -> varName
val show_term_list : term list -> varName
val show_subst : subst -> string

val apply_subst : term -> subst -> term
val bound : varName -> subst -> bool

val compose : subst -> subst -> (varName * term) list
val restrict : subst -> varName list -> (varName * term) list

val mgu : term -> term -> (varName * term) list
val mgm : term -> term -> (varName * term) list
