(** Rewriting utilities for terms.
  * This module does not support AC connectives. *)

exception Not_unifiable
exception Not_matchable

(** Unification and matching for free terms *)

val mgu : Term.term -> Term.term -> Term.subst
val mgm : Term.term -> Term.term -> Term.subst

(** Utilities for handling a (non-AC) theory *)

val normalize : Term.term -> (Term.term*Term.term) list -> Term.term

val variants :
  Term.term ->
  (Term.term * Term.term) list ->
  (Term.term * Term.subst) list
val unifiers :
  Term.term -> Term.term -> (Term.term * Term.term) list -> Term.subst list
