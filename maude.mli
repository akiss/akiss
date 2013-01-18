val variants :
  Term.term ->
  (Term.term * Term.term) list ->
  (Term.term * Term.subst) list
val unifiers :
  Term.term -> Term.term -> (Term.term * Term.term) list -> Term.subst list
val equals : Term.term -> Term.term -> (Term.term * Term.term) list -> bool
val normalize : Term.term -> (Term.term * Term.term) list -> Term.term
