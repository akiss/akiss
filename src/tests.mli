val merge_tests :
  Base.raw_statement -> Base.raw_statement -> Base.raw_statement list
exception Attack
val get_lst_of_test : Base.predicate -> (Types.term * Types.term) list
val add_merged_tests : Bijection.possible_runs -> unit
val register_solution :
  Bijection.solutions -> Bijection.Solutions.elt -> unit
val find_compatible_run_init :
  Bijection.correspondance ->
  Bijection.correspondance -> Bijection.RunSet.elt -> bool
val find_possible_run : Bijection.solutions -> Bijection.Solutions.elt option
val equivalence : Types.procId -> Types.procId -> unit
