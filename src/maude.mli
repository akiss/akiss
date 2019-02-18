(*val show_binder_maude : Types.statement_role -> string
val print_maude_term : Types.term -> Types.subst_maker option -> string
val print_maude_term_list :
  Types.term list -> Types.subst_maker option -> string
val print_maude_pairlst :
  bool -> (Types.term * Types.term) list -> Types.subst_maker -> string
val print_maude_variants : Types.term -> string
val print_maude_matchers : Types.term -> Types.term -> string
val print_maude_rules : unit -> string
val input_line : in_channel -> string
val times : int -> string -> string
val print_maude_signature : unit -> string
val find_in_path : string -> string
val maude_binary : string lazy_t
val maude_command : string lazy_t
val get_chans : unit -> in_channel * out_channel
val run_maude : (Format.formatter -> unit) -> (in_channel -> 'a) -> 'a*)
type maude_mode = E | AC | XOR
val acunifiers :
  maude_mode ->
  (Types.term * Types.term) list ->
  Types.subst_maker -> Types.subst_maker list
val variants : Types.term -> (Types.term * Types.substitution) list
val acmatchers :
  Types.statement_role ref ->
  (Types.term * Types.term) list -> Types.subst_lst -> Types.subst_lst list
val xormatchers :
  Types.statement_role ref ->
  (Types.term * Types.term) list -> Types.subst_lst -> Types.subst_lst list
