exception Bug
val last_time : float ref
val about_seed : bool ref
val debug_seed : bool ref
val about_saturation : bool ref
val debug_saturation : bool ref
val about_tests : bool ref
val debug_tests : bool ref
val about_completion : bool ref
val debug_completion : bool ref
val about_bijection : bool ref
val debug_execution : bool ref
val about_theory : bool ref
val debug_merge : bool ref
val about_maude : bool ref
val about_canonization : bool ref
val about_progress : bool ref
val about_location : bool ref
val use_xml : bool ref
val about_all_attacks : bool ref
val about_bench : bool ref
val trmap : ('a -> 'b) -> 'a list -> 'b list
val unique : 'a list -> 'a list
val create_consecutive : int -> int -> int list
val combine : 'a list -> 'b list -> ('a * 'b) list
val list_diff : 'a list -> 'a list -> 'a list
val list_intersect : 'a list -> 'a list -> 'a list
val is_prefix : 'a list -> 'a list -> bool
val iterate : ('a -> 'a) -> 'a -> 'a
val iterate_n : int -> ('a -> 'a) -> 'a -> 'a
val take : int -> 'a list -> 'a list
val all_prefixes : 'a list -> 'a list list
val show_string_list : string list -> string
val output_string : Format.formatter -> string -> unit
val pp_list :
  (Format.formatter -> 'a -> unit) ->
  string -> Format.formatter -> 'a list -> unit
val get_opt : 'a option -> 'a
