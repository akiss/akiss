(** main file *)
open Util
open Parser_functions
open Bijection
open Process

let usage = Printf.sprintf
  "Usage: %s [options] specification-file list"
  (Filename.basename Sys.argv.(0))

let  set_debug = function
  | "progress" -> about_progress := true
  | "else" -> about_completion := true
  | "canon" ->  about_canonization := true
  | "seed" -> about_seed := true
  | "sat" -> about_saturation := true
  | "saturation" -> about_saturation := true ; debug_saturation := true
  | "maude" -> about_maude := true
  | "bij" -> about_bijection := true
  | _ -> raise (Arg.Bad("Undefined semantics"))


(** all available options *)    
let command_line_options_list = [
   ("-progress", Arg.Set(about_progress),
    "Print messages indicating what Akiss is doing");
   ("-all", Arg.Set(about_all_attacks),
    "Find all attacks: does not stop the program when a first attack is found.");
   ("-loc", Arg.Set(about_location), 
    "Show the correspondance between indexes and actions");
   ("-sat", Arg.Set(about_saturation), 
    "Show the saturated bases"); 
   ("-tests", Arg.Set(about_tests), 
    "Show the tests and their solutions");
   ("-comp", Arg.Set(about_completion), 
    "Show all partial contradictions"); 
   ("-xml", Arg.Set(use_xml),
    "Print data in .xml format, works only with -sat, -comp, -tests options, 
    to be rendered by a web browser make sure the style.css file is in the parent directory");
   ("-bij", Arg.Set(about_bijection), 
    "Show tests correspondance (the injections M)");
   ("-bench", Arg.Set(about_bench),
    "Show bench and stats about the number of tests, statements in knowledge base etc. . To use with a list of files in arguments.");
   ("-rare", Arg.Set(about_rare),
    "Print info in about rare events (where bugs are more likely...)");
   ("-canonization", Arg.Set(about_canonization),
    "Enable debug output about canonization rules");
   ("-seed", Arg.Set(about_seed), 
    "Enable debug output about seed"); 
   ("-saturation", Arg.Set(debug_saturation), 
    "Enable debug output about saturation"); 
   ("-tests-info", Arg.Set(debug_tests), 
    "Show information about tests");
   ("-completions", Arg.Set(debug_completion), 
    "Enable debug output about completions"); 
   ("-execution", Arg.Set(debug_execution), 
    "Show tests executions debugging"); 
   ("-merge", Arg.Set(debug_merge), 
    "Show information about merging tests");
   ("-maude", Arg.Set(about_maude), 
    "Show information about maude interface");
   ("-xor", Arg.Set(debug_xor), 
    "Show information about specific xor process");
   ("-latex", Arg.Set(do_latex),
    "for the paper benchs");
   ("-d",
     Arg.Symbol(["progress";"completion";"canon";"seed";"sat";"saturation";"maude";"exec"],set_debug),
   " Enable additional debug information");
 (*"--extra", Arg.Int (fun i -> extra_output := i),
   "<n>  Display information <n>"*)
  (*("--output-dot", Arg.String (fun s -> dotfile := Some s),
   "<file>  Output statement graph to <file>");*)
 (* ("-j", Arg.Int (fun i -> jobs := i),
   "<n>  Use <n> parallel jobs (if supported)");*)
  (*("--ac-compatible", Arg.Set ac_toolbox,
   "Use the AC-compatible toolbox even on non-AC theories (experimental)");
  ("--disable-por", Arg.Set(disable_por),
   "Disable partial order reduction (por) optimisations")*)
]

(** Reset all variables between two distinct files *)
let reset_global () =
  environment := (Env.empty:env_elt Env.t);
  rewrite_rules := [];
  processes_list := [];
  functions_list := [];
  tuple_arity := [] ;
  use_xor := false;
  nonces := [];
  processes_infos.next_location <- 0;
  processes_infos.next_nonce <- 0;
  processes_infos.processes <- BangDag.empty;
  processes_infos.location_list <- [] ;
  processes_infos.nonce_list <- [];
  processes_infos.max_phase <- 0;
  Hashtbl.clear memoize_call;
  (*records = [];*)
  latex_identifier := "";
  Maude.clean_maude ();
  Dag.clean_memoization ()



let process_file f =
  if not( Sys.is_directory f) then (
  if !about_bench then Printf.printf "%70s%!" f;
  
  let ch_in = open_in f in
  let lexbuf = Lexing.from_channel ch_in in
  
  let _ =
    try
      while true do
        Parser_queries.parse_one_declaration (Grammar.main Lexer.token lexbuf)
      done
    with
      | Failure msg -> Printf.printf "%s\n" msg; exit 0
      | End_of_file -> () in
  
  close_in ch_in;
  reset_global ())
  
let () =
  (*Printf.printf "Akiss starts\n%!" ;*)
  Arg.parse command_line_options_list process_file usage;
  exit 0

