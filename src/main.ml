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


    
let command_line_options_list = [
  ("-d",
   Arg.Symbol(["progress";"completion";"canon";"seed";"sat";"saturation";"maude";"exec"],set_debug),
   " Enable additional debug information");
   ("-comp", Arg.Set(about_completion), 
    "Show all completions"); 
   ("-completions", Arg.Set(debug_completion), 
    "Enable debug output about completions"); 
   ("-canonization", Arg.Set(about_canonization),
    "Enable debug output about canonization rules");
   ("-seed", Arg.Set(about_seed), 
    "Enable debug output about seed"); 
   ("-sat", Arg.Set(about_saturation), 
    "Enable verbose output about saturation"); 
   ("-saturation", Arg.Set(debug_saturation), 
    "Enable debug output about saturation"); 
   ("-bij", Arg.Set(about_bijection), 
    "Show tests correspondance");
   ("-loc", Arg.Set(about_location), 
    "Show location information");
   ("-execution", Arg.Set(debug_execution), 
    "Show tests executions debugging"); 
   ("-tests", Arg.Set(about_tests), 
    "Show information about tests");
   ("-tests-info", Arg.Set(debug_tests), 
    "Show information about tests");
   ("-merge", Arg.Set(debug_merge), 
    "Show information about merging tests");
   ("-maude", Arg.Set(about_maude), 
    "Show information about maude interface");
   ("-progress", Arg.Set(about_progress),
    "Print info in about progression of Akiss");
   ("-bench", Arg.Set(about_bench),
    "Bench compatible output");
   ("-xml", Arg.Set(use_xml),
    "Print info in xml format");
   ("-all", Arg.Set(about_all_attacks),
    "Find all attacks");
   ("-latex", Arg.Set(do_latex),
    "for the paper benchs");
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

(******* Parsing *****)
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
  let nb = Base.new_base () in
  (*records = [];*)
  bijection.p <- Process.EmptyP ; 
  bijection.q <- Process.EmptyP ;
  bijection.satP <- nb ;
  bijection.satQ <- nb ;
  bijection.indexP <- Dag.Dag.empty ;
  bijection.indexQ <- Dag.Dag.empty ;
  bijection.choices_indexP <- Dag.Dag.empty ;
  bijection.choices_indexQ <- Dag.Dag.empty ;
  bijection.next_id <- 0 ;
  bijection.next_comp_id <- 0;
  bijection.tests <- Tests.empty;
  (*registered_tests <- Tests.empty;*)
  bijection.runs_for_completions_P <- [];
  bijection.runs_for_completions_Q <- [];
  bijection.partial_completions_P <- Dag.Dag.empty;
  bijection.partial_completions_Q <- Dag.Dag.empty;
  bijection.todo_completion_P <- [];
  bijection.todo_completion_Q <- [];
  bijection.locs <- Dag.LocationSet.empty;
  bijection.initial_completions <- [];
  bijection.initial_tests <- [];
  bijection.attacks <- [];
  (*htable = Hashtbl.create 5000 ;*)
  Hashtbl.reset bijection.htable_st ;
  latex_identifier := ""



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

