 open Parser_functions
 open Util
 open Types
(****** Parse query *******)

(*let query_list = ref []*)

let parse_query env line = function
  | Saturate(ident,line) -> 
      let p = try Env.find ident env with Not_found -> error_message line (Printf.sprintf "The process %s is not declared" ident) in
      begin 
        match p with
          | Proc(procId) -> Horn.saturate !rewrite_rules procId
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a process is expected." ident (display_env_elt_type env_elt))
      end
  | Trace_Eq(_,_) (*-> query_list := (Process.Trace_Equivalence,parse_extended_process env proc_1, parse_extended_process env proc_2)::!query_list *)
  | Obs_Eq(_,_) -> error_message line "Observational equivalence not implemented yet"

(****** Parse declaration *******)


let parse_one_declaration = function
 (* | Setting(sem,line) -> parse_setting line sem*)
  | FuncDecl flst -> List.iter (fun f -> environment := parse_functions !environment f) flst
  | ReducList lst -> rewrite_rules := List.map 
      ( fun r -> parse_rewrite_rule !environment r) lst @ !rewrite_rules
  | ChanNames identlst -> List.iter (fun ident -> environment := parse_channel_name !environment ident) identlst
(*  | FreeName ident -> environment := parse_free_name !environment ident *)
  | ProcessList (ExtendedProcess(_,_,_)::q as prlst) -> 
      environment := parse_process_declaration_list !environment prlst
  | Query (query,line) -> 
      if !about_seed then begin Printf.printf "Rewrite rules (%d):\n" (List.length !rewrite_rules);
         List.iter (fun r -> Printf.printf "- %s\n" (show_rewrite_rule r)) !rewrite_rules end;
      parse_query !environment line query 
  | _ -> failwith "todo"
