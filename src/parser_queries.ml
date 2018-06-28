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
          | Proc(procId) -> let (l,kb) = Horn.saturate procId in
              Printf.printf (if !use_xml then "<?xml-stylesheet type='text/css' href='style.css' ?>%s" else "Saturation is done %s\n") (Base.show_kb kb) 
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a process is expected." ident (display_env_elt_type env_elt))
      end
  | Trace_Eq((ident,line),(ident',line')) -> 
      let p = try Env.find ident env with Not_found -> error_message line (Printf.sprintf "The process %s is not declared" ident) in
      let q = try Env.find ident' env with Not_found -> error_message line (Printf.sprintf "The process %s is not declared" ident') in
      begin 
        match (p,q) with
          | (Proc(procId),Proc(procId')) -> Tests.equivalence procId procId'  
          | (env_elt,Proc(_)) 
          | (_,env_elt) -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a process is expected." ident (display_env_elt_type env_elt))
      end
  | Obs_Eq(_,_) -> error_message line "Observational equivalence not implemented yet"

(****** Parse declaration *******)


let parse_one_declaration = function
 (* | Setting(sem,line) -> parse_setting line sem*)
  | FuncDecl flst -> List.iter (fun f -> environment := parse_functions !environment f) flst
  | ReducList lst -> rewrite_rules := List.map 
      ( fun r -> parse_rewrite_rule !environment r) lst @ !rewrite_rules
  | ChanNames identlst -> List.iter (fun ident -> environment := parse_channel_name !environment ident) identlst
  | FreeName flst -> List.iter (fun f -> environment := parse_free_name !environment f) flst 
  | ProcessDecl( p ) -> processes_list := p :: !processes_list
      (*environment := parse_process_declaration_list !environment prlst*)
  | Query (query,line) -> 
      (match !processes_list with
      [] -> ()
      | _ -> 
        environment := parse_process_declaration_list !environment (List.rev !processes_list);
        processes_list:=[]);
      if !about_seed then begin Printf.printf "Rewrite rules (%d):\n" (List.length !rewrite_rules);
         List.iter (fun r -> Printf.printf "- %s\n" (show_rewrite_rule r)) !rewrite_rules end;
      parse_query !environment line query 
  | _ -> failwith "todo"
