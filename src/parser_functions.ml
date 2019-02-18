open Types
(* Types *)

(*
type setting =
  | Classic
  | Private
  | Eavesdrop
*)

type ident = string * int

type temp_term =
  | Id of ident
  | FuncApp of ident * temp_term list
  | Tuple of temp_term list
  | FPlus of temp_term * temp_term
  | FZero

type functions =
  | Function of ident * int * bool


type pattern =
  | PVar of ident
  | PTuple of pattern list
  | PTest of temp_term

type plain_process =
  | Nil
  | Call of ident * temp_term list
  | Choice of plain_process * plain_process
  | Par of plain_process * plain_process
  | Bang of int * plain_process * int
  | New of ident * plain_process
  | In of ident * ident * plain_process
  | Out of ident * temp_term * plain_process
  | Let of pattern * temp_term * plain_process * plain_process
  | IfThenElse of temp_term * temp_term * plain_process * plain_process
  | Seq of plain_process * plain_process
  | Phase of int * plain_process

type extended_process =
  | EPlain of plain_process

type query =
  | Saturate of ident
  | Trace_Eq of bool * ident * ident
  | Obs_Eq of extended_process * extended_process

type extended2_process =
  | ExtendedProcess of ident * ident list * extended_process

type declaration =
(*  | Setting of setting * int *)
  | Latex of string
  | FuncDecl of functions list
  | ReducList of ( temp_term * temp_term ) list
  | FreeName of ident list
  | ChanNames of ident list
  | PrivateChanNames of ident list
  | Query of query * int
  | ProcessDecl of extended2_process
(** parsed process *)




(**** Environement ****)

type env_elt =
  | Var of relative_location 
  | XVar of varId
  | Name of relative_nonce 
  | Func of funId 
  | Chan of chanId
  | Proc of procId
  | ArgVar of argId
  | PatVar of relative_temp_term

module StringComp =
struct
  type t = string
  let compare = compare
end

module Env = Map.Make(StringComp)

let environment = ref (Env.empty:env_elt Env.t)

let processes_list : extended2_process list ref = ref [] 

type symb_chan =
  | Const of chanId
  | Sym of argId

let display_env_elt_type = function
  | ArgVar(arg) -> (string_of_int (arg.th+1)) ^"-th argument of a process" 
  | Var (i,_) -> "a variable n°" ^ (string_of_int i)
  | XVar _ -> "a reduction variable"
  | Name (i,_) -> " name n°" ^ (string_of_int i)  
(*  | PublicName _ -> "a public name"*)
  | Func _ -> "a function" 
  | Chan _ -> "a channel"
  | Proc p -> "the process " ^ (show_procId p) 
  | PatVar _ -> "a variable of a pattern"

let rec show_temp_term = function
  | Id (s,l) -> s
  | FuncApp((s,l),args) -> s ^ "(...)"
  | Tuple(args) -> "((...))"
  | FPlus(s,t) -> (show_temp_term s) ^ "+" ^(show_temp_term t)
  | FZero -> "0"

let show_environment env = 
  Env.fold (fun k v str -> str ^ k ^ ": " ^ (display_env_elt_type v) ^ "\n" ) env "Environement:"

(**** Error message ****)

let error_message line str =
  Printf.printf "Error! Line %d : %s\n" line str;
  exit 0

let warning_message line str =
  Printf.printf "Warning! Line %d : %s\n" line str

(****** Function declaration *******)

let rec parse_rewrite_rule lhs env binder nb = function 
  | Id (s,line) ->
      begin try
        match Env.find s env with
          | XVar(v) -> ( Types.Var(v),env,nb)
          | Func(f) when f.arity  = 0 -> (Fun ({id=Regular(f);has_variables=false},[]),env,nb)
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a variable or constant constructor function symbol is expected." s (display_env_elt_type env_elt))
      with
        | Not_found ->
           if lhs then 
           let x = {n = nb ; status = binder} in  (Types.Var(x), Env.add s (XVar x) env,nb+1)
           else error_message line (Printf.sprintf "The variable %s does not appear in the left hand side." s)
      end
  | FuncApp((s,line),args) ->
      begin try
        match Env.find s env with
          | Func f ->
              if (f.arity) <> List.length args
              then error_message line (
                Printf.sprintf "The function %s is given %d arguments but is expecting %d arguments" 
                s (List.length args) (f.arity));
              let (args', env',nb') = parse_rewrite_rule_list lhs env binder nb args in
              Fun({id=Regular(f);has_variables=true}, args'), env', nb'
          | env_elt -> error_message line (
              Printf.sprintf "The identifiant %s is declared as %s but a constructor function symbol is expected." 
              s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The function %s is not declared" s)
      end
  | FPlus(s,t) -> let (args', env',nb') = parse_rewrite_rule_list lhs env binder nb [s;t] in
              Fun({id=Plus;has_variables=true}, args'), env', nb'
  | FZero -> zero,env,nb
  | Tuple(args) -> 
      let n = List.length args in
      let (args', env',nb') = parse_rewrite_rule_list lhs env binder nb args in
      Fun({id=Tuple(n);has_variables=true}, args'), env', nb'
and parse_rewrite_rule_list lhs env binder nb= function
  | [] -> ([],env,nb)
  | t::q ->
      let (t',env',nb') = parse_rewrite_rule lhs env binder nb t in
      let (q',env'',nb'') = parse_rewrite_rule_list lhs env' binder nb' q in
      (t'::q',env'',nb'')

let rewrite_rules : rewrite_rule list ref = ref []

let rewrite_rule_proj i n =
  let binder = ref Types.Rule in
  let vars = ref [] in
  for i = n - 1 downto 0 do
  vars := Types.Var({status = binder; n = i})::!vars
  done ; 
  {
   binder_rule = binder; 
   nbvars_rule =n; 
   lhs=Fun({id=Projection(i,n);has_variables=true},[ Fun({id=Tuple(n);has_variables=true},!vars)]); 
   rhs=List.nth !vars i
  }

let rewrite_rule_proj n =
  for i = 0 to n - 1 do
    rewrite_rules := rewrite_rule_proj i n :: !rewrite_rules
  done
  
let rewrite_rule_xor_1 =
  let binder = ref Types.Rule in
  let x = Types.Var({status = binder; n=0}) in
  let y = Types.Var({status = binder; n=1}) in
  { 
    binder_rule = binder;
    nbvars_rule = 2;
    lhs = Fun({id=Plus;has_variables=true},[Fun({id=Plus;has_variables=true},[x;y]);y]);
    rhs = x;
  }

let rewrite_rule_xor_2 =
  let binder = ref Types.Rule in
  let x = Types.Var({status=binder;n=0}) in
  { 
    binder_rule = binder;
    nbvars_rule = 1;
    lhs = Fun({id=Plus;has_variables=true},[x;x]);
    rhs = zero;
  }
  
let rewrite_rule_xor_3 =
  let binder = ref Types.Rule in
  let x = Types.Var({status=binder;n=0}) in
  { 
    binder_rule = binder;
    nbvars_rule = 1;
    lhs = Fun({id=Plus;has_variables=true},[x;zero]);
    rhs = x;
  }

let parse_rewrite_rule env (lhs,rhs) = 
  let binder = ref Types.Rule in
  let (t,env,nb) = (parse_rewrite_rule true env binder 0 lhs) in
  let (t',_,_) =(parse_rewrite_rule false env binder 0 rhs) in
  {binder_rule = binder; nbvars_rule=nb; lhs=t; rhs=t'}

let functions_list : funId list ref = ref []

let parse_functions env = function
  | Function((s,line),n,true) ->
      if Env.mem s env
      then error_message line (Printf.sprintf "The identifier %s is already defined." s);

      let f = {name = s; arity = n} in
      functions_list := f :: !functions_list;
      Env.add s (Func f) env
  | Function((_,line),_,false) -> error_message line "Private constructor function symbol not implemented yet."



(******** Parse free names *******)

let parse_free_name env (s,line) =
  if Env.mem s env
  then error_message line (Printf.sprintf "The identifier %s is already defined." s);

  let n = {name = s; arity = 0} in
  functions_list := n :: !functions_list;
  Env.add s (Func n) env


(******** Parse channel names *******)

let parse_channel_name env (s,line) =
  if Env.mem s env
  then error_message line (Printf.sprintf "The identifier %s is already defined." s);

  let ch = {name = s; visibility = Public} in
  Env.add s (Chan ch) env

let parse_private_channel_name env (s,line) =
  if Env.mem s env
  then error_message line (Printf.sprintf "The identifier %s is already defined." s);

  let ch = {name = s; visibility = Hidden} in
  Env.add s (Chan ch) env


(******** Parse chan ********)

let parse_chan procId env = function 
  (s,line) -> try 
      match Env.find s env with
          | Chan(c) -> C(c)
          | ArgVar(id) -> begin match !(procId.types.(id.th)) with
              | ChanType ->  (*Printf.printf "<< %s<%d<< %d\n" s line id.th;*) A(id) 
              | TermType -> error_message line (Printf.sprintf "Expecting a channel but %s : term provided." s)
              | Unknown -> (*Printf.printf "%s the %d-th argument is a chan\n" s (id.th+1);*) procId.types.(id.th) := ChanType; A(id) end
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a channel name or a function argument is expected." s (display_env_elt_type env_elt))
      with
        | Not_found -> error_message line (Printf.sprintf "The channel %s is not declared" s)
      


(******** Parse temp_terms ********)

let (tuple_arity : int list ref) = ref []
let use_xor = ref false

let rec parse_temp_term procId env = function
  | Id (s,line) ->
      begin try
        match Env.find s env with
          | Var(v) -> V(v)
          | Name(n) -> N(n)
(*          | PublicName(n) -> Term.apply_function n []*)
          | Chan(c) -> error_message line (Printf.sprintf "Excepting a term but %s : chan provided." s)
          | Func(f) when f.arity = 0 -> F(f,[])
          | ArgVar(id) -> begin match !(procId.types.(id.th)) with
              | TermType ->  (*Printf.printf "<< %s<%d<< %d\n" s line id.th;*) A(id) 
              | ChanType -> error_message line (Printf.sprintf "Excepting a term but %s : chan provided." s)
              | Unknown -> (*Printf.printf "%s the %d-th argument is a term\n" s (id.th+1);*)
                  procId.types.(id.th) := TermType; A(id) end 
          | PatVar(t) -> t
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a name, a variable, a channel or constant is expected." s (display_env_elt_type env_elt))
      with
        | Not_found -> error_message line (Printf.sprintf "The identifier %s is not declared" s)
      end
  | FuncApp((s,line),args) ->
      begin try
        match Env.find s env with
          | Func(f) ->
              if (f.arity) <> List.length args
              then error_message line (Printf.sprintf "The function %s is given %d arguments but is expecting %d arguments" s (List.length args) (f.arity));

              F(f, (List.map (parse_temp_term procId env) args))
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a name or a function is expected." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The function %s is not declared" s)
      end
  | FPlus(s,t) -> if not !use_xor then (use_xor := true; rewrite_rules := rewrite_rule_xor_1 :: rewrite_rule_xor_2 :: rewrite_rule_xor_3 :: !rewrite_rules);
      Xor( (List.map (parse_temp_term procId env) [s;t]))
  | FZero -> Z
  | Tuple(args) ->
      let n = List.length args in
      if not (List.mem n !tuple_arity) 
      then begin tuple_arity := n ::!tuple_arity ; rewrite_rule_proj n end ; 
      T(n,List.map (parse_temp_term procId env) args)

let rec parse_temp_term_or_chan procId env = function
  | Id (s,line) ->
      begin try
        match Env.find s env with
          | Var(v) -> V(v)
          | Name(n) -> N(n)
(*          | PublicName(n) -> Term.apply_function n []*)
          | Chan(c) -> C(c)
          | Func(f) when f.arity = 0 -> F(f,[])
          | ArgVar(id) -> A(id) (* begin match !(procId.types.(id.th)) with
              | TermType ->  (*Printf.printf "<< %s<%d<< %d\n" s line id.th;*) A(id) 
              | ChanType -> error_message line (Printf.sprintf "Excepting a term but %s : chan provided." s)
              | Unknown -> A(id)  end *)
          | PatVar(t) -> t
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a name, a variable, a channel or constant is expected." s (display_env_elt_type env_elt))
      with
        | Not_found -> error_message line (Printf.sprintf "The identifier %s is not declared" s)
      end
  | x -> parse_temp_term procId env x


let type_of_arg (pr : procId) env a = 
  match a with
  | Id (s,line) -> begin
     try match Env.find s env with
     | Chan(c) -> (-1, ChanType)
     | ArgVar(id) -> (*Printf.printf ">> %s = %d\n%s\n"(id.name) (id.th)(show_environment env);*) (id.th,  !(pr.types.(id.th))) 
     | _ -> (-1, TermType)
      with
        | Not_found -> error_message line (Printf.sprintf "The identifier %s is not declared" s)
     end
  | _ -> (-1, TermType)
     
(*let parse_temp_chan env a = 
  match a with
  | Id (s,line) -> begin
     try match Env.find s env with
     | Chan(c) -> c
     | _ -> assert false
      with
        | Not_found -> error_message line (Printf.sprintf "The identifier %s is not declared" s)
     end
  | _ -> assert false*)

(******** Parse pattern ********)

let rec parse_pattern procId env prev_env term  = function
  | PVar (s,line) ->
      if Env.mem s env
      then warning_message line (Printf.sprintf "The identifier %s is already defined." s);
      let env' = Env.add s (PatVar(term)) env in
      term, env'

  | PTuple(args) ->
      let n = List.length args in
      let args',env' = parse_pattern_list procId env prev_env term  0 n args in
      if not (List.mem n !tuple_arity) 
      then begin tuple_arity := n ::!tuple_arity ; rewrite_rule_proj n end ; 
      T(n,args'), env'
  | PTest temp_term ->
      let temp_term' = parse_temp_term procId prev_env temp_term in
      temp_term', env

and parse_pattern_list procId env prev_env term  i n = function
  | [] -> [], env
  | pat::q ->
      let pat',env' = parse_pattern procId env prev_env (P(i, n,term)) pat   in
      let pat_l,env'' = parse_pattern_list procId env' prev_env term (i+1) n q in
      pat'::pat_l, env''



(******** Process **********)

 (* *)

let rec parse_plain_process procId env (nbloc,nbnonces) = function
  | Call((s,line),temp_term_list) ->
      begin try
        match Env.find s env with
          | Proc(procId') ->
              (*Printf.printf "call of %s\n%!"(show_procId procId') ;*)
              if procId'.arity <> List.length temp_term_list
              then error_message line 
                (Printf.sprintf "The process %s is given %d arguments but is expecting %d arguments" s (List.length temp_term_list) procId'.arity);
              List.iteri (fun i t -> 
                let th, typ = type_of_arg procId env t in
                (*Printf.printf "type of %s of %s: %s\n" (show_temp_term t)(show_procId procId') (show_typ typ);*)
                if typ = Unknown && !(procId'.types.(i)) = Unknown then procId.types.(th) <- procId'.types.(i)   else
                if typ = Unknown then procId.types.(th) := !(procId'.types.(i))  else
                if !(procId'.types.(i)) = Unknown then procId'.types.(i) := typ else
                if !(procId'.types.(i)) <> typ then error_message line (Printf.sprintf "The process %s is given %d-th argument of type %s but is expecting argument of type %s." s (i+1) (show_typ procId'.types.(i)) (show_typ (ref typ)))
              ) temp_term_list ;
              let temp_term_list' = List.map (parse_temp_term_or_chan procId env) temp_term_list in
              (nbloc + 1,nbnonces,CallB((nbloc,Some s),1,procId',temp_term_list')) 
          | env_elt -> error_message line (Printf.sprintf "The identifier %s is declared as %s but a process is expected." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The identifier %s is not declared" s)
      end 
  | Nil -> (nbloc,nbnonces,NilB)
  | Bang(n,proc,line) ->
    if n < 1
      then error_message line "The integer should be at least 1.";
    begin 
      let i = ref (-1) in
      let names,args,types = Env.fold (fun name x (names,args,types) -> 
        let f ty name  arg = incr i; (Env.add name (ArgVar {name=name;th=(!i)}) names, arg :: args , ty :: types) in
        match x with
          | ArgVar(arg) -> (f procId.types.(arg.th) name (A(arg)))
          | Var (v) -> (f (ref TermType) name (V(v)))
          | Name(n)->  (f (ref TermType) name (N(n))) 
          | PatVar(t) -> f (ref TermType) name t
          | _ -> (names,args,types)) env (!environment,[],[])
      in
      let procId' = { name="bang";arity=(!i + 1);types=(Array.of_list (List.rev types)); process = NilB; nbloc= 0; nbnonces= 0; } in
      (*Printf.printf "procID = %s \n bang %d \n new process %s\n" (show_procId procId) n (show_relative_term_list args);*)
      let (nbloc',nbnonce',proc')= parse_plain_process procId' names (0,0) proc in
      procId'.nbloc<-nbloc';
      procId'.nbnonces<-nbnonce';
      procId'.process<-proc';
      (nbloc + 1,nbnonces,CallB((nbloc,Some "bang"),n,procId',List.rev args)) 
    end
  | Seq(_,_)-> error_message 0 "Sequence is not yet implemented."
  | Par(p1,p2) ->
      let (nbl,nbn,pr1)=parse_plain_process procId env (nbloc,nbnonces) p1 in
      let (nbl,nbn,pr2)=parse_plain_process procId env (nbl,nbn) p2 in
      (nbl,nbn, match pr1, pr2 with
        | ParB l_1, ParB l_2 -> ParB (l_1@l_2)
        | ParB l_1, proc2 -> ParB (proc2 :: l_1)
        | pr1, ParB l_2 -> ParB (pr1::l_2)
        | pr1, pr2 -> ParB ([pr1;pr2])
      )
  | Choice(p1,Choice(p2,p3)) -> parse_plain_process procId env (nbloc,nbnonces) (Choice(Choice(p1,p2),p3))
  | Choice(p1,p2) ->
      let (nbl,nbn,pr1)=parse_plain_process procId env (nbloc,nbnonces) p1 in
      let (nbl,nbn,pr2)=parse_plain_process procId env (nbl,nbn) p2 in
      begin
       match pr1, pr2 with
        | ChoiceB (l_1,lp1), ChoiceB (l_2,lp2) -> assert false
        | ChoiceB (l_1,lp1), proc2 -> (nbl,nbn,ChoiceB (l_1, proc2 :: lp1))
        | pr1, ChoiceB (l_2,lp2) -> assert false
        | pr1, pr2 -> let l=(nbl,Some ("+")) in (nbl+1,nbn,ChoiceB(l,[pr1;pr2]))
      end
  | New((s,line),proc) ->
      if Env.mem s env
      then warning_message line (Printf.sprintf "The identifier %s is already defined." s);

      let env' = Env.add s (Name (nbnonces,s)) env in
      let (nbl,nbn,pr) = parse_plain_process procId env' (nbloc,nbnonces+1) proc in
      (nbl,nbn,NameB((nbnonces,s),pr))
  | In(ch,(s,line),proc) ->
      if Env.mem s env
      then warning_message line (Printf.sprintf "The identifier %s is already defined." s);

      let ch' = parse_chan procId env ch in
      let x =(nbloc,Some s) in
      (*let x = Term.Variable.fresh_with_label Term.Free Term.Variable.fst_ord_type s in*)
      let env' = Env.add s (Var(x)) env in
      let (nbl,nbn,pr) =  parse_plain_process procId env' (nbloc+1,nbnonces) proc in
      (nbl,nbn,InputB(ch',x,pr))
  | Out((ch,line),t,proc) ->
      let ch' = parse_chan procId env (ch,line)
      and t' = parse_temp_term procId env t
      and l = (nbloc,Some (string_of_int line)) 
      and  (nbl,nbn,proc') = parse_plain_process procId env (nbloc+1,nbnonces) proc in

      (nbl,nbn,OutputB(ch',l,t',proc'))
  | Let(pat,t,proc_then,proc_else) ->
      let t' = parse_temp_term procId env t in
      let pat',env' = parse_pattern procId env env t' pat in
      let (nbl,nbn,proc_then') = parse_plain_process procId env' (nbloc,nbnonces) proc_then in
      if pat' = t' then (nbl,nbn,proc_then')
      else
        let l=(nbl,Some ("let")) in 
        let (nbl,nbn,proc_else') = parse_plain_process procId env (nbl+1,nbn) proc_else in
        (nbl,nbn,TestIfB(l,pat',t',proc_then',proc_else'))
  | IfThenElse(t1,t2,p1,p2) ->
      let t1' = parse_temp_term procId env t1 in
      let t2' = parse_temp_term procId env t2 in
      let l=(nbloc,Some ("if")) in 
      let (nbl,nbn,pr1)=parse_plain_process procId env (nbloc +1,nbnonces) p1 in
      let (nbl,nbn,pr2)=parse_plain_process procId env (nbl,nbn) p2 in
      (nbl,nbn, TestIfB (l, t1',t2',pr1,pr2))
  | Phase(i,p) -> 
      let (nbl,nbn,pr) = parse_plain_process procId env (nbloc,nbnonces) p in
      (nbl,nbn,PhaseB(i,pr))
  (*| _ -> failwith("Syntax not implemented yet")*)

let parse_extended_process procId env = function
  | EPlain proc -> 
      (*Printf.printf "parsing %s\n" (show_procId procId);*)
      parse_plain_process procId env (0,0) proc  

(****** Process declaration ********)

let rec parse_list_argument procId proc env index = function
  | [] ->
      parse_extended_process procId env proc
  | (var_s,line)::q ->
        try
          begin match Env.find var_s env with
            | ArgVar _ -> error_message line (Printf.sprintf "The identifier %s is already defined as argument of the function" var_s);
            | _ -> error_message line (Printf.sprintf "The identifier %s is already defined" var_s);
          end
        with Not_found -> parse_list_argument procId proc (Env.add var_s (ArgVar {name=var_s;th=index}) env) (index + 1) q

let get_process_name (ExtendedProcess((s,line),args,_)) = 
  if Env.mem s !environment
  then error_message line (Printf.sprintf "The identifier %s is already defined." s);
  let n = List.length args in
  environment := Env.add s (Proc ({name=s; arity= n; types=Array.init n (fun _ -> ref Unknown) ; process= NilB; nbloc=0; nbnonces=0})) !environment


let parse_process_declaration_list lst =
  List.iter (function ExtendedProcess((s,line),args,p) -> 
    match Env.find s !environment with
   | Proc(prId) -> 
      let (nbloc,nbnonce,process) = parse_list_argument prId p !environment 0 args in
      prId.process <- process ;
      prId.nbloc <- nbloc;
      prId.nbnonces <- nbnonce
    | _ -> assert false
  ) lst 
  (*;Printf.printf "%s\n" (show_environment !environment)*)


(* To be accessed by maude.ml and parsemaude.ml *)  
let nonces : ((int * nonceId) list)ref = ref [] 
let frames : ((int * location) list)ref = ref []  
    
    
(****** Parse setting *******)
(*
let already_chosen_semantics = ref false

let parse_setting line sem =
  if !already_chosen_semantics
  then warning_message line "A setting for the semantics has already been chosen. This new setting erases the previous one.";

  match sem with
    | Classic -> Process.chosen_semantics := Process.Classic; already_chosen_semantics := true
    | Private -> Process.chosen_semantics := Process.Private; already_chosen_semantics := true
    | Eavesdrop -> Process.chosen_semantics := Process.Eavesdrop; already_chosen_semantics := true
*)

