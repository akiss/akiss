(*open Parser*)
open Types
open Term
open Dag
open Parser_functions
open Util

(** {2 Processes} *)




type action = 
  | Input of location  
  | Output of location * term
  | Test of term * term
  | TestInequal of term * term
;;

type process =
  | EmptyP
  | ParallelP of process list
  | SeqP of action * process
  | ChoiceP of location * ((int * process) list)
  | CallP of location * procId * term array * chanId array
  
type process_infos = {
   first_location : int ;
   first_nonce : int;
}

type processes_infos = {
   mutable next_location : int ;
   mutable next_nonce : int;
   mutable processes : process_infos Dag.t;
   mutable location_list : location list;
}

let processes_infos = {
     next_location = 0 ;
     next_nonce = 0 ;
     processes = Dag.empty ;
     location_list = [];
}

let show_action a =
  match a with
  | Input(l) -> Printf.sprintf "in(%d)" l.p
  | Output(l,t) -> Printf.sprintf "out(%d: %s)" l.p  (show_term t)
  | Test(s,t) -> "[" ^ (show_term s) ^ "=" ^ (show_term t) ^ "]"
  | TestInequal(s,t) -> "[" ^ (show_term s) ^ "!=" ^ (show_term t) ^ "]"


let rec show_process pr = 
  match pr with
  | EmptyP -> ""
  | ParallelP(lp) ->( List.fold_left (fun str p -> str ^ "|" ^ (show_process p)) "(" lp ) ^ ")"
  | SeqP(a,p) -> (show_action a) ^ ";" ^ (show_process p)
  | ChoiceP(l,lp)->( List.fold_left (fun str (i,p) -> str ^ "+" ^ (show_process p)) "(" lp ) ^ ")"
  | CallP(l,procId,args,chans) -> procId.name

let rec show_process_start i pr = 
  if i = 0 then "..." else
  match pr with
  | EmptyP -> ""
  | ParallelP(lp) ->( List.fold_left (fun str p -> str ^ "|" ^ (show_process_start i p)) "(" lp ) ^ ")"
  | ChoiceP(l,lp)->( List.fold_left (fun str (i,p) -> str ^ "+" ^ (show_process_start i p)) "(" lp ) ^ ")"
  | SeqP(a,p) -> (show_action a) ^ ";" ^ (show_process_start (i - 1) p)
  | CallP(l,procId,args,chans) -> procId.name

let rec count_type_nb typ pr i =
  if i = -1 then -1 
  else
  if pr.types.(i) = typ then 1 + count_type_nb typ pr (i - 1)
  else count_type_nb typ pr (i - 1)
  
let rec convert_term pr locations nonces arguments term =
  match term with
  | F(f,args) -> 
    Fun({id=Regular(f);has_variables=true},
      List.map (convert_term pr locations nonces arguments) args)
  | T(n,args) -> 
    Fun({id=Tuple(n);has_variables=true},
      List.map (convert_term pr locations nonces arguments) args)
  | P(i,n,args) -> 
    Fun({id=Projection(i,n);has_variables=true},
      [convert_term pr locations nonces arguments args])
  | N((rel_n,_)) -> Fun({id=Nonce(nonces.(rel_n));has_variables=false},[])
  | V((rel_loc,_)) -> Fun({id=Input(locations.(rel_loc));has_variables=true},[])
  | A(th) -> arguments.(count_type_nb pr.types.(th.th) pr th.th)
  | C(_) -> assert false
  
let convert_chan pr chans chan =
  match chan with 
  | C(c) -> c
  | A(th) ->
     (*Printf.printf "A({th= %d}) type: %s |- %d\n" th.th (show_typ  pr.types.(th.th))(count_type_nb pr.types.(th.th) pr th.th);*)
      chans.(count_type_nb pr.types.(th.th) pr th.th)
  | _ -> assert(false)
  
let new_location (pr : procId) p ( io : io ) str =
  try List.find (fun l -> l.p = p) processes_infos.location_list
  with
  | Not_found-> 
    begin if true then match io with 
    | Input(chan) -> Printf.printf "%d : in(%s) of %s \n" p str pr.name   
    | Output(chan) -> Printf.printf "%d : out(%s) of %s \n" p str pr.name
    | _ -> () end ;
    let l = {p=p;io=io;name=str} in
    processes_infos.location_list <- l :: processes_infos.location_list;
    l

let rec convert_pr infos process =
  let (pr, location, nonce, locations, nonces, args, chans) = infos in
  (*Printf.printf "Converting: %s \n%!" (show_bounded_process process);*)
  match process with
  | NilB -> EmptyP
  | NameB ((rel_n,str),p) -> 
     nonces.(rel_n) <- {name = str; n=nonce+rel_n}; 
     convert_pr infos p
  | InputB (ch,(rel_loc,Some str),p) -> 
     locations.(rel_loc) <- new_location pr (location+rel_loc) (Input(convert_chan pr chans ch))  str;
     SeqP(Input(locations.(rel_loc)),convert_pr infos p)
  | OutputB(ch,(rel_loc,Some str),term,p) -> 
     locations.(rel_loc) <- new_location pr (location+rel_loc) (Output(convert_chan pr chans ch))  str ;
     SeqP(Output(locations.(rel_loc),convert_term pr locations nonces args term),
       convert_pr infos p)
  | TestIfB((rel_loc,Some str),s,t,p1,p2) -> 
     let s = convert_term pr locations nonces args s in 
     let t = convert_term pr locations nonces args t in 
     locations.(rel_loc) <- new_location pr (location+rel_loc) Choice str;
     if p2 = NilB then SeqP(Test(s,t),convert_pr infos p1) else
     if p1 = NilB then SeqP(TestInequal(s,t),convert_pr infos p2) else
     begin
       ChoiceP(locations.(rel_loc),[(1,SeqP(Test(s,t),convert_pr infos p1));
       (0,SeqP(TestInequal(s,t),convert_pr infos p2))])
     end
  | ParB(prlst) -> 
     ParallelP(List.map (convert_pr infos)prlst)
  | ChoiceB((rel_loc,Some s),lb) -> 
     locations.(rel_loc) <- new_location pr (location+rel_loc) Choice s;
     ChoiceP(locations.(rel_loc),List.mapi (fun i p -> (i, convert_pr infos p)) lb)
  | CallB((rel_loc,Some s),p,arguments) -> 
     let ar = Array.make (1+(count_type_nb TermType p (p.arity - 1))) zero in
     let channels = Array.make (1+(count_type_nb ChanType p (p.arity - 1))) null_chan in
     let nbt = ref 0 in 
     let nbc = ref 0 in
     List.iteri (fun i x -> 
       if p.types.(i) = TermType 
       then begin ar.(!nbt) <- convert_term pr locations nonces args x; incr nbt end
       else if p.types.(i) = ChanType 
       then begin channels.(!nbc) <- convert_chan pr chans x; incr nbc end
     ) arguments;
     locations.(rel_loc) <- new_location pr (location+rel_loc) Call s;
     CallP(locations.(rel_loc),p,ar,channels)
  | _ -> assert false
 
let expand_call loc (procId : procId) args chans=
  if !about_seed then Format.printf "Expansion of %s (%d;%d)\nwhich is %s \n%!"
     (show_procId procId)(Array.length args)(Array.length chans) (show_bounded_process procId.process);
  let indexes =
  try Dag.find loc processes_infos.processes
  with Not_found -> begin 
    let ind = {
      first_location = processes_infos.next_location ;
      first_nonce = processes_infos.next_nonce ;
    } in
    processes_infos.next_nonce <- processes_infos.next_nonce + procId.nbnonces ;
    processes_infos.next_location <- processes_infos.next_location + procId.nbloc ;
    processes_infos.processes <- Dag.add loc ind processes_infos.processes ;
    ind end in
  convert_pr (procId, indexes.first_location, indexes.first_nonce, 
    (Array.make procId.nbloc null_location),
    (Array.make procId.nbnonces null_nonce), args, chans) procId.process
 
(*let is_io_action a =
  match a with
  | Input(_,_)
  | Output(_,_) -> true
  | Test (_,_) -> false
  | TestInequal (_,_) -> false

let is_test_action a = 
  match a with
  | Input(_,_)
  | Output(_,_) -> false
  | Test (_,_) 
  | TestInequal (_,_) -> true
      
let remove_term_in_io_action a =
  match a with
  | Input(c,_) -> Input(c,"")
  | Output(c,_) -> Output(c,Var(""))
  | Test(t1,t2) -> Test(t1,t2)
  | TestInequal(t1,t2) -> TestInequal(t1,t2)
    
module ActionSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = action
  end );;

type trace =
  | NullTrace
  | Trace of action * trace
;;

let rec trace_size = function
  | NullTrace -> 0
  | Trace(_, t) -> 1 + (trace_size t)
;;


type process = trace list;;

(** {3 Printing} *)

let str_of_tr tr = match tr with
  | Some(t) -> show_term t
  | None -> "ok"
;;

let show_frame fr = 
  show_string_list (trmap show_term fr)
;;

let show_action = function
  | Input(ch, x) -> Printf.sprintf "in(%s,%s)" ch x
  | Output(ch, t) -> Printf.sprintf "out(%s,%s)" ch (show_term t)
  | Test(s,t) -> Printf.sprintf "[%s=%s]" (show_term s) (show_term t)
  | TestInequal(s,t) -> Printf.sprintf "[%s!=%s]" (show_term s) (show_term t)
;;

let rec show_action_lst = function 
	| t::q -> (show_action t)^","^(show_action_lst q)
	| [] -> "."

let rec show_trace = function
  | NullTrace -> "0"
  | Trace(a, rest) -> (show_action a) ^ "." ^ (show_trace rest)
;;

let rec show_process process =
  String.concat "\n\n" (trmap show_trace process)
;;

(** {3 Parsing} *)

open Ast

let rec parse_action = function
  | TempActionOut(ch, t) ->
     if List.mem ch !channels then
       Output(ch, parse_term t)
     else if List.mem ch Theory.privchannels then
       Output(ch, parse_term t)
     else
       Printf.ksprintf failwith "Undeclared channel: %s" ch
  | TempActionIn(ch, x) ->
    if List.mem ch !channels || List.mem ch Theory.privchannels  then
      if List.mem x !vars then
	Input(ch, x)
      else
	Printf.ksprintf failwith "Undeclared variable: %s" x
    else
      Printf.ksprintf failwith "Undeclared channel: %s" ch
  | TempActionTest(s, t) -> Test(parse_term s, parse_term t)
  | TempActionTestInequal(s, t) -> TestInequal(parse_term s, parse_term t)
;;

let replace_var_in_term x t term =
  apply_subst term [(x, t)]
;;





let rec expand tempPr args =
  match tempPr with
  | TempEmpty -> EmptyP
  | TempAction(a,pr) -> SeqP(parse_action a, expand pr args)
  | TempLet(x,t,pr) -> expand pr ( (x,t) :: args)
  | TempInterleave(p1,p2) -> ParallelP( expand p1 args, expand p2 args)
  | _ -> invalid_arg("todo expand")
*)

(*type symbProcess =
  | SymbNul
  | SymbAct of action list (* non-empty list, in reverse order, only tests except the head *)
  | SymbSeq of symbProcess * symbProcess
  | SymbPar of symbProcess * symbProcess
  | SymbAlt of symbProcess * symbProcess
  | SymbEither of symbProcess * symbProcess
  | SymbPhase of symbProcess * symbProcess

let rec show_symb = function
  | SymbNul -> "0"
  | SymbAct a -> "(act " ^ String.concat " " (List.map show_action a) ^ ")"
  | SymbSeq (p1, p2) -> "(seq " ^ show_symb p1 ^ " " ^ show_symb p2 ^ ")"
  | SymbPar (p1, p2) -> "(par " ^ show_symb p1 ^ " " ^ show_symb p2 ^ ")"
  | SymbAlt (p1, p2) -> "(alt " ^ show_symb p1 ^ " " ^ show_symb p2 ^ ")"
  | SymbEither (p1, p2) -> "(either " ^ show_symb p1 ^ " or " ^ show_symb p2 ^ ")"
  | SymbPhase (p1, p2) -> "(phase " ^ show_symb p1 ^ " " ^ show_symb p2 ^ ")"


let rec actions_of p =
  match p with
  | SymbNul -> ActionSet.empty
  | SymbAct a -> ActionSet.of_list (List.rev_map remove_term_in_io_action (List.filter is_io_action a))
  | SymbSeq (p1, p2) 
  | SymbAlt (p1, p2) 
  | SymbEither (p1, p2) 
  | SymbPhase (p1, p2) 
  | SymbPar (p1, p2) -> ActionSet.union (actions_of p1) (actions_of p2)


let action_determinate p =

  let rec ad p =
    match p with
    | SymbNul -> true
    | SymbAct a -> true
    | SymbSeq (SymbAct a, p) -> ad p
    | SymbSeq (p, SymbNul) -> ad p
    | SymbSeq (SymbSeq (p1, p2), p) -> ad p1 &&  ad (SymbSeq (p2, p))
    | SymbPar (p1, p2) -> ActionSet.is_empty (ActionSet.inter (actions_of p1) (actions_of p2)) && ( ad p1 && ad p2 )
    | SymbEither (p1, p2) -> ad p1 && ad p2
    | SymbSeq (_, _) 
    | SymbPhase (_, _)
    | SymbAlt (_, _) -> if !about_traces then Format.printf "The process is not action_determinate because of %s\n" (show_symb p); false
  in
  match p with 
  | SymbPhase (p1, p2) -> ad p1 && ad p2
  | _ as p -> ad p
    
let replace_var_in_act x t a =
  match a with
  | Input (_, _) -> a
  | Output (c, term) -> Output (c, replace_var_in_term x t term)
  | Test (term1, term2) ->
     let term1 = replace_var_in_term x t term1 in
     let term2 = replace_var_in_term x t term2 in
     Test (term1, term2)
  | TestInequal (term1, term2) ->
     let term1 = replace_var_in_term x t term1 in
     let term2 = replace_var_in_term x t term2 in
     TestInequal (term1, term2)

let rec replace_var_in_symb x t p =
  match p with
  | SymbNul -> SymbNul
  | SymbAct a -> SymbAct (List.map (replace_var_in_act x t) a)
  | SymbSeq (p1, p2) ->
     let p1 = replace_var_in_symb x t p1 in
     let p2 = replace_var_in_symb x t p2 in
     SymbSeq (p1, p2)
  | SymbPar (p1, p2) ->
     let p1 = replace_var_in_symb x t p1 in
     let p2 = replace_var_in_symb x t p2 in
     SymbPar (p1, p2)
  | SymbAlt (p1, p2) ->
     let p1 = replace_var_in_symb x t p1 in
     let p2 = replace_var_in_symb x t p2 in
     SymbAlt (p1, p2)
  | SymbEither (p1, p2) ->
     let p1 = replace_var_in_symb x t p1 in
     let p2 = replace_var_in_symb x t p2 in
     SymbEither (p1, p2)
  | SymbPhase (p1, p2) ->
     let p1 = replace_var_in_symb x t p1 in
     let p2 = replace_var_in_symb x t p2 in
     SymbPhase (p1, p2)

let rec symb_of_temp process processes =
  match process with
  | TempEmpty -> SymbNul
  | TempAction a -> SymbAct [parse_action a]
  | TempSequence (p1, p2) ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbSeq (p1, p2)
  | TempInterleave (p1, p2) ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbPar (p1, p2)
  | TempChoice (TempSequence (TempAction(TempActionTest(s1,t1)), p1), TempSequence (TempAction(TempActionTestInequal(s2,t2)), p2)) when s1 = s2 && t1 = t2 ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbEither (SymbSeq(SymbAct[parse_action (TempActionTest(s1,t1))],p1),SymbSeq(SymbAct[parse_action (TempActionTestInequal(s2,t2))],p2))
  | TempChoice (TempSequence (TempAction(TempActionTestInequal(s1,t1)), p1), TempSequence (TempAction(TempActionTest(s2,t2)), p2)) when s1 = s2 && t1 = t2 ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbEither (SymbSeq(SymbAct[parse_action (TempActionTestInequal(s1,t1))],p1),SymbSeq(SymbAct[parse_action (TempActionTest(s2,t2))],p2))
  | TempChoice (p1, p2) ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbAlt (p1, p2)
  | TempPhase (p1, p2) ->
     let p1 = symb_of_temp p1 processes in
     let p2 = symb_of_temp p2 processes in
     SymbPhase (p1, p2)
  | TempLet (x, tt, process) ->
     let t = parse_term tt in
     let p = symb_of_temp process processes in
     replace_var_in_symb x t p
  | TempProcessRef (name) ->
     List.assoc name processes

       
let rec simplify = function
  | SymbNul -> SymbNul
  | SymbAct a -> SymbAct a
  | SymbSeq (p1, p2) ->
     (match simplify p1, simplify p2 with
     | SymbNul, p -> p
     | p, SymbNul -> p
     | p1, p2 -> SymbSeq (p1, p2))
  | SymbPar (p1, p2) ->
     (match simplify p1, simplify p2 with
     | SymbNul, p -> p
     | p, SymbNul -> p
     | p1, p2 -> SymbPar (p1, p2))
  | SymbAlt (p1, p2) as p -> p (* It may be a sequance after it*)
     (*match simplify p1, simplify p2 with
     | SymbNul, p -> p
     | p, SymbNul -> p
     | p1, p2 -> SymbAlt (p1, p2)*)
  | SymbEither (p1, p2) ->
     (match simplify p1, simplify p2 with
     | SymbNul, p -> p
     | p, SymbNul -> p
     | p1, p2 -> SymbEither (p1, p2))
  | SymbPhase (p1, p2) -> 
     (match simplify p1, simplify p2 with
     | SymbNul, p -> p
     | p1, p2 -> SymbPhase (p1, p2))


let rec optimize_tests p =
  if Theory.privchannels = []
  then (*unlinearize SymbNul (compress_tests [] [] (linearize p))*)
  begin let res = compress_tests [] p in
  if !about_traces then Format.printf "Optimized trace %s\n\n" (show_symb res);
  res
  end
  else p
(* this optimization is currently disabled in the presence of private
   channels as it creates a bug in the pre-treatment: tests before a
   private communication are removed, even though they should not
   be *)

(*and linearize = function
  | SymbNul -> []
  | SymbAct _ as a -> [a]
  | SymbSeq (p1, p2) -> linearize p1 @ linearize p2
  | SymbPar (p1, p2) -> [SymbPar (optimize_tests p1, optimize_tests p2)]
  | SymbAlt (p1, p2) -> [SymbAlt (optimize_tests p1, optimize_tests p2)]
  | SymbPhase (p1, p2) -> [SymbPhase (optimize_tests p1, optimize_tests p2)]*)

(*and unlinearize res = function
  | [] -> res
  | x :: xs -> unlinearize (SymbSeq (x, res)) xs*)

(*and compress_tests res accu = function
  | [] -> if accu = [] then res else SymbAct accu :: res
  | SymbAct [Test (_, _) as a] :: xs ->
     compress_tests res (a :: accu) xs
  | SymbAct [Input (_, _) | Output (_, _) as a] :: xs ->
     compress_tests (SymbAct (a :: accu) :: res) [] xs
  | p :: xs ->
     let res = if accu = [] then res else SymbAct accu :: res in
     compress_tests (p :: res) [] xs*)

and compress_tests accu p = 
  match p with
  | SymbNul -> if accu = [] then SymbNul else SymbAct accu
  | SymbAct _ -> compress_tests accu (SymbSeq(p,SymbNul))
  | SymbSeq (SymbAct [t], p1) -> 
	if is_test_action t 
	then compress_tests (t :: accu) p1 
	else SymbSeq (SymbAct(t :: accu), (compress_tests [] p1))
  | SymbSeq (SymbSeq(p1,p2),p3) -> compress_tests accu (SymbSeq (p1,SymbSeq(p2,p3)))
  | SymbSeq (p1, p2) -> SymbSeq (compress_tests accu p1,compress_tests [] p2)
(*  | SymbSeq (p1, p2) -> linearize p1 @ linearize p2*)
  | SymbPar (p1, p2) -> let res=SymbPar (compress_tests [] p1, compress_tests [] p2)in if accu = [] then res else SymbSeq ( SymbAct accu, res)
  | SymbEither (p1, p2) -> SymbEither (compress_tests accu p1, compress_tests accu p2)
  | SymbAlt (p1, p2) -> SymbAlt (compress_tests accu p1, compress_tests accu p2)
(*  | SymbAlt (p1, p2) -> [SymbAlt (optimize_tests p1, optimize_tests p2)]*)
  | SymbPhase (p1, p2) -> let res=SymbPhase (compress_tests [] p1, compress_tests [] p2)in if accu = [] then res else SymbSeq ( SymbAct accu, res)

let rec maybe_null = function
  | SymbNul -> true
  | SymbAct a -> false
  | SymbSeq (p1, p2) -> (maybe_null p1) && (maybe_null p2)
  | SymbAlt (p1, p2) -> (maybe_null p1) || (maybe_null p2)
  | SymbEither (p1, p2) -> (maybe_null p1) || (maybe_null p2)
  | SymbPar (p1, p2) -> (maybe_null p1) && (maybe_null p2)
  | SymbPhase (p1, p2) -> (maybe_null p2)


let rec delta = function
  | SymbNul -> []
  | SymbAct a -> [ (a, SymbNul) ]
  | SymbSeq (p1, p2) ->
     List.rev_append
     (List.map (fun (a, p) ->
       (a, simplify (SymbSeq (p, p2))) 
     )  (delta p1))
	(if maybe_null p1 then delta p2 else [])
  | SymbAlt (p1, p2) -> delta p1 @ delta p2
  | SymbEither (p1, p2) -> delta p1 @ delta p2
  | SymbPar (p1, p2) ->
     let s1 =
       List.fold_left (fun accu (a, p) ->
         (a, simplify (SymbPar (p, p2))) :: accu
       ) [] (delta p1)
     in
     let s2 =
       List.fold_left (fun accu (a, p) ->
         (a, simplify (SymbPar (p1, p))) :: accu
       ) s1 (delta p2)
     in
     s2
  | SymbPhase (p1, p2) ->
      List.rev_append
        (List.map (fun (a,p) -> a, simplify (SymbPhase (p,p2))) (delta p1))
        (delta p2)

type action_classification =
  | PublicAction
  | PrivateInput of id * id
  | PrivateOutput of id * term

let classify_action = function
  | [] -> assert false
  | Test (_, _) :: _ -> PublicAction
  | TestInequal (_, _) :: _ -> PublicAction
  | Input (c, x) :: _ ->
     if List.mem c Theory.privchannels
     then PrivateInput (c, x) else PublicAction
  | Output (c, t) :: _ ->
     if List.mem c Theory.privchannels
     then PrivateOutput (c, t) else PublicAction

module Trace = struct type t = trace let compare = Pervasives.compare end
module TraceSet = Set.Make (Trace)

let rec trace_prepend a t =
  match a with
  | [] -> t
  | x :: xs -> trace_prepend xs (Trace (x, t))

let rec traces p =
  let d = delta p in
  let r =
    List.fold_left (fun accu (a, q) ->
      match classify_action a with
      | PublicAction ->
         TraceSet.fold (fun q accu ->
           TraceSet.add (trace_prepend a q) accu
         ) (traces q) accu
      | PrivateInput (_, _) -> accu
      | PrivateOutput (c, t) ->
         List.fold_left (fun accu (a, _) ->
           match classify_action a with
           | PrivateInput (c', x) when c = c' ->
              List.fold_left (fun accu (a, q) ->
                match classify_action a with
                | PrivateInput (c', x') when x = x' ->
                   assert (c = c');
                  TraceSet.fold (fun q accu ->
                    TraceSet.add q accu
                  ) (traces (replace_var_in_symb x t q)) accu
                | _ -> accu
              ) accu (delta q)
           | _ -> accu
         ) accu d
    ) TraceSet.empty d
  in
  if TraceSet.is_empty r then TraceSet.singleton NullTrace else r

(** Computing the set of traces with partial order reduction
  *
  * We implement the compressed strategy of Baelde, Hirschi & Delaune
  * for the subset of processes that is supported for it. *)

(*let rec canonize = function
  | SymbSeq (SymbAct [],q) -> assert false
  | SymbSeq (SymbAct [a],q) -> SymbSeq (SymbAct [a], q)
  | SymbSeq (SymbAct l,q) ->
      List.fold_left
        (fun q a -> SymbSeq (SymbAct [a], q))
        q l
  | SymbSeq (p, SymbNul) -> canonize p
  | SymbAct l -> canonize (SymbSeq (SymbAct l, SymbNul))
  | (SymbPar _ | SymbNul | SymbEither _) as p -> p
  | SymbSeq _ | SymbAlt _ | SymbPhase _ -> failwith "unsupported"*)

let prepend_traces a trace_set =
  TraceSet.fold
    (fun tr accu ->
       TraceSet.add (trace_prepend a tr) accu)
    trace_set
    TraceSet.empty

let traces_por p =
  assert (Theory.privchannels = []) ;
  let rec traces async sync =
    match async with
      | p :: async ->
          (* While there are async processes, execute them in a fixed
           * and arbitrary order: break parallels, execute outputs
           * as well as tests *)
          begin match p with
            | SymbNul ->
                traces async sync
            | SymbAct l -> (*There is no canonize anymore*)
                traces (SymbSeq(SymbAct l,SymbNul)::async) sync
            | SymbPar (q1,q2) ->
                traces (q1::q2::async) sync
            | SymbEither (q1,q2) ->
                TraceSet.union (traces (q1::async) sync)(traces (q2::async) sync)
            | SymbSeq (SymbAct ((Output (c,t) :: tests ) as a), q) ->
                let trset = prepend_traces a (traces (q::async) sync) in
                if tests = [] then trset else
                TraceSet.union
                  trset
                  (traces async sync)
            | SymbSeq (SymbAct ((*Test (t,t') as a*) (test :: tests) as a), q) when is_test_action test ->
                TraceSet.union
                  (prepend_traces a (traces (q::async) sync))
                  (traces async sync) (* the failure of the test blocks only the current thread *)
            | SymbSeq (SymbAct (Input _ :: _), q) ->
                traces async (p::sync)
            | _ ->
                failwith
                  (Printf.sprintf "unsupported async proc: %s" (show_symb p))
          end
      | [] ->
          (* Focus a process, execute it until focus should be released *)
          let rec focus p sync =
            match p with
              | SymbSeq (SymbAct ((Input (c,x) :: tests) as a), q) ->
                  prepend_traces a (focus q sync)
              | SymbSeq (SymbAct ((*Test (t,t')*) (test :: tests) as a), q) when is_test_action test ->
                  (* In case the test fails, the continuation is null
                   * so we have an improper block: no need to explore further
                   * traces. *)
                  prepend_traces a (focus q sync)
              | SymbNul ->
                  (* Obvious improper block *)
                  TraceSet.singleton NullTrace
              | SymbAct l -> (*There is no canonize anymore*)
                  focus (SymbSeq(SymbAct l,SymbNul)) sync
              | SymbPar (_,_)
              | SymbEither (_,_)
(*              | SymbSeq (SymbEither _, _) *)
              | SymbSeq (SymbAct (Output _ :: _), _) ->
                  (* In case of Par, this could be improper
                   * but we don't care and it won't happen in practice. *)
                  traces [p] sync
              | _ ->
                  failwith
                    (Printf.sprintf "unsupported sync proc: %s" (show_symb p))
          in
          let rec all_foci prev trace_set = function
            | p::next ->
                let trace_set =
                  TraceSet.union trace_set (focus p (List.rev_append prev next))
                in
                  all_foci (p::prev) trace_set next
            | [] -> trace_set
          in
          let trace_set = all_foci [] TraceSet.empty sync in
            if TraceSet.is_empty trace_set then
              TraceSet.singleton NullTrace
            else trace_set
  in
    traces [p] []

(** Extend traces_por with shallow support for phases *)
let traces_por p =
  match p with
    | SymbPhase (p1,p2) ->
        let s1 = traces_por p1 in
        let rec aux = function
          | NullTrace -> traces_por p2
          | Trace (Input _ as a, t) ->
              TraceSet.union
                (traces_por p2)
                (prepend_traces [a] (aux t))
          | Trace (a,t) ->
              prepend_traces [a] (aux t)
        in
          TraceSet.fold
            (fun t s ->
               TraceSet.union s (aux t))
            s1 TraceSet.empty
    | _ -> traces_por p

let traces p =
  let traces = if !Theory.por then traces_por else traces in
  let res = TraceSet.elements @@ traces @@ simplify @@ optimize_tests p in
  if !about_traces then begin Format.printf "Generated traces\n"; List.iter (fun t -> Format.printf "%s\n" (show_trace t)) res; Format.printf "\n%!"; end;
  res

let parse_process p ps =
  simplify @@ symb_of_temp p ps
*)
