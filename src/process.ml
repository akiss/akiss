(*open Parser*)
open Types
open Dag
open Parser_functions
open Util

(** {2 Processes} *)

module BangLocation =
       struct
         type t = location * int
         let compare (x,i) (y,j) =
           compare (x.p,i) (y.p,j)
       end


module BangDag = Map.Make(BangLocation)
module BangSet = Set.Make(BangLocation)


type action = 
  | Input of location  
  | Output of location * term
  | OutputA of location * term (* auxiliary output for seed generation *)
  | Test of term * term
  | TestInequal of term * term
;;

type process =
  | EmptyP
  | ParallelP of process list
  | SeqP of action * process
  | ChoiceP of location * ((int * process) list)
  | CallP of location * int * procId * term array * chanId array
  
type process_infos = {
   first_location : int ;
   first_nonce : int;
}

type processes_infos = {
   mutable next_location : int ;
   mutable next_nonce : int;
   mutable processes : process_infos BangDag.t;
   mutable location_list : location list;
   mutable nonce_list : nonceId list;
   mutable max_phase : int;
}

let processes_infos = {
     next_location = 0 ;
     next_nonce = 0 ;
     processes = BangDag.empty ;
     location_list = [];
     nonce_list = [];
     max_phase = 0;
}

(*let (=process=) x y =
  match x,y with
  | SeqP(a,p),SeqP(a',p') -> 
  | ChoiceP(l,_),ChoiceP(l',_) -> l==l'
  | CallP(l,_,_,_,_),CallP(l',_,_,_,_) -> l==l'*)

let show_action a =
  match a with
  | Input(l) -> Printf.sprintf "in(%d)" l.p
  | Output(l,t)  -> Printf.sprintf "out(%d: %s)" l.p  (show_term t)
  | OutputA(l,t) -> Printf.sprintf "out'(%d: %s)" l.p  (show_term t)
  | Test(s,t) -> "[" ^ (show_term s) ^ "=" ^ (show_term t) ^ "]"
  | TestInequal(s,t) -> "[" ^ (show_term s) ^ "!=" ^ (show_term t) ^ "]"


let rec show_process pr = 
  match pr with
  | EmptyP -> ""
  | ParallelP(lp) ->( List.fold_left (fun str p -> str ^ "|" ^ (show_process p)) "(" lp ) ^ ")"
  | SeqP(a,p) -> (show_action a) ^ ";" ^ (show_process p)
  | ChoiceP(l,lp)->( List.fold_left (fun str (i,p) -> str ^ "+" ^ (show_process p)) "(" lp ) ^ ")"
  | CallP(l,i,procId,args,chans) -> procId.name ^ (if i = 1 then "" else (string_of_int i))

let rec show_process_start i pr = 
  if i = 0 then "..." else
  match pr with
  | EmptyP -> "0"
  | ParallelP(lp) ->( List.fold_left (fun str p -> str ^ "|" ^ (show_process_start i p)) "(" lp ) ^ ")"
  | ChoiceP(l,lp)->( List.fold_left (fun str (j,p) -> str ^ "+" ^ (show_process_start i p)) "(" lp ) ^ ")"
  | SeqP(a,p) -> (show_action a) ^ ";" ^ (show_process_start (i - 1) p)
  | CallP(l,j,procId,args,chans) -> procId.name ^ (if j = 1 then "" else (string_of_int j))

let rec count_type_nb typ pr i =
  if i = -1 then -1 
  else
  if !(pr.types.(i)) = typ then 1 + count_type_nb typ pr (i - 1)
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
  | A(th) -> arguments.(count_type_nb !(pr.types.(th.th)) pr th.th)
  | C(_) -> assert false
  
let convert_chan pr chans chan =
  match chan with 
  | C(c) -> c
  | A(th) ->
     (*Printf.printf "A({th= %d}) type: %s |- %d\n" th.th (show_typ  pr.types.(th.th))(count_type_nb pr.types.(th.th) pr th.th);*)
      chans.(count_type_nb !(pr.types.(th.th)) pr th.th)
  | _ -> assert(false)
  
let new_nonce str n =
  try List.find (fun l -> l.n = n) processes_infos.nonce_list
  with
  | Not_found ->
    let nonce = {name=str;n=n} in
    if !about_location then 
      Printf.printf "n[%d] : %s\n" n str;
    processes_infos.nonce_list <- nonce :: processes_infos.nonce_list;
    nonce

  
let new_location (pr : procId) p ( io : io ) str parent phase =
  try List.find (fun l -> l.p = p) processes_infos.location_list
  with
  | Not_found-> 
    let par = match parent with Some p -> p.p | None -> 0 in
    begin if !about_location then 
      match io with 
      | Input(chan) -> Printf.printf "%d : in(%s)  > %d[ph:%d] \n" p str par phase
      | Output(chan) -> Printf.printf "%d : out(%s) > %d[ph:%d]\n" p str par phase
      | Call -> Printf.printf " %d : %s      > %d[ph:%d] \n" p str par phase
      | Choice-> Printf.printf " %d: %s       > %d[ph:%d] \n" p str par phase
      end ;
    let l = {
      p=p; 
      io=io; 
      name=str; 
      phase=phase; 
      observable = (match io with Input(chan) | Output(chan) -> chan.visibility | _ -> Hidden);
      parent=parent
    } in
    processes_infos.location_list <- l :: processes_infos.location_list;
    l

let rec convert_pr infos process parent phase=
  let (pr, location, nonce, locations, nonces, args, chans) = infos in
  (*Printf.printf "Converting: %s \n%!" (show_bounded_process process);*)
  try
  match process with
  | NilB -> EmptyP
  | NameB ((rel_n,str),p) -> 
     nonces.(rel_n) <- new_nonce str (nonce+rel_n); 
     convert_pr infos p parent phase
  | InputB (ch,(rel_loc,Some str),p) -> 
    let chan = convert_chan pr chans ch in
    let new_loc = new_location pr (location+rel_loc) (Input(chan))  str parent phase in
     locations.(rel_loc) <- new_loc;
     SeqP(Input(locations.(rel_loc)),convert_pr infos p (if chan.visibility = Public then Some new_loc else parent) phase)
  | OutputB(ch,(rel_loc,Some str),term,p) -> 
    let chan = convert_chan pr chans ch in
    let new_loc = new_location pr (location+rel_loc) (Output(chan))  str parent phase in
     locations.(rel_loc) <- new_loc;
     SeqP(Output(locations.(rel_loc),convert_term pr locations nonces args term),
       convert_pr infos p (if chan.visibility = Public then Some new_loc else parent) phase)
  | TestIfB((rel_loc,Some str),s,t,p1,p2) -> 
     let s = convert_term pr locations nonces args s in 
     let t = convert_term pr locations nonces args t in 
     if p2 = NilB then SeqP(Test(s,t),convert_pr infos p1 parent phase) else
     if p1 = NilB then SeqP(TestInequal(s,t),convert_pr infos p2 parent phase) else
     begin
       locations.(rel_loc) <- new_location pr (location+rel_loc) Choice str parent phase;
       ChoiceP(locations.(rel_loc),[(0,SeqP(TestInequal(s,t),convert_pr infos p2 parent phase));
       (1,SeqP(Test(s,t),convert_pr infos p1 parent phase))])
     end
  | ParB(prlst) -> 
     ParallelP(List.map (fun pr -> convert_pr infos pr parent phase)prlst)
  | ChoiceB((rel_loc,Some s),lb) -> 
     locations.(rel_loc) <- new_location pr (location+rel_loc) Choice s parent phase;
     ChoiceP(locations.(rel_loc),List.mapi (fun i p -> (i, convert_pr infos p parent phase)) lb)
  | CallB((rel_loc,Some s),i,p,arguments) -> 
    (*Printf.printf "call of %s (args length = %d)\n with " (show_procId p) (Array.length args); List.iter (fun t -> Printf.printf "%s," (show_relative_term t))arguments; Printf.printf "\n";*)
     let ar = Array.make (1+(count_type_nb TermType p (p.arity - 1))) zero in
     let channels = Array.make (1+(count_type_nb ChanType p (p.arity - 1))) null_chan in
     let nbt = ref 0 in 
     let nbc = ref 0 in
     List.iteri (fun i x -> 
       (* Printf.printf " - %d" i;*)
       if !(p.types.(i)) = TermType 
       then begin ar.(!nbt) <- convert_term pr locations nonces args x; incr nbt end
       else if !(p.types.(i)) = ChanType 
       then begin channels.(!nbc) <- convert_chan pr chans x; incr nbc end
     ) arguments;
     locations.(rel_loc) <- new_location pr (location+rel_loc) Call s parent phase;
     CallP(locations.(rel_loc),i,p,ar,channels)
  | PhaseB(i,p) -> processes_infos.max_phase <- max processes_infos.max_phase i ; convert_pr infos p parent i
  | _ -> assert false
  with Invalid_argument(_) -> Printf.eprintf "Error when converting %s \n" (show_bounded_process process);exit 6
 
let expand_call loc copy (procId : procId) args chans=
  if  !about_seed then Format.printf "Expansion of %s (%s;%d)\nwhich is %s \n%!"
     (show_procId procId)(String.concat "," (Array.to_list(Array.map show_term args)))(Array.length chans) (show_bounded_process procId.process);
  let indexes =
  try (BangDag.find (loc,copy) processes_infos.processes)
  with Not_found -> begin 
    if !about_location 
    then Format.printf "Locations of %d: %s n°%d\n%!" loc.p (procId.name) copy ;
    let ind = {
      first_location = processes_infos.next_location;
      first_nonce = processes_infos.next_nonce ; 
    } in
    processes_infos.next_nonce <- processes_infos.next_nonce + procId.nbnonces ;
    processes_infos.next_location <- processes_infos.next_location + procId.nbloc;
    processes_infos.processes <- BangDag.add (loc,copy) ind processes_infos.processes ;
    ind
    end
  in
  let process = convert_pr (procId, indexes.first_location, indexes.first_nonce, 
      (Array.make procId.nbloc null_location),
      (Array.make procId.nbnonces null_nonce), args, chans) 
      procId.process loc.parent loc.phase  in
  process
(*  convert_pr (procId, indexes.first_location, indexes.first_nonce, 
    (Array.make procId.nbloc null_location),
    (Array.make procId.nbnonces null_nonce), args, chans) procId.process loc.parent *)

let rec repl_hidden_loc loc term t =
   match t with
   | Fun({id=Input(l)},[]) -> if l = loc then term else t
   | Fun(f,args) -> Fun(f,List.map (repl_hidden_loc loc term) args)
   | _ -> t
   
let repl_hidden_loc loc term t =
  Rewriting.normalize (repl_hidden_loc loc term t) (! Parser_functions.rewrite_rules)
  
let  apply_subst_action loc term a =
  match a with
  | Input(l) -> a
  | Output(l,t) -> Output(l,repl_hidden_loc loc term t)
  | OutputA(l,t) -> assert false
  | Test(s,t) -> Test(repl_hidden_loc loc term s,repl_hidden_loc loc term t)
  | TestInequal(s,t) -> TestInequal(repl_hidden_loc loc term s,repl_hidden_loc loc term t)
 
let rec apply_subst_process loc term pr = try
  match pr with
  | EmptyP -> pr
  | ParallelP(lp) -> ParallelP(List.map (apply_subst_process loc term) lp)
  | SeqP(a,p) -> SeqP(apply_subst_action loc term a,apply_subst_process loc term p)
  | ChoiceP(l,lp)->ChoiceP(l,List.map (fun (i,p) -> (i,apply_subst_process loc term p)) lp)
  | CallP(l,i,procId,args,chans) -> 
    CallP(l,i,procId,Array.map (fun t -> repl_hidden_loc loc term t) args,chans)
  with Invalid_argument a -> Format.printf "Process substitution error\n" ; raise (Invalid_argument a)
