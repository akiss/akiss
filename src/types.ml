let show_array sep f arr =
  Array.fold_left (fun str e -> if str = "" then f e else str ^ sep ^ (f e)) "" arr


type visi_type = Public | Hidden (* private or public channels *)

(* type of chans (e.g. c from in(c,x) ) *)
type chanId = {
    name : string;
    visibility : visi_type ;
}

let null_chan = { name = "null chan" ; visibility = Public}

(* type of functions signature *)
type funId = {
   name : string ;
   arity : int ;
}

(*** Transitional Types from parsed file to processes ***)

(* types of identifiers when "parsing" processes *)
type typ =
  | TermType 
  | ChanType 
  | Unknown

let show_typ t = 
  match !t with
  | TermType -> "term"
  | ChanType -> "chan"
  | Unknown -> "?"

(* Arguments of processes *)
type argId = {name : string; th : int }
type relative_location = int * (string option) (* option for input *)
type relative_nonce = int * string (* name of the nonce *)
type relative_temp_term =
  | F of funId * relative_temp_term list (* function *)
  | Xor of relative_temp_term list (* xor operator *)
  | Z (* zero *)
  | T of int * relative_temp_term list (* tuple *)
  | P of int * int * relative_temp_term (* pattern *)
  | N of relative_nonce (* nonce *)
  | V of relative_location (* input variable *)
  | A of argId (* argument of the function *)
  | C of chanId (* channel name (the type of expression is not known yet) *)

(* inner structure of declared processes *)  
type bounded_process =
  | NilB 
  | NameB of relative_nonce * bounded_process (* new x; P *)
  | InputB of relative_temp_term * relative_location * bounded_process 
  | OutputB of relative_temp_term * relative_location * relative_temp_term * bounded_process
  | TestIfB of relative_location * relative_temp_term * relative_temp_term * bounded_process * bounded_process
  | ParB of bounded_process list (* parallel processes *)
  | ChoiceB of relative_location * (bounded_process list) (* choice *)
  | CallB of relative_location * int * procId * relative_temp_term list (* process call *)
  | PhaseB of int * bounded_process (* phases (not fully implemented yet *)
  
(* types of declared processes *)  
and procId = { 
   name : string ; 
   arity : int; 
   types : (typ ref) array;
   mutable process : bounded_process; 
   mutable nbloc : int; 
   mutable nbnonces : int
   }


let show_procId p = 
  Printf.sprintf "%s(%d) : [%s] loc: %d n: %d " p.name p.arity (show_array "," show_typ p.types) p.nbloc p.nbnonces

let rec show_bounded_process p = 
  match p with
  | NilB -> ""
  | NameB((i,s),p) -> "new(" ^ (s) ^ (string_of_int i) ^ ");" ^ show_bounded_process p
  | InputB(ch,(i,_),p) -> "in(" ^ (show_relative_term ch) ^ "," ^ (string_of_int i) ^ ");" ^ show_bounded_process p
  | OutputB(ch,(i,_),t,p) -> 
      "out(" ^ (show_relative_term ch) ^ (string_of_int i)^ "," ^ (show_relative_term t) ^ ");" ^ show_bounded_process p
  | TestIfB(l,s,t,p1,p2) -> Printf.sprintf "if %s = %s then %s else %s" (show_relative_term s)(show_relative_term t)(show_bounded_process p1)(show_bounded_process p2)
  | ParB(lst) -> (List.fold_left (fun s t -> s ^ " || " ^ show_bounded_process t) "(" lst) ^ ")"
  | ChoiceB(l,lst) -> (List.fold_left (fun s t -> s ^ " ++ " ^ show_bounded_process t) "(" lst) ^ ")"
  | CallB(l,i,p,args) -> (List.fold_left (fun s t -> s ^ "," ^ show_relative_term t) (p.name ^ (string_of_int i) ^ "(") args) ^ ")"
  | PhaseB(i,p) -> "phase " ^ (string_of_int i) ^"." ^  show_bounded_process p

and show_relative_term t = 
  match t with 
  | F (f,args) -> if args = [] then f.name else (List.fold_left (fun s t -> (if s = "" then (f.name ^ "(") else s ^ ",") ^ show_relative_term t) "" args) ^ ")"
  | Xor(args) -> (List.fold_left (fun s t -> (if s = "" then ( "(") else s ^ "+") ^ show_relative_term t) "" args) ^ ")"
  | Z -> "0"
  | T (n,args) -> (List.fold_left (fun s t -> s ^ "," ^ show_relative_term t)  "(" args) ^ ")"
  | P (i,n,t) -> Printf.sprintf "Proj_%d(%s)" i (show_relative_term t)
  | N(i,s) -> s
  | V(i,Some str) -> str ^ "_" ^ (string_of_int i)
  | V(i,None) -> string_of_int i
  | A(a) -> a.name ^  ":" ^ (string_of_int a.th) 
  | C(c) -> c.name

let rec show_relative_term_list  = function
  | [] -> ""
  | [t] -> show_relative_term t
  | t :: q -> show_relative_term t ^ "," ^ (show_relative_term_list q)
  

(* Type used to know from which statement variables come from *)
type statement_role =
  | Master (* first statement *)
  | Slave (* second statement *)
  | New (* second statement should never be set at New when performing substitution *)
  | Rule (* second statement for rewrite rule *)
  | Extra of int (* for extra variables when doing ac unification, 
  the integer denotes which unification when they are done in sequences *)

let show_binder = function 
  | Master -> "M"
  | Slave -> "$"
  | New -> "*"
  | Rule -> "§"
  | Extra(n) -> "~"

type varId = {
   n : int ; (* from 0 to nbvars-1 *)
   status : statement_role ref ; (* ref to the shared status of the statement *)
}

(* actual nonce *)
type nonceId = {
  name : string ;
  n : int ;
}

let null_nonce = {name = "null" ; n= -1}

(* type of indexes, for commodity calls also have index *)
type io =
   | Input of chanId
   | Output of chanId * term
   | Choice
   | Call

(* type of indexes *)   
and location = {
 p : int;
 io : io;
 name : string;
 phase : int ;
 observable : visi_type ;
 parent : location option; (*the previous i/o of the syntax tree *)
}

(* type of terms *)
and funName = 
  | Regular of funId (* f,g,h *)
  | Nonce of nonceId (* new n. P *)
  | Plus
  | Zero
  | Tuple of int
  | Projection of int * int
  | Frame of location (*ie w0, w1,.. *)
  | InputVar of location (* transitional for processes *)

and funInfos = { 
   id : funName;
   has_variables : bool ; 
}

and term =
  | Fun of funInfos * term list
  | Var of varId
  
let rec null_location = { p = -1; io = Call; name = "null_loc"; phase = 0 ; observable = Hidden; parent = None}

let root_location i = { p = i; io = Call; name = "root"; phase = 0 ; observable = Hidden; parent = None}

let show_varId id = (show_binder !(id.status)) ^ (string_of_int id.n)

(*let show_location l = Format.sprintf "%d: %s %s (%d)" l.p (show_io l.io) l.name l.phase*)

let rec show_term t =
 match t with
 | Fun({id=Regular(f)},args) -> if args = [] then f.name else f.name ^ "(" ^ (show_term_list args) ^ ")"
 | Fun({id=Tuple(n)},args) -> "(" ^ (show_term_list args) ^ ")"
 | Fun({id=Projection(m,n)},args) -> "Proj_"^(string_of_int m)^"(" ^ (show_term_list args) ^ ")"
 | Fun({id=Plus},[l;r]) ->  (show_term l) ^ "+" ^ (show_term r) 
 | Fun({id=Plus},args) ->   "+?" ^ (string_of_int (List.length args)) 
 | Fun({id=Zero},[]) ->   "0" 
 | Fun({id=Nonce(n)},[]) -> Format.sprintf "n[%d]" n.n  
 | Fun({id=InputVar(l)},[]) -> Format.sprintf "i[%d]" l.p  
 | Fun({id=Frame(l)},[]) -> Format.sprintf "w[%d]" l.p
 | Var(id) -> show_varId id
 | _ -> invalid_arg ("Todo")

and show_term_list = function
  | [x] -> show_term x
  | x :: l -> ( (show_term x) ^ "," ^ (show_term_list l) )
  | [] -> ""

(*let show_io io = match io with
  | Input(c) -> "in(" ^ c.name ^ ")"
  | Output(c,t) -> "out(" ^ c.name ^ "," ^ (show_term t) ^ ")"
  | _ -> "?"*)

  
  
let zero = Fun({id=Zero;has_variables=false},[])

(* type of rewrite rules *)
type rewrite_rule = {
  binder_rule : statement_role ref; (* for unifications during normalization etc. *)
  nbvars_rule : int ; (* number of variables involved *)
  lhs : term ; (* left hand side *)
  rhs : term ; (* right hand side *)
}

let show_rewrite_rule r = 
  Format.sprintf
    "(%s:%d) %s ==> %s\n"(show_binder !(r.binder_rule)) r.nbvars_rule (show_term r.lhs)(show_term r.rhs)

(* substitution type for matching *)
type subst_lst = (varId * term) list

let show_subst_lst lst =
  List.fold_left (fun str (x,t) -> str ^ "; " ^ (show_varId x) ^ "->" ^ (show_term t)) "subst_lst: " lst

type subst_array =
    (term option) array
    
(* type for new variables introduced by AC unification *)    
type subst_extra = { 
  binder_extra : statement_role ref; 
  nb_extra : int; 
  subst_extra : subst_array 
}

(* type of substitutions produced by unification *)
type subst_maker = { 
  m : subst_array ; 
  s : subst_array; 
  e : (subst_extra list)
}

let show_subst_array subst =
  (Array.fold_left (fun str t -> (if str = "" then "[|" else (str ^ ".")) ^ (match t with None -> "?" | Some t -> show_term t)) "" subst) ^ "|]"

let show_subst_maker subst =
  "subst_maker \n" ^
  (show_subst_array subst.m) ^ "\n" ^
  (show_subst_array subst.s) ^
  (List.fold_right (fun s str -> str ^ "\n" ^ (show_subst_array s.subst_extra)) subst.e "")

(* type of substitutions when they are applied on terms *)
(* the function Rewriting.pack cast the first type into this one *)
type substitution = {
    binder : statement_role ref;
    nbvars : int ;
    slave : term array ; 
    master : term array ;
}

let show_substitution subst =
  Array.fold_left (fun str t -> str ^  ", " ^(show_term t))
  ((Array.fold_left (fun str t -> str ^ ", " ^ (show_term t)) 
    (Printf.sprintf "substitution  (%d%s) : \nmaster: " subst.nbvars (show_binder !(subst.binder))) 
  subst.master) ^ "\nslave: ") subst.slave
