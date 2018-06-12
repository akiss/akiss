let show_array sep f arr =
  Array.fold_left (fun str e -> if str = "" then f e else str ^ sep ^ (f e)) "" arr
 
type chanId = {
    name : string;
    (*id : int;*)
}

let null_chan = { name = "null chan" }

type funId = {
   name : string ;
   arity : int ;
}
type typ =
  | TermType 
  | ChanType 
  | Unknown

let show_typ = function
  | TermType -> "term"
  | ChanType -> "chan"
  | Unknown -> "?"

type argId = {name : string; th : int }
type relative_location = int * (string option) (* option for input *)
type relative_nonce = int * string (* name of the nonce *)
type relative_temp_term =
  | F of funId * relative_temp_term list
  | T of int * relative_temp_term list
  | P of int * int * relative_temp_term
  | N of relative_nonce
  | V of relative_location
  | A of argId
  | C of chanId

type bounded_process =
  | NilB 
  | NameB of relative_nonce * bounded_process
  | InputB of relative_temp_term * relative_location * bounded_process
  | OutputB of relative_temp_term * relative_location * relative_temp_term * bounded_process
  | TestIfB of relative_location * relative_temp_term * relative_temp_term * bounded_process * bounded_process
  | ParB of bounded_process list
  | ChoiceB of relative_location * (bounded_process list)
  | CallB of relative_location * procId * relative_temp_term list 
(*  | LetB of relative_pattern * relative_temp_term * bounded_process * bounded_process*)
and procId = { 
   name : string ; 
   arity : int; 
   types : typ array;
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
  | CallB(l,p,args) -> (List.fold_left (fun s t -> s ^ "," ^ show_relative_term t) (p.name ^ "(") args) ^ ")"
and show_relative_term t = 
  match t with 
  | F (f,args) -> if args = [] then f.name else (List.fold_left (fun s t -> (if s = "" then (f.name ^ "(") else s ^ ",") ^ show_relative_term t) "" args) ^ ")"
  | T (n,args) -> (List.fold_left (fun s t -> s ^ "," ^ show_relative_term t)  "(" args) ^ ")"
  | P (i,n,t) -> Printf.sprintf "Proj_%d(%s)" i (show_relative_term t)
  | N(i,s) -> s
  | V(i,Some str) -> str ^ (string_of_int i)
  | V(i,None) -> string_of_int i
  | A(a) -> a.name ^ (string_of_int a.th) 
  | C(c) -> c.name


type statement_role =
  | Master
  | Slave
  | New
  | Rule

let show_binder = function 
  | Master -> "M"
  | Slave -> "$"
  | New -> "*"
  | Rule -> "r"

type varId = {
   n : int ; (* ref ?*)
   status : statement_role ref ;
}

type nonceId = {
  name : string ;
  n : int ;
}

let null_nonce = {name = "null" ; n= -1}

type io =
   | Input of chanId
   | Output of chanId
   | Phase
   | Choice
   | Call
   | Virtual of varId

type location = {
 p : int;
 io : io;
 name : string;
 parent : location option; (*the previous i/o of the syntax tree *)
}

let rec null_location = { p = -1; io = Phase; name = "null_loc"; parent = None}

type funName = 
  | Regular of funId (* f,g,h *)
  | Nonce of nonceId (* new n. P *)
  | Plus
  | Zero
  | Tuple of int
  | Projection of int * int
  | Frame of location (*ie w0, w1,.. *)
  | Input of location (* transitional for process *)

type funInfos = { 
   id : funName;
   has_variables : bool ; 
}

type term =
  | Fun of funInfos * term list
  | Var of varId

let rec show_term t =
 match t with
 | Fun({id=Regular(f)},args) -> if args = [] then f.name else f.name ^ "(" ^ (show_term_list args) ^ ")"
 | Fun({id=Tuple(n)},args) -> "(" ^ (show_term_list args) ^ ")"
 | Fun({id=Projection(m,n)},args) -> "Proj_"^(string_of_int m)^"(" ^ (show_term_list args) ^ ")"
 | Fun({id=Plus},[l;r]) ->  (show_term l) ^ "+" ^ (show_term r) 
 | Fun({id=Zero},[]) ->   "0" 
 | Fun({id=Nonce(n)},[]) -> Format.sprintf "n[%d]" n.n  
 | Fun({id=Input(l)},[]) -> Format.sprintf "i[%d]" l.p  
 | Fun({id=Frame(l)},[]) -> Format.sprintf "w[%d]" l.p
 | Var(id) -> (show_binder !(id.status)) ^ (string_of_int id.n)
 | _ -> invalid_arg ("Todo")
and show_term_list = function
  | [x] -> show_term x
  | x :: l -> ( (show_term x) ^ "," ^ (show_term_list l) )
  | [] -> ""

let zero = Fun({id=Zero;has_variables=false},[])

type rewrite_rule = {
  binder : statement_role ref;
  nbvars : int ; 
  lhs : term ;
  rhs : term ;
}

let show_rewrite_rule r = 
  Format.sprintf
    "(%s:%d) %s ==> %s\n"(show_binder !(r.binder)) r.nbvars (show_term r.lhs)(show_term r.rhs)

type subst_lst = (varId * term) list

type subst_array =
    (term option) array


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
