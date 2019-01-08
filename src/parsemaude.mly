%{


open Types
open Term
open Parser_functions

let debug = false

let current_max_var = ref 0
let current_binder = ref (ref Master)

let update_subst pairlst =
  let subst = copy_subst_add_extra !maude_current_sigma !current_max_var !current_binder in
  List.iter (fun (x,t) -> 
    let sigm = find_sub x subst in 
    try
    sigm.(x.n) <- Some t
    with Invalid_argument a -> Printf.printf "%s index %s %d\n" (show_subst_maker subst)(show_binder !(x.status)) x.n; raise (Invalid_argument a)) pairlst;
  subst
  
let make_substitution_variant pairlst =
  (*Printf.printf "cur nbv %d\n" (!current_max_var);*)
  let dumb = Fun({id=Plus;has_variables=false}, []) in
  let master = Array.make !maude_current_nbv dumb in
  List.iter (fun ((x : varId),t) -> 
    master.(x.n) <- t) pairlst;
  Array.iteri (fun i t -> if t == dumb then (master.(i) <- Var({status = !current_binder;n = !current_max_var });incr current_max_var)) master;
  {
    binder = !current_binder; 
    master =  master ;
    slave = Array.make 0 zero;
    nbvars = !current_max_var
  } 
  

%}


%token Sharp
%token EOF
%token No More Unify Get Variants Reduce Match
%token In Empty Substitution
%token Ms Cpu Real Second
%token Unifier Variant Result Solution
%token Maude Line1
%token <string> Identifier
%token <string> Func
%token <string> Number
%token <int> Nonce
%token <int> Tuple
%token <int * int> Proj
%token <Types.varId> Var
%token <int> Int
%token Equals Dot Wedge Comma Colon Arrow
%token EqualUnify EqualMatch
%token LeftP RightP
%token Zero
%token Plus
%token Unifiers Match
%token Variants
%token Rewritesline Decisiontimeline
%token Bool True False
%token Greater
%token Term
%token Maude
%token Bye



%start main

%type < [ `Variants of ( (Types.term * Types.substitution) list) | `Unify of (Types.subst_maker list) | `Match of (Types.subst_lst list) | `Norm of Types.term | `Equal of bool ] > main

%%
main:
 | firstLine result Maude { if debug then Printf.printf "done!\n" ; $2 }
 | error { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error in Maude " }
 
     firstLine:
 | Line1 { }
 | Maude Line1 { }
          
     result:
 | unifierPreamble unifierList { `Unify $2 }
 | acunifierPreamble acunifierList { `Unify $2 }
 | matchPreamble matcherList { `Match $2 }
 | variantPreamble variantList { `Variants $2 }
 | reducePreamble Rewritesline Result resultTerm {`Norm zero }
 | equalsPreamble Rewritesline Result Bool Colon bool { `Equal true }
     
     unifierPreamble:
 | Variant Unify In Identifier Colon term EqualUnify term Dot {
  if debug then Printf.printf "unifierPreamble "}

     unifierList:
 | No Unifiers Dot Rewritesline {[]}  
 | No More Unifiers Dot Rewritesline {[]}  
 | unifier unifierList
     {$1::$2}
     
     unifier:
 | Unifier Sharp Number Rewritesline substitution {
      let sigma = update_subst $5 in
      current_binder := ref (Extra (List.length !maude_current_sigma.e));
      current_max_var := 0;
      sigma
  }

     acunifierPreamble:
 | Unify In Identifier Colon setequationsPreamble Dot
 Decisiontimeline{ 
    if debug then Printf.printf "acunifierPreamble ";
    current_binder := ref (Extra (List.length !maude_current_sigma.e));
    current_max_var := 0;
  }
  
  setequationsPreamble:
 | term EqualUnify term {}
 | term EqualUnify term Wedge setequationsPreamble {}
     
     acunifierList:
 | No Unifier Dot { [] }
 | acunifier {[$1]}
 | acunifier acunifierList { $1::$2 }

     acunifier:
 | Solution Number substitution {  
      let sigma = update_subst $3 in
      current_binder := ref (Extra (List.length !maude_current_sigma.e));
      current_max_var := 0;
      sigma
   }

     matchPreamble:
 | Match In Identifier Colon term EqualMatch term Dot
 Decisiontimeline{ if debug then Printf.printf "matchPreamble ";  }
     
     matcherList:
 | No Match Dot { [] }
 | matcher {[$1]}
 | matcher matcherList { $1::$2 }

     matcher:
 | Solution Number substitution
     { $3}

     
     variantPreamble:
 | Get Variants In Identifier Colon term Dot { 
    if debug then Printf.printf "variantPreamble "; 
    current_binder := ref Master;
    current_max_var := 0}

     variantList:
 | No More Variants Dot Rewritesline { []}  
 | variant variantList {
       $1 :: $2 }
      
    variant:
 | Variant Sharp Number Rewritesline resultTerm substitution {
      if debug then Printf.printf "variant no %s" $3; 
      let v = ($5,(make_substitution_variant $6)) in
      current_binder := ref Master;
      current_max_var := 0;
      v}
     
     resultTerm:
 | Term Colon term { if debug then Printf.printf "resultTerm ";$3 }

     reducePreamble:
 | Reduce In Identifier Colon term Dot { } 

     equalsPreamble:
 | Reduce In Identifier Colon term Equals Equals term Dot { }
     
     term:
 | Nonce
     { Fun({id=Nonce(List.assoc $1 !Parser_functions.nonces); has_variables=false},[])
     }
 | Var Colon Term {Var($1)}
 | Sharp Number Colon Term {
    let n = int_of_string $2 in
    current_max_var := max !current_max_var n ;
    Var ({status= !current_binder ; n=(n - 1)}) } 
 | Func LeftP termlist RightP { 
    match Parser_functions.Env.find $1 !Parser_functions.environment with
    | Func(f) -> Fun({id=Regular(f);has_variables=true},$3)
    | _ -> assert false
    }
 | Func { 
    match Parser_functions.Env.find $1 !Parser_functions.environment with
    | Func(f) -> Fun({id=Regular(f);has_variables=false},[])
    | _ -> assert false
    }
 | Tuple LeftP termlist RightP { 
    Fun({id=Tuple($1);has_variables=true},$3)
    }
 | Proj LeftP termlist RightP { 
    let x,y = $1 in
    Fun({id=Projection(x,y);has_variables=true},$3)
    }
 | term Plus term { Fun({id=Plus;has_variables=true}, [$1;$3])}
 | Zero {zero}
 | LeftP term RightP {$2}

termlist:
 | { [] }
 | netermlist { $1 }

netermlist:
 | term { [ $1 ] }
 | term Comma netermlist { $1 :: $3 }

substitution:
 | {if debug then Printf.printf "endsubst "; [] }
 | Empty Substitution {if debug then Printf.printf "emptysubst "; [] }
 | assignment substitution {if debug then Printf.printf "substitution "; $1 :: $2 }

assignment:
 | Var Colon Term Arrow term  { if debug then Printf.printf "assignment ";($1, $5) }

bool:
 | True  {true}     
 | False {false}     

%%
