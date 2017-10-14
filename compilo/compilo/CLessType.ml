(** AST d'un sous-langage de C *)

open Printf

(**/**)       
(* Position du parseur pour reporter les erreurs; à ignorer *)
let cline = ref 1
let ccol = ref 0
let oldcline = ref 0
let oldccol = ref 0
let cfile = ref "stdin"
let fatal _ s = failwith s
(**/**)

(** {2 Définitions des types de l'arbre de syntaxique abstrait} *)
                         
(** Type des opérateurs unaire *)
type uop = 
  Not    (** négation booléenne *)
| MinusM (** moins unaire i.e. -x *)
| Deref  (** déréference i.e. *x *)
    
(** Type des opérateurs binaires *)
type bop =
  Mult (** multiplication *) | Add (** addition*)| Div (** division *) | Sub (** soustraction *)| Mod (** modulo*)
  | And (** et booléen*) | Or (** ou booléen*)
  | EQ  (** égale *)
  | NEQ (** différent *)
  | LE  (** plus petit ou égale *)
  | LL  (** strictement plus petit *)
(* | Index gestion des tableaux 
  | SetReference *)

                    
(** Type des expressions C *)                    
type expression =
  Var of string (** nom d'une variable *)
| Const of int (** entier littéral, i.e. constante *)
| Set of string * expression (** assigement de variable i.e. [Set("x",e)] -> x=e; *)
| Call of string * expression list (** appel de fonction i.e. [Call("f",[e1;e2; ...])] -> f(e1,e2,...) *)
| UOperator of uop * expression (** application d'opérateur unaire *)
| BOperator of expression * bop * expression (** application d'opérateur binaire *)
| Seq of expression list (** séquence d'expression i.e. [Seq([e1;e2;...])] -> e1;e2;... *)
| String of string (** string littéral i.e. chaine de caractères constante *)
(*| SetArray of string * expression * expression (** Assigement de tableau i.e. [SetArray("x",i,e)] -> x[i]=e; *) gestion des tableaux
| Ref of string (** get a reference i.e. &x*)*)
    
type statement =
  | BlockStat of string list * statement list
  (** bloc: liste de déclaration de variable locale
et liste de statement *)
  | Expr of expression (** une expression *)
  | IfStat of expression * statement * statement (** bloc if-then-else: [IfStat(e,s1,s2)] -> if(e)\{s1\}else\{s2\} *)
  | WhileStat of expression * statement (** bloc while: [WhileStat(e,s)] -> while(e)\{s\} *)
  | ReturnStat of expression option (** retour d'une fonction *)

type declaration =
  | VarDec of string * (int option)  (** définition de variable global *)
  | FunDec of string * ( string list ) * statement (** définition de fonction *)                 


(** {2 Iterateurs génériques sur les arbres} *)              

(** Iterateur sur les expressions *)
let rec iter_fun_expr f e =
  match f e with
  | Some x -> x
  | None -> (
    match e with
    | UOperator(mop,e) -> UOperator(mop,iter_fun_expr f e)
    | BOperator(e1,bop,e2) -> BOperator(iter_fun_expr f e1,bop,
                                        iter_fun_expr f e2)

    | Set(s,e) -> Set(s,iter_fun_expr f e)
    | Seq(el) -> Seq (List.map (iter_fun_expr f) el)
    | Var(x) -> Var(x)
    | Const(i) -> Const(i)
    | String(s) -> String(s)
    | Call(fn,el) -> Call(fn,List.map (iter_fun_expr f) el)
    (*| Ref(x) -> Ref(x)
    | SetArray(s,i,e) -> SetArray(s,iter_fun_expr f i,iter_fun_expr f e)*)
  )

(** Iterateur sur les statements *)              
let rec iter_fun_stat f g s = 
  match g s with
  | Some x -> x
  | None -> (
    match s with
    | BlockStat(dl,sl) ->
       BlockStat(dl,List.map (iter_fun_stat f g) sl)
    | Expr(e) -> Expr(iter_fun_expr f e)
    | IfStat(e,s1,s2) -> IfStat(iter_fun_expr f e,
                                iter_fun_stat f g s1,
                                iter_fun_stat f g s2)
    | WhileStat(e,s) -> WhileStat(iter_fun_expr f e,
                                  iter_fun_stat f g s)
    | ReturnStat(Some e) -> ReturnStat(Some (iter_fun_expr f e))
    | ReturnStat(None) -> ReturnStat(None)  
  )
            
let rec iter_fun_top f g = function
  | VarDec(n,v) -> VarDec(n,v)
  | FunDec(fn,al,s) -> FunDec(fn,al,iter_fun_stat f g s) 
