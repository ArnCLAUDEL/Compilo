type token =
  | IDENTIFIER of (string)
  | TYPE_NAME of (string)
  | CONSTANT of (int)
  | STRING_LITERAL of (string)
  | SIZEOF
  | PTR_OP
  | INC_OP
  | DEC_OP
  | LEFT_OP
  | RIGHT_OP
  | LE_OP
  | GE_OP
  | EQ_OP
  | NE_OP
  | AND_OP
  | OR_OP
  | MUL_ASSIGN
  | DIV_ASSIGN
  | MOD_ASSIGN
  | ADD_ASSIGN
  | SUB_ASSIGN
  | LEFT_ASSIGN
  | RIGHT_ASSIGN
  | AND_ASSIGN
  | XOR_ASSIGN
  | OR_ASSIGN
  | SEMI_CHR
  | OPEN_BRACE_CHR
  | CLOSE_BRACE_CHR
  | COMMA_CHR
  | COLON_CHR
  | EQ_CHR
  | OPEN_PAREN_CHR
  | CLOSE_PAREN_CHR
  | OPEN_BRACKET_CHR
  | CLOSE_BRACKET_CHR
  | DOT_CHR
  | AND_CHR
  | OR_CHR
  | XOR_CHR
  | BANG_CHR
  | TILDE_CHR
  | ADD_CHR
  | SUB_CHR
  | STAR_CHR
  | DIV_CHR
  | MOD_CHR
  | OPEN_ANGLE_CHR
  | CLOSE_ANGLE_CHR
  | QUES_CHR
  | TYPEDEF
  | EXTERN
  | STATIC
  | AUTO
  | REGISTER
  | CHAR
  | SHORT
  | INTEGER
  | LONG
  | SIGNED
  | UNSIGNED
  | FLOATING
  | DOUBLE
  | CONST
  | VOLATILE
  | VOID
  | STRUCT
  | UNION
  | ENUM
  | ELLIPSIS
  | EOF
  | CASE
  | DEFAULT
  | IF
  | ELSE
  | SWITCH
  | WHILE
  | DO
  | FOR
  | GOTO
  | CONTINUE
  | BREAK
  | RETURN
  | ASM

open Parsing;;
let _ = parse_error;;
# 2 "CLessGram.mly"

(*
 *	Copyright (c) 2005 by Laboratoire Spécification et Vérification (LSV),
 *	UMR 8643 CNRS & ENS Cachan.
 *	Written by Jean Goubault-Larrecq.  Derived from the csur project.
 *
 *	Permission is granted to anyone to use this software for any
 *	purpose on any computer system, and to redistribute it freely,
 *	subject to the following restrictions:
 *
 *	1. Neither the author nor its employer is responsible for the consequences of use of
 *		this software, no matter how awful, even if they arise
 *		from defects in it.
 *
 *	2. The origin of this software must not be misrepresented, either
 *		by explicit claim or by omission.
 *
 *	3. Altered versions must be plainly marked as such, and must not
 *		be misrepresented as being the original software.
 *
 *	4. This software is restricted to non-commercial use only.  Commercial
 *		use is subject to a specific license, obtainable from LSV.
 * 
*)

(*
	Modified version by Benoit Barbot 2016 
*)

(* Analyse syntaxique d'un sous-ensemble (tres) reduit de C.
 *)
                  
open CLessType

let get_index ()= Index 
let get_setArray (x,y,z) = SetArray (x,y,z) 
let get_reference x = Ref x 
let get_dereference () = Deref
let get_setReference () =  SetReference 
						      
# 131 "CLessGram.ml"
let yytransl_const = [|
  261 (* SIZEOF *);
  262 (* PTR_OP *);
  263 (* INC_OP *);
  264 (* DEC_OP *);
  265 (* LEFT_OP *);
  266 (* RIGHT_OP *);
  267 (* LE_OP *);
  268 (* GE_OP *);
  269 (* EQ_OP *);
  270 (* NE_OP *);
  271 (* AND_OP *);
  272 (* OR_OP *);
  273 (* MUL_ASSIGN *);
  274 (* DIV_ASSIGN *);
  275 (* MOD_ASSIGN *);
  276 (* ADD_ASSIGN *);
  277 (* SUB_ASSIGN *);
  278 (* LEFT_ASSIGN *);
  279 (* RIGHT_ASSIGN *);
  280 (* AND_ASSIGN *);
  281 (* XOR_ASSIGN *);
  282 (* OR_ASSIGN *);
  283 (* SEMI_CHR *);
  284 (* OPEN_BRACE_CHR *);
  285 (* CLOSE_BRACE_CHR *);
  286 (* COMMA_CHR *);
  287 (* COLON_CHR *);
  288 (* EQ_CHR *);
  289 (* OPEN_PAREN_CHR *);
  290 (* CLOSE_PAREN_CHR *);
  291 (* OPEN_BRACKET_CHR *);
  292 (* CLOSE_BRACKET_CHR *);
  293 (* DOT_CHR *);
  294 (* AND_CHR *);
  295 (* OR_CHR *);
  296 (* XOR_CHR *);
  297 (* BANG_CHR *);
  298 (* TILDE_CHR *);
  299 (* ADD_CHR *);
  300 (* SUB_CHR *);
  301 (* STAR_CHR *);
  302 (* DIV_CHR *);
  303 (* MOD_CHR *);
  304 (* OPEN_ANGLE_CHR *);
  305 (* CLOSE_ANGLE_CHR *);
  306 (* QUES_CHR *);
  307 (* TYPEDEF *);
  308 (* EXTERN *);
  309 (* STATIC *);
  310 (* AUTO *);
  311 (* REGISTER *);
  312 (* CHAR *);
  313 (* SHORT *);
  314 (* INTEGER *);
  315 (* LONG *);
  316 (* SIGNED *);
  317 (* UNSIGNED *);
  318 (* FLOATING *);
  319 (* DOUBLE *);
  320 (* CONST *);
  321 (* VOLATILE *);
  322 (* VOID *);
  323 (* STRUCT *);
  324 (* UNION *);
  325 (* ENUM *);
  326 (* ELLIPSIS *);
    0 (* EOF *);
  327 (* CASE *);
  328 (* DEFAULT *);
  329 (* IF *);
  330 (* ELSE *);
  331 (* SWITCH *);
  332 (* WHILE *);
  333 (* DO *);
  334 (* FOR *);
  335 (* GOTO *);
  336 (* CONTINUE *);
  337 (* BREAK *);
  338 (* RETURN *);
  339 (* ASM *);
    0|]

let yytransl_block = [|
  257 (* IDENTIFIER *);
  258 (* TYPE_NAME *);
  259 (* CONSTANT *);
  260 (* STRING_LITERAL *);
    0|]

let yylhs = "\255\255\
\002\000\002\000\002\000\002\000\002\000\004\000\005\000\005\000\
\003\000\007\000\008\000\009\000\009\000\009\000\009\000\011\000\
\011\000\013\000\013\000\014\000\014\000\014\000\014\000\014\000\
\016\000\017\000\018\000\019\000\020\000\010\000\015\000\021\000\
\021\000\021\000\021\000\022\000\022\000\022\000\023\000\024\000\
\024\000\024\000\024\000\024\000\025\000\025\000\025\000\026\000\
\027\000\028\000\029\000\029\000\030\000\030\000\012\000\012\000\
\006\000\006\000\031\000\033\000\033\000\034\000\034\000\035\000\
\036\000\032\000\032\000\032\000\032\000\037\000\037\000\037\000\
\037\000\037\000\043\000\044\000\038\000\038\000\038\000\038\000\
\046\000\046\000\045\000\045\000\039\000\039\000\047\000\048\000\
\040\000\040\000\049\000\050\000\041\000\041\000\041\000\051\000\
\042\000\042\000\001\000\001\000\001\000\053\000\053\000\052\000\
\052\000\055\000\056\000\056\000\057\000\057\000\058\000\058\000\
\059\000\054\000\000\000"

let yylen = "\002\000\
\001\000\002\000\001\000\001\000\003\000\001\000\001\000\002\000\
\001\000\001\000\001\000\001\000\004\000\003\000\004\000\001\000\
\003\000\001\000\002\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\003\000\003\000\003\000\001\000\003\000\003\000\001\000\001\000\
\003\000\003\000\003\000\003\000\001\000\003\000\003\000\001\000\
\001\000\001\000\001\000\003\000\001\000\003\000\001\000\003\000\
\001\000\003\000\003\000\000\000\001\000\001\000\003\000\001\000\
\001\000\001\000\001\000\002\000\002\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\002\000\003\000\003\000\004\000\
\001\000\002\000\001\000\002\000\001\000\002\000\001\000\001\000\
\005\000\007\000\001\000\001\000\005\000\006\000\007\000\001\000\
\002\000\003\000\001\000\002\000\001\000\003\000\005\000\001\000\
\001\000\002\000\001\000\003\000\001\000\003\000\002\000\003\000\
\003\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\067\000\066\000\101\000\000\000\000\000\
\099\000\105\000\104\000\000\000\068\000\100\000\009\000\069\000\
\000\000\010\000\075\000\114\000\000\000\102\000\000\000\000\000\
\113\000\006\000\000\000\087\000\011\000\000\000\000\000\027\000\
\028\000\025\000\026\000\029\000\088\000\091\000\092\000\096\000\
\012\000\000\000\003\000\004\000\000\000\076\000\000\000\057\000\
\000\000\000\000\032\000\020\000\021\000\022\000\023\000\024\000\
\000\000\000\000\040\000\000\000\000\000\049\000\050\000\051\000\
\000\000\000\000\081\000\000\000\083\000\070\000\071\000\072\000\
\073\000\074\000\077\000\000\000\000\000\085\000\000\000\000\000\
\000\000\000\000\000\000\111\000\000\000\107\000\000\000\000\000\
\008\000\000\000\002\000\000\000\086\000\000\000\000\000\000\000\
\031\000\019\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\065\000\
\000\000\000\000\062\000\064\000\084\000\078\000\082\000\079\000\
\000\000\000\000\000\000\000\000\097\000\000\000\103\000\106\000\
\000\000\112\000\005\000\030\000\014\000\000\000\016\000\058\000\
\000\000\056\000\033\000\034\000\035\000\000\000\000\000\043\000\
\044\000\041\000\042\000\000\000\000\000\052\000\000\000\059\000\
\000\000\080\000\000\000\000\000\000\000\098\000\110\000\108\000\
\000\000\015\000\013\000\063\000\000\000\000\000\000\000\017\000\
\000\000\093\000\000\000\000\000\000\000\000\000\094\000\090\000\
\095\000"

let yydgoto = "\002\000\
\007\000\041\000\042\000\043\000\044\000\045\000\019\000\046\000\
\047\000\133\000\134\000\048\000\049\000\050\000\051\000\052\000\
\053\000\054\000\055\000\056\000\057\000\058\000\059\000\060\000\
\061\000\062\000\063\000\064\000\065\000\066\000\067\000\008\000\
\113\000\114\000\115\000\116\000\069\000\070\000\071\000\072\000\
\073\000\074\000\021\000\075\000\076\000\077\000\078\000\079\000\
\080\000\081\000\082\000\009\000\010\000\011\000\086\000\087\000\
\088\000\025\000\012\000"

let yysindex = "\009\000\
\001\000\000\000\233\254\000\000\000\000\000\000\215\254\013\255\
\000\000\000\000\000\000\009\255\000\000\000\000\000\000\000\000\
\250\254\000\000\000\000\000\000\042\255\000\000\031\255\238\254\
\000\000\000\000\035\255\000\000\000\000\010\000\049\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\041\255\000\000\000\000\046\255\000\000\029\255\000\000\
\050\255\010\000\000\000\000\000\000\000\000\000\000\000\000\000\
\088\255\047\255\000\000\007\255\114\255\000\000\000\000\000\000\
\084\255\085\255\000\000\013\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\109\255\042\255\000\000\074\255\076\255\
\097\255\235\255\098\255\000\000\013\255\000\000\116\255\115\255\
\000\000\246\254\000\000\251\255\000\000\010\000\010\000\010\000\
\000\000\000\000\010\000\010\000\010\000\010\000\010\000\010\000\
\010\000\010\000\010\000\010\000\010\000\010\000\010\000\000\000\
\121\255\129\255\000\000\000\000\000\000\000\000\000\000\000\000\
\109\255\010\000\010\000\031\000\000\000\089\255\000\000\000\000\
\023\255\000\000\000\000\000\000\000\000\058\255\000\000\000\000\
\006\255\000\000\000\000\000\000\000\000\088\255\088\255\000\000\
\000\000\000\000\000\000\007\255\007\255\000\000\084\255\000\000\
\049\255\000\000\072\255\092\255\031\000\000\000\000\000\000\000\
\010\000\000\000\000\000\000\000\175\255\175\255\251\255\000\000\
\086\255\000\000\092\255\175\255\175\255\175\255\000\000\000\000\
\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\158\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\066\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\092\000\000\000\000\000\000\000\000\000\118\000\000\000\
\144\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\170\000\017\255\000\000\229\255\006\001\000\000\000\000\000\000\
\159\255\087\255\000\000\141\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\133\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\150\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\196\000\222\000\000\000\
\000\000\000\000\000\000\246\000\014\001\000\000\019\001\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\128\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\000\000\248\255\000\000\153\000\228\255\000\000\000\000\
\000\000\157\255\000\000\173\255\124\000\000\000\218\255\000\000\
\000\000\000\000\000\000\000\000\038\000\000\000\058\000\035\000\
\000\000\000\000\000\000\071\000\072\000\000\000\107\000\238\255\
\000\000\000\000\037\000\000\000\187\255\176\000\140\255\000\000\
\000\000\000\000\000\000\184\255\115\000\000\000\000\000\000\000\
\000\000\000\000\000\000\187\000\000\000\000\000\067\000\000\000\
\000\000\000\000\000\000"

let yytablesize = 567
let yytable = "\017\000\
\006\000\090\000\068\000\118\000\120\000\085\000\117\000\157\000\
\135\000\001\000\136\000\098\000\138\000\015\000\003\000\084\000\
\004\000\104\000\105\000\094\000\022\000\013\000\091\000\131\000\
\005\000\023\000\024\000\039\000\039\000\039\000\039\000\039\000\
\039\000\083\000\162\000\094\000\018\000\003\000\027\000\004\000\
\167\000\163\000\015\000\039\000\026\000\027\000\039\000\005\000\
\154\000\015\000\039\000\117\000\039\000\126\000\106\000\107\000\
\166\000\016\000\068\000\112\000\139\000\140\000\141\000\095\000\
\039\000\039\000\137\000\172\000\028\000\018\000\029\000\174\000\
\093\000\092\000\030\000\094\000\128\000\168\000\003\000\031\000\
\004\000\096\000\032\000\033\000\034\000\035\000\036\000\161\000\
\005\000\102\000\103\000\132\000\159\000\155\000\156\000\169\000\
\170\000\003\000\110\000\004\000\111\000\094\000\175\000\176\000\
\177\000\165\000\122\000\005\000\123\000\015\000\085\000\026\000\
\027\000\055\000\037\000\158\000\055\000\038\000\094\000\039\000\
\055\000\094\000\055\000\040\000\127\000\132\000\108\000\109\000\
\089\000\124\000\089\000\089\000\099\000\100\000\101\000\028\000\
\018\000\029\000\171\000\142\000\143\000\030\000\148\000\149\000\
\112\000\129\000\031\000\152\000\130\000\032\000\033\000\034\000\
\035\000\036\000\089\000\089\000\089\000\115\000\153\000\173\000\
\089\000\144\000\145\000\146\000\147\000\089\000\109\000\060\000\
\089\000\089\000\089\000\089\000\089\000\097\000\053\000\015\000\
\061\000\026\000\027\000\089\000\150\000\037\000\151\000\119\000\
\038\000\053\000\039\000\020\000\053\000\164\000\040\000\121\000\
\053\000\014\000\053\000\160\000\000\000\000\000\000\000\000\000\
\089\000\028\000\018\000\089\000\000\000\089\000\000\000\030\000\
\000\000\089\000\000\000\000\000\031\000\000\000\000\000\032\000\
\033\000\034\000\035\000\036\000\000\000\000\000\097\000\097\000\
\097\000\097\000\097\000\097\000\097\000\097\000\097\000\097\000\
\097\000\097\000\097\000\015\000\000\000\026\000\027\000\000\000\
\000\000\045\000\045\000\045\000\045\000\000\000\000\000\037\000\
\000\000\000\000\038\000\015\000\039\000\026\000\027\000\045\000\
\040\000\000\000\045\000\000\000\000\000\125\000\045\000\000\000\
\045\000\000\000\015\000\030\000\026\000\027\000\000\000\000\000\
\031\000\000\000\000\000\032\000\033\000\034\000\035\000\036\000\
\000\000\000\000\000\000\030\000\132\000\000\000\000\000\015\000\
\031\000\026\000\027\000\032\000\033\000\034\000\035\000\036\000\
\000\000\000\000\030\000\000\000\000\000\000\000\000\000\031\000\
\000\000\000\000\032\000\033\000\034\000\035\000\036\000\000\000\
\003\000\028\000\004\000\000\000\000\000\000\000\000\000\030\000\
\000\000\000\000\005\000\000\000\031\000\000\000\000\000\032\000\
\033\000\034\000\035\000\036\000\007\000\007\000\007\000\007\000\
\007\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\007\000\000\000\000\000\007\000\
\000\000\007\000\000\000\007\000\007\000\007\000\001\000\001\000\
\001\000\001\000\001\000\001\000\007\000\007\000\007\000\007\000\
\007\000\007\000\007\000\000\000\000\000\000\000\001\000\000\000\
\000\000\001\000\000\000\001\000\000\000\001\000\001\000\001\000\
\018\000\018\000\018\000\018\000\018\000\018\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\000\000\000\000\000\000\
\018\000\000\000\000\000\018\000\000\000\018\000\000\000\018\000\
\000\000\018\000\031\000\031\000\031\000\031\000\031\000\031\000\
\018\000\018\000\018\000\018\000\018\000\018\000\018\000\000\000\
\000\000\000\000\031\000\000\000\000\000\031\000\000\000\000\000\
\000\000\031\000\000\000\031\000\036\000\036\000\036\000\036\000\
\036\000\036\000\031\000\031\000\031\000\031\000\031\000\031\000\
\031\000\000\000\000\000\000\000\036\000\000\000\000\000\036\000\
\000\000\000\000\000\000\036\000\000\000\036\000\037\000\037\000\
\037\000\037\000\037\000\037\000\036\000\036\000\000\000\000\000\
\000\000\036\000\036\000\000\000\000\000\000\000\037\000\000\000\
\000\000\037\000\000\000\000\000\000\000\037\000\000\000\037\000\
\038\000\038\000\038\000\038\000\038\000\038\000\037\000\037\000\
\000\000\000\000\000\000\037\000\037\000\000\000\000\000\000\000\
\038\000\000\000\000\000\038\000\000\000\000\000\000\000\038\000\
\000\000\038\000\046\000\046\000\046\000\046\000\000\000\000\000\
\038\000\038\000\000\000\000\000\000\000\038\000\038\000\000\000\
\046\000\000\000\000\000\046\000\048\000\048\000\000\000\046\000\
\000\000\046\000\047\000\047\000\047\000\047\000\000\000\000\000\
\048\000\000\000\054\000\048\000\000\000\000\000\000\000\048\000\
\047\000\048\000\000\000\047\000\000\000\054\000\000\000\047\000\
\054\000\047\000\000\000\000\000\054\000\000\000\054\000"

let yycheck = "\008\000\
\000\000\030\000\021\000\076\000\077\000\024\000\076\000\124\000\
\092\000\001\000\094\000\050\000\096\000\001\001\056\001\034\001\
\058\001\011\001\012\001\030\001\027\001\045\001\031\000\034\001\
\066\001\032\001\033\001\011\001\012\001\013\001\014\001\015\001\
\016\001\003\001\134\000\030\001\028\001\056\001\004\001\058\001\
\157\000\036\001\001\001\027\001\003\001\004\001\030\001\066\001\
\121\000\001\001\034\001\121\000\036\001\082\000\048\001\049\001\
\156\000\045\001\077\000\068\000\099\000\100\000\101\000\035\001\
\048\001\049\001\095\000\167\000\027\001\028\001\029\001\171\000\
\027\001\033\001\033\001\030\001\085\000\161\000\056\001\038\001\
\058\001\032\001\041\001\042\001\043\001\044\001\045\001\030\001\
\066\001\043\001\044\001\034\001\070\001\122\000\123\000\165\000\
\166\000\056\001\015\001\058\001\016\001\030\001\172\000\173\000\
\174\000\034\001\033\001\066\001\033\001\001\001\129\000\003\001\
\004\001\027\001\073\001\027\001\030\001\076\001\030\001\078\001\
\034\001\030\001\036\001\082\001\027\001\034\001\013\001\014\001\
\001\001\033\001\003\001\004\001\045\001\046\001\047\001\027\001\
\028\001\029\001\167\000\102\000\103\000\033\001\108\000\109\000\
\153\000\030\001\038\001\027\001\034\001\041\001\042\001\043\001\
\044\001\045\001\027\001\028\001\029\001\000\000\030\001\074\001\
\033\001\104\000\105\000\106\000\107\000\038\001\034\001\027\001\
\041\001\042\001\043\001\044\001\045\001\050\000\016\001\001\001\
\027\001\003\001\004\001\027\000\110\000\073\001\111\000\077\000\
\076\001\027\001\078\001\012\000\030\001\153\000\082\001\077\000\
\034\001\007\000\036\001\129\000\255\255\255\255\255\255\255\255\
\073\001\027\001\028\001\076\001\255\255\078\001\255\255\033\001\
\255\255\082\001\255\255\255\255\038\001\255\255\255\255\041\001\
\042\001\043\001\044\001\045\001\255\255\255\255\099\000\100\000\
\101\000\102\000\103\000\104\000\105\000\106\000\107\000\108\000\
\109\000\110\000\111\000\001\001\255\255\003\001\004\001\255\255\
\255\255\013\001\014\001\015\001\016\001\255\255\255\255\073\001\
\255\255\255\255\076\001\001\001\078\001\003\001\004\001\027\001\
\082\001\255\255\030\001\255\255\255\255\027\001\034\001\255\255\
\036\001\255\255\001\001\033\001\003\001\004\001\255\255\255\255\
\038\001\255\255\255\255\041\001\042\001\043\001\044\001\045\001\
\255\255\255\255\255\255\033\001\034\001\255\255\255\255\001\001\
\038\001\003\001\004\001\041\001\042\001\043\001\044\001\045\001\
\255\255\255\255\033\001\255\255\255\255\255\255\255\255\038\001\
\255\255\255\255\041\001\042\001\043\001\044\001\045\001\255\255\
\056\001\027\001\058\001\255\255\255\255\255\255\255\255\033\001\
\255\255\255\255\066\001\255\255\038\001\255\255\255\255\041\001\
\042\001\043\001\044\001\045\001\011\001\012\001\013\001\014\001\
\015\001\016\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\027\001\255\255\255\255\030\001\
\255\255\032\001\255\255\034\001\035\001\036\001\011\001\012\001\
\013\001\014\001\015\001\016\001\043\001\044\001\045\001\046\001\
\047\001\048\001\049\001\255\255\255\255\255\255\027\001\255\255\
\255\255\030\001\255\255\032\001\255\255\034\001\035\001\036\001\
\011\001\012\001\013\001\014\001\015\001\016\001\043\001\044\001\
\045\001\046\001\047\001\048\001\049\001\255\255\255\255\255\255\
\027\001\255\255\255\255\030\001\255\255\032\001\255\255\034\001\
\255\255\036\001\011\001\012\001\013\001\014\001\015\001\016\001\
\043\001\044\001\045\001\046\001\047\001\048\001\049\001\255\255\
\255\255\255\255\027\001\255\255\255\255\030\001\255\255\255\255\
\255\255\034\001\255\255\036\001\011\001\012\001\013\001\014\001\
\015\001\016\001\043\001\044\001\045\001\046\001\047\001\048\001\
\049\001\255\255\255\255\255\255\027\001\255\255\255\255\030\001\
\255\255\255\255\255\255\034\001\255\255\036\001\011\001\012\001\
\013\001\014\001\015\001\016\001\043\001\044\001\255\255\255\255\
\255\255\048\001\049\001\255\255\255\255\255\255\027\001\255\255\
\255\255\030\001\255\255\255\255\255\255\034\001\255\255\036\001\
\011\001\012\001\013\001\014\001\015\001\016\001\043\001\044\001\
\255\255\255\255\255\255\048\001\049\001\255\255\255\255\255\255\
\027\001\255\255\255\255\030\001\255\255\255\255\255\255\034\001\
\255\255\036\001\013\001\014\001\015\001\016\001\255\255\255\255\
\043\001\044\001\255\255\255\255\255\255\048\001\049\001\255\255\
\027\001\255\255\255\255\030\001\015\001\016\001\255\255\034\001\
\255\255\036\001\013\001\014\001\015\001\016\001\255\255\255\255\
\027\001\255\255\016\001\030\001\255\255\255\255\255\255\034\001\
\027\001\036\001\255\255\030\001\255\255\027\001\255\255\034\001\
\030\001\036\001\255\255\255\255\034\001\255\255\036\001"

let yynames_const = "\
  SIZEOF\000\
  PTR_OP\000\
  INC_OP\000\
  DEC_OP\000\
  LEFT_OP\000\
  RIGHT_OP\000\
  LE_OP\000\
  GE_OP\000\
  EQ_OP\000\
  NE_OP\000\
  AND_OP\000\
  OR_OP\000\
  MUL_ASSIGN\000\
  DIV_ASSIGN\000\
  MOD_ASSIGN\000\
  ADD_ASSIGN\000\
  SUB_ASSIGN\000\
  LEFT_ASSIGN\000\
  RIGHT_ASSIGN\000\
  AND_ASSIGN\000\
  XOR_ASSIGN\000\
  OR_ASSIGN\000\
  SEMI_CHR\000\
  OPEN_BRACE_CHR\000\
  CLOSE_BRACE_CHR\000\
  COMMA_CHR\000\
  COLON_CHR\000\
  EQ_CHR\000\
  OPEN_PAREN_CHR\000\
  CLOSE_PAREN_CHR\000\
  OPEN_BRACKET_CHR\000\
  CLOSE_BRACKET_CHR\000\
  DOT_CHR\000\
  AND_CHR\000\
  OR_CHR\000\
  XOR_CHR\000\
  BANG_CHR\000\
  TILDE_CHR\000\
  ADD_CHR\000\
  SUB_CHR\000\
  STAR_CHR\000\
  DIV_CHR\000\
  MOD_CHR\000\
  OPEN_ANGLE_CHR\000\
  CLOSE_ANGLE_CHR\000\
  QUES_CHR\000\
  TYPEDEF\000\
  EXTERN\000\
  STATIC\000\
  AUTO\000\
  REGISTER\000\
  CHAR\000\
  SHORT\000\
  INTEGER\000\
  LONG\000\
  SIGNED\000\
  UNSIGNED\000\
  FLOATING\000\
  DOUBLE\000\
  CONST\000\
  VOLATILE\000\
  VOID\000\
  STRUCT\000\
  UNION\000\
  ENUM\000\
  ELLIPSIS\000\
  EOF\000\
  CASE\000\
  DEFAULT\000\
  IF\000\
  ELSE\000\
  SWITCH\000\
  WHILE\000\
  DO\000\
  FOR\000\
  GOTO\000\
  CONTINUE\000\
  BREAK\000\
  RETURN\000\
  ASM\000\
  "

let yynames_block = "\
  IDENTIFIER\000\
  TYPE_NAME\000\
  CONSTANT\000\
  STRING_LITERAL\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 71 "CLessGram.mly"
             ( Var _1 )
# 595 "CLessGram.ml"
               : 'primary_expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 72 "CLessGram.mly"
                         ( get_reference _2)
# 602 "CLessGram.ml"
               : 'primary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'constant) in
    Obj.repr(
# 73 "CLessGram.mly"
                   ( Const _1 )
# 609 "CLessGram.ml"
               : 'primary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'string_literal) in
    Obj.repr(
# 74 "CLessGram.mly"
                  ( String _1 )
# 616 "CLessGram.ml"
               : 'primary_expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 75 "CLessGram.mly"
                                                    ( _2 )
# 623 "CLessGram.ml"
               : 'primary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 78 "CLessGram.mly"
                    ( _1 )
# 630 "CLessGram.ml"
               : 'constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 81 "CLessGram.mly"
                         ( _1 )
# 637 "CLessGram.ml"
               : 'string_literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'string_literal) in
    Obj.repr(
# 83 "CLessGram.mly"
            ( 
              (_1) ^ (_2)
            )
# 647 "CLessGram.ml"
               : 'string_literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 88 "CLessGram.mly"
                              (  _1 )
# 654 "CLessGram.ml"
               : 'identifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 89 "CLessGram.mly"
                              ( () )
# 660 "CLessGram.ml"
               : 'open_brace))
; (fun __caml_parser_env ->
    Obj.repr(
# 90 "CLessGram.mly"
                              ( () )
# 666 "CLessGram.ml"
               : 'close_brace))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'primary_expression) in
    Obj.repr(
# 94 "CLessGram.mly"
                     ( _1 )
# 673 "CLessGram.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'postfix_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 96 "CLessGram.mly"
 ( BOperator (_1,get_index (), _3) )
# 681 "CLessGram.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'close_paren) in
    Obj.repr(
# 98 "CLessGram.mly"
 ( 
	   Call (_1, [])
	)
# 691 "CLessGram.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'argument_expression_list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'close_paren) in
    Obj.repr(
# 102 "CLessGram.mly"
 (
		Call (_1, List.rev _3)
	)
# 702 "CLessGram.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 110 "CLessGram.mly"
                                ( [_1] )
# 709 "CLessGram.ml"
               : 'argument_expression_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'argument_expression_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 111 "CLessGram.mly"
                                                                   ( 
          _3 :: _1 )
# 718 "CLessGram.ml"
               : 'argument_expression_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'postfix_expression) in
    Obj.repr(
# 116 "CLessGram.mly"
                             ( _1 )
# 725 "CLessGram.ml"
               : 'unary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'unary_operator) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 118 "CLessGram.mly"
 ( 
          let  c = _1 in
	  match c with
	      ADD_CHR -> _2
	    | SUB_CHR -> UOperator (MinusM, _2)
	    | BANG_CHR -> UOperator (Not, _2)
	    | STAR_CHR -> UOperator (get_dereference (), _2)
	    | _-> failwith "error"
	    )
# 741 "CLessGram.ml"
               : 'unary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'add_chr) in
    Obj.repr(
# 130 "CLessGram.mly"
                    ( _1 )
# 748 "CLessGram.ml"
               : 'unary_operator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'sub_chr) in
    Obj.repr(
# 131 "CLessGram.mly"
                    ( _1 )
# 755 "CLessGram.ml"
               : 'unary_operator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bang_chr) in
    Obj.repr(
# 132 "CLessGram.mly"
                    ( _1 )
# 762 "CLessGram.ml"
               : 'unary_operator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tilde_chr) in
    Obj.repr(
# 133 "CLessGram.mly"
                    ( _1 )
# 769 "CLessGram.ml"
               : 'unary_operator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'star_chr) in
    Obj.repr(
# 134 "CLessGram.mly"
             ( _1 )
# 776 "CLessGram.ml"
               : 'unary_operator))
; (fun __caml_parser_env ->
    Obj.repr(
# 137 "CLessGram.mly"
                        ( ADD_CHR   )
# 782 "CLessGram.ml"
               : 'add_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 138 "CLessGram.mly"
                        ( SUB_CHR   )
# 788 "CLessGram.ml"
               : 'sub_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 139 "CLessGram.mly"
                        ( BANG_CHR  )
# 794 "CLessGram.ml"
               : 'bang_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 140 "CLessGram.mly"
                        ( TILDE_CHR )
# 800 "CLessGram.ml"
               : 'tilde_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 141 "CLessGram.mly"
                        ( STAR_CHR  )
# 806 "CLessGram.ml"
               : 'star_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 143 "CLessGram.mly"
                              ( () )
# 812 "CLessGram.ml"
               : 'close_paren))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expression) in
    Obj.repr(
# 146 "CLessGram.mly"
                           ( _1 )
# 819 "CLessGram.ml"
               : 'cast_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 149 "CLessGram.mly"
                          ( _1 )
# 826 "CLessGram.ml"
               : 'multiplicative_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'multiplicative_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 151 "CLessGram.mly"
 ( 
	  BOperator (_1, Mult , _3)
	)
# 836 "CLessGram.ml"
               : 'multiplicative_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'multiplicative_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 155 "CLessGram.mly"
 (
		BOperator (_1, Div , _3)
	)
# 846 "CLessGram.ml"
               : 'multiplicative_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'multiplicative_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 159 "CLessGram.mly"
 (
		BOperator (_1, Mod , _3)
	)
# 856 "CLessGram.ml"
               : 'multiplicative_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'multiplicative_expression) in
    Obj.repr(
# 166 "CLessGram.mly"
            ( _1 )
# 863 "CLessGram.ml"
               : 'additive_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'additive_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'multiplicative_expression) in
    Obj.repr(
# 168 "CLessGram.mly"
 (
	  BOperator (_1, Add , _3)
	)
# 873 "CLessGram.ml"
               : 'additive_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'additive_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'multiplicative_expression) in
    Obj.repr(
# 172 "CLessGram.mly"
 (
	BOperator (_1, Sub , _3)
	)
# 883 "CLessGram.ml"
               : 'additive_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'additive_expression) in
    Obj.repr(
# 178 "CLessGram.mly"
                              ( _1 )
# 890 "CLessGram.ml"
               : 'shift_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 182 "CLessGram.mly"
                           ( _1 )
# 897 "CLessGram.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'relational_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 184 "CLessGram.mly"
 (
	BOperator( _1, LL , _3)
	)
# 907 "CLessGram.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'relational_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 188 "CLessGram.mly"
 (
		BOperator( _3, LL , _1)
	)
# 917 "CLessGram.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'relational_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 192 "CLessGram.mly"
 ( 
	  	BOperator( _1, LE , _3)
	)
# 927 "CLessGram.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'relational_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 196 "CLessGram.mly"
 (
		BOperator( _3, LE , _1)
	)
# 937 "CLessGram.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'relational_expression) in
    Obj.repr(
# 202 "CLessGram.mly"
                                ( _1 )
# 944 "CLessGram.ml"
               : 'equality_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'equality_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'relational_expression) in
    Obj.repr(
# 204 "CLessGram.mly"
 (
		BOperator( _1, EQ , _3)
	)
# 954 "CLessGram.ml"
               : 'equality_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'equality_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'relational_expression) in
    Obj.repr(
# 208 "CLessGram.mly"
 (
		BOperator( _1, NEQ , _3)
	)
# 964 "CLessGram.ml"
               : 'equality_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'equality_expression) in
    Obj.repr(
# 214 "CLessGram.mly"
                              ( _1 )
# 971 "CLessGram.ml"
               : 'and_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'and_expression) in
    Obj.repr(
# 218 "CLessGram.mly"
                         ( _1 )
# 978 "CLessGram.ml"
               : 'exclusive_or_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'exclusive_or_expression) in
    Obj.repr(
# 222 "CLessGram.mly"
                                  ( _1 )
# 985 "CLessGram.ml"
               : 'inclusive_or_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'inclusive_or_expression) in
    Obj.repr(
# 226 "CLessGram.mly"
                                  ( _1 )
# 992 "CLessGram.ml"
               : 'logical_and_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'logical_and_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'inclusive_or_expression) in
    Obj.repr(
# 228 "CLessGram.mly"
 (
		BOperator (_1, And , _3)
	)
# 1002 "CLessGram.ml"
               : 'logical_and_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'logical_and_expression) in
    Obj.repr(
# 234 "CLessGram.mly"
                                 ( _1 )
# 1009 "CLessGram.ml"
               : 'logical_or_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'logical_or_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'logical_and_expression) in
    Obj.repr(
# 236 "CLessGram.mly"
 (
		BOperator (_1, Or , _3)
	)
# 1019 "CLessGram.ml"
               : 'logical_or_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'logical_or_expression) in
    Obj.repr(
# 242 "CLessGram.mly"
                       ( _1 )
# 1026 "CLessGram.ml"
               : 'assignment_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'unary_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 245 "CLessGram.mly"
     (
	     let left = _1 in
	     match left with
	       Var x -> Set (x, _3)
	     | UOperator (uop,e) when (try uop = get_dereference () with _-> false)
	       -> BOperator (e,get_setReference (),_3)
	     | BOperator (Var x, bop , i) when (try bop = get_index () with _-> false)
	       -> get_setArray (x, i, _3)
	     |_ -> failwith "error"   
	   )
# 1043 "CLessGram.ml"
               : 'assignment_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 258 "CLessGram.mly"
                                ( _1 )
# 1050 "CLessGram.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 260 "CLessGram.mly"
 ( 
	  Seq [_1; _3]
	)
# 1060 "CLessGram.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'optional_init_declarator_list) in
    Obj.repr(
# 267 "CLessGram.mly"
 ( List.rev _2 )
# 1068 "CLessGram.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    Obj.repr(
# 271 "CLessGram.mly"
          ( [] )
# 1074 "CLessGram.ml"
               : 'optional_init_declarator_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'init_declarator_list) in
    Obj.repr(
# 272 "CLessGram.mly"
                        ( _1 )
# 1081 "CLessGram.ml"
               : 'optional_init_declarator_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'init_declarator) in
    Obj.repr(
# 278 "CLessGram.mly"
            ( [_1] )
# 1088 "CLessGram.ml"
               : 'init_declarator_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'init_declarator_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'init_declarator) in
    Obj.repr(
# 280 "CLessGram.mly"
            ( _3 :: _1 )
# 1096 "CLessGram.ml"
               : 'init_declarator_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'declarator) in
    Obj.repr(
# 283 "CLessGram.mly"
                            ( _1 )
# 1103 "CLessGram.ml"
               : 'init_declarator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 286 "CLessGram.mly"
                     ( let x = _1 in x )
# 1110 "CLessGram.ml"
               : 'declarator))
; (fun __caml_parser_env ->
    Obj.repr(
# 290 "CLessGram.mly"
        (())
# 1116 "CLessGram.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 291 "CLessGram.mly"
           ( () )
# 1122 "CLessGram.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 292 "CLessGram.mly"
                 ( () )
# 1128 "CLessGram.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'type_specifier) in
    Obj.repr(
# 293 "CLessGram.mly"
                           ( () )
# 1135 "CLessGram.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'compound_statement) in
    Obj.repr(
# 296 "CLessGram.mly"
            ( _1 )
# 1142 "CLessGram.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expression_statement) in
    Obj.repr(
# 298 "CLessGram.mly"
            ( Expr _1 )
# 1149 "CLessGram.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'selection_statement) in
    Obj.repr(
# 300 "CLessGram.mly"
            ( _1 )
# 1156 "CLessGram.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'iteration_statement) in
    Obj.repr(
# 302 "CLessGram.mly"
            ( _1 )
# 1163 "CLessGram.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'jump_statement) in
    Obj.repr(
# 304 "CLessGram.mly"
            ( _1 )
# 1170 "CLessGram.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'open_brace) in
    Obj.repr(
# 307 "CLessGram.mly"
                        ( _1 )
# 1177 "CLessGram.ml"
               : 'open_block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'close_brace) in
    Obj.repr(
# 308 "CLessGram.mly"
                          ( _1 )
# 1184 "CLessGram.ml"
               : 'close_block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'open_block) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'close_block) in
    Obj.repr(
# 312 "CLessGram.mly"
        ( BlockStat ([], []) )
# 1192 "CLessGram.ml"
               : 'compound_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'open_block) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'close_block) in
    Obj.repr(
# 314 "CLessGram.mly"
 ( BlockStat ([], List.rev _2) )
# 1201 "CLessGram.ml"
               : 'compound_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'open_block) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'declaration_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'close_block) in
    Obj.repr(
# 316 "CLessGram.mly"
 ( BlockStat (_2, []) )
# 1210 "CLessGram.ml"
               : 'compound_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'open_block) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declaration_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'close_block) in
    Obj.repr(
# 318 "CLessGram.mly"
 ( BlockStat (_2, List.rev _3) )
# 1220 "CLessGram.ml"
               : 'compound_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'declaration) in
    Obj.repr(
# 324 "CLessGram.mly"
          ( _1 )
# 1227 "CLessGram.ml"
               : 'declaration_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'declaration_list) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'declaration) in
    Obj.repr(
# 326 "CLessGram.mly"
          ( _1 @ _2 )
# 1235 "CLessGram.ml"
               : 'declaration_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 332 "CLessGram.mly"
          ( [_1] )
# 1242 "CLessGram.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 334 "CLessGram.mly"
          ( _2 :: _1 )
# 1250 "CLessGram.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'semi_chr) in
    Obj.repr(
# 339 "CLessGram.mly"
            ( Seq [] )
# 1257 "CLessGram.ml"
               : 'expression_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 341 "CLessGram.mly"
            ( _1 )
# 1264 "CLessGram.ml"
               : 'expression_statement))
; (fun __caml_parser_env ->
    Obj.repr(
# 344 "CLessGram.mly"
                    ( () )
# 1270 "CLessGram.ml"
               : 'semi_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 346 "CLessGram.mly"
          ( () )
# 1276 "CLessGram.ml"
               : 'ifkw))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'ifkw) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 350 "CLessGram.mly"
 ( 
          IfStat (_3, _5, (BlockStat ([], [])))
	)
# 1287 "CLessGram.ml"
               : 'selection_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'ifkw) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expression) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'statement) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 354 "CLessGram.mly"
 ( 
          IfStat (_3, _5, _7)
	)
# 1299 "CLessGram.ml"
               : 'selection_statement))
; (fun __caml_parser_env ->
    Obj.repr(
# 359 "CLessGram.mly"
                ( () )
# 1305 "CLessGram.ml"
               : 'whilekw))
; (fun __caml_parser_env ->
    Obj.repr(
# 360 "CLessGram.mly"
            ( () )
# 1311 "CLessGram.ml"
               : 'forkw))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'whilekw) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'close_paren) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 363 "CLessGram.mly"
    (
	    WhileStat (_3, _5)
	   )
# 1323 "CLessGram.ml"
               : 'iteration_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'forkw) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'expression_statement) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expression_statement) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'close_paren) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 368 "CLessGram.mly"
 ( 
	 BlockStat ([], [ Expr _3 ;
			        WhileStat (_4, _6)])
	)
# 1337 "CLessGram.ml"
               : 'iteration_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'forkw) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expression_statement) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'expression_statement) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'close_paren) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 374 "CLessGram.mly"
 ( 
          BlockStat ([], [ Expr _3;
			    	 WhileStat (_4,
				  BlockStat ([], [_7; Expr _5]))])
	)
# 1353 "CLessGram.ml"
               : 'iteration_statement))
; (fun __caml_parser_env ->
    Obj.repr(
# 381 "CLessGram.mly"
                ( )
# 1359 "CLessGram.ml"
               : 'return))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'return) in
    Obj.repr(
# 385 "CLessGram.mly"
            ( ReturnStat None )
# 1366 "CLessGram.ml"
               : 'jump_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'return) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 387 "CLessGram.mly"
            (  ReturnStat (Some _2) )
# 1374 "CLessGram.ml"
               : 'jump_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'external_declaration) in
    Obj.repr(
# 392 "CLessGram.mly"
          ( _1 )
# 1381 "CLessGram.ml"
               : (CLessType.declaration list)))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : (CLessType.declaration list)) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'external_declaration) in
    Obj.repr(
# 394 "CLessGram.mly"
          ( _1 @ _2 )
# 1389 "CLessGram.ml"
               : (CLessType.declaration list)))
; (fun __caml_parser_env ->
    Obj.repr(
# 396 "CLessGram.mly"
          ( [] )
# 1395 "CLessGram.ml"
               : (CLessType.declaration list)))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'identifier) in
    Obj.repr(
# 400 "CLessGram.mly"
                                     ( VarDec(_2,None) )
# 1403 "CLessGram.ml"
               : 'glob_var_declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 401 "CLessGram.mly"
                                                            ( VarDec(_2,Some _4) )
# 1412 "CLessGram.ml"
               : 'glob_var_declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'function_definition) in
    Obj.repr(
# 405 "CLessGram.mly"
            ( [_1] )
# 1419 "CLessGram.ml"
               : 'external_declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'glob_var_declaration) in
    Obj.repr(
# 407 "CLessGram.mly"
            ( [_1] )
# 1426 "CLessGram.ml"
               : 'external_declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 410 "CLessGram.mly"
                                                 ( _2 )
# 1434 "CLessGram.ml"
               : 'parameter_declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_declaration) in
    Obj.repr(
# 415 "CLessGram.mly"
          ( [_1] )
# 1441 "CLessGram.ml"
               : 'parameter_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'parameter_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_declaration) in
    Obj.repr(
# 417 "CLessGram.mly"
          ( _3 :: _1 )
# 1449 "CLessGram.ml"
               : 'parameter_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_list) in
    Obj.repr(
# 421 "CLessGram.mly"
                         ( List.rev _1)
# 1456 "CLessGram.ml"
               : 'parameter_type_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'parameter_list) in
    Obj.repr(
# 422 "CLessGram.mly"
                                            ( List.rev _1 )
# 1463 "CLessGram.ml"
               : 'parameter_type_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 426 "CLessGram.mly"
                                  ( [] )
# 1469 "CLessGram.ml"
               : 'parameter_declarator))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'parameter_type_list) in
    Obj.repr(
# 427 "CLessGram.mly"
                                                      ( _2 )
# 1476 "CLessGram.ml"
               : 'parameter_declarator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_declarator) in
    Obj.repr(
# 431 "CLessGram.mly"
 ( _2, _3 )
# 1485 "CLessGram.ml"
               : 'function_declarator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'function_declarator) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'compound_statement) in
    Obj.repr(
# 436 "CLessGram.mly"
 ( 
          let var, decls = _1 in
	  FunDec ( var, decls, _2)
	)
# 1496 "CLessGram.ml"
               : 'function_definition))
(* Entry translation_unit *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let translation_unit (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : (CLessType.declaration list))
;;
