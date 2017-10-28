type token =
  | LABEL of (string)
  | LPAR
  | RPAR
  | COLON
  | COMMA
  | DOLLAR
  | INTPH
  | ADDRPH
  | RPH
  | LPH
  | REGISTER of (ASMType.reg)
  | INTEGER of (int)
  | MOVOP
  | PUSHOP
  | POPOP
  | CALLOP
  | RETOP
  | ADDOP
  | MULOP
  | SUBOP
  | DIVOP
  | XOROP
  | OROP
  | ANDOP
  | NEGOP
  | NOTOP
  | CMPOP
  | TESTOP
  | MINUS
  | SETEOP
  | SETNEOP
  | SETNSOP
  | SETGOP
  | JMPOP
  | JZOP
  | JNZOP
  | LEAOP

open Parsing;;
let _ = parse_error;;
# 2 "ASMGram.mly"
  
open ASMType

let mon a f = let v1,v2 = a in (f v1),v2
let mon2 (a1,h1) (a2,h2) f = (f a1 a2),(h1@h2)
  

# 51 "ASMGram.ml"
let yytransl_const = [|
  258 (* LPAR *);
  259 (* RPAR *);
  260 (* COLON *);
  261 (* COMMA *);
  262 (* DOLLAR *);
  263 (* INTPH *);
  264 (* ADDRPH *);
  265 (* RPH *);
  266 (* LPH *);
  269 (* MOVOP *);
  270 (* PUSHOP *);
  271 (* POPOP *);
  272 (* CALLOP *);
  273 (* RETOP *);
  274 (* ADDOP *);
  275 (* MULOP *);
  276 (* SUBOP *);
  277 (* DIVOP *);
  278 (* XOROP *);
  279 (* OROP *);
  280 (* ANDOP *);
  281 (* NEGOP *);
  282 (* NOTOP *);
  283 (* CMPOP *);
  284 (* TESTOP *);
  285 (* MINUS *);
  286 (* SETEOP *);
  287 (* SETNEOP *);
  288 (* SETNSOP *);
  289 (* SETGOP *);
  290 (* JMPOP *);
  291 (* JZOP *);
  292 (* JNZOP *);
  293 (* LEAOP *);
    0|]

let yytransl_block = [|
  257 (* LABEL *);
  267 (* REGISTER *);
  268 (* INTEGER *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\000\000\000\000"

let yylen = "\002\000\
\001\000\002\000\001\000\001\000\003\000\004\000\004\000\005\000\
\005\000\001\000\001\000\002\000\002\000\004\000\002\000\002\000\
\002\000\002\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\002\000\002\000\004\000\004\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\004\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\010\000\000\000\000\000\000\000\004\000\
\011\000\001\000\000\000\000\000\038\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\039\000\
\000\000\002\000\000\000\000\000\000\000\000\000\012\000\013\000\
\000\000\015\000\016\000\018\000\017\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\026\000\027\000\000\000\000\000\
\030\000\031\000\032\000\033\000\034\000\035\000\036\000\000\000\
\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\007\000\006\000\000\000\000\000\014\000\019\000\021\000\020\000\
\022\000\023\000\024\000\025\000\028\000\029\000\037\000\009\000\
\008\000"

let yydgoto = "\003\000\
\013\000\040\000"

let yysindex = "\027\000\
\074\255\025\255\000\000\000\000\245\254\018\255\029\255\000\000\
\000\000\000\000\031\255\020\255\000\000\030\255\032\255\074\255\
\074\255\074\255\074\255\074\255\074\255\074\255\074\255\074\255\
\074\255\074\255\074\255\074\255\074\255\074\255\074\255\074\255\
\074\255\074\255\074\255\074\255\074\255\074\255\074\255\000\000\
\034\255\000\000\043\255\052\255\075\255\076\255\000\000\000\000\
\078\255\000\000\000\000\000\000\000\000\082\255\083\255\084\255\
\085\255\086\255\087\255\088\255\000\000\000\000\089\255\090\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\091\255\
\000\000\094\255\095\255\068\255\093\255\074\255\074\255\074\255\
\074\255\074\255\074\255\074\255\074\255\074\255\074\255\074\255\
\000\000\000\000\096\255\097\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\242\255\000\000"

let yytablesize = 262
let yytable = "\041\000\
\003\000\049\000\050\000\051\000\052\000\053\000\054\000\055\000\
\056\000\057\000\058\000\059\000\060\000\061\000\062\000\063\000\
\064\000\065\000\066\000\067\000\068\000\069\000\070\000\071\000\
\072\000\014\000\045\000\001\000\002\000\042\000\043\000\046\000\
\044\000\047\000\015\000\048\000\073\000\016\000\017\000\018\000\
\019\000\020\000\021\000\022\000\023\000\024\000\025\000\026\000\
\027\000\028\000\029\000\030\000\031\000\074\000\032\000\033\000\
\034\000\035\000\036\000\037\000\038\000\039\000\075\000\093\000\
\094\000\095\000\096\000\097\000\098\000\099\000\100\000\101\000\
\102\000\103\000\004\000\005\000\076\000\077\000\091\000\006\000\
\007\000\008\000\078\000\009\000\010\000\011\000\079\000\080\000\
\081\000\082\000\083\000\084\000\085\000\086\000\087\000\088\000\
\089\000\090\000\104\000\105\000\000\000\000\000\012\000\092\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\003\000"

let yycheck = "\011\001\
\000\000\016\000\017\000\018\000\019\000\020\000\021\000\022\000\
\023\000\024\000\025\000\026\000\027\000\028\000\029\000\030\000\
\031\000\032\000\033\000\034\000\035\000\036\000\037\000\038\000\
\039\000\001\001\007\001\001\000\002\000\012\001\002\001\012\001\
\002\001\004\001\010\001\004\001\003\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\011\001\030\001\031\001\
\032\001\033\001\034\001\035\001\036\001\037\001\011\001\078\000\
\079\000\080\000\081\000\082\000\083\000\084\000\085\000\086\000\
\087\000\088\000\001\001\002\001\002\001\002\001\011\001\006\001\
\007\001\008\001\005\001\010\001\011\001\012\001\005\001\005\001\
\005\001\005\001\005\001\005\001\005\001\005\001\005\001\005\001\
\003\001\003\001\003\001\003\001\255\255\255\255\029\001\011\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\005\001"

let yynames_const = "\
  LPAR\000\
  RPAR\000\
  COLON\000\
  COMMA\000\
  DOLLAR\000\
  INTPH\000\
  ADDRPH\000\
  RPH\000\
  LPH\000\
  MOVOP\000\
  PUSHOP\000\
  POPOP\000\
  CALLOP\000\
  RETOP\000\
  ADDOP\000\
  MULOP\000\
  SUBOP\000\
  DIVOP\000\
  XOROP\000\
  OROP\000\
  ANDOP\000\
  NEGOP\000\
  NOTOP\000\
  CMPOP\000\
  TESTOP\000\
  MINUS\000\
  SETEOP\000\
  SETNEOP\000\
  SETNSOP\000\
  SETGOP\000\
  JMPOP\000\
  JZOP\000\
  JNZOP\000\
  LEAOP\000\
  "

let yynames_block = "\
  LABEL\000\
  REGISTER\000\
  INTEGER\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : ASMType.reg) in
    Obj.repr(
# 31 "ASMGram.mly"
              ( R _1 )
# 284 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 32 "ASMGram.mly"
                    ( C(IL _2) )
# 291 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    Obj.repr(
# 33 "ASMGram.mly"
           ( C(HollInt) )
# 297 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    Obj.repr(
# 34 "ASMGram.mly"
            ( HollArg )
# 303 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : ASMType.reg) in
    Obj.repr(
# 35 "ASMGram.mly"
                        ( ARI(IL 0,_2) )
# 310 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : ASMType.reg) in
    Obj.repr(
# 36 "ASMGram.mly"
                                ( ARI(IL _1,_3) )
# 318 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : ASMType.reg) in
    Obj.repr(
# 37 "ASMGram.mly"
                              ( ARI(HollInt,_3) )
# 325 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : ASMType.reg) in
    Obj.repr(
# 38 "ASMGram.mly"
                                      ( ARI(IL(-_2),_4) )
# 333 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 1 : ASMType.reg) in
    Obj.repr(
# 39 "ASMGram.mly"
                                    ( ARI(HollIntM,_4) )
# 340 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 40 "ASMGram.mly"
           ( L _1 )
# 347 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    Obj.repr(
# 41 "ASMGram.mly"
         ( HollLabel )
# 353 "ASMGram.ml"
               : ASMType.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 45 "ASMGram.mly"
                 ( Label (L _1) )
# 360 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    Obj.repr(
# 46 "ASMGram.mly"
               ( Label HollLabel )
# 366 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 48 "ASMGram.mly"
                                   ( MOV(_2,_4) )
# 374 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 49 "ASMGram.mly"
                     ( PUSH(_2) )
# 381 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 50 "ASMGram.mly"
                    ( POP(_2) )
# 388 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 51 "ASMGram.mly"
                    ( RET )
# 395 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 52 "ASMGram.mly"
                     ( CALL(_2) )
# 402 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 54 "ASMGram.mly"
                                   ( ADD(_2,_4) )
# 410 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 55 "ASMGram.mly"
                                   ( SUB(_2,_4) )
# 418 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 56 "ASMGram.mly"
                                    ( MUL(_2,_4) )
# 426 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 57 "ASMGram.mly"
                                    ( DIV(_2,_4) )
# 434 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 58 "ASMGram.mly"
                                    ( XOR(_2,_4) )
# 442 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 59 "ASMGram.mly"
                                   ( OR(_2,_4) )
# 450 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 60 "ASMGram.mly"
                                    ( AND(_2,_4) )
# 458 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 61 "ASMGram.mly"
                     ( NEG (_2) )
# 465 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 62 "ASMGram.mly"
                     ( NOT (_2) )
# 472 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 64 "ASMGram.mly"
                                    ( CMP (_2,_4) )
# 480 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 65 "ASMGram.mly"
                                     ( TEST (_2,_4) )
# 488 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 67 "ASMGram.mly"
                      ( SETE _2 )
# 495 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 68 "ASMGram.mly"
                      ( SETNE _2 )
# 502 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 69 "ASMGram.mly"
                      ( SETNS _2 )
# 509 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 70 "ASMGram.mly"
                      ( SETG _2 )
# 516 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 72 "ASMGram.mly"
                     ( JMP _2 )
# 523 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 73 "ASMGram.mly"
                     ( JZ _2 )
# 530 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 74 "ASMGram.mly"
                     ( JNZ _2 )
# 537 "ASMGram.ml"
               : ASMType.instruction))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : ASMType.arg) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : ASMType.arg) in
    Obj.repr(
# 77 "ASMGram.mly"
           ( LEAQ (_2 ,_4) )
# 545 "ASMGram.ml"
               : ASMType.instruction))
(* Entry argument *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry instruction *)
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
let argument (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : ASMType.arg)
let instruction (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : ASMType.instruction)
;;
# 80 "ASMGram.mly"
  
# 576 "ASMGram.ml"
