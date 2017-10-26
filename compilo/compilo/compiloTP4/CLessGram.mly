%{

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
						      
%}

%token <string> IDENTIFIER TYPE_NAME
%token <int> CONSTANT
%token <string> STRING_LITERAL
%token SIZEOF
%token PTR_OP INC_OP DEC_OP LEFT_OP RIGHT_OP LE_OP GE_OP EQ_OP NE_OP
%token AND_OP OR_OP MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN ADD_ASSIGN
%token SUB_ASSIGN LEFT_ASSIGN RIGHT_ASSIGN AND_ASSIGN
%token XOR_ASSIGN OR_ASSIGN
%token SEMI_CHR OPEN_BRACE_CHR CLOSE_BRACE_CHR COMMA_CHR COLON_CHR
%token EQ_CHR OPEN_PAREN_CHR CLOSE_PAREN_CHR OPEN_BRACKET_CHR
%token CLOSE_BRACKET_CHR DOT_CHR AND_CHR OR_CHR XOR_CHR BANG_CHR
%token TILDE_CHR ADD_CHR SUB_CHR STAR_CHR DIV_CHR MOD_CHR
%token OPEN_ANGLE_CHR CLOSE_ANGLE_CHR QUES_CHR
%token TYPEDEF EXTERN STATIC AUTO REGISTER
%token CHAR SHORT INTEGER LONG SIGNED UNSIGNED FLOATING DOUBLE CONST VOLATILE VOID
%token STRUCT UNION ENUM ELLIPSIS EOF
%token CASE DEFAULT IF ELSE SWITCH WHILE DO FOR GOTO CONTINUE BREAK RETURN
%token ASM

%type <(CLessType.declaration list)> translation_unit

%right CLOSE_PAREN_CHR ELSE

%start translation_unit
%%

primary_expression:
  identifier { Var $1 }
    | AND_CHR identifier { get_reference $2}
        | constant { Const $1 }
	| string_literal { String $1 }
        | OPEN_PAREN_CHR expression CLOSE_PAREN_CHR { $2 }
        ;

constant : CONSTANT { $1 };

string_literal:
          STRING_LITERAL { $1 }
        | STRING_LITERAL string_literal 
            { 
              ($1) ^ ($2)
            } 


identifier  : IDENTIFIER      {  $1 };
open_brace  : OPEN_BRACE_CHR  { () };
close_brace : CLOSE_BRACE_CHR { () };


postfix_expression:
  primary_expression { $1 }
  | postfix_expression OPEN_BRACKET_CHR expression CLOSE_BRACKET_CHR
	{ BOperator ($1,get_index (), $3) }
        | identifier OPEN_PAREN_CHR close_paren
	{ 
	   Call ($1, [])
	}
        | identifier OPEN_PAREN_CHR argument_expression_list close_paren
	{
		Call ($1, List.rev $3)
	}
        ;

/* Les argument_expression_list sont des listes a l'envers */

argument_expression_list:
          assignment_expression { [$1] }
        | argument_expression_list COMMA_CHR assignment_expression { 
          $3 :: $1 }
        ;

unary_expression:
          postfix_expression { $1 }
        | unary_operator cast_expression
	{ 
          let  c = $1 in
	  match c with
	      ADD_CHR -> $2
	    | SUB_CHR -> UOperator (MinusM, $2)
	    | BANG_CHR -> UOperator (Not, $2)
	    | STAR_CHR -> UOperator (get_dereference (), $2)
	    | _-> failwith "error"
	    }
        ;

unary_operator:
          add_chr   { $1 }
        | sub_chr   { $1 }
        | bang_chr  { $1 }
        | tilde_chr { $1 }
	| star_chr  { $1 }
        ;

add_chr     : ADD_CHR   { ADD_CHR   };
sub_chr     : SUB_CHR   { SUB_CHR   };
bang_chr    : BANG_CHR  { BANG_CHR  };
tilde_chr   : TILDE_CHR { TILDE_CHR };
star_chr    : STAR_CHR  { STAR_CHR  };

close_paren : CLOSE_PAREN_CHR { () };

cast_expression:
          unary_expression { $1 } ;

multiplicative_expression:
          cast_expression { $1 }
        | multiplicative_expression STAR_CHR cast_expression
	{ 
	  BOperator ($1, Mult , $3)
	}
        | multiplicative_expression DIV_CHR cast_expression
	{
		BOperator ($1, Div , $3)
	}
        | multiplicative_expression MOD_CHR cast_expression
	{
		BOperator ($1, Mod , $3)
	}
        ;

additive_expression:
          multiplicative_expression 
            { $1 }
        | additive_expression ADD_CHR multiplicative_expression
	{
	  BOperator ($1, Add , $3)
	}
        | additive_expression SUB_CHR multiplicative_expression
	{
	BOperator ($1, Sub , $3)
	}
        ;

shift_expression:
          additive_expression { $1 }
        ;

relational_expression:
          shift_expression { $1 }
        | relational_expression OPEN_ANGLE_CHR shift_expression
	{
	BOperator( $1, LL , $3)
	}
        | relational_expression CLOSE_ANGLE_CHR shift_expression
	{
		BOperator( $3, LL , $1)
	}
        | relational_expression LE_OP shift_expression
	{ 
	  	BOperator( $1, LE , $3)
	}
        | relational_expression GE_OP shift_expression
	{
		BOperator( $3, LE , $1)
	}
        ;

equality_expression:
          relational_expression { $1 }
        | equality_expression EQ_OP relational_expression
	{
		BOperator( $1, EQ , $3)
	}
        | equality_expression NE_OP relational_expression
	{
		BOperator( $1, NEQ , $3)
	}
        ;

and_expression:
          equality_expression { $1 }
        ;

exclusive_or_expression:
          and_expression { $1 }
        ;

inclusive_or_expression:
          exclusive_or_expression { $1 }
        ;

logical_and_expression:
          inclusive_or_expression { $1 }
        | logical_and_expression AND_OP inclusive_or_expression
	{
		BOperator ($1, And , $3)
	}
        ;

logical_or_expression:
          logical_and_expression { $1 }
        | logical_or_expression OR_OP logical_and_expression
	{
		BOperator ($1, Or , $3)
	}
        ;

assignment_expression:
	logical_or_expression { $1 }
	|	       
	 unary_expression EQ_CHR assignment_expression
	    {
	     let left = $1 in
	     match left with
	       Var x -> Set (x, $3)
	     | UOperator (uop,e) when (try uop = get_dereference () with _-> false)
	       -> BOperator (e,get_setReference (),$3)
	     | BOperator (Var x, bop , i) when (try bop = get_index () with _-> false)
	       -> get_setArray (x, i, $3)
	     |_ -> failwith "error"   
	   }
        ;

expression:
          assignment_expression { $1 }
        | expression COMMA_CHR assignment_expression
	{ 
	  Seq [$1; $3]
	}
        ;

declaration:
	type_specifier optional_init_declarator_list SEMI_CHR
	{ List.rev $2 }
        ;

optional_init_declarator_list : 
          { [] }
	| init_declarator_list { $1 }
	;

/* Une init_declarator_list est une liste a l'envers de declarator. */
init_declarator_list
        : init_declarator 
            { [$1] }
        | init_declarator_list COMMA_CHR init_declarator 
            { $3 :: $1 }
        ;

init_declarator: declarator { $1 };

declarator:
          identifier { let x = $1 in x }
        ;

type_specifier:
	| VOID {()}
	| INTEGER { () }
	| CHAR STAR_CHR { () }
	| type_specifier STAR_CHR { () };

statement: compound_statement   
            { $1 }
        | expression_statement 
            { Expr $1 }
        | selection_statement  
            { $1 }
        | iteration_statement  
            { $1 }
        | jump_statement       
            { $1 }
	    ;

open_block : open_brace { $1 };
close_block : close_brace { $1 };

compound_statement: 
          open_block close_block 
        { BlockStat ([], []) }
        | open_block statement_list close_block
	{ BlockStat ([], List.rev $2) }
        | open_block declaration_list close_block
	{ BlockStat ($2, []) }
        | open_block declaration_list statement_list close_block
	{ BlockStat ($2, List.rev $3) }
        ;

/* Une declaration_list est une liste non inversee de declaration */
declaration_list
        : declaration 
          { $1 }
        | declaration_list declaration 
          { $1 @ $2 }
        ;

/* Une statement_list est une liste inversee de statement */
statement_list
        : statement 
          { [$1] }
        | statement_list statement 
          { $2 :: $1 }
        ;

expression_statement: 
         semi_chr 
            { Seq [] }
        | expression SEMI_CHR 
            { $1 }
        ;

semi_chr : SEMI_CHR { () }

ifkw : IF { () };

selection_statement
        : ifkw OPEN_PAREN_CHR expression CLOSE_PAREN_CHR statement
	{ 
          IfStat ($3, $5, (BlockStat ([], [])))
	}
        | ifkw OPEN_PAREN_CHR expression CLOSE_PAREN_CHR statement ELSE statement
	{ 
          IfStat ($3, $5, $7)
	}
        ;

whilekw : WHILE { () };
forkw : FOR { () };

iteration_statement: whilekw OPEN_PAREN_CHR expression close_paren statement
	   {
	    WhileStat ($3, $5)
	   }
        | forkw OPEN_PAREN_CHR expression_statement expression_statement close_paren statement
	/* for (e0; e; ) c == e0; while (e) c; */
	{ 
	 BlockStat ([], [ Expr $3 ;
			        WhileStat ($4, $6)])
	}
        | forkw OPEN_PAREN_CHR expression_statement expression_statement expression close_paren statement
	/* for (e0; e; e1) c == e0; while (e) { c; e1 } */
	{ 
          BlockStat ([], [ Expr $3;
			    	 WhileStat ($4,
				  BlockStat ([], [$7; Expr $5]))])
	}
        ;

return : RETURN { };

jump_statement:
          return SEMI_CHR 
            { ReturnStat None }
        | return expression SEMI_CHR 
            {  ReturnStat (Some $2) }
        ;

translation_unit:
          external_declaration 
          { $1 }
        | translation_unit external_declaration 
          { $1 @ $2 }
        | EOF 
          { [] }
        ;
	
glob_var_declaration:
	type_specifier identifier SEMI_CHR  { VarDec($2,None) }
    |   type_specifier identifier EQ_CHR CONSTANT SEMI_CHR  { VarDec($2,Some $4) }

external_declaration
        : function_definition 
            { [$1] }
        | glob_var_declaration 
            { [$1] }
        ;

parameter_declaration: type_specifier identifier { $2 };

/*!!!should check no repeated param name! */
/* Une parameter_list est une liste inversee de parameter_list. */
parameter_list: parameter_declaration 
          { [$1] }
        | parameter_list COMMA_CHR parameter_declaration
          { $3 :: $1 }
        ;

parameter_type_list
        : parameter_list { List.rev $1}
        | parameter_list COMMA_CHR ELLIPSIS { List.rev $1 }
        ;

parameter_declarator :
	  OPEN_PAREN_CHR CLOSE_PAREN_CHR { [] }
	| OPEN_PAREN_CHR parameter_type_list CLOSE_PAREN_CHR { $2 }
	    ;

function_declarator : type_specifier identifier parameter_declarator
	{ $2, $3 }
	    ;

function_definition
        : function_declarator compound_statement
	{ 
          let var, decls = $1 in
	  FunDec ( var, decls, $2)
	}
	;


%%
