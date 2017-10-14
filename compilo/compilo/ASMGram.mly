%{
  
open ASMType

let mon a f = let v1,v2 = a in (f v1),v2
let mon2 (a1,h1) (a2,h2) f = (f a1 a2),(h1@h2)
  

%}

%token <string> LABEL
%token LPAR RPAR COLON COMMA DOLLAR
%token INTPH ADDRPH RPH LPH
%token <ASMType.reg> REGISTER
%token <int> INTEGER
%token MOVOP PUSHOP POPOP CALLOP RETOP
%token ADDOP MULOP SUBOP DIVOP XOROP OROP ANDOP NEGOP NOTOP
%token CMPOP TESTOP
%token MINUS
%token SETEOP SETNEOP SETNSOP SETGOP
%token JMPOP JZOP JNZOP
%token LEAOP

%type <ASMType.arg> argument
%type <ASMType.instruction> instruction

%start argument instruction
%%
  
argument:  
   | REGISTER { R $1 }
   | DOLLAR INTEGER { C(IL $2) }
   | INTPH { C(HollInt) }
   | ADDRPH { HollArg }
   | LPAR REGISTER RPAR { ARI(IL 0,$2) }
   | INTEGER LPAR REGISTER RPAR { ARI(IL $1,$3) }
   | INTPH LPAR REGISTER RPAR { ARI(HollInt,$3) }
   | MINUS INTEGER LPAR REGISTER RPAR { ARI(IL(-$2),$4) }
   | MINUS INTPH LPAR REGISTER RPAR { ARI(HollIntM,$4) }
   | LABEL { L $1 }
   | LPH { HollLabel }


instruction:
   | LABEL COLON { Label (L $1) }
   | LPH COLON { Label HollLabel }	
   
   | MOVOP argument COMMA argument { MOV($2,$4) }
   | PUSHOP argument { PUSH($2) }
   | POPOP argument { POP($2) }
   | RETOP argument { RET }
   | CALLOP argument { CALL($2) }
    
   | ADDOP argument COMMA argument { ADD($2,$4) }
   | SUBOP argument COMMA argument { SUB($2,$4) }
   | MULOP argument COMMA argument  { MUL($2,$4) }
   | DIVOP argument COMMA argument  { DIV($2,$4) }
   | XOROP argument COMMA argument  { XOR($2,$4) }
   | OROP argument COMMA argument  { OR($2,$4) }
   | ANDOP argument COMMA argument  { AND($2,$4) }
   | NEGOP argument  { NEG ($2) }
   | NOTOP argument  { NOT ($2) }

   | CMPOP argument COMMA argument  { CMP ($2,$4) } 
   | TESTOP argument COMMA argument  { TEST ($2,$4) }  

   | SETEOP argument  { SETE $2 }
   | SETNEOP argument { SETNE $2 }
   | SETNSOP argument { SETNS $2 }
   | SETGOP argument  { SETG $2 }

   | JMPOP argument  { JMP $2 }
   | JZOP argument   { JZ $2 }
   | JNZOP argument  { JNZ $2 }

   | LEAOP argument COMMA argument
           { LEAQ ($2 ,$4) }	

%%
  
