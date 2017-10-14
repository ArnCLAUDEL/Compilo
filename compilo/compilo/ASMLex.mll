{

open ASMType
open ASMGram

}

let digit  = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z' '_' '0'-'9']
let hex    = ['a'-'f' 'A'-'F' '0'-'9']
let expo   = ['E' 'e'] ['+' '-']? digit+
let fs     = ['f' 'F' 'l' 'L']
let is     = ['u' 'U' 'l' 'L']*

rule asmtoken = parse
  | [' ' '\t' '\012' '\013' '\n' '\014']+ { asmtoken lexbuf }
  | ":" { COLON }
  | "," { COMMA }
  | "-" { MINUS }
  | "(" { LPAR }
  | ")" { RPAR }
  | "$" { DOLLAR }
  | ['-']? digit+  as lxm { INTEGER(int_of_string lxm)}
  | "%rax" { REGISTER RAX } | "%rbx" { REGISTER  RBX }
  | "%rcx" { REGISTER RCX } | "%rdx" {REGISTER  RDX }
  | "%rbp" { REGISTER RBP } | "%rsp" { REGISTER RSP }
  | "%rsi" { REGISTER RSI } | "%rdi" { REGISTER RDI }
  | "%r8" { REGISTER R8 } | "%r9" { REGISTER R9 }
  | "%r10" { REGISTER R10 } | "%r11" { REGISTER R11 }
  | "%r12" { REGISTER R12 } | "%r13" { REGISTER R13 }
  | "%r14" { REGISTER R14 } | "%r15" { REGISTER R15 }
  | "%al" { REGISTER AL }
  | "%rip" { REGISTER RIP }
      
  | "movq" { MOVOP}
  | "pushq" { PUSHOP}
  | "popq" { POPOP}
  | "callq" { CALLOP}
  | "retq" { RETOP}

  | "addq" { ADDOP}
  | "subq" { SUBOP}
  | "imulq" { MULOP}
  | "idivq" { DIVOP}
  | "xorq" { XOROP}
  | "orq" { OROP}
  | "andq" { ANDOP}
  | "negq" { NEGOP}
  | "notq" { NOTOP}

  | "cmpq" { CMPOP}
  | "testq" { TESTOP}

  | "sete" { SETEOP}
  | "setne" { SETNEOP}
  | "setns" { SETNSOP}
  | "setg" { SETGOP}

  | "jmp" { JMPOP}
  | "jz" { JZOP}	
  | "jnz" { JNZOP}

  | "leaq" {LEAOP}

  | "%s" { LPH }  
  | "%i" { INTPH }
  | "%a" { ADDRPH }
  (* | "%r" { REGISTER HollReg }*)

  | letter* as lxm { LABEL lxm  }
  | _ { failwith ("bad character in '" ^ (lexbuf.Lexing.lex_buffer) ^ "'") }
