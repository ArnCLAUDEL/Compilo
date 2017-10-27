open CLessType
open Tools
open ASMType

let regl = ["%rdi"; "%rsi"; "%rdx"; "%rcx"; "%r8"; "%r9"]


let rec taille_expr e =
	match e with
		| Var(_)
		| Const(_)
		| String(_) -> 1
		| Set(_,e) -> 1 + (taille_expr e)
		| Call(_, []) -> 1
		| Call(s, e :: t) -> (taille_expr e) + (taille_expr (Call(s, t)))
		| UOperator(_, e) -> 1 + (taille_expr e)
		| BOperator(e1,_,e2) -> 1 + (taille_expr e1) + (taille_expr e2)
		| Seq([]) -> 0
		| Seq(e :: t) -> (taille_expr e) + taille_expr(Seq(t)) 
and taille_stat s =
	match s with
		| Expr e -> (taille_expr e)
		| BlockStat(_, []) -> 0
		| BlockStat([], s::t) -> (taille_stat s) + (taille_stat (BlockStat([], t)))
		| BlockStat(varl, sl) -> (List.length varl) + (taille_stat (BlockStat([],sl)))
		| IfStat(e,s1,s2) -> 1 + (taille_expr e) + (taille_stat s1) + (taille_stat s2)
		| WhileStat(e, s) -> 1 + (taille_expr e) + (taille_stat s)
		| ReturnStat(e) -> match e with
							| None -> 1
							| Some e -> 1 + (taille_expr e) 

let stack_args argl il = 
	let rec stack argl rl il = 
		match (argl,rl) with
			| ([],_)
			| (_,[]) -> il
			| ((a :: at),(r :: rt)) -> (stack at rt (il |% p ("pushq "^r)))
	in (stack argl regl il)

and stack_args_name argl varl sp =
	let rec stack argl varl sp index =
		match (argl,index) with
		| ([],_) -> varl
		| (v :: t,index) -> let sp2 = (match index with
								| i when i < 6 	-> sp+8
								| i when i = 6 	-> -16
								| _ 			-> sp-8) in
							((stack t varl sp2 (index+1)) |% (v, (parse_arg "%i(%rbp)" (-sp2))))

	in (stack argl varl sp 0)

let check_inlining s =
	try let (argl,st) = (getFunDec s) in
		((List.length argl) + (taille_stat st)) < 40
	with Not_found -> false


let rec generate_asm_expression varl sp e il =
  try match e with
  | Ref(v) -> il |% (pa "leaq %a, %rax" (addr_lbl_of_string v))
  | Const i -> il |% pi "movq %i, %rax" i
  | Set(s,e1) -> (generate_asm_expression varl sp e1 il) |% (pa "movq %rax, %a" (List.assoc s varl))
  | Var s -> il |% (pa "movq %a, %rax"  (List.assoc s varl))
  | String s -> il |% (pa "leaq %a, %rax" (addr_lbl_of_string s))
  | Seq([]) -> il
  | Seq(e :: t) -> (generate_asm_expression varl sp (Seq t) 
  						(generate_asm_expression varl sp e il))
  
  | Call(s, []) -> 	if(check_inlining s) 
					then (	let (argl, st) = (getFunDec s) in
							let f_lbl = (fresh_lbl s) in
							(generate_asm_statement 
								(stack_args_name argl varl (sp))
								(8*(List.length argl))
								f_lbl st
								(stack_args argl il)) 
							|% p (f_lbl^":"))
					else (	let call_i = ("callq "^s) in
		  					if(sp mod 16 == 0)
		  					then il |% p call_i
		  					else il |% p "subq $8, %rsp"
		  							|% p call_i
		  							|% p "addq $8, %rsp")
  | Call(s, argl) -> 
  					let rec gen_args argl rl il = 
						match (argl,rl) with
							| ([],_)
							| (_,[]) -> il
							| ((a :: at),(r :: rt)) -> (gen_args at rt 
															((generate_asm_expression varl sp a il)
																|% p ("pushq %rax"))) 	
														|% p ("movq (%rsp),"^r)
														|% p("addq $8, %rsp")
					in
						(generate_asm_expression varl sp (Call(s, [])) (gen_args argl regl il))

  | UOperator(op, e) ->
  					let il2 = (generate_asm_expression varl sp e il) in
  					(match op with
  						| Deref -> il2 |% p "movq (%rax), %rax"
  						| MinusM -> il2 |% p "negq %rax"
  						| Not -> (let z = (fresh_lbl "z") in
  									let ez = (fresh_lbl "ez") in
  										(il2 |% p "testq %rax, %rax"
  											|% p ("jz "^z)
  											|% p ("movq $0, %rax")
  											|% p ("jmp "^ez)
  											|% p (z^":")
  											|% p ("movq $1, %rax")
  											|% p (ez^":"))))
  | BOperator(e1, op, e2) -> 
			      let il2 = (generate_asm_expression varl sp e1
							  ((generate_asm_expression varl sp e2 il) |% p "pushq %rax")) in  
			      let expr = " (%rsp), %rax" in
			    (match op with
			        | Add -> il2 	|% p ("addq"^expr)
			        | Sub -> il2 	|% p ("subq"^expr)
			        | Mult -> il2 	|% p ("imulq"^expr)
					| Mod -> il2 	|% p "movq $0, %rdx" |% p ("idivq"^expr) |% p "movq %rdx, %rax"
					| Div -> il2 	|% p "movq $0, %rdx" |% p ("idivq"^expr)
					| And -> il2 	|% p ("andq"^expr)
					| Or -> il2  	|% p ("orq"^expr)
					| SetReference -> il2 	|% p ("movq %rax, %rbx") |% p ("popq %rax") |% p ("movq %rax, (%rbx)")
					| _ -> il2 	|% p ("cmpq %rax, (%rsp)") |% p ("movq $0, %rax")
								|% p (match op with
										| EQ -> "sete %al"
										| NEQ -> "setne %al"
										| LE -> "setns %al"
										| LL -> "setg %al"
										| _ -> "")
				)
			   	|% p "addq $8, %rsp"
  with Match_failure(_) -> raise (Code_gen_failure_expression e)
              
and generate_asm_statement varl sp retlbl s il =
  try match s with
  | BlockStat(_, []) -> il
  | BlockStat([], s :: t) -> (generate_asm_statement varl sp retlbl (BlockStat([],t))
								(generate_asm_statement varl sp retlbl s il))
  
  | BlockStat(v :: t,sl) -> (let sp2 = sp+8 in
	  							(generate_asm_statement 
							      ((v, (parse_arg "-%i(%rbp)" (sp2)))::varl)
							      sp2 retlbl (BlockStat(t,sl))
							      (il |% p "subq $8, %rsp")
							    ) 
							    |% p "addq $8, %rsp")

  | WhileStat(e,s) -> let lbl_begin_while = fresh_lbl "begin_while" in
  						let lbl_end_while = fresh_lbl "end_while" in
	  					(generate_asm_statement varl sp retlbl s 
		  						((generate_asm_expression varl sp e (il |% p (lbl_begin_while^":")))
		  								|% p "testq %rax, %rax"
		  								|% p ("jz "^lbl_end_while))
		  				)
	  					|% p ("jmp "^lbl_begin_while)
	  					|% p (lbl_end_while^":")

  | Expr(e) -> generate_asm_expression varl sp e il
  
  | IfStat (e, s1, s2) -> let lbl_else_if = fresh_lbl "else_if" in
				 let lbl_end_if = fresh_lbl "end_if" in
				 	(generate_asm_statement varl sp retlbl s2
				      	((generate_asm_statement varl sp retlbl s1
						    ((generate_asm_expression varl sp e il)
								|% p "testq %rax, %rax"
								|% p ("jz "^lbl_else_if)
						    )
						  	|% p ("jmp "^lbl_end_if)
						  	|% p (lbl_else_if^":"))
				    	)
				    	|% p (lbl_end_if^":"))
  
  | ReturnStat Some(e) -> 
      (generate_asm_statement varl sp retlbl (ReturnStat None) 
        (generate_asm_expression varl sp e il))

  | ReturnStat None ->
     match retlbl with
     	| "" -> il 	|% pi "addq %i, %rsp" sp
				 	|% p  "popq %rbp"
				 	|% p  "retq"
     	| _ -> 	il 	|% pi "addq %i, %rsp" sp
     				|% p ("jmp "^retlbl)
  with Match_failure(_) -> raise (Code_gen_failure_statment s)


let generate_asm_top varl il = function
  | VarDec(_) -> il
  | FunDec(label,argl,statement) -> let il2 =  (il 	|% p (label^":")
                                                  	|% p "pushq %rbp"
                                                  	|% p "movq %rsp, %rbp") in
										(match argl with
											| [] -> (generate_asm_statement varl 0 "" statement il2)
											| argl -> (generate_asm_statement 
														(stack_args_name argl varl 0)
														((8*(List.length argl)))
														"" statement 
														(stack_args argl il2)))
  
