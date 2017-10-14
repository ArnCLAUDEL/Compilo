(** Interprète un programme assembleur *)

(** État de la machine virtuelle *)
type state

(** Jump ou Call vers une adresse incorrecte *)   
exception Invalid_jmp

(** Adresse de pile invalide *)
exception Invalid_stack_addr

(** Adresse de tas invalide *)  
exception Invalid_heap_addr

(** Édition des liens incomplète *)
exception NotLinked

(** Écris du code assembleur en différenciant les adresses *)
val unbox_arg : ASMType.arg -> ASMType.arg

(** Fonction malloc *)  
val allocator : string -> ASMType.instruction list

(** [link fun prog] édite les liens du programme [prog] et renvoi un tableau d'instruction ainsi
que l'index du début de la fonction [fun] dans ce tableau *)
val link : string -> ASMType.asm_program -> ASMType.instruction array * int

(** Créé une nouvelle machine virtuelle *)
val new_state : ASMType.instruction array * int -> int -> state
  
(** 
[ run_machine l state] exécute la machine virtuelle [state] avec le niveau de débogage [l] et renvoie le contenue de RAX à la fin de l'exécution *)
val run_machine : int -> state -> int
