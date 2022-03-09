val verify_simple_entailment : Ast.simple_entailment -> bool * History.entry

val verify_entailment : Ast.entailment -> bool * History.t

val verify_specification : Ast.specification -> bool * string * History.t

val show_verification :
  case:Ast.specification -> no:int -> verdict:string -> verbose:bool -> history:History.t -> string
