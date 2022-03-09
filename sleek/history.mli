type entry

val show_entry : entry -> verbose:bool -> string

val make_entry : unit -> entry

val set_first : Inference.Set.elem -> entry -> unit

val add_iteration : string * Ast.simple_entailment -> entry -> unit

val add_unfolding : entry -> entry -> unit

val set_terms : Ast.term list -> entry -> unit

val set_constraints : Ast.pi -> entry -> unit

val set_verdict : bool -> entry -> unit

type t

val from_entries : entry list list -> t

val show : t -> verbose:bool -> string
