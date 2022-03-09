module Set : sig
  include module type of List

  type elem = Signals.t * Ast.term option

  type t = elem list

  val empty : t

  val is_empty : t -> bool

  val from : Signals.t -> Ast.term option -> t

  val union : t -> t -> t

  val zip : Proofctx.t -> t -> t -> t
end

val nullable : Ast.instants -> bool

val first : Proofctx.t -> Ast.instants -> Set.t

val partial_deriv : Proofctx.t -> Set.elem -> Ast.instants -> Ast.instants
