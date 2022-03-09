type term =
  | Const of int
  | Var   of string
  | Gen   of int
  | Plus  of term * term
  | Minus of term * term

val show_term : term -> string

type atomic_op =
  | Eq
  | Lt
  | Le
  | Gt
  | Ge

type pi =
  | True
  | False
  | Atomic of atomic_op * term * term
  | And    of pi * pi
  | Or     of pi * pi
  | Imply  of pi * pi
  | Not    of pi

val show_pi : pi -> string

type instants =
  | Bottom
  | Empty
  | Instant  of Signals.t
  | Await    of Signals.event
  | Sequence of instants * instants
  | Union    of instants * instants
  | Parallel of instants * instants
  | Kleene   of instants
  | Timed    of instants * term

val show_instants : instants -> string

type simple_effects = pi * instants

val show_simple_effects : simple_effects -> string

type effects = simple_effects list

val show_effects : effects -> string

type simple_entailment =
  | SimpleEntail of {
      lhs : simple_effects;
      rhs : simple_effects;
    }

val show_simple_entailment : simple_entailment -> string

type entailment =
  | Entail of {
      lhs : effects;
      rhs : effects;
    }

val show_entailment : entailment -> string

type specification = Spec of entailment * bool

val show_specification : specification -> string
