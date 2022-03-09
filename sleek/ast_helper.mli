open Ast

val ( +* ) : term -> term -> term

val ( -* ) : term -> term -> term

val ( =* ) : term -> term -> pi

val ( >* ) : term -> term -> pi

val ( >=* ) : term -> term -> pi

val ( <* ) : term -> term -> pi

val ( <=* ) : term -> term -> pi

val ( &&* ) : pi -> pi -> pi

val ( ||* ) : pi -> pi -> pi

val ( =>* ) : pi -> pi -> pi

val ( !* ) : pi -> pi

type term_gen = int ref

val next_term : term_gen -> term

val total_terms_of_es : instants -> term_gen -> term * pi

val visit_pi : (term -> term -> unit) -> pi -> unit

val filter_pi : (term -> term -> bool) -> pi -> pi option

val trim_pi : pi -> term list -> pi

val normalize_pi : pi -> pi

val normalize_es : instants -> instants

val normalize : simple_effects -> simple_effects
