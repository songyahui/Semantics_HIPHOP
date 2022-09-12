(* Type of events *)

type literal
type value
type _signal
type event

val show_event : event -> string

val compare_event : event -> event -> bool

val present : _signal -> event

val absent : _signal -> event

val is_present : event -> bool


val constructINT: int -> literal
val constructSTRING: string -> literal
val constructBOOL: bool -> literal
val makeSignal : string -> value option -> _signal


val constructUnit : value 
val constructVariable : string -> value 
val constructLiteral : literal -> value 
val constructAccess : string list -> value 


(* Type of signals *)
type t = event list 

val isEventExist : event -> t -> bool

val show : t -> string

val normalize_ins : t-> t


val empty : t

val is_empty : t -> bool

val from : _signal -> t

val initUndef : _signal list -> t

val setAbsent: _signal -> t -> t option 

val setPresent: _signal -> t -> t option 

val controdicts: t -> bool 

val controdicts_final: t -> bool 

val fstHelper : event -> t

val add_UndefSigs: _signal list -> t -> t 

val make : event list -> t

val merge : t -> t -> t

val ( |- ) : t -> t -> bool
