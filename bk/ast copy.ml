(* Hiphop.js Syntax *)
(*-| Representations for modules' exports.*)




type ('a, 'b, 'c)  either = Left of 'a | Right of 'b 

type literal = 
    | INT of int
    | STRING of string
    | BOOL of bool
    
type param = 
    | IN of string
    | OUT of string 
    | Data of string

type expression = 
    | Unit
    | Variable of string
    | Literal of literal
    | Access of string list 
    | BinOp of string * expression * expression
    | FunctionCall of expression * expression list 
    | NewExpr of expression
    | Emit of string * expression option
    | Await of expression 
    | DoEvery of expression * expression
    | ForkPar of expression list 
    | Seq of expression * expression 
    | Abort of  expression * expression 
    | Loop of  expression 
    | Hop of  expression 
    | Yield
    | Halt
    | Signal of string * expression
    | Present of expression * expression * expression option
    | Async of string * expression 
    | Lambda of expression * expression
    | Continue of expression * expression 
    | Return of expression 
    | Break of expression 
    | Trap of expression * expression
    | Run of expression
    | FunctionExpr of param list * expression




type statement = 
    | ImportStatement of string
    | VarDeclear of string * expression 
    | ConsDeclear of string * expression 
    | ModduleDeclear of string * param list * expression * Sleek.effects * Sleek.effects
    | Let of expression * expression
    | FunctionDeclear of string * param list * expression
    | Call of string list * expression list 
    | Assign of string list * expression
    | TryCatch of expression * expression * expression


type parfst = SL of Sleek__Signals.t | W of (Sleek__Signals.event)
 
type prog_states = (Sleek.pi* Sleek.instants* (parfst * Sleek.term option) option) list
type prog_states_reverse =  (Sleek.pi * (parfst *  Sleek.term option) * Sleek.instants) list
