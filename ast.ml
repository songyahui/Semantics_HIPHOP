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

type value = 
    | Variable of string
    | Literal of literal
    | Access of string list 

type event = string * value option

type expression = 
    | Unit
    | Value of value
    | BinOp of string * expression * expression
    | FunctionCall of value * expression list  
    | NewExpr of expression
    | DoEvery of expression * expression
    | ForkPar of expression list 
    | Seq of expression * expression 
    | Loop of  expression 
    | Hop of  expression 
    | Yield
    | Halt
    | Signal of string * expression
    | Present of event * expression * expression
    | Lambda of expression * expression
    | Continue of expression * expression 
    | Return of expression 
    | Run of expression
    | FunctionExpr of param list * expression
(* Preemptive and promise-related constructs *)
    | Emit of event
    | Async of event * expression * expression
    | Await of event 
    | Abort of event * expression  
    | Interrupt of  expression * expression 
    | Suspend of event * expression 
    | Every of  event * expression 
    | Exit of int 
    | Trap of expression 






type statement = 
    | ImportStatement of string
    | VarDeclear of string * expression 
    | ConsDeclear of string * expression 
    | ModduleDeclear of string * param list * expression * Sleek.effects * (Sleek.effects list)
    | Let of expression * expression
    | FunctionDeclear of string * param list * expression
    | Call of string list * expression list 
    | Assign of string list * expression



type prog_states = (Sleek.instants* (Sleek.Signals.t) option * int) list
