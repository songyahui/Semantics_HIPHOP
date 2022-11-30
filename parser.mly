%{ open Ast %}
%{ open List %}

%token <string> STRING
%token <string> VAR 
%token <int> INTE
%token  LPAR RPAR SIMI  COMMA LBRACK RBRACK      
%token  MINUS PLUS   
%token EOF GT LT EQ  GTEQ LTEQ   CONCAT 
%token VARKEY KLEENE NEW HIPHOP MODULE IN OUT 
%token EMIT AWAIT DO EVERY FORK PAR LOOP YIELD ABORT SIGNAL SUSPENT
%token HALT CONST LET HOP FUNCTION ASYNC IMPLY 
%token RETURN EXIT COLON ELSE TRAP RUN
%token REQUIRE ENSURE  LSPEC RSPEC PRESENT COUNT



%start program entialments 
%type <(Ast.statement) list> program
%type <(string) list> entialments


%%
entialments:
| EOF {[]}
| a = STRING SIMI r = entialments { ( a) ::r }

program:
| EOF {[]}
| a = statement r = program { append [a] r }


access_aux:
| {[]}
| CONCAT f = VAR obj = access_aux  {f::obj}

literal: 
| n = INTE {INT n}
| str = STRING {STRING str}





expression_shell:
| {Value Unit}
| ex1 = expression_continuation obj = maybeSeq {
  match obj with 
  | None -> ex1 
  | Some n -> Seq(ex1, n)
  }

maybeSeq:
| {None}
| SIMI n = expression_shell {Some n}

expression_continuation:
| ex1 = expression v = maybeContinue {
  match v with 
  | None -> ex1 
  | Some obj -> Continue (ex1, obj)
  }

maybeContinue:
| {None}
| CONCAT obj = expression_continuation {Some obj}

maybeArgument:
| {None} 
| LPAR obj = maybeValue RPAR {obj}

event: 
| ex = VAR ar = maybeArgument { (ex, ar)}
| LPAR ev =event RPAR {ev}


auxEvent:
| COUNT LPAR i=INTE COMMA ev=event RPAR {(i, ev)}

events:
| ev = event {Ev ev}
| ev = auxEvent  {Count ev}

expression:
| {Value Unit}
| LPAR ex = expression RPAR {ex}
| LBRACK ex = expression_shell RBRACK {ex}
| NEW ex = expression {NewExpr ex}
| b = binary_continuation {b}
| EMIT  ev=event {Emit ev }
| AWAIT ev=events {Await ev}
| DO LBRACK ex1 = expression_shell RBRACK EVERY ex2 = event {DoEvery (ex1, ex2)}
| FORK LBRACK ex1 = expression_shell RBRACK PAR LBRACK ex2 = expression_shell RBRACK obj = maybePar {ForkPar (ex1::ex2::obj)}
| LOOP LBRACK ex1 = expression_shell RBRACK {Loop ex1}
| HOP LBRACK ex1 = expression_shell RBRACK {Hop ex1}
| ABORT ev = event LBRACK ex1 = expression_shell RBRACK {Abort (ev, ex1)}
| SUSPENT ev = event LBRACK ex1 = expression_shell RBRACK {Suspend (ev, ex1)}
| YIELD {Yield}
| SIGNAL ex = VAR SIMI ex1 = expression_shell {Signal (ex, ex1)}
| PRESENT ex = event LBRACK ex1 = expression_shell RBRACK obj = maybeElse {Present (ex, ex1, obj)}
| HALT {Halt}
| ASYNC ev=event LBRACK ex1 = expression_shell RBRACK SIMI  ex2 = expression_shell {Async (ev, ex1, ex2)}
| RETURN ex =  expression {Return ex}
| EXIT ex = INTE {Exit ex}
| RUN ex = expression {Run ex}
| FUNCTION LPAR parm = parameter RPAR LBRACK  ex = expression_shell RBRACK simiOrnot{FunctionExpr (parm, ex)}
| TRAP LBRACK  ex = expression_shell RBRACK {Trap ex}

maybeElse:
| {Value Unit}
|  ELSE LBRACK ex = expression_shell RBRACK { ex}

maybeValue:
| {None}
|  ex = expr_aux {Some ex}

maybePar:
| {[]}
| PAR LBRACK ex2 = expression_shell RBRACK {[ex2]}



expr_aux:
| LPAR RPAR {Unit}
| LPAR ex = expr_aux RPAR {ex}
| l = literal {Literal l }
| str = VAR ex = varOraccess 
  {
    match ex with 
    | None -> Variable str
    | Some obj -> Access  (str:: obj)
  }


varOraccess:
| {None}
| CONCAT f = VAR  obj =  access_aux {Some (f::obj)}

call_aux:
| {[]}
| ex = expression obj = call_aux1 {ex::obj}

call_aux1:
| {[]}
| COMMA obj = call_aux {obj}

binary_continuation:
| ex1 = binary v = binaryContinue {
  match v with 
  | None -> ex1 
  | Some obj -> Continue (ex1, obj)
  }

binaryContinue:
| {None}
| CONCAT obj = binary_continuation {Some obj}


binary :
| ex1 = expr_aux v = maybebinary_aux {
  match v with 
  | None -> Value ex1 
  | Some (Left (str, ex2)) -> 
    if String.compare str "=>" == 0 then Lambda (Value ex1, ex2)
    else BinOp (str, Value ex1, ex2)
  | Some (Right (obj)) -> FunctionCall (ex1, obj)
}

maybebinary_aux:
| {None}
| obj = binary_aux {
  Some obj
}

binary_aux:
| LPAR obj  = call_aux RPAR {Right (obj)}
| PLUS e2 = expression   {Left ( "+", e2)}
| MINUS e2 = expression   { Left( "-", e2)}
| EQ e2 = expression   {Left ( "=", e2)}
| KLEENE e2 = expression   {Left ( "*", e2)}
| LT e2 = expression   {Left ( "<", e2)}
| GT e2 = expression   {Left ( ">", e2)}
| LTEQ e2 = expression   {Left ( "<=", e2)}
| GTEQ e2 = expression   {Left ( ">=", e2)}
| IMPLY e2 = expression   {Left ( "=>", e2)}
| COLON LBRACK e2 = expression_shell RBRACK {Left(":", e2)}


simiOrnot:
| {()}
| SIMI {()}

maybemorePosts:
| {[]}
| LSPEC ENSURE post = STRING RSPEC rest = maybemorePosts {post :: rest}

statement:
| s = STRING simiOrnot{ImportStatement s}
| VARKEY str = VAR EQ ex = expression SIMI {VarDeclear (str, ex) }
| MODULE  mn = VAR LPAR parm = parameter RPAR 
LSPEC REQUIRE pre = STRING RSPEC posts = maybemorePosts
LBRACK   ex = expression_shell RBRACK {ModduleDeclear (mn, parm, ex, Sleek.parse_effects pre, List.map (fun a -> Sleek.parse_effects a) posts)}
| CONST str = VAR EQ ex = expression SIMI {ConsDeclear (str, ex) }
| LET  ex = VAR EQ ex2 = expression  SIMI{Let (Value (Variable ex),ex2)}
| FUNCTION mn = VAR LPAR parm = parameter RPAR LBRACK  ex = expression_shell RBRACK simiOrnot{FunctionDeclear (mn, parm, ex)}
| s = separated_list (CONCAT, VAR) obj = callOrAssign {
  match obj with 
  | Left exl -> Call (s, exl)
  | Right ex -> Assign (s, ex)
}

callOrAssign:
| LPAR obj  = call_aux RPAR SIMI {Left obj}
| EQ ex = expression SIMI{Right  ex}

param:
| IN str = VAR {IN str}
| OUT str = VAR {OUT str}
| VARKEY str = VAR {Data str}
| str = VAR {Data str}


parameter:
| {[]}
| p = param obj = maybeNext {
  match obj with 
  | None -> [p]
  | Some obj -> p::obj}

maybeNext:
| {None}
| COMMA v = parameter {Some v}


