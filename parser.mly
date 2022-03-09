%{ open Ast %}
%{ open List %}

%token <string> STRING
%token <string> VAR 
%token <int> INTE
%token  LPAR RPAR SIMI  COMMA LBRACK RBRACK      
%token  MINUS PLUS   
%token EOF GT LT EQ  GTEQ LTEQ   CONCAT 
%token VARKEY KLEENE NEW HIPHOP MODULE IN OUT 
%token EMIT AWAIT DO EVERY FORK PAR LOOP YIELD ABORT SIGNAL
%token IF HALT CONST LET HOP FUNCTION ASYNC IMPLY 
%token RETURN RAISE COLON ELSE TRY CATCH RUN
%token REQUIRE ENSURE  LSPEC RSPEC



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
| {Unit}
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



expression:
| LPAR ex = expression RPAR {ex}
| LBRACK ex = expression_shell RBRACK {ex}
| NEW ex = expression {NewExpr ex}
| b = binary_continuation {b}
| EMIT  ex = VAR LPAR obj = maybeExpr RPAR {Emit (ex,obj) }
| AWAIT ex = expression {Await ex}
| DO LBRACK ex1 = expression_shell RBRACK EVERY ex2 = expression {DoEvery (ex1, ex2)}
| FORK LBRACK ex1 = expression_shell RBRACK PAR LBRACK ex2 = expression_shell RBRACK obj = maybePar {ForkPar (ex1::ex2::obj)}
| LOOP LBRACK ex1 = expression_shell RBRACK {Loop ex1}
| HOP LBRACK ex1 = expression_shell RBRACK {Hop ex1}
| ABORT ex = expression LBRACK ex1 = expression_shell RBRACK {Abort (ex, ex1)}
| YIELD {Yield}
| SIGNAL ex = VAR SIMI ex1 = expression_shell {Signal (ex, ex1)}
| IF LPAR ex = expression RPAR LBRACK ex1 = expression_shell RBRACK obj = maybeElse {Present (ex, ex1, obj)}
| HALT {Halt}
| ASYNC str = VAR LBRACK ex1 = expression_shell RBRACK SIMI   ex2 = expression_shell {Async (str, ex1, ex2)}
| RETURN ex =  expression {Return ex}
| RAISE ex =  INTE {Raise ex}
| RUN ex = expression {Run ex}
| FUNCTION LPAR parm = parameter RPAR LBRACK  ex = expression_shell RBRACK simiOrnot{FunctionExpr (parm, ex)}
| TRY LBRACK  ex1 = expression_shell RBRACK CATCH LBRACK  ex2 = expression_shell RBRACK {Trap(ex1, ex2)}

maybeElse:
|  ELSE LBRACK ex = expression_shell RBRACK { ex}

maybeExpr:
| {None}
|  ex = expression {Some ex}

maybePar:
| {[]}
| PAR LBRACK ex2 = expression_shell RBRACK {[ex2]}



expr_aux:
| {Unit}
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
  | None -> ex1 
  | Some (Left (str, ex2)) -> 
    if String.compare str "=>" == 0 then Lambda (ex1, ex2)
    else if String.compare str ":" == 0 then Trap (ex1, ex2)
    else BinOp (str, ex1, ex2)
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

statement:
| s = STRING simiOrnot{ImportStatement s}
| VARKEY str = VAR EQ ex = expression SIMI {VarDeclear (str, ex) }
| HIPHOP MODULE  mn = VAR LPAR parm = parameter RPAR 
LSPEC REQUIRE pre = STRING RSPEC LSPEC ENSURE post = STRING RSPEC
LBRACK   ex = expression_shell RBRACK {ModduleDeclear (mn, parm, ex, Sleek.parse_effects pre, Sleek.parse_effects post)}
| CONST str = VAR EQ ex = expression SIMI {ConsDeclear (str, ex) }
| LET  ex = VAR EQ ex2 = expression  SIMI{Let (Variable ex,ex2)}
| FUNCTION mn = VAR LPAR parm = parameter RPAR LBRACK  ex = expression_shell RBRACK simiOrnot{FunctionDeclear (mn, parm, ex)}
| s = separated_list (CONCAT, VAR) obj = callOrAssign {
  match obj with 
  | Left exl -> Call (s, exl)
  | Right ex -> Assign (s, ex)
}
| TRY LBRACK  ex1 = expression_shell RBRACK CATCH LPAR e = expression RPAR LBRACK  ex2 = expression_shell RBRACK simiOrnot{TryCatch(ex1, e, ex2)}

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


