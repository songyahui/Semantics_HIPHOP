%{ open Ast %}
%{ open List %}

%token <string> STRING
%token <string> VAR 
%token <int> INTE
%token  LPAR RPAR SIMI  COMMA LBRACK RBRACK      
%token  MINUS PLUS   
%token EOF GT LT EQ  GTEQ LTEQ   CONCAT 
%token VARKEY KLEENE NEW EXPORTS HIPHOP MODULE IN OUT 
%token EMIT AWAIT DO EVERY FORK PAR LOOP YIELD ABORT SIGNAL
%token IF HALT CONST LET




%start program
%type <(Ast.statement) list> program


%%

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
| ex1 = expression obj = maybeSeq {
  match obj with 
  | None -> ex1 
  | Some n -> Seq(ex1, n)
  }

maybeSeq:
| {None}
| SIMI n = expression_shell {Some n}


expression:
| NEW ex = expression {NewExpr ex}
| b = binary {b}
| EMIT  ex = VAR LPAR obj = maybeExpr RPAR {Emit (ex,obj) }
| AWAIT LPAR ex = expression RPAR {Await ex}
| DO LBRACK ex1 = expression_shell RBRACK EVERY LPAR ex2 = expression RPAR{DoEvery (ex1, ex2)}
| FORK LBRACK ex1 = expression_shell RBRACK PAR LBRACK ex2 = expression_shell RBRACK obj = maybePar {ForkPar (ex1::ex2::obj)}
| LOOP LBRACK ex1 = expression_shell RBRACK {Loop ex1}
| ABORT LPAR ex = expression RPAR LBRACK ex1 = expression_shell RBRACK {Abort (ex, ex1)}
| YIELD {Yield}
| SIGNAL ex = VAR {Signal ex}
| IF LPAR ex = expression RPAR LBRACK ex1 = expression_shell RBRACK {Present (ex, ex1)}
| HALT {Halt}

maybeExpr:
| {None}
|  ex = expression {Some ex}

maybePar:
| {[]}
| PAR LBRACK ex2 = expression_shell RBRACK {[ex2]}

expr_aux:
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

binary :
| ex1 = expr_aux v = maybebinary_aux {
  match v with 
  | None -> ex1 
  | Some (Left (str, ex2)) -> BinOp (str, ex1, ex2)
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
|  GTEQ e2 = expression   {Left ( ">=", e2)}

statement:
| s = STRING {ImportStatement s}
| VARKEY str = VAR EQ ex = expression SIMI {VarDeclear (str, ex) }
| EXPORTS CONCAT ex = VAR EQ ex2 = expression  SIMI{ExportStatement(Variable ex,ex2)}
| HIPHOP MODULE  mn = VAR LPAR parm = parameter RPAR LBRACK  ex = expression_shell RBRACK {ModelDeclear (mn, parm, ex)}
| CONST str = VAR EQ ex = expression SIMI {ConsDeclear (str, ex) }
| LET  ex = VAR EQ ex2 = expression  SIMI{Let (Variable ex,ex2)}

param:
| IN str = VAR {IN str}
| OUT str = VAR {OUT str}


parameter:
| {[]}
| p = param obj = maybeNext {
  match obj with 
  | None -> [p]
  | Some obj -> p::obj}

maybeNext:
| {None}
| COMMA v = parameter {Some v}
