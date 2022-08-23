

(*%token UNKNOWN*)
%token EOF "eof"
%token TRUE "True" FALSE "False"
%token TRUTH "true" FALSENESS "false"
%token PAR "//" NOT "~" EXCLAM "!"
%token KLEENE "^*" ENTAIL "|-" IMPLY "->"
%token DOT "." COMMA "," COLON ":" COLON2 "::"
%token PLUS "+" MINUS "-" AND "&&" OR "||"
%token EQ "=" LT "<" LE "<=" GT ">" GE ">="
%token LPAREN "(" RPAREN ")"
%token LBRACE "{" RBRACE "}"
%token BOTTOM "_|_" EMPTY "empty"
%token QUESTION "?" SHARP "#"
%token <string> IDENT "ident"
%token <int> INT "int"
%token <string> STRING


%start specification only_entailment
%start only_effects only_instants
%start simple_entailment
%type <Ast.specification> specification
%type <Ast.entailment> only_entailment
%type <Ast.effects> only_effects
%type <Ast.instants> only_instants
%type <Ast.simple_entailment> simple_entailment

%right "//"
%nonassoc "#"
%right "->"
%left "||"
%left "&&"
%left "+" "-"
%right "."
%nonassoc "^*"

%%

specification:
    e=entailment ":" a=assertion "eof"  { Ast.Spec (e, a) }
  | e=entailment "::" a=assertion "eof" { Ast.Spec (e, a) }

only_entailment:
    e=entailment "eof"  { e }

only_effects:
    l=effects "eof"     { l }

only_instants:
    es=instants "eof"   { es }

simple_entailment:
    lhs=simple_effects "|-" rhs=simple_effects "eof"  { Ast.SimpleEntail {lhs; rhs} }

assertion:
    "true"              { true }
  | "false"             { false }

entailment:
    lhs=effects "|-" rhs=effects      { Ast.Entail {lhs; rhs} }

effects:
    e=simple_effects                  { [e] }
  | e=simple_effects "||" l=effects   { e :: l }

simple_effects:
    p=pi "&&" es=instants             { (p, es) }
  | p=pi ":"  es=instants             { (p, es) }

pi:
    "True"                            { Ast.True }
  | "False"                           { Ast.False }
  | pi=atomic                         { pi }
  | "~" "(" pi=paren_pi ")"           { Ast.Not pi }
  | "(" pi=paren_pi ")"               { pi }

paren_pi:
  | pi=pi                             { pi }
  | pi1=paren_pi "&&" pi2=paren_pi    { Ast_helper.(pi1 &&* pi2) }
  | pi1=paren_pi "||" pi2=paren_pi    { Ast_helper.(pi1 ||* pi2) }
  | pi1=paren_pi "->" pi2=paren_pi    { Ast_helper.(pi1 =>* pi2) }

atomic:
    t1=term "=" t2=term               { Ast_helper.(t1 =* t2) }
  | t1=term "<" t2=term               { Ast_helper.(t1 <* t2) }
  | t1=term "<=" t2=term              { Ast_helper.(t1 <=* t2) }
  | t1=term ">" t2=term               { Ast_helper.(t1 >* t2) }
  | t1=term ">=" t2=term              { Ast_helper.(t1 >=* t2) }

term:
    i="int"                           { Ast.Const i }
  | v="ident"                         { Ast.Var v }
  | t1=term "+" t2=term               { Ast_helper.(t1 +* t2) }
  | t1=term "-" t2=term               { Ast_helper.(t1 -* t2) }

instants:
    "_|_"                             { Ast.Bottom }
  | "empty"                           { Ast.Empty }
  | i=instant                         { Ast.Instant i }
  | e=waiting                         { Ast.Await e }
  | es1=instants "+" es2=instants     { Ast.Union (es1, es2) }
  | es1=instants "."  es2=instants    { Ast.Sequence (es1, es2) }
  | es1=instants "//" es2=instants    { Ast.Parallel (es1, es2) }
  | es=instants "^*"                  { Ast.Kleene (es) }
  | es=instants "#" t=term            { Ast.Timed (es, t) }
  | "(" es=instants ")"               { es }

instant:
    "{" "}"                           { Signals.empty }
  | "{" l=event_list "}"              { Signals.make l  }

event_list:
  | e=event                     { [ Signals.present e ] }
  | "!" e=event                   { [ Signals.absent e ] }
  | e=event "," l=event_list        { Signals.present e :: l }
  | "!" e=event "," l=event_list    { Signals.absent e :: l }

literal: 
| n = "int" {Signals.constructINT n}
| str = STRING {Signals.constructSTRING str}

value:
| "(" ")" {Signals.constructUnit}
| "(" ex = value ")" {ex}
| l = literal {Signals.constructLiteral l }
| str = "ident"  {Signals.constructVariable str}


maybeValue:
| {None}
|  ex = value {Some ex}


maybeArgument:
| {None} 
| "(" obj = maybeValue ")" {obj}


event: 
| ex = "ident"  ar = maybeArgument { Signals.makeSignal   ex ar }
| "(" ev =event ")" {ev}



waiting:
    e= event "?"                     { Signals.present e }

%%
