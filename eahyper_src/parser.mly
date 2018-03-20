%token TRUE
%token FALSE
%token <string> ID
%token NOT
%token AND
%token OR
%token IMPL
%token EQUIV
%token NEXT
%token UNTIL
%token WEAKUNTIL
%token RELEASE
%token EVENTUALLY
%token GLOBALLY
%token OP
%token CL
%token FORALL
%token EXISTS
%token UNDER
%token DOT
%token EOF

%right UNTIL RELEASE WEAKUNTIL
%left IMPL EQUIV
%left AND OR
%nonassoc EVENTUALLY GLOBALLY
%nonassoc NOT NEXT

%{
    open Formula
%}

%start parse_hyperltl_formula
%type <Formula.hyperltl_formula> parse_hyperltl_formula
%type <Formula.formula> formula_expr
%type <string> ap_id

%%

%public ap_id:
    s=ID                     { s }
    | s1=ap_id UNDER s2=ID   { s1 ^ "_" ^ s2 }

%public formula_expr:
    | TRUE                                      { True }
    | FALSE                                     { False }
    | s1=ap_id UNDER s2=ID                      { Var (s1,s2) }
    | NOT f=formula_expr                        { Not (f) }
    | f=formula_expr AND g=formula_expr         { And (f,g) }
    | f=formula_expr OR g=formula_expr          { Or (f,g) }
    | f=formula_expr IMPL g=formula_expr        { Impl (f,g) }
    | f=formula_expr EQUIV g=formula_expr       { Equiv (f,g) }
    | NEXT f=formula_expr                       { Next (f) }
    | f=formula_expr UNTIL g=formula_expr       { Until (f,g) }
    | f=formula_expr WEAKUNTIL g=formula_expr   { WeakUntil (f,g) }
    | f=formula_expr RELEASE g=formula_expr     { Release (f,g) }
    | EVENTUALLY f=formula_expr                 { Finally f }
    | GLOBALLY f=formula_expr                   { Globally f }
    | OP f=formula_expr CL                      { f }


parse_hyperltl_formula:
    | EXISTS s=ID DOT f=parse_hyperltl_formula   { Exists (s,f) }
    | FORALL s=ID DOT f=parse_hyperltl_formula   { Forall (s,f) }
    | f=formula_expr EOF                         { Body (f) }
