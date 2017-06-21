{
    open Parser
}

rule lex = parse
    | "True"             { TRUE }
    | "False"            { FALSE }
    | "&"                { AND }
    | "|"                { OR }
    | ['~' '!']          { NOT }
    | ['-' '='] '>'      { IMPL }
    | '<' ['-' '='] '>'  { EQUIV }
    | "X"                { NEXT }
    | "U"                { UNTIL }
    | "W"                { WEAKUNTIL }
    | "R"                { RELEASE }
    | "F"                { EVENTUALLY }
    | "G"                { GLOBALLY }
    | "forall"           { FORALL }
    | "exists"           { EXISTS }
    (*| ['A'-'Z' 'a'-'z']['0'-'9' 'A'-'Z' 'a'-'z']* as s { ID (s) }*)
    | ['0'-'9' 'A'-'Z' 'a'-'z']* as s { ID (s) }
    | "_"                { UNDER }
    | "."                { DOT }
    | [' ' '\t' '\n']    { lex lexbuf }
    | "("                { OP }
    | ")"                { CL }
    | eof                { EOF }
