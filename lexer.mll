
{
  open Parser;;
  exception Lexical_error;; 
}

rule multilinetoken = parse
     [' ' '\t' '\n' ';' ]  { token lexbuf }
  |  ['a'-'z' '\"' '\''  'A'-'Z' '0'-'9' ':' '(' ')' '.' '=' '-' '>' '<' '[' ']' '{' '}' ',' '*' ' ' '\t' '\n' '_']+
                { (* print_endline "ISNTV";*) INSTV(Lexing.lexeme lexbuf) } 
  | ";;"        { SEPARATOR }
  | "#open"[' ']*
                { OPENF } 
  | "#quit"[' ']*
                { QUIT }
  | eof         { EOF } 
  | _           { raise Lexical_error } 

and token = parse
    [' ' '\t' '\n']  { token lexbuf }
  | "lambda"    { LAMBDA }
  | "L"         { LAMBDA }
  | "true"      { TRUE }
  | "false"     { FALSE }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "succ"      { SUCC }
  | "pred"      { PRED }
  | "iszero"    { ISZERO }
  | "let"       { LET }
  | "letrec"    { LETREC }
  | "in"        { IN }
  | "Bool"      { BOOL }
  | "Nat"       { NAT }
  | "Real"      { REAL }
  | "Char"      { CHAR }
  | "Tuple"     { TUPLE }
  | "Record"    { RECORD }
  | "String"    { CHARARRAY }
  | "List"      { LIST }
  | "isnil"     { LISNIL }
  | "nil"       { LNIL }
  | "head"      { LHEAD }
  | "tail"      { LTAIL }
  | '['         { LBRACKET }
  | ']'         { RBRACKET }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | '.'         { DOT }
  | '*'         { EX }
  | '='         { EQ }
  | ','         { COMMA }
  | ':'         { COLON }
  | "::"        { LCONS }
  | "->"        { ARROW }
  | "{"         { LKEY }
  | "}"         { RKEY }
  | ";;"         { SEPARATOR}
  | "\""['0'-'9''a'-'z''A'-'Z' '\t' '\n' ' ']+"\""
                { CHARARRAYV (Lexing.lexeme lexbuf) }
  | "\'"['0'-'9''a'-'z''A'-'Z' '\t' '\n' ' ']"\'"        
                { CHARV (Lexing.lexeme_char lexbuf 1)}
  | ['0'-'9']+  { INTV (int_of_string (Lexing.lexeme lexbuf)) }
  | ['0'-'9']+'.'['0'-'9']+
                { let (ent,dec) = match (String.split_on_char '.' (Lexing.lexeme lexbuf)) with
                   | h::[hh] -> (h, hh)
                   | _ -> raise Lexical_error
                  in REALV (ent, dec)  }
  | ['a'-'z']['a'-'z' '_' '0'-'9']*
                { STRINGV (Lexing.lexeme lexbuf) }
  | eof         { EOF }
  | _           { raise Lexical_error } 

