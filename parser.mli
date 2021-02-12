type token =
  | LAMBDA
  | TRUE
  | FALSE
  | IF
  | THEN
  | ELSE
  | SUCC
  | PRED
  | ISZERO
  | LET
  | LETREC
  | IN
  | BOOL
  | NAT
  | REAL
  | TUPLE
  | RECORD
  | LIST
  | LISNIL
  | LNIL
  | LCONS
  | LHEAD
  | LTAIL
  | CHARARRAY
  | CHARARRAYV of (string)
  | CHAR
  | CHARV of (char)
  | LBRACKET
  | RBRACKET
  | LPAREN
  | RPAREN
  | LKEY
  | RKEY
  | EX
  | COMMA
  | DOT
  | EQ
  | COLON
  | ARROW
  | SEPARATOR
  | QUIT
  | OPENF
  | EOF
  | INTV of (int)
  | STRINGV of (string)
  | OPENFV of (string)
  | INSTV of (string)
  | REALV of (string * string)

val s1 :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> (Lambda.line list) option * bool
val s2_list :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Lambda.inst list
