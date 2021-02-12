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

open Parsing;;
let _ = parse_error;;
# 3 "parser.mly"
  open Lambda;;
# 56 "parser.ml"
let yytransl_const = [|
  257 (* LAMBDA *);
  258 (* TRUE *);
  259 (* FALSE *);
  260 (* IF *);
  261 (* THEN *);
  262 (* ELSE *);
  263 (* SUCC *);
  264 (* PRED *);
  265 (* ISZERO *);
  266 (* LET *);
  267 (* LETREC *);
  268 (* IN *);
  269 (* BOOL *);
  270 (* NAT *);
  271 (* REAL *);
  272 (* TUPLE *);
  273 (* RECORD *);
  274 (* LIST *);
  275 (* LISNIL *);
  276 (* LNIL *);
  277 (* LCONS *);
  278 (* LHEAD *);
  279 (* LTAIL *);
  280 (* CHARARRAY *);
  282 (* CHAR *);
  284 (* LBRACKET *);
  285 (* RBRACKET *);
  286 (* LPAREN *);
  287 (* RPAREN *);
  288 (* LKEY *);
  289 (* RKEY *);
  290 (* EX *);
  291 (* COMMA *);
  292 (* DOT *);
  293 (* EQ *);
  294 (* COLON *);
  295 (* ARROW *);
  296 (* SEPARATOR *);
  297 (* QUIT *);
  298 (* OPENF *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  281 (* CHARARRAYV *);
  283 (* CHARV *);
  299 (* INTV *);
  300 (* STRINGV *);
  301 (* OPENFV *);
  302 (* INSTV *);
  303 (* REALV *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\003\000\003\000\004\000\004\000\004\000\
\002\000\002\000\005\000\005\000\006\000\006\000\006\000\006\000\
\006\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
\007\000\007\000\007\000\009\000\009\000\009\000\009\000\009\000\
\009\000\014\000\014\000\016\000\016\000\017\000\017\000\010\000\
\010\000\018\000\018\000\019\000\019\000\011\000\011\000\012\000\
\012\000\012\000\013\000\013\000\008\000\008\000\008\000\008\000\
\008\000\015\000\021\000\021\000\022\000\022\000\020\000\020\000\
\020\000\020\000\020\000\020\000\000\000\000\000"

let yylen = "\002\000\
\001\000\002\000\002\000\002\000\003\000\002\000\001\000\001\000\
\002\000\003\000\002\000\004\000\001\000\006\000\006\000\006\000\
\008\000\001\000\003\000\002\000\002\000\002\000\003\000\002\000\
\002\000\002\000\002\000\003\000\001\000\001\000\001\000\001\000\
\001\000\001\000\002\000\003\000\001\000\004\000\003\000\003\000\
\003\000\003\000\003\000\003\000\005\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\003\000\003\000\003\000\
\002\000\003\000\003\000\005\000\003\000\003\000\003\000\001\000\
\001\000\001\000\001\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\008\000\000\000\001\000\007\000\069\000\
\000\000\000\000\000\000\046\000\047\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\050\000\049\000\
\000\000\000\000\000\000\051\000\000\000\052\000\070\000\000\000\
\000\000\000\000\018\000\029\000\030\000\031\000\032\000\033\000\
\034\000\006\000\003\000\000\000\002\000\000\000\048\000\000\000\
\024\000\025\000\026\000\000\000\000\000\020\000\021\000\022\000\
\064\000\065\000\066\000\000\000\068\000\067\000\000\000\000\000\
\000\000\000\000\000\000\035\000\037\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\009\000\000\000\011\000\000\000\
\000\000\027\000\005\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\057\000\000\000\000\000\000\000\000\000\000\000\
\000\000\058\000\000\000\000\000\000\000\028\000\000\000\000\000\
\040\000\041\000\000\000\010\000\019\000\023\000\000\000\000\000\
\000\000\000\000\000\000\000\000\036\000\063\000\000\000\000\000\
\055\000\056\000\000\000\039\000\054\000\000\000\000\000\043\000\
\012\000\000\000\000\000\000\000\000\000\000\000\000\000\062\000\
\038\000\000\000\015\000\014\000\016\000\000\000\000\000\000\000\
\045\000\000\000\060\000\017\000"

let yydgoto = "\003\000\
\008\000\031\000\009\000\010\000\032\000\033\000\034\000\066\000\
\035\000\036\000\037\000\038\000\039\000\040\000\041\000\068\000\
\069\000\074\000\075\000\070\000\096\000\097\000"

let yysindex = "\032\000\
\005\000\167\255\000\000\000\000\213\254\000\000\000\000\000\000\
\008\000\002\000\230\254\000\000\000\000\051\000\210\255\210\255\
\210\255\232\254\234\254\210\255\210\255\210\255\000\000\000\000\
\063\255\051\000\113\000\000\000\246\254\000\000\000\000\001\000\
\007\255\082\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\239\254\000\000\010\255\000\000\034\255\
\000\000\000\000\000\000\012\255\014\255\000\000\000\000\000\000\
\000\000\000\000\000\000\140\000\000\000\000\000\015\255\120\255\
\202\255\028\255\244\254\000\000\000\000\019\255\029\255\024\255\
\033\255\030\255\031\255\051\000\000\000\069\000\000\000\210\255\
\210\255\000\000\000\000\039\255\140\000\051\000\051\000\140\000\
\140\000\118\000\000\000\042\255\040\255\255\254\046\255\049\255\
\050\255\000\000\058\255\210\255\140\000\000\000\210\255\210\255\
\000\000\000\000\044\255\000\000\000\000\000\000\064\255\093\255\
\089\255\065\255\066\255\140\000\000\000\000\000\140\000\140\000\
\000\000\000\000\042\255\000\000\000\000\068\255\033\255\000\000\
\000\000\051\000\051\000\051\000\051\000\070\255\046\255\000\000\
\000\000\067\255\000\000\000\000\000\000\096\255\069\255\024\255\
\000\000\051\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\061\000\000\000\000\000\000\000\
\000\000\001\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\109\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\009\255\000\000\077\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\077\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\081\255\082\255\000\000\
\000\000\000\000\000\000\000\000\000\000\087\255\092\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\094\000\092\000\093\000\000\000\242\255\000\000\222\255\
\250\255\000\000\000\000\000\000\000\000\000\000\168\255\000\000\
\040\000\037\000\011\000\000\000\010\000\031\000"

let yytablesize = 428
let yytable = "\048\000\
\077\000\045\000\042\000\117\000\006\000\013\000\013\000\043\000\
\049\000\050\000\051\000\071\000\013\000\054\000\055\000\056\000\
\099\000\046\000\067\000\052\000\073\000\053\000\100\000\004\000\
\005\000\091\000\076\000\082\000\007\000\093\000\095\000\013\000\
\001\000\002\000\137\000\103\000\119\000\053\000\086\000\053\000\
\013\000\053\000\053\000\053\000\053\000\053\000\079\000\085\000\
\087\000\071\000\111\000\088\000\092\000\114\000\093\000\095\000\
\098\000\101\000\073\000\102\000\103\000\107\000\105\000\106\000\
\012\000\013\000\125\000\104\000\108\000\116\000\118\000\112\000\
\113\000\109\000\110\000\057\000\058\000\059\000\044\000\120\000\
\060\000\121\000\122\000\129\000\134\000\135\000\061\000\023\000\
\062\000\024\000\025\000\063\000\064\000\067\000\065\000\123\000\
\126\000\127\000\131\000\130\000\132\000\133\000\138\000\119\000\
\143\000\028\000\047\000\146\000\004\000\030\000\144\000\048\000\
\115\000\044\000\042\000\139\000\140\000\141\000\142\000\059\000\
\011\000\012\000\013\000\014\000\061\000\078\000\015\000\016\000\
\017\000\018\000\019\000\148\000\057\000\058\000\059\000\083\000\
\084\000\060\000\020\000\124\000\128\000\021\000\022\000\061\000\
\023\000\062\000\024\000\025\000\145\000\064\000\136\000\065\000\
\147\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\028\000\047\000\000\000\000\000\030\000\011\000\
\012\000\013\000\014\000\000\000\000\000\015\000\016\000\017\000\
\018\000\019\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\020\000\000\000\000\000\021\000\022\000\000\000\023\000\
\000\000\024\000\025\000\000\000\026\000\000\000\027\000\000\000\
\000\000\000\000\000\000\012\000\013\000\000\000\000\000\000\000\
\000\000\028\000\029\000\012\000\013\000\030\000\057\000\058\000\
\059\000\000\000\000\000\060\000\000\000\000\000\000\000\000\000\
\000\000\061\000\023\000\062\000\024\000\025\000\000\000\064\000\
\000\000\065\000\023\000\000\000\024\000\025\000\000\000\026\000\
\000\000\027\000\000\000\000\000\028\000\094\000\000\000\000\000\
\030\000\000\000\000\000\000\000\028\000\047\000\000\000\000\000\
\030\000\011\000\012\000\013\000\014\000\000\000\000\000\015\000\
\016\000\017\000\018\000\019\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\020\000\000\000\000\000\021\000\022\000\
\000\000\023\000\000\000\024\000\025\000\000\000\026\000\000\000\
\027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\044\000\000\000\028\000\029\000\004\000\005\000\030\000\
\000\000\000\000\007\000\011\000\012\000\013\000\014\000\000\000\
\000\000\015\000\016\000\017\000\018\000\019\000\048\000\048\000\
\000\000\000\000\000\000\000\000\000\000\020\000\000\000\000\000\
\021\000\022\000\000\000\023\000\000\000\024\000\025\000\000\000\
\026\000\048\000\027\000\012\000\013\000\048\000\000\000\048\000\
\048\000\000\000\048\000\000\000\048\000\028\000\047\000\000\000\
\048\000\030\000\000\000\000\000\048\000\000\000\080\000\048\000\
\048\000\000\000\023\000\048\000\024\000\025\000\000\000\026\000\
\000\000\027\000\012\000\013\000\000\000\081\000\000\000\000\000\
\000\000\000\000\000\000\000\000\028\000\047\000\000\000\000\000\
\030\000\000\000\057\000\058\000\059\000\000\000\000\000\060\000\
\000\000\023\000\000\000\024\000\025\000\061\000\026\000\062\000\
\027\000\000\000\000\000\089\000\000\000\090\000\000\000\000\000\
\057\000\058\000\059\000\028\000\072\000\060\000\000\000\030\000\
\000\000\115\000\000\000\061\000\000\000\062\000\000\000\000\000\
\000\000\089\000\000\000\090\000"

let yycheck = "\014\000\
\000\000\000\000\046\001\092\000\000\000\005\001\006\001\000\000\
\015\000\016\000\017\000\026\000\012\001\020\000\021\000\022\000\
\029\001\044\001\025\000\044\001\027\000\044\001\035\001\041\001\
\042\001\060\000\037\001\034\000\046\001\064\000\065\000\031\001\
\001\000\002\000\123\000\037\001\038\001\029\001\005\001\031\001\
\040\001\033\001\034\001\035\001\036\001\037\001\040\001\038\001\
\037\001\064\000\085\000\038\001\038\001\088\000\089\000\090\000\
\029\001\039\001\065\000\031\001\037\001\076\000\033\001\033\001\
\002\001\003\001\101\000\035\001\000\000\028\001\031\001\086\000\
\087\000\080\000\081\000\013\001\014\001\015\001\040\001\034\001\
\018\001\033\001\033\001\040\001\119\000\120\000\024\001\025\001\
\026\001\027\001\028\001\029\001\030\001\100\000\032\001\038\001\
\103\000\104\000\006\001\036\001\012\001\037\001\035\001\038\001\
\035\001\043\001\044\001\012\001\000\000\047\001\044\001\035\001\
\044\001\033\001\033\001\130\000\131\000\132\000\133\000\033\001\
\001\001\002\001\003\001\004\001\033\001\032\000\007\001\008\001\
\009\001\010\001\011\001\146\000\013\001\014\001\015\001\044\000\
\044\000\018\001\019\001\100\000\104\000\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\138\000\030\001\120\000\032\001\
\143\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\043\001\044\001\255\255\255\255\047\001\001\001\
\002\001\003\001\004\001\255\255\255\255\007\001\008\001\009\001\
\010\001\011\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\019\001\255\255\255\255\022\001\023\001\255\255\025\001\
\255\255\027\001\028\001\255\255\030\001\255\255\032\001\255\255\
\255\255\255\255\255\255\002\001\003\001\255\255\255\255\255\255\
\255\255\043\001\044\001\002\001\003\001\047\001\013\001\014\001\
\015\001\255\255\255\255\018\001\255\255\255\255\255\255\255\255\
\255\255\024\001\025\001\026\001\027\001\028\001\255\255\030\001\
\255\255\032\001\025\001\255\255\027\001\028\001\255\255\030\001\
\255\255\032\001\255\255\255\255\043\001\044\001\255\255\255\255\
\047\001\255\255\255\255\255\255\043\001\044\001\255\255\255\255\
\047\001\001\001\002\001\003\001\004\001\255\255\255\255\007\001\
\008\001\009\001\010\001\011\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\019\001\255\255\255\255\022\001\023\001\
\255\255\025\001\255\255\027\001\028\001\255\255\030\001\255\255\
\032\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\040\001\255\255\043\001\044\001\041\001\042\001\047\001\
\255\255\255\255\046\001\001\001\002\001\003\001\004\001\255\255\
\255\255\007\001\008\001\009\001\010\001\011\001\002\001\003\001\
\255\255\255\255\255\255\255\255\255\255\019\001\255\255\255\255\
\022\001\023\001\255\255\025\001\255\255\027\001\028\001\255\255\
\030\001\021\001\032\001\002\001\003\001\025\001\255\255\027\001\
\028\001\255\255\030\001\255\255\032\001\043\001\044\001\255\255\
\036\001\047\001\255\255\255\255\040\001\255\255\021\001\043\001\
\044\001\255\255\025\001\047\001\027\001\028\001\255\255\030\001\
\255\255\032\001\002\001\003\001\255\255\036\001\255\255\255\255\
\255\255\255\255\255\255\255\255\043\001\044\001\255\255\255\255\
\047\001\255\255\013\001\014\001\015\001\255\255\255\255\018\001\
\255\255\025\001\255\255\027\001\028\001\024\001\030\001\026\001\
\032\001\255\255\255\255\030\001\255\255\032\001\255\255\255\255\
\013\001\014\001\015\001\043\001\044\001\018\001\255\255\047\001\
\255\255\044\001\255\255\024\001\255\255\026\001\255\255\255\255\
\255\255\030\001\255\255\032\001"

let yynames_const = "\
  LAMBDA\000\
  TRUE\000\
  FALSE\000\
  IF\000\
  THEN\000\
  ELSE\000\
  SUCC\000\
  PRED\000\
  ISZERO\000\
  LET\000\
  LETREC\000\
  IN\000\
  BOOL\000\
  NAT\000\
  REAL\000\
  TUPLE\000\
  RECORD\000\
  LIST\000\
  LISNIL\000\
  LNIL\000\
  LCONS\000\
  LHEAD\000\
  LTAIL\000\
  CHARARRAY\000\
  CHAR\000\
  LBRACKET\000\
  RBRACKET\000\
  LPAREN\000\
  RPAREN\000\
  LKEY\000\
  RKEY\000\
  EX\000\
  COMMA\000\
  DOT\000\
  EQ\000\
  COLON\000\
  ARROW\000\
  SEPARATOR\000\
  QUIT\000\
  OPENF\000\
  EOF\000\
  "

let yynames_block = "\
  CHARARRAYV\000\
  CHARV\000\
  INTV\000\
  STRINGV\000\
  OPENFV\000\
  INSTV\000\
  REALV\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 70 "parser.mly"
        ((None, false))
# 379 "parser.ml"
               : (Lambda.line list) option * bool))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'operations) in
    Obj.repr(
# 72 "parser.mly"
        ((None, false))
# 386 "parser.ml"
               : (Lambda.line list) option * bool))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Lambda.line list) in
    Obj.repr(
# 74 "parser.mly"
        ((Some _1, true))
# 393 "parser.ml"
               : (Lambda.line list) option * bool))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'operations) in
    Obj.repr(
# 78 "parser.mly"
        ( [_1] )
# 400 "parser.ml"
               : Lambda.line list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'operations) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Lambda.line list) in
    Obj.repr(
# 80 "parser.mly"
        ( _1::_3 )
# 408 "parser.ml"
               : Lambda.line list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 84 "parser.mly"
        ( LnOpen(_2) )
# 415 "parser.ml"
               : 'operations))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 86 "parser.mly"
        ( LnInst(_1) )
# 422 "parser.ml"
               : 'operations))
; (fun __caml_parser_env ->
    Obj.repr(
# 88 "parser.mly"
        (LnQuit )
# 428 "parser.ml"
               : 'operations))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 's2) in
    Obj.repr(
# 92 "parser.mly"
        ([_1])
# 435 "parser.ml"
               : Lambda.inst list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 's2) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Lambda.inst list) in
    Obj.repr(
# 94 "parser.mly"
        (_1::_2)
# 443 "parser.ml"
               : Lambda.inst list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 98 "parser.mly"
      ( Eval (_1) )
# 450 "parser.ml"
               : 's2))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 100 "parser.mly"
      ( Asgn(_1,_3) )
# 458 "parser.ml"
               : 's2))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'appTerm) in
    Obj.repr(
# 104 "parser.mly"
      ( _1 )
# 465 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'term) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 106 "parser.mly"
      ( TmIf (_2, _4, _6) )
# 474 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 108 "parser.mly"
      ( TmAbs (_2, _4, _6) )
# 483 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 110 "parser.mly"
      ( TmLet (_2, _4, _6) )
# 492 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'ty) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 112 "parser.mly"
      ( TmLetRec (_2, _4, _6, _8) )
# 502 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 116 "parser.mly"
      ( _1 )
# 509 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'appTerm) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 118 "parser.mly"
      ( TmLCons(_1,_3) )
# 517 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 120 "parser.mly"
      ( TmLIsNil(_2) )
# 524 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 122 "parser.mly"
      ( TmLHead(_2) )
# 531 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 124 "parser.mly"
      ( TmLTail(_2) )
# 538 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'appTerm) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 126 "parser.mly"
      ( TmProj(_1, _3) )
# 546 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 128 "parser.mly"
      ( TmSucc _2 )
# 553 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 130 "parser.mly"
      ( TmPred _2 )
# 560 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 132 "parser.mly"
      ( TmIsZero _2 )
# 567 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'appTerm) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 134 "parser.mly"
      ( TmApp (_1, _2) )
# 575 "parser.ml"
               : 'appTerm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 138 "parser.mly"
      ( _2 )
# 582 "parser.ml"
               : 'atomicTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'key_structures) in
    Obj.repr(
# 140 "parser.mly"
      ( _1 )
# 589 "parser.ml"
               : 'atomicTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'booleanTerm) in
    Obj.repr(
# 142 "parser.mly"
      ( _1 )
# 596 "parser.ml"
               : 'atomicTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'alphaTerm) in
    Obj.repr(
# 144 "parser.mly"
      ( _1 )
# 603 "parser.ml"
               : 'atomicTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'numeralTerm) in
    Obj.repr(
# 146 "parser.mly"
      ( _1 )
# 610 "parser.ml"
               : 'atomicTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'lists) in
    Obj.repr(
# 148 "parser.mly"
      ( _1 )
# 617 "parser.ml"
               : 'atomicTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tyList) in
    Obj.repr(
# 152 "parser.mly"
      ( TmLNil(_1) )
# 624 "parser.ml"
               : 'lists))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'recursive_definitions) in
    Obj.repr(
# 154 "parser.mly"
      ( _2 )
# 631 "parser.ml"
               : 'lists))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tyList) in
    Obj.repr(
# 158 "parser.mly"
      ( TmLNil(_3) )
# 638 "parser.ml"
               : 'recursive_definitions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'recursive_definitionL1) in
    Obj.repr(
# 160 "parser.mly"
      ( _1 )
# 645 "parser.ml"
               : 'recursive_definitions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'atomicTerm) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'tyList) in
    Obj.repr(
# 164 "parser.mly"
      ( TmLCons(_1, TmLNil(_4)) )
# 653 "parser.ml"
               : 'recursive_definitionL1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atomicTerm) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'recursive_definitionL1) in
    Obj.repr(
# 166 "parser.mly"
      ( TmLCons(_1, _3) )
# 661 "parser.ml"
               : 'recursive_definitionL1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'tuple) in
    Obj.repr(
# 170 "parser.mly"
      ( _2 )
# 668 "parser.ml"
               : 'key_structures))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'record) in
    Obj.repr(
# 172 "parser.mly"
      ( _2 )
# 675 "parser.ml"
               : 'key_structures))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atomicTerm) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 176 "parser.mly"
      ( TmPair(_1, _3) )
# 683 "parser.ml"
               : 'tuple))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atomicTerm) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tuple) in
    Obj.repr(
# 178 "parser.mly"
      ( TmTuple(_1, _3) )
# 691 "parser.ml"
               : 'tuple))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTerm) in
    Obj.repr(
# 182 "parser.mly"
      ( TmRecVar( _1, _3) )
# 699 "parser.ml"
               : 'record))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'atomicTerm) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'record) in
    Obj.repr(
# 184 "parser.mly"
      ( TmRecord(TmRecVar( _1, _3), _5))
# 708 "parser.ml"
               : 'record))
; (fun __caml_parser_env ->
    Obj.repr(
# 188 "parser.mly"
      ( TmTrue )
# 714 "parser.ml"
               : 'booleanTerm))
; (fun __caml_parser_env ->
    Obj.repr(
# 190 "parser.mly"
      ( TmFalse )
# 720 "parser.ml"
               : 'booleanTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 194 "parser.mly"
      ( TmVar _1 )
# 727 "parser.ml"
               : 'alphaTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char) in
    Obj.repr(
# 196 "parser.mly"
      ( TmChar(It_A_Code(_1)))
# 734 "parser.ml"
               : 'alphaTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 198 "parser.mly"
      ( 
      let rec from_string_to_char_array idx =
        if(idx = (String.length _1) - 2) then 
          It_A_Code(_1.[idx]) 
        else 
          It_A_Chain(It_A_Code(_1.[idx]), from_string_to_char_array (idx+1))
      in TmString(from_string_to_char_array 1)
      )
# 748 "parser.ml"
               : 'alphaTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 209 "parser.mly"
      ( let rec f = function
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f _1 )
# 758 "parser.ml"
               : 'numeralTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string * string) in
    Obj.repr(
# 214 "parser.mly"
      ( let rec f = function
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in 
          let f2 dec idec =
            let rec lzeros ee = function
              | 0 -> f ee
              | x -> TmLZero( lzeros ee (x-1) )
            in 
              lzeros idec (String.length(dec) - String.length(string_of_int idec))
            in 
              let (ent, dec) = _1
                in let (ient, idec) = ((int_of_string ent), (int_of_string dec))
                in TmReal(f ient, (f2 dec idec))
      )
# 779 "parser.ml"
               : 'numeralTerm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomicTy) in
    Obj.repr(
# 231 "parser.mly"
      ( _1 )
# 786 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atomicTy) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ty) in
    Obj.repr(
# 233 "parser.mly"
      ( TyArr (_1, _3) )
# 794 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'tyRecord) in
    Obj.repr(
# 235 "parser.mly"
      ( _2 )
# 801 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'tyTuple) in
    Obj.repr(
# 237 "parser.mly"
      ( _2 )
# 808 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ty) in
    Obj.repr(
# 239 "parser.mly"
      ( TyList(_2) )
# 815 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 243 "parser.mly"
      (_2)
# 822 "parser.ml"
               : 'tyList))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ty) in
    Obj.repr(
# 247 "parser.mly"
      ( TyRecVar( _1, _3))
# 830 "parser.ml"
               : 'tyRecord))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'tyRecord) in
    Obj.repr(
# 249 "parser.mly"
      ( TyRecord(TyRecVar( _1, _3), _5) )
# 839 "parser.ml"
               : 'tyRecord))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ty) in
    Obj.repr(
# 253 "parser.mly"
      ( TyProd(_1, _3) )
# 847 "parser.ml"
               : 'tyTuple))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tyTuple) in
    Obj.repr(
# 255 "parser.mly"
      ( TyTuple(_1, _3) )
# 855 "parser.ml"
               : 'tyTuple))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 259 "parser.mly"
      ( _2 )
# 862 "parser.ml"
               : 'atomicTy))
; (fun __caml_parser_env ->
    Obj.repr(
# 261 "parser.mly"
      ( TyBool )
# 868 "parser.ml"
               : 'atomicTy))
; (fun __caml_parser_env ->
    Obj.repr(
# 263 "parser.mly"
      ( TyNat )
# 874 "parser.ml"
               : 'atomicTy))
; (fun __caml_parser_env ->
    Obj.repr(
# 265 "parser.mly"
      ( TyReal )
# 880 "parser.ml"
               : 'atomicTy))
; (fun __caml_parser_env ->
    Obj.repr(
# 267 "parser.mly"
      ( TyChar )
# 886 "parser.ml"
               : 'atomicTy))
; (fun __caml_parser_env ->
    Obj.repr(
# 269 "parser.mly"
      ( TyString )
# 892 "parser.ml"
               : 'atomicTy))
(* Entry s1 *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry s2_list *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let s1 (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : (Lambda.line list) option * bool)
let s2_list (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : Lambda.inst list)
