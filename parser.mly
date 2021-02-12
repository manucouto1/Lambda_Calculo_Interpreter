
%{
  open Lambda;;
%}

%token LAMBDA
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token SUCC
%token PRED
%token ISZERO
%token LET
%token LETREC
%token IN
%token BOOL
%token NAT
%token REAL
%token TUPLE
%token RECORD
%token LIST
%token LISNIL
%token LNIL
%token LCONS
%token LHEAD
%token LTAIL
%token CHARARRAY
%token CHARARRAYV
%token CHAR
%token CHARV

%token LBRACKET
%token RBRACKET
%token LPAREN
%token RPAREN
%token LKEY
%token RKEY
%token EX
%token COMMA
%token DOT
%token EQ
%token COLON
%token ARROW
%token SEPARATOR
%token QUIT
%token OPENF
%token EOF

%token <int> INTV
%token <string> STRINGV
%token <string> OPENFV
%token <string> INSTV
%token <string * string> REALV
%token <char> CHARV
%token <string> CHARARRAYV

%start s1
%start s2_list

%type <Lambda.inst list> s2_list
%type <Lambda.line list> operation_list
%type <(Lambda.line list) option * bool> s1

%%

s1:
      EOF
        {(None, false)}
    | operations EOF
        {(None, false)}
    | operation_list EOF
        {(Some $1, true)}

operation_list:
      operations SEPARATOR
        { [$1] }
    | operations SEPARATOR operation_list
        { $1::$3 }

operations:
      OPENF INSTV 
        { LnOpen($2) }
    | INSTV 
        { LnInst($1) }
    | QUIT
        {LnQuit }

s2_list:
      s2 EOF
        {[$1]}
    | s2 s2_list EOF
        {$1::$2}

s2 :
    term SEPARATOR
      { Eval ($1) }
  | STRINGV EQ term SEPARATOR
      { Asgn($1,$3) }

term :
    appTerm
      { $1 }
  | IF term THEN term ELSE term
      { TmIf ($2, $4, $6) }
  | LAMBDA STRINGV COLON ty DOT term
      { TmAbs ($2, $4, $6) }
  | LET STRINGV EQ term IN term
      { TmLet ($2, $4, $6) }
  | LETREC STRINGV COLON ty EQ term IN term
      { TmLetRec ($2, $4, $6, $8) }

appTerm :
    atomicTerm
      { $1 }
  |  appTerm LCONS atomicTerm  
      { TmLCons($1,$3) }
  | LISNIL atomicTerm
      { TmLIsNil($2) }
  | LHEAD atomicTerm 
      { TmLHead($2) }
  | LTAIL atomicTerm
      { TmLTail($2) }
  | appTerm DOT atomicTerm 
      { TmProj($1, $3) } 
  | SUCC atomicTerm
      { TmSucc $2 }
  | PRED atomicTerm
      { TmPred $2 }
  | ISZERO atomicTerm
      { TmIsZero $2 }
  | appTerm atomicTerm
      { TmApp ($1, $2) }
  
atomicTerm :
    LPAREN term RPAREN
      { $2 }
  | key_structures
      { $1 }
  | booleanTerm
      { $1 }
  | alphaTerm
      { $1 }
  | numeralTerm
      { $1 }
  | lists
      { $1 }

lists:
  |  tyList
      { TmLNil($1) }
  |  LBRACKET recursive_definitions 
      { $2 }
    
recursive_definitions:
  |  RBRACKET COLON tyList
      { TmLNil($3) }
  | recursive_definitionL1
      { $1 }

recursive_definitionL1:
  |  atomicTerm RBRACKET COLON tyList
      { TmLCons($1, TmLNil($4)) }
  |  atomicTerm COMMA recursive_definitionL1
      { TmLCons($1, $3) }
  
key_structures:
  | LKEY tuple RKEY
      { $2 }
  | LKEY record RKEY
      { $2 }

tuple:
    atomicTerm COMMA atomicTerm
      { TmPair($1, $3) }
  | atomicTerm COMMA tuple
      { TmTuple($1, $3) }

record:
    STRINGV EQ atomicTerm
      { TmRecVar( $1, $3) }
  | STRINGV EQ atomicTerm COMMA record
      { TmRecord(TmRecVar( $1, $3), $5)}

booleanTerm:
    TRUE
      { TmTrue }
  | FALSE
      { TmFalse }

alphaTerm:
    STRINGV
      { TmVar $1 }
  | CHARV
      { TmChar(It_A_Code($1))}
  | CHARARRAYV
      { 
      let rec from_string_to_char_array idx =
        if(idx = (String.length $1) - 2) then 
          It_A_Code($1.[idx]) 
        else 
          It_A_Chain(It_A_Code($1.[idx]), from_string_to_char_array (idx+1))
      in TmString(from_string_to_char_array 1)
      }

numeralTerm:
  | INTV
      { let rec f = function
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }
  | REALV 
      { let rec f = function
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
              let (ent, dec) = $1
                in let (ient, idec) = ((int_of_string ent), (int_of_string dec))
                in TmReal(f ient, (f2 dec idec))
      }
ty :
    atomicTy
      { $1 }
  | atomicTy ARROW ty
      { TyArr ($1, $3) }
  | LKEY tyRecord RKEY
      { $2 }
  | LKEY tyTuple RKEY 
      { $2 }
  | LIST ty
      { TyList($2) }

tyList:
    LBRACKET ty RBRACKET
      {$2}

tyRecord :
    STRINGV COLON ty
      { TyRecVar( $1, $3)}
  | STRINGV COLON ty COMMA tyRecord
      { TyRecord(TyRecVar( $1, $3), $5) }

tyTuple :
    ty EX ty
      { TyProd($1, $3) }
  | ty EX tyTuple
      { TyTuple($1, $3) }

atomicTy: 
    LPAREN ty RPAREN  
      { $2 }
  | BOOL
      { TyBool }
  | NAT
      { TyNat }
  | REAL
      { TyReal }
  | CHAR 
      { TyChar }
  | CHARARRAY
      { TyString }
  
