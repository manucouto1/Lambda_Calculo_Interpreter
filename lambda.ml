type ty =
    TyBool
  | TyNat
  | TyReal
  | TyChar
  | TyString
  | TyList of ty
  | TyRecVar of string * ty
  | TyRecord of ty * ty
  | TyTuple of ty * ty 
  | TyProd of ty * ty
  | TyArr of ty * ty
;;

type iterable_alpha =
    It_A_Code of char 
  | It_A_Chain of iterable_alpha * iterable_alpha

and iterable_record = 
    It_R_Code of string * term 
  | It_R_Chain of iterable_record * iterable_record

and term =
    TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmChar of iterable_alpha
  | TmString of iterable_alpha
  | TmZero
  | TmIsZero of term
  | TmSucc of term
  | TmPred of term
  | TmRecVar of string * term
  | TmRecord of term * term
  | TmLZero of term
  | TmReal of term * term
  | TmVar of string
  | TmPair of term * term
  | TmTuple of term * term
  | TmLNil of ty
  | TmLIsNil of term
  | TmLHead of term
  | TmLTail of term
  | TmLCons of term * term
  | TmProj of term * term
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLet of string * term * term
  | TmLetRec of string * ty * term * term
;;

type line = 
    LnInst of string
  | LnOpen of string
  | LnQuit
;;

type inst = 
    Asgn of string * term
  | Eval of term
;;


type inst_list = inst list
;; 

type context =
  (((string * term) list) * ((string * ty) list)) ref
;;

(* CONTEXT MANAGEMENT *)

let emptyctx =
  (ref ([], []))
;;

let addterm ctx x term = 
  let (terms,tys) = !ctx 
  in ctx:=((x, term) :: terms, tys)
;;

let getterm ctx x =
  let (terms,_) = !ctx 
  in List.assoc x terms
;;


let addtype ctx x ty = 
  let (terms,tys) = !ctx 
  in ctx := (terms, (x, ty) :: tys)
;;

let gettype ctx x =
  let (_, tys) = !ctx 
  in List.assoc x tys
;;
(* Exceptions *)
exception Critical_error of string
;;
exception Type_error of string
;;                             
exception Index_error of string
;;
exception NoRuleApplies
;;
exception Exit
;;
(* TYPE MANAGEMENT (TYPING) *)

let rec string_of_ty ty = match ty with
    TyBool ->
      "Bool"
  | TyNat ->
      "Nat"
  | TyReal ->
      "Real"
  | TyString -> 
      "String"
  | TyChar -> 
      "Char"
  | TyList ty1 ->
      "List "^ string_of_ty ty1 ^""
  | TyProd (ty1, ty2) -> 
      string_of_ty ty1 ^" * "^ string_of_ty ty2
  | TyTuple (ty1, tyNext) -> 
      (let rec iterate_tuple next = match next with
        | TyProd (ty1', ty2) ->
            string_of_ty ty1' ^ " * " ^ string_of_ty ty2 ^"}"
        | TyTuple (ty1', next') -> 
            string_of_ty ty1'^" * " ^ (iterate_tuple next')
        | _ as er-> string_of_ty er
      in "{" ^ string_of_ty ty1 ^ " * " ^ iterate_tuple tyNext)
  | TyRecVar (x,v) ->
      x^":"^(string_of_ty v)
  | TyRecord(r, next) as t ->
      (let rec iterate_record next = match next with
        | TyRecVar (x, v) -> 
            x^ ":" ^ string_of_ty v ^ "}"
        | TyRecord (r', next') ->
            string_of_ty r' ^","^ iterate_record next'
        | _ as er -> string_of_ty er
      in "{"^iterate_record t)
  | TyArr (ty1, ty2) ->
      "(" ^ string_of_ty ty1 ^ ")" ^ " -> " ^ "(" ^ string_of_ty ty2 ^ ")"
;;


let rec string_debug_of_ty ty = match ty with
    TyBool ->
      "TyBool"
  | TyNat ->
      "TyNat"
  | TyReal -> 
      "TyReal"
  | TyChar -> 
      "TyChar"
  | TyString -> 
      "TyString"
  | TyList ty1 ->
      "TyList("^string_debug_of_ty ty1^")"
  | TyRecVar (x,v) -> 
      "TyRecVar("^x^","^string_debug_of_ty v^")"
  | TyRecord (r, tyNext) ->
      "TyRecord(" ^string_debug_of_ty r^","^string_debug_of_ty tyNext ^")"
  | TyTuple (ty1, tyNext) ->
      "TyTuple(" ^string_debug_of_ty ty1 ^","^ string_debug_of_ty tyNext ^")"
  | TyProd(ty1, ty2) -> 
      "TyProd(" ^string_debug_of_ty ty1 ^","^ string_debug_of_ty ty2 ^")"
  | TyArr (ty1, ty2) ->
      "TyArr(" ^ string_debug_of_ty ty1 ^ "," ^ string_debug_of_ty ty2 ^ ")"
;;

let rec string_debug_of_it_aplha = function 
    It_A_Code c -> 
    "TmCode ("^(String.make 1 c)^")"
  | It_A_Chain (c, it) -> 
    "TmChain(" ^ string_debug_of_it_aplha c^","^string_debug_of_it_aplha it^")"


let rec string_debug_of_term = function 
  TmTrue ->
    "TmTrue"
  | TmFalse ->
    "TmFalse"
  | TmIf (t1,t2,t3) ->
    "TmIf " ^ "(" ^ string_debug_of_term t1^","^ string_debug_of_term t2^","^ string_debug_of_term t3^","^")" 
  | TmZero ->
    "TmZero"
  | TmChar c -> 
    "TmChar ("^string_debug_of_it_aplha c^")"
  | TmString(it) -> 
    "TmString("^string_debug_of_it_aplha it ^")"
  | TmLZero n -> 
    "TmLZero" ^"("^string_debug_of_term n ^")"
  | TmReal(n1, n2) -> 
    "TmReal" ^ "(" ^string_debug_of_term n1^","^string_debug_of_term n2^")"
  | TmSucc t -> 
    "TmSucc " ^ "(" ^ string_debug_of_term t ^ ")"
  | TmPred t ->
    "TmPred " ^ "(" ^ string_debug_of_term t ^ ")"
  | TmIsZero t ->
    "TmIsZero " ^ "(" ^ string_debug_of_term t ^ ")"
  | TmVar s ->
    "TmVar "^s
  | TmLIsNil(tm) -> 
    "TmLIsNil("^string_debug_of_term tm^")"
  | TmLNil(ty) -> 
    "TmLNil("^string_debug_of_ty ty^")"
  | TmLHead(tm) -> 
    "TmLHead("^string_debug_of_term tm^")"
  | TmLTail(tm) -> 
    "TmLTail("^string_debug_of_term tm^")"
  | TmLCons(tm1, tm2) -> 
    "TmLCons("^string_debug_of_term tm1^","^string_debug_of_term tm2^")"
  | TmPair (t1, t2) -> 
    "TmPair(" ^string_debug_of_term t1 ^","^string_debug_of_term t2 ^")"
  | TmTuple (t1, tnext) -> 
    "TmTuple("^string_debug_of_term t1 ^ "," ^ string_debug_of_term tnext ^")"
  | TmRecVar(x, v) -> 
    "TmRecVar("^x^","^string_debug_of_term v
  | TmRecord(r1, next) -> 
    "TmRecord(" ^string_debug_of_term r1 ^","^ string_debug_of_term next ^")"
  | TmProj( t1, n) -> 
    "TmProj("^string_debug_of_term t1 ^","^ string_debug_of_term n ^")"
  | TmAbs (s, tyS, t) ->
    "TmAbs(" ^ s ^ ", " ^ string_debug_of_ty tyS ^ ", " ^ string_debug_of_term t ^ ")"
  | TmApp (t1, t2) ->
    "TmApp(" ^ string_debug_of_term t1 ^ "," ^ string_debug_of_term t2 ^ ")"
  | TmLet (s, t1, t2) ->
    "TmLet(" ^ s ^ "," ^ string_debug_of_term t1 ^ "," ^ string_debug_of_term t2 ^ ")"
  | TmLetRec (s, ty, t1, t2) ->
    "TmLetRec(" ^ s ^ ","^ string_debug_of_ty ty ^"," ^ string_debug_of_term t1 ^ "," ^ string_debug_of_term t2 ^ ")"
;;    

let rec string_of_it_aplha = function 
    It_A_Code c -> 
      ( String.make 1 c)
  | It_A_Chain (c, it) -> 
      string_of_it_aplha c^string_of_it_aplha it

let rec string_of_term = function
    TmTrue ->
      "true"
  | TmFalse ->
      "false"
  | TmIf (t1,t2,t3) ->
      "if " ^ "(" ^ string_of_term t1 ^ ")" ^
      " then " ^ "(" ^ string_of_term t2 ^ ")" ^
      " else " ^ "(" ^ string_of_term t3 ^ ")"
  | TmZero ->
      "0"
  | TmChar c -> 
      "\'"^string_of_it_aplha c^"\'"
  | TmString (it) -> 
      "\""^string_of_it_aplha it^"\""
  | TmLZero n -> 
      "0"^(string_of_term n)
  | TmReal (n1,n2) -> 
      let n1' = string_of_term n1 in
      let n2' = string_of_term n2 in
        n1'^"."^n2'
  | TmSucc t ->
     let rec f n t' = match t' with
          TmZero -> string_of_int n
        | TmSucc s -> f (n+1) s
        | _ -> "succ " ^ "(" ^ string_of_term t ^ ")"
      in f 1 t
  | TmPred t ->
      "pred " ^ "(" ^ string_of_term t ^ ")"
  | TmIsZero t ->
      "iszero " ^ "(" ^ string_of_term t ^ ")"
  | TmVar s ->
      s
  | TmProj(t1,n)-> 
      "TmProj("^string_of_term t1^","^ string_of_term n^")"
  | TmPair (t1,t2) -> 
      "{"^string_of_term t1^","^string_of_term t2^"}"
  | TmTuple (t1, tnext) -> 
      (let rec iterate_tuple next = match next with 
         | TmPair (t1', t2) -> 
             string_of_term t1' ^ "," ^ string_of_term t2 ^ "}"
         | TmTuple (t1', next') -> 
             string_of_term t1' ^ "," ^ iterate_tuple next'
         | _ as er-> string_of_term er
       in "{" ^ string_of_term t1 ^ "," ^ iterate_tuple tnext)
  | TmRecVar(x, v) -> 
      x^"="^string_of_term v
  | TmRecord(r1, next) -> 
      (let rec iterate_record next = match next with
          | TmRecVar (x, v) -> 
              x ^"="^ string_of_term v ^"}"
          | TmRecord (r1', next') ->
              string_of_term r1' ^","^ iterate_record next'
          | _ as er -> string_of_term er
        in "{" ^string_of_term r1 ^","^ iterate_record next )
  
  | TmLIsNil(tm) -> 
      "TmLIsNil("^string_of_term tm^")"
  | TmLNil(ty) -> 
      "[ ]"
  | TmLHead(tm) -> 
      "TmLHead("^string_of_term tm^")"
  | TmLTail(tm) -> 
      "TmLTail("^string_of_term tm^")"
  | TmLCons(tm1, tm2) -> 
      let rec string_of_list = function
          TmLNil ty -> 
            "]"
        | TmLCons (h, t) -> 
            ","^string_of_term h^(string_of_list t)
        | _ as er-> string_of_term er
      in "["^string_of_term tm1^string_of_list tm2
  | TmAbs (s, tyS, t) ->
      "(lambda " ^ s ^ ":" ^ string_of_ty tyS ^ ". " ^ string_of_term t ^ ")"
  | TmApp (t1, t2) ->
      "(" ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ ")"
  | TmLet (s, t1, t2) ->
      "let " ^ s ^ " = " ^ string_of_term t1 ^ " in " ^ string_of_term t2
  | TmLetRec (s, tyS, t1, t2) ->
    "let " ^ s ^ ":" ^ string_of_ty tyS ^ " = " ^ string_of_term t1 ^ " in " ^ string_of_term t2

;;

let rec isnumericval tm = match tm with
    TmZero -> true
  | TmLZero n -> isnumericval n
  | TmReal (n1, n2) -> (isnumericval n1) && (isnumericval n2) 
  | TmSucc t -> isnumericval t
  | _ -> false
;;

let rec isval tm = match tm with
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | TmPair _ -> true
  (*| TmLIsNil _ -> true*)
  | TmLNil _ -> true
  | TmLCons _ -> true
  | TmTuple _ -> true
  | TmRecord _ -> true
  | TmChar _ -> true
  | TmString _ -> true 
  | t when isnumericval t -> true
  | _ -> false
;;

let rec typeof ctx tm =  match tm with
    (* T-True *)
    TmTrue | TmFalse ->
      TyBool

    (* T-If *)
  | TmIf (t1, t2, t3) ->
      if typeof ctx t1 = TyBool then
        let tyT2 = typeof ctx t2 in
        if typeof ctx t3 = tyT2 then tyT2
        else raise (Type_error ("arms of conditional have different types "^string_debug_of_ty(typeof ctx t3)^"\n"^ string_debug_of_ty tyT2))
      else
        raise (Type_error "guard of conditional not a boolean")
      
    (* T-Zero *)
  | TmZero ->
      TyNat

  | TmLNil ty1 -> 
      TyList(ty1)
  
  | TmChar _ -> 
      TyChar

  | TmString _ -> 
      TyString

  | TmLIsNil (tm) -> (match (typeof ctx tm) with
      | TyList _ ->  TyBool
      | _ -> raise (Type_error "The list doesnt have the expected type"))

  (* Llama recursivamente a typeof hasta que llega al ultimo elemento TmLNil donde está guardado el tipo de la lista*)
  | TmLCons (h, t) -> 
      let ty = (typeof ctx h) in 
        (match (typeof ctx t) with 
          | TyList ty' -> if ty = ty' then TyList ty' else raise (Type_error "Wrong list types")
          | _ -> raise (Type_error "Head type doesnt match constructor type"))

  | TmLHead (tm) -> 
      (match (typeof ctx tm ) with 
        | TyList ty -> ty
        | _ -> raise (Type_error "Head doesnt match the expected type"))
        
  | TmLTail(tm) -> 
      (match (typeof ctx tm ) with 
        | TyList _ as ty -> ty
        | _ -> raise (Type_error "Head doesnt match the expected type"))

  | TmPair (t1, t2) -> 
      TyProd( typeof ctx t1 , typeof ctx t2)

  | TmProj (t, x) when not(isval t) -> 
      typeof ctx t

  | TmProj (TmRecord (x, n), TmVar k) ->
      (let rec iterate_record next = match next with
        | (TmRecord( TmRecVar(x', v), next')) ->
            if x' = k then typeof ctx v else iterate_record next'
        | (TmRecVar( x', v)) -> 
            if x' = k then typeof ctx v else raise (Index_error "Index out of range")
        | _ -> raise (Type_error "Wrong index type")
      in iterate_record (TmRecord (x, n)))

  | TmProj (t, n) -> 
      (let rec iterate_tuple next it =  match (next, it) with 
          | (TmTuple (t',_), TmSucc(TmZero)) -> 
              typeof ctx t'
          | (TmPair (t1, t2), TmSucc(TmZero)) ->
              typeof ctx t1
          | (TmPair (t1, t2), TmSucc(TmSucc(TmZero))) -> 
              typeof ctx t2
          | (TmTuple (_, next'), TmSucc(it')) -> 
              iterate_tuple next' it' 
          | (_,TmZero) -> 
              raise (Index_error "Index out of range")
          | _ -> raise (Type_error "Wrong index type")
        in let rec projection data = match data with
            | TmVar(x) -> 
                projection (getterm ctx x)
            | TmTuple(_,_) | TmPair(_,_) as tm' ->
                iterate_tuple tm' n
            | _ -> 
              raise (Type_error "Traying to project wrong type")
        in projection t )

  | TmTuple(tm1, tmNext) -> 
       (let rec iterateTypes next = match next with
          | TmPair(tm1', tm2) -> 
              TyProd(typeof ctx tm1', typeof ctx tm2)
          | TmTuple(tm1', next') ->
              TyTuple(typeof ctx tm1', iterateTypes next')
          | _ -> raise (Type_error "wrong types")
        in TyTuple(typeof ctx tm1, iterateTypes tmNext))
  
  | TmRecVar(x, v) -> 
      TyRecVar(x, typeof ctx v)

  | TmRecord(r1, tmNext) -> 
      TyRecord(typeof ctx r1, typeof ctx tmNext)

  | TmLZero n1 -> 
      if (typeof ctx n1 = TyNat) then TyNat
      else raise (Type_error "wrong type, bad float number format")

  | TmReal (n1, n2) ->
      if (typeof ctx n1 = TyNat) && (typeof ctx n2 = TyNat) then TyReal
      else raise (Type_error "wrong type, bad float number format")

    (* T-Succ *)
  | TmSucc t1 ->
      if typeof ctx t1 = TyNat then TyNat
      else raise (Type_error "argument of succ is not a number")

    (* T-Pred *)
  | TmPred t1 ->
      if typeof ctx t1 = TyNat then TyNat
      else raise (Type_error "argument of pred is not a number")

    (* T-Iszero *)
  | TmIsZero t1 ->
      if typeof ctx t1 = TyNat then TyBool
      else raise (Type_error "argument of iszero is not a number")

    (* T-Var *)
  | TmVar x ->
      (try gettype ctx x with
       _ -> raise (Type_error ("no binding type for variable " ^ x)))

    (* T-Abs *)
  | TmAbs (x, tyT1, t2) ->
      addtype ctx x tyT1;
      let tyT2 = typeof ctx t2 in
      TyArr (tyT1, tyT2)

    (* T-App *)
  | TmApp (t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match tyT1 with
           TyArr (tyT11, tyT12) ->
             if tyT2 = tyT11 then tyT12
             else raise (Type_error "parameter type mismatch ")
         | _ -> raise (Type_error ("arrow type expected got "^string_of_ty tyT1)))

    (* T-Let *)
  | TmLet (x, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      addtype ctx x tyT1;
      typeof ctx t2

    (* T-LetRec --> TODO comprobar que está bien *)
  | TmLetRec (x, ty, t1, t2) ->
      addtype ctx x ty;
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      if  tyT1 = ty then
        let rec find_out tyRec = match tyRec with 
          | TyArr(_,o) as actualType -> if actualType = tyT2 then tyT2 else find_out o
          | _ as finalType-> if finalType = tyT2 then tyT2 else raise (Type_error ("parameter type mismatch letrec \n"^ string_of_ty tyT2 ^" \n"^string_of_ty finalType^"\n" ))
        in find_out ty 
      else raise (Type_error ("parameter type mismatch letrec \n"^ string_of_ty ty ^" \n"^string_of_ty tyT1^"\n" ))
;;


(* TERMS MANAGEMENT (EVALUATION) *)

let rec ldif l1 l2 = match l1 with
    [] -> []
  | h::t -> if List.mem h l2 then ldif t l2 else h::(ldif t l2)
;;

let rec lunion l1 l2 = match l1 with
    [] -> l2
  | h::t -> if List.mem h l2 then lunion t l2 else h::(lunion t l2)
;;

let rec free_vars tm = match tm with
    TmTrue ->
      []
  | TmFalse ->
      []
  | TmIf (t1, t2, t3) ->
      lunion (lunion (free_vars t1) (free_vars t2)) (free_vars t3)
  | TmZero ->
      []
  | TmReal (n1, n2) -> 
      lunion (free_vars n1) (free_vars n2) 
  | TmPair (t1, t2) -> 
      lunion (free_vars t1) (free_vars t2)
  | TmTuple (t1, next) -> 
      lunion (free_vars t1) (free_vars next)
  | TmLNil _ -> 
      []
  | TmChar _ | TmString _ -> 
      []
  | TmLIsNil(tm) | TmLHead(tm) | TmLTail(tm) -> 
      free_vars tm
  | TmLCons(h,t) -> 
      lunion (free_vars h) (free_vars t)
  | TmProj(t1, t2) -> 
      free_vars t1
  (* | TmProj (t, TmVar x) -> 
      ( let rec iterate_record next = match next with
          | (TmRecord( TmRecVar(x', v), next')) ->
              if x' = x then free_vars v else iterate_record next'
          | (TmRecVar( x', v)) -> 
              if x' = x then free_vars v else raise (Index_error "Index out of range")
          | _ -> raise (Type_error "Wrong index type")
        in iterate_record t )
  | TmProj(t,n) -> 
      ( match (t,n) with
          | (TmPair (t1, t2), TmSucc(TmZero)) ->
              free_vars t1
          | (TmPair (t1, t2), TmSucc(TmSucc(TmZero))) -> 
              free_vars t2
          | (_,_) -> []) *)
  | TmRecVar(x, v) -> 
      free_vars v
  | TmRecord(t, n) -> 
      lunion (free_vars t) (free_vars n) 
  | TmLZero n -> 
      free_vars n
  | TmSucc t ->
      free_vars t
  | TmPred t ->
      free_vars t
  | TmIsZero t ->
      free_vars t
  | TmVar s ->
      [s]
  | TmAbs (s, _, t) ->
      ldif (free_vars t) [s]
  | TmApp (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
  | TmLet (s, t1, t2) ->
      lunion (ldif (free_vars t2) [s]) (free_vars t1)
  | TmLetRec (s, _, t1, t2) ->
      lunion (ldif (free_vars t2) [s]) (free_vars t1)
;;

let rec fresh_name x l =
  if not (List.mem x l) then x else fresh_name (x ^ "'") l
;;

let rec subst x s tm ctxT = match tm with
    TmTrue | TmFalse ->
      tm
  | TmIf (t1, t2, t3) ->
      TmIf (subst x s t1 ctxT, subst x s t2 ctxT, subst x s t3 ctxT)
  | TmChar _ | TmString _ ->
      tm 
  | TmZero ->
      TmZero
  | TmLZero n -> 
      TmLZero (subst x s n ctxT)
  | TmReal(n1, n2) -> 
      TmReal ((subst x s n1 ctxT), (subst x s n2 ctxT))
  | TmSucc t ->
      TmSucc (subst x s t ctxT)
  | TmPred t ->
      TmPred (subst x s t ctxT)
  | TmIsZero t ->
      TmIsZero (subst x s t ctxT)
  | TmVar y ->
      if y = x then s else tm
  | TmAbs (y, tyY, t) -> 
      if y = x then tm
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmAbs (y, tyY, subst x s t ctxT)
           else let z = fresh_name y (free_vars t @ fvs) in
                TmAbs (z, tyY, subst x s (subst y (TmVar z) t ctxT) ctxT)  
  
  | TmLNil ty ->
      TmLNil ty
  | TmLIsNil(t) -> 
      TmLIsNil(subst x s t ctxT)
  | TmLHead(t) ->
      TmLHead(subst x s t ctxT)
  | TmLTail(t) -> 
      TmLTail(subst x s t ctxT)
  | TmLCons(t1, t2) -> 
      TmLCons(subst x s t1 ctxT, subst x s t2 ctxT)
  | TmPair (t1, t2) -> 
      TmPair (subst x s t1 ctxT, subst x s t2 ctxT)
  | TmTuple (t1, next) -> 
      TmTuple (subst x s t1 ctxT, subst x s next ctxT)
  | TmRecVar(x, v) -> 
      TmRecVar(x, subst x s v ctxT)
  | TmRecord(r, next) -> 
      TmRecord(subst x s r ctxT, subst x s next ctxT)
  | TmProj (t, n) -> 
      TmProj (subst x s t ctxT, subst x s n ctxT)
  | TmApp (t1, t2) ->
      TmApp (subst x s t1 ctxT, subst x s t2 ctxT)
  | TmLet (y, t1, t2) ->
      if y = x then TmLet (y, subst x s t1 ctxT, t2)
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmLet (y, subst x s t1 ctxT, subst x s t2 ctxT)
           else let z = fresh_name y (free_vars t2 @ fvs) in
                TmLet (z, subst x s t1 ctxT, subst x s (subst y (TmVar z) t2 ctxT) ctxT)
                
  | TmLetRec (y, _, t1, t2) ->
      if y = x then TmLet (y, subst x s t1 ctxT, t2)
      else let fvs = free_vars s in
          if not (List.mem y fvs)
          then TmLet (y, subst x s t1 ctxT, subst x s t2 ctxT)
          else let z = fresh_name y (free_vars t2 @ fvs) in
                TmLet (z, subst x s t1 ctxT, subst x s (subst y (TmVar z) t2 ctxT) ctxT)
;;
      


let fix x t1 ctx' = subst x t1 t1 ctx'
;;

let rec eval1 tm ctx dbg = 

  if dbg then 
    print_endline (string_of_term tm); 

  match tm with
    (* E-IfTrue *)
    TmIf (TmTrue, t2, _) ->
      t2

    (* E-IfFalse *)
  | TmIf (TmFalse, _, t3) ->
      t3

    (* E-If *)
  | TmIf (t1, t2, t3) ->
      let t1' = eval1 t1 ctx dbg in
        TmIf (t1', t2, t3)

    (* E-Succ *)
  | TmSucc t1 ->
      let t1' = eval1 t1 ctx dbg in
        TmSucc t1'
  
  | TmLZero n -> 
      let n' = eval1 n ctx dbg in 
        TmLZero n'
    (* E-Float*)
  | TmReal (n1, n2) -> 
      let (n1', n2') = (eval1 n1 ctx dbg, eval1 n2 ctx dbg) in
        TmReal (n1', n2')

    (* E-PredZero *)
  | TmPred TmZero ->
      TmZero

    (* E-PredSucc *)
  | TmPred (TmSucc nv1) when isnumericval nv1 ->
      nv1

    (* E-Pred *)
  | TmPred t1 ->
      let t1' = eval1 t1 ctx dbg in
        TmPred t1'
  
  (* E-IszeroZero *)
  | TmIsZero TmZero ->
      TmTrue

    (* E-IszeroSucc *)
  | TmIsZero (TmSucc nv1) when isnumericval nv1 ->
      TmFalse

    (* E-Iszero *)
  | TmIsZero t1 ->
      let t1' = eval1 t1 ctx dbg in
        TmIsZero t1'
  
  | TmPair(t1, t2) when not (isval t1 && isval t2) ->
      let t1' = eval1 t1 ctx dbg in
      let t2' = eval1 t2 ctx dbg in 
        TmPair(t1', t2')

  | TmTuple (t1, next) when not (isval t1 && isval next) -> 
      let t1' = eval1 t1 ctx dbg in
      let next' = eval1 next ctx dbg in
        TmTuple(t1', next')

  | TmLIsNil (tm') when isval tm'-> 
      (match tm' with 
        | TmLNil _ -> 
            TmTrue
        | _ -> 
            TmFalse)

  | TmLIsNil (tm') -> 
      let tm'' = eval1 tm' ctx dbg in
        tm''
  
  | TmLHead (tm') when isval tm' ->
      (match tm' with 
        | TmLNil _ -> tm'
        | TmLCons(h, _) -> h
        | _ -> raise (Critical_error "Traying to eval tail operation over wrong type"))

  | TmLHead (tm') -> 
      let tm'' = eval1 tm' ctx dbg in
        TmLHead (tm'')
  
  | TmLTail (tm') when isval tm' ->
      (match tm' with
        | TmLNil _ -> tm'
        | TmLCons(h, t) -> t
        | _ -> raise (Critical_error "Traying to eval tail operation over wrong type"))

  | TmLTail (tm') -> 
      let tm'' = eval1 tm' ctx dbg in
        TmLTail (tm'')
  
  | TmLCons (hh, tt) when isval hh  -> 
      let t' = eval1 tt ctx dbg in
        TmLCons(hh, t')

  | TmLCons (hh, tt) when not (isval hh) -> 
      let h' = eval1 hh ctx dbg in
        TmLCons(h', tt)

  (* Esto es del record no del recursivo *)
  | TmRecVar (x, v) -> 
      TmRecVar (x, eval1 v ctx dbg)

  | TmRecord (r1, next) -> 
      TmRecord( eval1 r1 ctx dbg, eval1 next ctx dbg)

  | TmProj (TmRecord (t,v), TmVar x) -> 
      (let rec iterate_record next = match next with
        | (TmRecord( TmRecVar(x', v), next')) ->
            if x' = x then v else iterate_record next'
        | (TmRecVar( x', v)) -> 
             if x' = x then v else raise (Index_error "Index out of range")
        | _ -> raise (Type_error "Wrong index type")
      in iterate_record (TmRecord (t,v)))
  
  | TmProj(t, n) when isval t ->
      (let rec iterateEval next it = match (next, it) with  
        | (TmTuple(e, _), TmSucc(TmZero)) -> 
            e 
        | (TmTuple(_, next'), TmSucc(it')) -> 
            iterateEval next' it' 
        | (TmPair(t1, t2), TmSucc(TmZero)) -> 
            t1
        | (TmPair(t1,t2),TmSucc(TmSucc(TmZero))) ->
            t2
        | _ -> raise NoRuleApplies
      in iterateEval t n)
  
  | TmProj(t, n) ->
      let t' = eval1 t ctx dbg in
      TmProj(t',n)
  
  | TmApp (TmAbs(x, _, t12), v2) when isval v2 ->
      subst x v2 t12 ctx

    (* E-App2: evaluate argument before applying function *)
  | TmApp (v1, t2) when isval v1 ->
      let t2' = eval1 t2 ctx dbg in
      TmApp (v1, t2')
  
    (* E-App1: evaluate function before argument *)
  | TmApp (t1, t2) ->
      let t1' = eval1 t1 ctx dbg in
      TmApp (t1', t2)

    (* E-LetV *)
  | TmLet (x, v1, t2) when isval v1 ->
      subst x v1 t2 ctx

    (* E-Let *)
  | TmLet(x, t1, t2) ->
      let t1' = eval1 t1 ctx dbg in
      TmLet (x, t1', t2) 

    (* E-Let *)
  | TmLetRec(x, ty , t1, t2) as tm ->
    addterm ctx x tm;
    let t2' = eval1 t2 ctx dbg in 
    let t1' = subst x t1 t2' ctx in  
      eval1 t1' ctx dbg

  | TmVar x ->
      (try 
      match (getterm ctx x) with
        | TmLetRec (_,_,t1,_) -> t1
        | _ as trm -> trm
    with Not_found -> raise NoRuleApplies)

  | _ ->
      raise NoRuleApplies
;;

let rec eval tm ctx dbg =
  if dbg then 
      print_endline ("\nTOKENS:\n"^(string_debug_of_term tm)^"\n\nEVAL:"); 
      (* print_endline ("EVAL:"); *)
  try
    let tm' = eval1 tm ctx dbg in
      eval tm' ctx dbg
  with
    NoRuleApplies -> tm
;;

let print_ctx ctx =
  let (tml, tyl) = !ctx 
    in let rec print_term_list = function 
        [] -> ()
      | (s,e)::l -> 
        print_string s; 
        print_string " = "; 
        print_string (string_of_term e) ; 
        print_endline " " ; 
        print_term_list l
    
      in let rec print_ty_list = function 
        [] -> ()
      | (s,e)::l -> 
        print_string s; 
        print_string" : "; 
        print_string (string_of_ty e) ; 
        print_endline " " ; 
        print_ty_list l
  in 
    print_endline "Context terms: ";
    print_term_list tml; 
    print_endline "Context Types: ";
    print_ty_list tyl
;;

let eval_exec tm ctx dbg = 
  let _ = typeof ctx tm in 
  let tm' = (eval tm ctx dbg) in 
  let ty' = typeof ctx tm' in 
    (None, tm', ty')
;;

let exec ctx inst dbg = 
  let (s'', tm'', ty'') = match inst with
    (* | Eval(TmLetRec(x,y,z,t) as tm) -> 
        addterm ctx x tm;
        eval_exec tm ctx dbg *)
    | Eval(tm) -> 
        eval_exec tm ctx dbg
    | Asgn(s,(TmLetRec(x,y,z,t) as tm)) -> 
        addterm ctx x tm;
        let (_, tm', ty') = eval_exec tm ctx dbg in
          addtype ctx s ty';
          addterm ctx s tm';
          (Some s, tm', ty')
    | Asgn(s,tm) -> 
      let (_, tm', ty') = eval_exec tm ctx dbg in
        addtype ctx s ty';
        addterm ctx s tm';
        (Some s, tm',ty')
  in match (s'') with 
      | Some s ->     print_endline (s^" = "^string_of_term tm'' ^ " : " ^ string_of_ty ty'')
      | None ->     print_endline (string_of_term tm'' ^" : " ^ string_of_ty ty'');
  if dbg then
      print_ctx ctx
;;
