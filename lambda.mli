
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

val emptyctx : context;;

val addterm : context -> string -> term -> unit;;
val getterm : context -> string -> term;;

val addtype : context -> string -> ty -> unit;;
val gettype : context -> string -> ty;;

val string_of_ty : ty -> string;;
val typeof : context -> term -> ty;;

val string_of_term : term -> string;;

val eval : term -> context -> bool -> term;;
val exec : context -> inst -> bool -> unit 


(* Exceptions *)
exception Critical_error of string;;
exception Index_error of string;;
exception NoRuleApplies;;
exception Type_error of string;;
exception Exit;;
