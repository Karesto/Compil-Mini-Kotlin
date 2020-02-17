(* Syntaxe abstraite pour mini-Kotlin*)

(* expressions entières *)
type ident = string

type unop =
  | Unot (* !e *)
  | Uneg (* -e *)

type location = Lexing.position * Lexing.position

type binop =
  | Add | Sub | Mul | Div | Mod                   (* + - * / % *)
  | Eeeq | Neeq | Eeq | Neq | Lt | Le | Gt | Ge  (* === !== == != < <= > >= *)
  | And | Or                                         (* && || *)

type _type =
  | Ttype  of ident * _type list
  | Tnull
  | Twhat  of _type
  | Tarot  of _type list * _type

type constant =
  | Cthis
  | Cnull
  | Cbool   of bool
  | Cstring of string
  | Cint    of int32

type param = Par of ident * _type * location

type paramc =
  |Parvar of ident * _type * location
  |Parval of ident * _type * location

type expression =
     {
       corp : corps;
       loc  : location
     }

and corps =
  | Ecst    of constant
  | Epar    of expression
  | Eacc    of acces
  | Eeg     of acces * expression
  | Ecall   of ident * (expression list)
  | Ebinop  of binop * expression * expression
  | Eunop   of unop * expression
  | Eif     of expression * (blocexpr) * ((blocexpr) option)
  | Ewhile  of expression * (blocexpr)
  | Ereturn of expression option
  | Efun    of (param list) * _type option * bloc


and blocexpr =
  | B of bloc | E of expression

and acces =
  | Aident of ident * location
  | Adot of expression * ident * location
  | Awhat of expression * ident * location

and bloc = {blc : varexpr list ; loc : location}

and varexpr=
  |V  of var
  |E2 of expression

and var =
  |Var of ident * (_type option) * expression * location
  |Val of ident * (_type option) * expression * location

and _class = Cls of ident * ((ident list) option) * (paramc list) * (var list) * location

and decl =
  | Dvar of var
  | Dclass of _class
  | Dfun of func

and func=
  | Func of ((ident list) option) * ident * (param list) * (_type option) * bloc * location

type file = decl list


(* Types Nécéssaires plus tard pour le typeur*)


type typev =
  {
    typ   : _type;
    lvl   : int   ;
    mut   : bool  ;
    mutable quest_removable : bool;
  }

type typef =
  {
    typ   : _type;
    lvl   : int;
    idl   : ident list ;

  }

type typec =
  {
    lvl   : int;
    idl   : ident list ;
    params: paramc list;
    champs: (ident, _type) Hashtbl.t;
    mut_champs: (ident, bool) Hashtbl.t
  }


type val_id =
  |Fonc of typef
  |Vari of typev
  |Clas of typec
