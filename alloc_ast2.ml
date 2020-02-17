open Ast
open Typed_ast


module Sset = Set.Make(struct type t = string let compare = compare end)


type allocated_expression =
     {
       amain : allocated_corp;
       aloc    : Ast.location;
       atyp   : _type
     }

and allocated_corp =
  | AEcst    of constant
  | AEacc    of allocated_acces
  | AEeg     of allocated_acces * allocated_expression
  | AEcall   of ident * (allocated_expression list)
  | AEbinop  of binop * allocated_expression * allocated_expression
  | AEunop   of unop  * allocated_expression
  | AEif     of allocated_expression * (allocated_blocexpr) * ((allocated_blocexpr) option)
  | AEwhile  of allocated_expression * (allocated_blocexpr)
  | AEreturn of allocated_expression option
  | AElam    of int * (allocated_expression list)
  | AEfun    of (param list) * _type option * allocated_bloc *int* ((string, int*int) Hashtbl.t)


and allocated_acces =
  | Glovar  of ident * location * _type
  | Locvar  of int   * location * _type
  | Clovar  of int
  | AAdot   of allocated_expression * ident * location * _type
  | AAwhat  of allocated_expression * ident * location * _type

and allocated_blocexpr =
  | AB of allocated_bloc | AE of allocated_expression


and allocated_bloc = {
            ablc : allocated_varexpr list ;
            abtyp : _type
            }

and allocated_varexpr=
  | AV  of allocated_var
  | AE2 of allocated_expression

and allocated_var =
  | AVar of ident * (_type option) * allocated_expression * location * _type * int
  | AVal of ident * (_type option) * allocated_expression * location * _type * int

(*
and allocated_func=
  | AFunc of ((ident list) option) * ident * (param list) * (_type option) * allocated_bloc * location * _type
*)

and allocated_func =
  | AFunc of ident * allocated_bloc

and allocated_class = ACls of ident * ((ident list) option) * (paramc list) * (allocated_var list) * location

and allocated_decl =
  | ADvar   of allocated_var   * int
  | ADclass of allocated_class * int
  | ADfun   of allocated_func  * int


type allocated_file = allocated_decl list
