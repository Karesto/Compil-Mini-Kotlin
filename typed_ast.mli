(* Syntaxe abstraite typée pour mini-Kotlin*)
open Ast
(* expressions entières *)

type typed_expression =
     {
       main : typed_corp;
       loc  : Ast.location;
       etyp  : _type
     }

and typed_corp =
  | TEcst    of constant
  | TEacc    of typed_acces
  | TEeg     of typed_acces * typed_expression
  | TEcall   of ident * (typed_expression list)
  | TEbinop  of binop * typed_expression * typed_expression
  | TEunop   of unop  * typed_expression
  | TEif     of typed_expression * (typed_blocexpr) * ((typed_blocexpr) option)
  | TEwhile  of typed_expression * (typed_blocexpr)
  | TEreturn of typed_expression option
  | TEfun    of (param list) * _type option * typed_bloc


and typed_acces =
  | TAident of ident * location * _type
  | TAdot   of typed_expression * ident * location * _type
  | TAwhat  of typed_expression * ident * location * _type

and typed_blocexpr =
  | TB of typed_bloc | TE of typed_expression


and typed_bloc = {
            blc : typed_varexpr list ;
            btyp : _type
            }

and typed_varexpr=
  | TV  of typed_var
  | TE2 of typed_expression

and typed_var =
  | TVar of ident * (_type option) * typed_expression * location * _type
  | TVal of ident * (_type option) * typed_expression * location * _type

and typed_func=
  | TFunc of ((ident list) option) * ident * (param list) * (_type option) * typed_bloc * location * _type

and typed_class = TCls of ident * ((ident list) option) * (paramc list) * (typed_var list) * location

and typed_decl =
  | TDvar   of typed_var
  | TDclass of typed_class
  | TDfun   of typed_func


type typed_file = typed_decl list
