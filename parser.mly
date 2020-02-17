%{
  open Ast

%}

(*
Ceci est expérimental:
Comprendre les problèmes de Shift/reduce (cad relire le cours)
OU METTRE les locations
Shift reduce me daddy
Les commentaires séparateurs
Que veut dire nonassoc


--------------------------------------Questions ------------------------------
Class, le match est il nécéssaire?
*)
%token <int32>  INT
%token <string> STRING
%token <string> IDENT
%token FALSE TRUE
%token LPAR RPAR VIRG
%token IF ELSE WHILE RETURN
%token FUNC
%token ROBIN EQ
%token OR AND
%token PLUS MINUS PROD DIV MOD
%token EEQ NEQ SMALS SMALEQ BIGGS BIGGEQ
%token EEEQ NEEQ
%token EOF
%token CLASS DATA NULL THIS VAL VAR
%token BANG DOT NANI NANII
%token RACC LACC DDOT VDOT
%token UMINUS
(* L'ORDRE ? *)
%nonassoc IF
%nonassoc ELSE
%nonassoc WHILE RETURN
%right    EQ
%left     OR
%left     AND
%left     EEEQ NEEQ EEQ NEQ
%left     BIGGS BIGGEQ SMALS SMALEQ
%left     PLUS MINUS
%left     PROD DIV MOD
%right    UMINUS BANG                           (*MINUS UNAIRE ?*)
%left     DOT NANII
%right    ROBIN
%nonassoc NANI



/* Point d'entrée de la grammaire */
%start fichier
%type <Ast.file> fichier

%%

fichier:
    d=list(decl); EOF  {d};


decl:
    |v = var;VDOT     {Dvar(v)  }
    |c = _class       {Dclass(c)}
    |f = func         {Dfun(f)  }



/*-------------------------------------------VAR-------------------------------------------------*/
var:
  |VAR;s = IDENT;a=option(DDOT;t=_typp {t});EQ;e=expr
    {
      Var(s,a,e,($startpos, $endpos))
    }
  |VAL;s = IDENT;a=option(DDOT;t=_typp {t});EQ;e=expr
    {
      Val(s,a,e,($startpos, $endpos))
    }



/*-------------------------------------------CLASS------------------------------------------------*/
_class:
    |DATA;CLASS; s1=IDENT;a1 = option(SMALS;l1 = separated_nonempty_list(VIRG,IDENT);BIGGS {l1});
    LPAR;l2=separated_nonempty_list(VIRG,paramc);RPAR;v=varlistspe
    {

      Cls(s1,a1,l2,v,($startpos, $endpos))

    }


%inline varlistspe:
    |           {[]}
    |RACC;LACC                          {[]}
    |RACC;VDOT;LACC                     {[]}
    |RACC; l = prb_vdot2 ;LACC          {l}




prb_vdot2:
    |v=var                    {[v]}
    |v=var;VDOT               {[v]}
    |v=var;VDOT;vs=prb_vdot2  {v::vs}

/*-------------------------------------------FUNC-------------------------------------------------*/
func:
  |FUNC;a1 = option(SMALS;l = separated_nonempty_list(VIRG,IDENT);BIGGS {l}); s1=IDENT;
   LPAR;l =separated_list(VIRG,param);RPAR;a=option(DDOT;t=_typp {t});b=bloc
    {
      Func (a1,s1,l,a,b,($startpos, $endpos))
    }

/*-------------------------------------------BLOC-------------------------------------------------*/
varexprlist:

    |v=varexpr                      {[v]}
    |v=varexpr;VDOT                 {[v]}
    |v=varexpr;VDOT;vs=varexprlist  {v::vs}

bloc:
    |RACC;LACC
    {
      {blc = [] ; loc = ($startpos, $endpos)}
    }
    |RACC;VDOT;LACC
    {
      {blc = [] ; loc = ($startpos, $endpos)}
    }
    |RACC; l = varexprlist ;LACC
    {
      {blc = l ; loc = ($startpos, $endpos)}
    }


/*-------------------------------------------PARAM------------------------------------------------*/

varexpr:
    |v=var   {V(v)}
    |e=expr  {E2(e)}


/*-------------------------------------------PARAM------------------------------------------------*/
expr:
/* On gère les constantes */
|i = INT        (*dépassement entiers ?--------------------------*)
    {
      {corp = Ecst(Cint(i))     ; loc = ($startpos, $endpos)}
    }
|TRUE
    {
      {corp = Ecst(Cbool(true)) ; loc = ($startpos, $endpos)}
    }
|FALSE
    {
      {corp = Ecst(Cbool(false)); loc = ($startpos, $endpos)}
  }
|a = STRING
    {
      {corp = Ecst(Cstring(a))  ; loc = ($startpos, $endpos)}
    }
|THIS
    {
      {corp = Ecst(Cthis)       ; loc = ($startpos, $endpos)}
    }
|NULL
    {
      {corp = Ecst(Cnull)       ; loc = ($startpos, $endpos)}
    }

/*Les Parenthèses dans des expr*/
|LPAR; e = expr; RPAR
    {e}
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ACCES~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
|a = acces
    {
      {corp = Eacc(a)         ; loc = ($startpos, $endpos)}
    }

|a = acces;EQ;e=expr
    {
      {corp = Eeg(a,e)         ; loc = ($startpos, $endpos)}
    }

|s = IDENT; LPAR;l = separated_list(VIRG, expr); RPAR
    {
      {corp = Ecall(s,l)       ; loc = ($startpos, $endpos)}
    }

/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~Mono-Opérateurs~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
|BANG ;e=expr
    {
      {corp = Eunop(Unot,e)      ;loc = ($startpos, $endpos)}
    }

|MINUS;e=expr
    {
      {corp = Eunop(Uneg,e)     ; loc = ($startpos, $endpos)}
    }
    %prec UMINUS

|e1=expr; o = binop; e2=expr
    {
      {corp = Ebinop(o,e1,e2)   ; loc = ($startpos, $endpos)}
    }

/*Pourquoi séparer les ifs ?????*/
|IF;LPAR;e=expr;RPAR;b1=blocexpr
    {
      {corp = Eif(e,b1,None)    ; loc = ($startpos, $endpos)}
    }
    %prec IF

|IF;LPAR;e=expr;RPAR;b1=blocexpr;ELSE;b2=blocexpr
    {
      {corp = Eif(e,b1,Some b2) ; loc = ($startpos, $endpos)}
    }

|WHILE;LPAR;e=expr;RPAR;b=blocexpr      %prec WHILE
    {
      {corp = Ewhile (e,b)      ; loc = ($startpos, $endpos)}
    }

|RETURN;e=expr
    {
      {corp = Ereturn(Some e)   ; loc = ($startpos, $endpos)}
    }
    %prec RETURN

|RETURN;
    {
      {corp = Ereturn(None)     ; loc = ($startpos, $endpos)}
    }

|FUNC;LPAR;l=separated_list(VIRG,param);RPAR;t=option(DDOT;t=_typp {t});b=bloc
    {
      {corp = Efun(l,t,b)       ; loc = ($startpos, $endpos)}
    }





%inline binop:
|EEEQ   {Eeeq}
|NEEQ   {Neeq}
|EEQ    {Eeq }
|NEQ    {Neq }
|SMALS  {Lt  }
|SMALEQ {Le  }
|BIGGS  {Gt  }
|BIGGEQ {Ge  }
|PLUS   {Add }
|MINUS  {Sub }
|PROD   {Mul }
|DIV    {Div }
|MOD    {Mod }
|AND    {And }
|OR     {Or  }
/*
is this ok ?
*/
%inline blocexpr:
|s = expr   {E(s)}
|b = bloc   {B(b)}



/*-------------------------------------------PARAM-----------------------------------------------*/

_typp:
|s = IDENT;SMALS;l = separated_nonempty_list(VIRG,_typp);BIGGS
    {
      Ttype (s,l)
    }
|s = IDENT
    {
      Ttype (s,[])
    }
|t = _typp;nonempty_list(NANI)
    {
      Twhat(t)
    }

|LPAR;t=_typp;RPAR
    {
      t
    }
|LPAR;RPAR;ROBIN;t=_typp
    {
      Tarot([],t)
    }
|LPAR;t1=_typp;RPAR;ROBIN;t=_typp
    {
      Tarot([t1],t)
    }
|LPAR;tf=_typp;VIRG;tl=separated_nonempty_list(VIRG,_typp);RPAR;ROBIN;t=_typp
    {
      Tarot(tf::tl,t)
    }


/*-------------------------------------------PARAM-----------------------------------------------*/
param:
|s=IDENT;DDOT;t=_typp
    {
      Par(s,t,($startpos, $endpos))
    }


/*-------------------------------------------PARAM-----------------------------------------------*/
paramc:
|VAR;s=IDENT;DDOT;t=_typp
    {
      Parvar(s,t,($startpos, $endpos))
    }
|VAL;s=IDENT;DDOT;t=_typp
    {
      Parval(s,t,($startpos, $endpos))
    }


/*-------------------------------------------PARAM-----------------------------------------------*/
acces:
|s = IDENT
    {
      Aident(s,($startpos, $endpos))
    }
|e=expr;DOT;s=IDENT
    {
      Adot(e,s,($startpos, $endpos))
    }
|e=expr;NANII;s=IDENT
    {
      Awhat(e,s,($startpos, $endpos))
    }
