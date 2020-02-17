open Format
open X86_64
open Ast
open Typed_ast
open Alloc_ast

(*

*)







(*                      Les précieux conseils de maxime
Pour une variable globale, elle sera sur le tas et pas sur la pile: Tu pourras l'appeler directement avec $x

---------étapes d'appel d'une fonction : -----------

Empiler les arguments
Faire call pour empiler l'adresse de retour
Empiler rbp
Décrémenter rsp



Le fichier main doit aussi etre modifié, une ofis qu'on aura les fonctions compiler et alloc fichier

*)





(* phase 1 : allocation des variables *)
(*Cette phase va permettre de savoir où se treouvent nos variables dans la pile quand on va compiler plus tard*)
(*Je fais comme dans le td*)
(*ça calcule "l'espace nécéssaire " pour faire chaque opération , le nombre de variables a poser*)

exception VarUndef of string

let (genv : (string, unit) Hashtbl.t) = Hashtbl.create 23 (*Ne sert à rien*)

module Smap = Map.Make(String)

type local_env = ident Smap.t

let strings = Hashtbl.create 23

let (fc : (string, bool) Hashtbl.t) = Hashtbl.create 23
let (cl : (string, string list) Hashtbl.t) = Hashtbl.create 23

(*Ne sert à rien*)
(*
On va avoir besoin de certaines fonctions pour savoir de combien on doit dépiler rsp (la taille que prend le calcul du bloc d'une fonction)
C'est ce qu'on a fait en TD10 mais en plus complet quoi
*)

(*
On suppose qu'on est dansle corps d'une fonction avec next qui indique où on se trouve dans le monde

Ce serait bien que tu modifies ce qui est écrit pour que ça redevienne des allocated_expression
C'est pas très dur mais voila je ne sais pas pourquoi je n'ai pas fait ça dès le début

Hésite pas a créer d'autres alloc comme pour blocexpr par exmple (ça va rester le meme schéma que le typeur a peu près)
ça ne veut pas dire copier coller car il y 'a des subtilités

*)
let full_e e new_e = {amain = new_e; aloc = e.loc ; atyp = e.etyp}



let rec free_var_expr expr =
   match expr.main with
   | TEcst    (c)           -> Sset.empty
   | TEacc    (eacc)        -> free_var_acc eacc
   | TEeg     (a,aex)       -> Sset.union (free_var_acc a)   (free_var_expr aex)
   | TEcall   (x,l)         -> List.fold_left (fun s x -> Sset.union s (free_var_expr x))  Sset.empty l
   | TEbinop  (op,e1,e2)    -> Sset.union (free_var_expr e1) (free_var_expr e2)
   | TEunop   (op,e)        -> free_var_expr e
   | TEif     (e,b,None)    -> Sset.union (free_var_blxpr b) (free_var_expr e)
   | TEif     (e,b,Some b2) -> Sset.union (Sset.union (free_var_blxpr b) (free_var_expr e)) (free_var_blxpr b2)
   | TEwhile  (e,b)         -> Sset.union (free_var_blxpr b) (free_var_expr e)
   | TEreturn None          -> Sset.empty
   | TEreturn (Some e)      -> free_var_expr e
   | TEfun    (p,t,b)       -> free_var_bloc b

and free_var_acc acc =
   match acc with
   |TAident (x,l,t)   -> Sset.singleton x
   |TAdot   (e,i,l,t) -> free_var_expr  e
   |TAwhat  (e,i,l,t) -> free_var_expr  e


and free_var_bloc b  =
   let rec trait l s =
      match l with
      | []      -> s
      | (TE2 e)::q -> trait q (free_var_expr e)
      | (TV  v)::q -> let sets = trait q s in
                      let x =
                        match v with
                        |TVar (name,_,_,_,_)
                        |TVal (name,_,_,_,_) -> name
                      in
                      Sset.remove x sets
   in
   trait b.blc Sset.empty

and free_var_blxpr b =
   match b with
   |TB tb -> free_var_bloc tb
   |TE te -> free_var_expr te

(*Var free end*)



let rec extract_id_prmclist l =
   (*
   entrée: liste de param_c
   sortie: liste de leur id,loc
   *)
   match l with
   |Parvar(x,_,_)::q |Parval(x,_,_)::q -> x::extract_id_prmclist q
   |[]            -> []

let rec alloc_expr next env expr =
  match expr.main with
  |TEcst c ->
    full_e expr (AEcst c), next

  |TEbinop (b,e1,e2) ->
    let ae1, next1 = alloc_expr next env e1 in
    let ae2, next2 = alloc_expr next env e2 in
    full_e expr (AEbinop(b,ae1,ae2)), max next1 next2

  |TEunop (u, e) ->
    let ae, next = alloc_expr next env e in
    full_e expr (AEunop(u, ae)), next

  |TEacc acc ->
    let a,nexta = alloc_acc next env acc in
    full_e expr (AEacc(a)),nexta

  | TEeg (acc, e) ->
    let aa, nexta = alloc_acc  next env acc in
    let ae, nexte = alloc_expr next env e   in
    full_e expr (AEeg(aa,ae)), max nexta nexte
  | TEif (e, TB bl, None) ->
    let ae, nexte = alloc_expr next env e in
    let ab, nextb = alloc_bloc next env bl in
    full_e expr (AEif(ae, AB ab, None)), max nexte nextb

  | TEif     (e,blxpr,None)             ->
     let ae ,nexte   = alloc_expr     next env e     in
     let ab ,nextb   = alloc_blocexpr next env blxpr in
     full_e expr (AEif(ae,ab,None)), max nexte nextb

  |TEif(e, TB bl, Some (TB bl2)) ->
    let ae, nexte = alloc_expr next env e in
    let ab1, nextb1 = alloc_bloc next env bl in
    let ab2, nextb2 = alloc_bloc next env bl2 in
    full_e expr (AEif(ae, AB ab1, Some (AB ab2))), max nexte (max nextb1 nextb2)

  | TEif     (e,blxpr,Some blxpr2)      ->
     let ae  ,nexte  = alloc_expr     next env e      in
     let ab1 ,nextb1 = alloc_blocexpr next env blxpr  in
     let ab2 ,nextb2 = alloc_blocexpr next env blxpr2 in
     full_e expr (AEif(ae,ab1,Some ab2)), max nexte (max nextb1 nextb2)

  | TEwhile  (e,blxpr)                  ->
     let ae ,nexte = alloc_expr     next env e     in
     let ab ,nextb = alloc_blocexpr next env blxpr in
     full_e expr (AEwhile(ae,ab)), max nexte nextb

  | TEreturn None                        ->
      full_e expr (AEreturn None), next

  | TEreturn (Some a)                    ->
     let ae ,nexte = alloc_expr next env a    in
     full_e expr (AEreturn (Some ae)), nexte

   (*
   Apparamanet on a besoin d'un 4 ème paramètre ici
   Maxime pense qu'il faudra l'ajouter plus tard
   On compile les paramètres dans l'ordre inverse ? (enfin on les met dans la pile dans l'ordre inverse pour le moment)
   *)
   |TEcall(x ,  l) ->
     let l, fpmax =
      List.fold_left
      (fun (l, fpmax) e ->
         let e, fpmax' = alloc_expr next env e in
         e::l, max fpmax fpmax')([], next) l
     in
     full_e expr (AEcall ("f"^x, List.rev l)), fpmax

   | TEfun    (pl,a,bloc)->
      let l = List.rev (List.map (function Ast.Par (x, _, _) -> x) pl) in
      let env, next =
        List.fold_right
          (fun x (env, next) ->
            let next = next + 8 in
            Smap.add x next env, next)
          l  (Smap.empty, 8)
      in
      let ab, nextb = alloc_bloc next env bloc in
      let s = free_var_bloc bloc in
      full_e expr (AEfun(pl,a,ab,s)), nextb

and alloc_acc next env acc =
   match acc with
   |TAident (x,l,t)   -> (try Locvar (Smap.find x env,l,t),next with |_ -> Glovar(x,l,t),next)
   |TAdot   (a,x,l,t) -> (*Trouver x se fera plus tard apparament*)
                         let aa, nexta = alloc_expr next env a in
                         AAdot(aa,x,l,t), nexta
   |TAwhat  (a,x,l,t) ->(*Trouver x se fera plus tard apparament et de voir si c'est null mais bon*)
                         let aa, nexta = alloc_expr next env a in
                         AAwhat(aa,x,l,t), nexta


and alloc_bloc next env bloc =
   let rec traitement next env blc =
   match blc with
   | [] -> [], next
   | (TE2 e)::q ->
    let e,  nexte = alloc_expr next env e in
    let bl, nextb = traitement next env q in
     (AE2 e)::bl, max nexte nextb
   | (TV v)::q ->  let v,n,nenv =
                  (match v with
                  | TVar (a,b,e,l,t)->
                  print_endline("made locvar "^a);
                  let ae, nexte = alloc_expr next env e in
                  AV (AVar(a,b,ae,l,t,next+8)),
                  nexte + 8,
                  Smap.add a (next+8) env

                  | TVal (a,b,e,l,t) ->
                  print_endline("made locvar "^a);
                  let ae, nexte = alloc_expr next env e in
                  AV (AVal(a,b,ae,l,t,next+8)),
                  nexte + 8,
                  Smap.add a (next+8) env
                  )in
                  let bl, nextb = traitement n nenv q in
                  v::bl, max n nextb

   in
   let vxprl,next= traitement next env bloc.blc in
   {ablc = vxprl; abtyp = bloc.btyp}, next


and alloc_blocexpr next env blxpr =
  print_endline("started alloc_blocexpr");
  match blxpr with
  |TB b ->
      print_endline("it's a bloc");
     let ab, nextb = alloc_bloc next env b in AB (ab), nextb
  |TE e ->
     let ae, nexte = alloc_expr next env e in AE (ae), nexte


let alloc_vdec v env next=
    match v with
    | TVar (a,b,e,l,t) -> Hashtbl.replace genv a (); let ae, nexte = alloc_expr next env e in
                           AVar(a,b,ae,l,t,0),nexte
    | TVal (a,b,e,l,t) -> Hashtbl.replace genv a (); let ae, nexte = alloc_expr next env e in
                           AVal(a,b,ae,l,t,0),nexte
let rec traite_vlist l env next=
   match l with
    | [] -> [], next
    | v::q ->  let v,n,nenv =
                   (match v with
                   | TVar (a,b,e,l,t)->
                   let ae, nexte = alloc_expr next env e in
                   AVar(a,b,ae,l,t,next+8),
                   nexte + 8,
                   Smap.add a (next+8) env

                   | TVal (a,b,e,l,t) ->
                   let ae, nexte = alloc_expr next env e in
                   AVal(a,b,ae,l,t,next+8),
                   nexte + 8,
                   Smap.add a (next+8) env
                   )
                   in
                   let bl, nextb = traite_vlist q nenv (next+8) in
                   v::bl, max n nextb


let alloc_decl decl =
    match decl with
    |TDfun (TFunc(a, f, pl, _, bl, _,_)) ->
          let l = List.map (function Ast.Par (x, _, _) -> x) pl in
          let env, next =
            List.fold_right
              (fun x (env, next) ->
                Smap.add x (-next - 8) env, next + 8)
              l  (Smap.empty, 8)
          in
          let bl, fpmax = alloc_bloc 0 env bl in
          ADfun (AFunc ("f"^f, bl), fpmax)

    | TDclass (TCls (a,b,prmcl,varl,l)) ->
         (*
         ici je suppose que c'est comme ça que ça marche:
         c'est une suite de déclarations de variable la classe.
         Je vais donc supposer que ça va compiler comme ça
         tu vas empiler les arguments sur la pile
         tu vas évaluer la première expression
         tu empile ensuite cette la valeur de cette dernière
         et tu continues
         J'ai besoin de que ce soit comme cela pour que tes "appels" soient au bons endroits.
         (car si jamais une variable declarée après utilise une déclarée avant, c'est un peu la mort)
         donc comme ça tu saura où il faut chercher après le 0, ce sera plus long en execution
         mais plus simple à coder
         *)
          let env  ,next  = List.fold_left (fun (s,n) x-> Smap.add x (n+8) s,n+8) (Smap.empty,0) (extract_id_prmclist prmcl) in
          let vlist,nextv = traite_vlist varl env next in
          ADclass(ACls(a,b,prmcl,vlist,l),nextv)


    | TDvar   v                  ->
          let a,b = alloc_vdec v Smap.empty 0 in
          ADvar (a,b)







let alloc = List.map alloc_decl
(*
Si tu bloques à un moment, fait autre chose, c'est à dire la partie 2, qui va prendre ce nouveau type et qui va faire le code assembleur
Tu utiliseras le x86_64, je ne sais pas lequel mais je penses le .ml
Inspire toi du TD10 et du compilateur rust (valable aussi pour alloc expr je crois)
J'essayerai d'ajouter d'autres liens d'inspiration ici :
Si tu sais faire du rust : https://github.com/Sakarah/rustception/blob/master/src/allocator.rs
Celui la est en Caml mais je le trouve pas trop clair (plus clair que le rust) : https://github.com/Ekdohibs/pscala/blob/master/code_production.ml
Y'a des commentaires sur celui la mais je ne vois pas les alloc : https://github.com/cyber-meow/MiniAda_compiler/blob/master/produce_code.ml
*)





let rec lindex x = function
  |[] -> assert false
  |t::q when t = x -> 0
  |t::q -> 1 + (lindex x q)

let and_counter    = ref (-1)
let orr_counter    = ref (-1)
let iff_counter    = ref (-1)
let whi_counter    = ref (-1)
let wah_counter    = ref (-1)
let cur_f = ref ""
let act () = string_of_int  !and_counter
let oct () = string_of_int  !orr_counter
let ict () = string_of_int  !iff_counter
let wct () = string_of_int  !whi_counter
let wah () = string_of_int  !wah_counter
let compare setter =
        movq   (imm 0)   !%r9  ++
        cmpq   !%rbx !%rax ++
        setter !%r9b ++
        pushq  !%r9



let popn  n = addq (imm n) !%rsp
let pushn n = subq (imm n) !%rsp

let rec compile_expr e = match e.amain with
   |AEcst (c) ->
   (match c with
   |Cint(i)  ->pushq (imm (Int32.to_int i))
   |Cstring s ->
    if not (Hashtbl.mem strings s) then (Hashtbl.add strings s ("s"^(string_of_int (Hashtbl.length strings))));
    pushq (ilab (Hashtbl.find strings s))
   |Cbool b -> if b then pushq (imm 1) else pushq (imm 0)
   |Cnull -> pushq (ilab "null")
   |Cthis -> pushq !%rdi
)
  |AEacc(Locvar(fp_x, _, _)) ->
     pushq (ind ~ofs:(-fp_x) rbp)

  |AEacc(AAdot(e, x, _, _)) ->
    let ec = (match e.atyp with |Ttype (c, _) -> c |_ -> assert false) in
    let fp_x = 8*(lindex x (Hashtbl.find cl ec)) in

    compile_expr e ++
    popq rdi ++
    pushq (ind ~ofs:fp_x rdi)

  |AEacc(AAwhat(e,x, _, _)) ->
    (match e.atyp with
      |Ttype(c, _) ->
        let fp_x = 8*(lindex x (Hashtbl.find cl c)) in
        compile_expr e ++
        popq rdi ++
        pushq (ind ~ofs:fp_x rdi)

      |Twhat(Ttype(c, _)) ->
        incr wah_counter;
        let w = wah() and fp_x = 8*(lindex x (Hashtbl.find cl c)) in
        compile_expr e ++
        popq rdi ++
        cmpq (ilab ("null")) !%rdi ++
        jz ("whan"^w) ++
        pushq (ind ~ofs:fp_x rdi) ++
        jmp ("what"^w) ++
        label ("whan"^w) ++
        pushq (ilab("null")) ++
        label ("what"^w)

      |Tnull ->
        compile_expr e

      |_ -> assert false

    )


  |AEacc(Glovar(x,_,_)) ->
    pushq (lab x)

  |AEeg(Locvar(fp_x, _, _), e) ->
    compile_expr e ++
    popq rax ++
    movq !%rax (ind ~ofs:(-fp_x) rbp)

  |AEeg(Glovar(x,_,_), e) ->
    compile_expr e ++
    popq rax ++ movq !%rax (lab x)

  |AEeg(AAdot(e, x, _, _), e2) ->
    let ec = (match e.atyp with |Ttype (c, _) -> c |_ -> assert false) in
    let fp_x = 8*(lindex x (Hashtbl.find cl ec)) in

    compile_expr e ++
    compile_expr e2 ++
    popq rax ++
    popq rdi ++
    movq !%rax (ind ~ofs:fp_x rdi)

  |AEeg(AAwhat(e, x, _, _), e2) ->
  compile_expr e ++
  compile_expr e2 ++
  popq rax ++
  popq rdi ++
  (match e.atyp with
    |Ttype(c, _) ->
      let fp_x = 8*(lindex x (Hashtbl.find cl c)) in
      movq !%rax (ind ~ofs:fp_x rdi)

    |Twhat(Ttype(c, _)) ->
      incr wah_counter;
      let w = wah() and fp_x = 8*(lindex x (Hashtbl.find cl c)) in

      cmpq (ilab ("null")) !%rdi ++
      jz ("what"^w) ++
      movq !%rax (ind ~ofs:fp_x rdi) ++
      label ("what"^w)

    |Tnull -> nop

    |_ -> assert false

  )

  |AEunop(o, e) ->
    compile_expr e ++
    popq rax ++
    (match o with
      |Unot -> movq (imm 1) !%rbx ++ notq !%rbx ++ notq !%rax ++ subq !%rbx !%rax
      |Uneg -> negq !%rax) ++
    pushq !%rax

    |AEbinop(And,e1,e2) ->
       incr and_counter;
       let a = act() in
       compile_expr e1                   ++
       popq  rbx                         ++
       testq (reg rbx) (reg rbx)         ++
       jz    ("and" ^ a)              ++
      pushq !%rbx ++
  	  compile_expr e2                   ++
  	  popq  rax                         ++
      popq rbx ++
  	  andq  (reg rax) (reg rbx)         ++
  	  label ("and" ^ a)             ++
      pushq !%rbx ++
  	  xorq  (reg rax) (reg rax)

    |AEbinop(Or,e1,e2) ->
       incr orr_counter;
       let o = oct() in
       compile_expr e1                   ++
       popq rbx                          ++
       testq (reg rbx) (reg rbx)         ++
       jnz    ("or" ^ o)             ++
      pushq !%rbx ++
  	  compile_expr e2                   ++
  	  popq  rax                         ++
      popq rbx ++
  	  orq  (reg rax) (reg rbx)         ++
  	  label ("or" ^ o)              ++
      pushq !%rbx ++
  	  xorq  (reg rax) (reg rax)




  |AEbinop(o, e1, e2) ->
    compile_expr e1 ++
    compile_expr e2 ++
    popq rbx ++ popq rax ++ xorq !%rdx !%rdx ++
    (match o with
      | Add -> addq !%rbx !%rax ++ pushq !%rax
      | Sub -> subq !%rbx !%rax ++ pushq !%rax
      | Mul -> imulq !%rbx !%rax ++ pushq !%rax
      | Div -> cqto ++ idivq !%rbx ++ pushq !%rax
      | Mod -> cqto ++ idivq !%rbx ++ pushq !%rdx
      | Eeq -> compare sete
      | Neq -> compare setne
      | Ge  -> compare setge
      | Le  -> compare setle
      | Gt  -> compare setg
      | Lt  -> compare setl
      | Eeeq -> movq (ind rbx) !%rbx ++ movq (ind rax) !%rax ++ compare sete
      | Neeq -> movq (ind rbx) !%rbx ++ movq (ind rax) !%rax ++ compare setne

 )

 |AEreturn (Some e) ->
   compile_expr e ++
   popq rax ++
   jmp ("end"^(!cur_f))

 |AEreturn none ->
   movq (ilab "null") !%rax ++
   jmp ("end"^(!cur_f))

  | AEif (e,b1, None)   ->
      incr iff_counter;
      let i = ict() in
      compile_expr e            ++
      popq rax                  ++
      testq (reg rax) (reg rax) ++
      jz    ("not_if" ^ i)      ++
      compile_blxpr b1          ++
      jmp   ("if" ^ i)          ++
      label ("not_if" ^ i)      ++
      nop                       ++
      label ("if" ^ i)

  | AEif   (e,b1,Some b2) ->
     incr iff_counter;
     let i = ict() in
     compile_expr e            ++
     popq rax                  ++
     testq (reg rax) (reg rax) ++
     jz    ("not_if" ^ i)      ++
     compile_blxpr b1          ++
     jmp   ("else" ^ i)        ++
     label ("not_if" ^ i)      ++
     compile_blxpr b2          ++
     label ("else" ^ i)

  |AEwhile(e,b) ->
    incr whi_counter;
    let w = wct() in
    print_endline("doing while "^w);
    let code1 =
    label ("while"^w) ++
    compile_expr e ++
    popq rax ++
    testq (reg rax) (reg rax)++
    jz ("end_while"^w) in
    print_endline("done with cond "^w);
    let code2 =
    compile_blxpr b ++
    jmp ("while"^w) ++
    label ("end_while"^w) in
    print_endline("finished while "^w);
    code1 ++ code2


  | AEcall ("fprint", [e]) when e.atyp = Ttype("Int", []) ->
    compile_expr e ++
    popq rdi       ++
    call "printint"




  (*| AEcall ("fprint", [e]) when e.atyp = Ttype("String",[]) ->
    compile_expr e   ++
    popq rdi         ++
    xorq !%rax !%rax ++
    call "printf"*)

  | AEcall ("fprint", [e]) when e.atyp = Ttype("Int", []) ->
    compile_expr e ++
    popq rdi       ++
    call "printint"

  | AEcall (s, l) when e.atyp = Ttype("Unit", []) ->
    List.fold_left (++) nop (List.map compile_expr l) ++
    call s ++
    popn ((List.length l)*8)

  | AEcall (s, l) ->
    if (Hashtbl.find fc s) then
    (let n = List.length l in
    List.fold_left (++) nop (List.map compile_expr l) ++
    call s ++
    popn (n*8)++
    pushq !%rax)
    else
   (print_endline("fail class call");assert false)


  | _ ->
    (match e.amain with
      |AEcst _ -> print_endline("failed on a constant")
      |AEacc(Glovar(x,_,_)) -> print_endline("failed on an glovar acc: "^x)
      |AEacc _ -> print_endline("failed on an access")
      |AEeg(Glovar(x,_,_), _) -> print_endline("failed on an glovar eg: "^x)
      |AEeg _ -> print_endline("failed on an eg")
      |AEcall _ -> print_endline("failed on a call")
      |AEbinop _ -> print_endline("failed on a binop")
      |AEunop _ -> print_endline("failed on an unop")
      |AEif _ -> print_endline("failed on an if")
      |AEwhile _ -> print_endline("failed on a while")
      |AEreturn _ -> print_endline("failed on a return")
      |AEfun _ -> print_endline("failed on a func")
    );
    print_endline(Typer.tp(e.atyp));assert false

(*and compile_bloc bl =
  let rec aux = function
  |[] -> pushq (imm 0)
  |[AE2 e]    -> compile_expr e
  |(AE2 e)::q -> compile_expr e ++ popq rax ++ aux q
  |(AV(AVar(_,_,e,_,_,n)))::q | (AV(AVal(_,_,e,_,_,n)))::q ->
    compile_expr e ++ popq rax ++ movq !%rax (ind ~ofs:(-n) rbp)
     ++ (aux q)
  in
  aux bl.ablc*)
  and compile_bloc bl =
    let rec aux = function
    |[] -> nop
    |(AE2 e)::q -> compile_expr e ++ aux q
    |(AV(AVar(_,_,e,_,_,n)))::q | (AV(AVal(_,_,e,_,_,n)))::q ->
      compile_expr e ++ popq rax ++ movq !%rax (ind ~ofs:(-n) rbp)
       ++ (aux q)
    in
    aux bl.ablc
and compile_blxpr = function
    | AB b -> compile_bloc b
    | AE e -> compile_expr e


let compile_decl (codevar, codefun, codemain) = function
  |ADfun (AFunc (f, bl), fpmax) ->
    Hashtbl.replace fc f true;
    cur_f := f;
    let code =
      label f ++
      pushq !%rbp ++
      movq !%rsp !%rbp ++ pushn fpmax ++
      compile_bloc bl ++ (*pushq (imm 0) ++*)
      label ("end"^f) ++
      popn fpmax ++ popq rbp ++ ret
    in
    codevar, code ++ codefun, codemain

  |ADvar(AVar(x, _, e, _, _, _), fpmax) | ADvar(AVal(x, _, e, _, _, _),fpmax) ->
    let code =
      pushn fpmax ++
      compile_expr e ++
      popq rax ++ movq !%rax (lab x) ++
      popn fpmax
    in
    codevar ++ code, codefun, codemain

  |ADclass(ACls(c,_,b,[],_), fpmax) ->
    Hashtbl.replace fc ("f"^c) true;
    Hashtbl.add cl c (List.rev (List.map (function Parvar(x,_,_) | Parval(x,_,_) -> x ) b) );
    let n = List.length b in
    let code = ref(
      label ("f"^c) ++
      pushq !%rbp ++
      movq !%rsp !%rbp ++
      pushn (fpmax) ++
      movq (imm (8*n)) !%rdi ++
      call "malloc" ++
      movq !%rax !%rdi)

    in
    for i = 0 to (n-1) do
      code := !code ++ pushq (ind ~ofs:(8*i+16) rbp) ++ popq rax ++ movq !%rax (ind ~ofs:(8*i) rdi)
    done;
    code := !code ++ movq !%rdi !%rax ++ popn (fpmax) ++ popq rbp ++ ret;
    codevar, !code ++ codefun, codemain

  |ADclass(ACls(c,_,b,vl,_), fpmax) ->
    Hashtbl.replace fc ("f"^c) true;
    Hashtbl.add cl c (
      (List.rev (List.map (function Parvar(x,_,_) | Parval(x,_,_) -> x ) b))
      @(List.map (function AVar(x,_,_,_,_,_) | AVal(x,_,_,_,_,_) -> x ) vl)
      );
    let nb = List.length b and nv = List.length vl and rvl = ref vl in
    let n = nb + nv in
    let code = ref(
      label ("f"^c) ++
      movq (imm (8*n)) !%rdi ++
      call "malloc" ++
      (*movq !%rax !%rdi*)
      movq !%rax !%rdi ++
      pushq !%rbp ++
      movq !%rsp !%rbp ++
      pushn (fpmax))

    in
    for i = 0 to (nb-1) do
      code := !code ++ pushq (ind ~ofs:(8*i+16) rbp) ++ popq rax ++ movq !%rax (ind ~ofs:(8*i) rdi)
    done;

    for i = nb to (n-1) do
      let e = (match List.hd !rvl with |AVar (_,_,e,_,_,_) | AVal(_,_,e,_,_,_) -> e) in
      code := !code ++ compile_expr e ++ popq rax ++ movq !%rax (ind ~ofs:(8*i) rdi);
      rvl := List.tl !rvl
    done;
    code := !code ++ movq !%rdi !%rax ++ popn (fpmax) ++ popq rbp ++ ret;
    codevar, !code ++ codefun, codemain

  | _ -> assert false

  let compile_program p ofile =
    let p = alloc p in
    let codevar, codefun, code = List.fold_left compile_decl (nop, nop, nop) p in
    let p =
      {
        text =
          globl "main" ++ label "main" ++
          codevar ++
          movq !%rsp !%rbp ++
          call "fmain" ++
          (*popn 8 ++*)
          xorq !%rax !%rax ++
          ret ++
          label "printint" ++
          movq !%rdi !%rsi ++
          movq (ilab ("pint")) !%rdi ++
          xorq !%rax !%rax ++
          call "printf" ++
          ret ++
          label "fprint" ++
          pushq !%rbp ++
          movq !%rsp !%rbp ++
          pushq (ind ~ofs:16 rbp) ++
          popq rdi ++
          cmpq (ilab ("null")) !%rdi ++
          jne ("notnull") ++
          movq (ilab ("pnull")) !%rdi ++
          label "notnull" ++
          xorq !%rax !%rax ++
          call "printf" ++
          popq rbp ++
          ret ++
          codefun;

        data =
          Hashtbl.fold (fun x _ l -> label x ++ dquad [2] ++ l) genv (
          Hashtbl.fold (fun s l c -> label l ++ string s ++ c) strings
          (label "pint" ++ string "%d" ++ label "pnull" ++ string "null" ++
          label "null" ++ dint [0]))
      }
    in
    let f = open_out ofile in
    let fmt = formatter_of_out_channel f in
    X86_64.print_program fmt p;
    fprintf fmt "@?";
    close_out f
