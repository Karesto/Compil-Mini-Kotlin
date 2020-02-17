open Typed_ast
open Ast
(*
---------------------A faire:---------------------------------
Enlever les prints
Relire les messages d'erreurs et enlever les chiffres de débog
Non nullité while et returns (check)
Factorisation des erreurs
Possibilité d'optimiser check_ret_expr (appel a type expr qui se répètera dans blocf et autres)
Ainsi que check_ret_blc


-----------------------------Indications-----------------------
Une erreur avec "keyword this" en tant que 2eme string ne printera que le premier string
les autres auront un expected type but type.
*)

(*Ai plus ou moins commencé classes, plus moins que plus par contre*)

exception Typing_error of Ast.location * string * string

let tint   = Ttype("Int",[])
let tbool  = Ttype("Boolean" ,[])
let tstri  = Ttype("String"  ,[])
let tunit  = Ttype("Unit" ,[])


let error_check res b_loc = if not(res) then raise (Typing_error (b_loc,"Return expected","Return expected")) else ()

let is_none = function
  |None   -> true
  |Some b -> false

let get = function
  |None   -> failwith "Get a None is not possible"
  |Some b -> b

let gere_option opt ifnone ifsome =
match opt with
  |None -> ifnone
  |Some a -> ifsome a

let rec is_sametyp t1 t2 =
    match t1,t2 with
    |Ttype (a1,l1),Ttype (a2,l2) -> (a1 = a2 && l1 = l2)
    |Twhat (t11)    ,Twhat (t21) -> is_sametyp t11 t21
    |Twhat(t), _ -> (t2= Tnull)||(is_sametyp t t2)
    (*|_ ,Twhat(t) -> (t1= Tnull)||(is_sametyp t1 t)*)
    |Tnull,Tnull -> true
    |Tarot(l1,t1),Tarot(l2,t2) -> (try (List.for_all2 is_sametyp l1 l2) && t1 = t2
                                  with _ -> false)
    |_,_ -> false

let rec tp a =
   (*
   Cette fonction permet de convertir un type en string
   *)
    match a with
    |Ttype(s,[])-> s
    |Ttype(s,tl)-> s ^ "[" ^ (string_of_typlist tl) ^ "]"
    |Tnull -> "Null"
    |Twhat t -> tp(t) ^"?"
    |Tarot (tl,t)->"(" ^ (string_of_typlist tl) ^ ")->" ^ tp(t)

and string_of_typlist t =
   match t with
   |[x]  -> tp(x)
   |[]   -> ""
   |x::q -> tp(x)^"," ^ string_of_typlist (q)


let rec removewhat t =
   match t with
   |Twhat tn -> tn
   |a -> a

let rec typ_castable  t1 t2 =
   (*
   t1 is declared type & t2 is expr type
   *)
    match t1,t2 with
    |Ttype (a1,l1),Ttype (a2,l2) -> (a1 = a2 && l1 = l2)
    |Twhat (t11)    ,Twhat (t21) -> typ_castable (removewhat t11) (removewhat t21)
    |Twhat(t), _ -> (t2= Tnull)||(typ_castable t t2)
    |_, Twhat(t) -> false
    |Tnull,Tnull -> true
    |Tarot(l1,t1),Tarot(l2,t2) -> (try (List.for_all2 typ_castable l1 l2) && t1 = t2
                                  with _ -> false)
    |_,_ -> false

let dump a = ()

let rec list_eq_length loc l1 l2 =
   (*
      Prend deux listes l1 l2 et une localisation
      l1 : Liste de paramètres
      l2 : liste d'arguments
      Ne fait rien si elles sont de taille égale.
      Lève une erreur (typing_erreur) à la location si elles sont de taille différente

   *)
   match l1,l2 with
   |x::t1,y::t2 -> list_eq_length loc t1 t2;
   |[],[]       -> ();
   |[],_        -> raise (Typing_error (loc, "Too many arguments"   , "keyword this"))
   |_,[]        -> raise (Typing_error (loc, "Not enought arguments", "keyword this"))




let print_bool b = print_endline(if b then "true" else "false")


let ret_typed e l t = {main=e;loc = l;etyp =t}

let extr_tblxpr = function
     | TB (tb) -> tb.btyp
     | TE (te) -> te.etyp

let extr_tacc = function
      | TAident (_,_,t)
      | TAdot   (_,_,_,t)
      | TAwhat  (_,_,_,t) -> t

let extr_tvarexpr = function
      | TE2 (e) -> e.etyp
      | TV (TVar (_,_,_,_,t))
      | TV (TVal (_,_,_,_,t)) -> t
















let lvl = ref 0
let is_var  env v  =
   if (Hashtbl.mem  (fst env) v) then
     begin
      let valeur = (Hashtbl.find (fst env) v) in
      match valeur with
      |Fonc t -> false
      |Vari t -> (t.lvl <= !lvl) && t.mut
      |Clas t -> false
     end
    else false

let is_val   env v  =
  if (Hashtbl.mem  (fst env) v) then
    begin
     let valeur = (Hashtbl.find (fst env) v) in
     match valeur with
     |Fonc t -> false
     |Vari t -> (t.lvl <= !lvl) && not(t.mut)
     |Clas t -> false
    end
   else false

let rec well_formed env = function
    |Tnull -> true
    |Twhat t -> well_formed env t
    |Tarot (tli, t) -> List.for_all (well_formed env) (t::tli)
    |Ttype (c, tli) -> try (List.for_all (well_formed env) tli) && (match Hashtbl.find (fst env) c with | Clas _ -> true | _ -> false)
                        with Not_found -> false

let var_type env v l=
  if (Hashtbl.mem  (fst env) v) then
    begin
     let valeur = (Hashtbl.find (fst env) v) in
     match valeur with
     |Fonc t -> raise (Typing_error (l,"Var","Function"))
     |Vari t -> (if (t.lvl <= !lvl) && t.mut then t.typ else raise (Typing_error (l,"Non_exist_id : "^v,"keyword this")))
     |Clas t -> raise (Typing_error (l,"Var","Class"))
    end
  else raise (Typing_error (l,"Non_exist_id "^v,"keyword this"))

let val_type env v l=
  if (Hashtbl.mem  (fst env) v) then
    begin
     let valeur = (Hashtbl.find (fst env) v) in
     match valeur with
     |Fonc t -> raise (Typing_error (l,"Val","Function"))
     |Vari t -> (if (t.lvl <= !lvl) && not(t.mut) then t.typ else raise (Typing_error (l,"Non_exist_id "^v,"keyword this")))
     |Clas t -> raise (Typing_error (l,"Val","Class"))
    end
  else raise (Typing_error (l,"Non_exist_id "^v,"keyword this"))


let vtype env v l =
  if (Hashtbl.mem  (fst env) v) then
    begin
     let valeur = (Hashtbl.find (fst env) v) in
     match valeur with
     |Fonc t -> raise (Typing_error (l,"Var","Function"))
     |Vari t -> (if (t.lvl <= !lvl) then t.typ else raise (Typing_error (l,"Non_exist_id "^v,"keyword this")))
     |Clas t -> raise (Typing_error (l,"Var","Class"))
    end
  else raise (Typing_error (l,"Non_exist_id "^v,"keyword this"))

let vtype_complet env v l =
     if (Hashtbl.mem  (fst env) v) then
       begin
        let valeur = (Hashtbl.find (fst env) v) in
        match valeur with
        |Fonc t -> raise (Typing_error (l,"Var","Function"))
        |Vari t -> (if (t.lvl <= !lvl) then t else raise (Typing_error (l,"Non_exist_id "^v,"keyword this")))
        |Clas t -> raise (Typing_error (l,"Var","Class"))
       end
     else raise (Typing_error (l,"Non_exist_id "^v,"keyword this"))



let is_fun   env v  =
  if (Hashtbl.mem  (fst env) v) then
    begin
     let valeur = (Hashtbl.find (fst env) v) in
     match valeur with
     |Fonc t -> (t.lvl <= !lvl)
     |Vari t -> (
                  match t.typ with
                  |Tarot(_,_) -> t.lvl <= !lvl
                  |_ -> false
                )
     |Clas t -> false
    end
   else false

let fun_type env v l =
   (*A changer Clast*)
  if (Hashtbl.mem  (fst env) v) then
    begin
     let valeur = (Hashtbl.find (fst env) v) in
     match valeur with
     |Fonc t -> (if (t.lvl <= !lvl) then t.typ else raise (Typing_error (l,"Non_exist_id "^v,"keyword this")))
     |Vari t -> if t.lvl <= !lvl then
                (
                  match t.typ with
                  |Tarot(_,_) -> t.typ
                  |_ -> raise (Typing_error (l,"Var/Val " ^ v ^  "  is not callable","keyword this"))
                )
                else raise (Typing_error (l,"Var/Val " ^ v ^  "  is not callable","keyword this"))
     |Clas t -> raise (Typing_error (l,"Class","Callable"))
    end
  else raise (Typing_error (l,"Non_exist_id "^v,"keyword this"))


let taken_id env x =
    if (Hashtbl.mem  (fst env) x) then
      begin
        let valeur = Hashtbl.find (fst env) x in
        match valeur with
        |Fonc t -> (t.lvl = !lvl)
        |Vari t -> (t.lvl = !lvl)
        |Clas t -> (t.lvl = !lvl)
      end
    else false

let add_var env x typ l=
    if (taken_id env x) then raise (Typing_error (l,"Ident taken","keyword this"))
    else Hashtbl.replace (fst env) x (Vari {typ= typ; lvl = !lvl ; mut = true ; quest_removable = false})


let add_val env x typ l=
    if (taken_id env x) then raise (Typing_error (l,"Ident taken","keyword this"))
    else Hashtbl.replace (fst env) x (Vari {typ= typ; lvl = !lvl ; mut = false ; quest_removable = false})

let add_fun env f typ idl l=
    if (taken_id env f) then raise (Typing_error (l,"Ident taken","keyword this"))
    else Hashtbl.replace (fst env) f (Fonc{typ= typ ; lvl = !lvl; idl=idl})

let add_class env c cl l=
    if (taken_id env c) then raise (Typing_error (l, "Ident taken", "keyword this"))
    else Hashtbl.replace (fst env) c cl

let add_param env = function
  |Par(x,t,l) -> add_val env x t l

let rec type_of_prmlist = function
  |[] -> []
  |Par(x,t,l)::q -> t::type_of_prmlist q


let copy_env env tr= (Hashtbl.copy (fst env), tr)


let loc_blexpr = function
    |B bl -> bl.loc
    |E e  -> e.loc

let rec compress = function
  | a :: (b :: _ as t) -> if a = b then compress (b::t) else (a :: compress t)
  | [] -> []
  | [a] -> [a]

let is_duplicate2 l =
   (*
   Dit si une liste contient des doublons; O(nlogn)
   *)
  let l1 = List.sort compare l in
  let l2 = compress l1 in
  not (List.length l1 = List.length l2)

let rec is_duplicate = function
  | [] -> false
  | t::q when List.mem t q -> false
  | t::q -> is_duplicate q

let rec extract_id_prmlist l =
   (*
   entrée: liste de params
   sortie: liste de leur id,loc
   *)
   match l with
   |Par(x,_,lo)::q -> (x,lo)::extract_id_prmlist q
   |[]            -> []

let rec extract_id_prmclist l =
   (*
   entrée: liste de param_c
   sortie: liste de leur id,loc
   *)
   match l with
   |Parvar(x,_,lo)::q |Parval(x,_,lo)::q -> (x,lo)::extract_id_prmclist q
   |[]            -> []

let rec extract_id_varllist l =
   (*
   entrée: liste de var/vals
   sortie: liste de leur id,loc
   *)
   match l with
   |Var(x,_,_,lo)::q |Val(x,_,_,lo)::q -> (x,lo)::extract_id_varllist q
   |[]            -> []

let is_duplicate_idents l =
   (*
   Crash si la liste contient un doublon, nous dit ou c'est
   Complexité : O(n) ?
   *)
   let h = Hashtbl.create 23 in
   List.iter
      (fun x -> if Hashtbl.mem h (fst x) then raise (Typing_error ((snd x), "Parameter " ^ (fst x) ^" is already mentionned", "keyword this"))
      else  Hashtbl.add h (fst x) true )
      l


let rec is_typ_wat t1 t2 =
   match t1,t2 with
   |Twhat(t),tn when t = tn -> true,1
   |tn,Twhat(t) when t = tn -> true,2
   |_,_ -> false,3



let rec whos_null env (e:Ast.expression)=
(*
   Cette fonction prend une expression supposée booléenne et renvoie
   l1 : liste des elements qui sont des ?, qui ne le sont plus si l'expression = true
   l2 : liste des elements qui sont des ?, qui ne ne sont plus si l'expression = false

   Attention : il faut lui passer un nouvel environnement car ça fait vraiment n'imp ?
   Je fais sans pour l'instaant car je crois qu'il n'y a pas de cas ou ça pose pb


*)
   match e.corp with

   | Epar    exp ->  whos_null env exp
   | Ebinop  (Eeeq ,e1,e2) -> (begin
          match e1.corp, e2.corp with
          |Ecst(Cnull),Eacc(Aident(x,l))
          |Eacc(Aident(x,l)),Ecst(Cnull) -> ([],[x,l])
          (* cas autre : string? === string par exemple *)
          |Eacc(Aident(x,l1)),Eacc(Aident(y,l2)) ->
                let t1,t2 = vtype env x l1,vtype env y l2 in
                let vbool,t = is_typ_wat t1 t2 in
                if vbool then
                   (
                      match t with
                      | 1 -> modifquestpos env x l1;([x,l1],[])
                      | 2 -> modifquestpos env y l2;([y,l2],[])
                      | _ ->  raise (Typing_error (e.loc,"this should never appear on your screen","keyword this"))
                   )
               else [],[]
          |_ -> [],[]
      end)
   | Ebinop  (Neeq ,e1,e2) ->
      begin
          match e1.corp, e2.corp with
          (* le cas de base avec null*)
          |Ecst(Cnull),Eacc(Aident(x,l))
          |Eacc(Aident(x,l)),Ecst(Cnull) -> modifquestpos env x l ;([x,l],[])
          | _ -> [],[]
      end

   | Ebinop  (And,e1,e2) ->
   (
      let l11,l12 = whos_null env e1
      and l21,l22 = whos_null env e2 in
      (l11@l21),(l12@l22)
   )
 (*On type quand même dans des cas bizarres où on bidouille des variables*)
   |_ ->(dump (type_expr env e));[],[]



and modifquestpos env x l =
   if (Hashtbl.mem  (fst env) x) then
     begin
     let valeur = (Hashtbl.find (fst env) x) in
     match valeur with
     |Fonc t -> raise (Typing_error (l,"Var/Val","Function"))
     |Vari t -> t.quest_removable <- true
     |Clas t -> raise (Typing_error (l,"Var/Val","Class"))
     end
    else raise (Typing_error (l,"Non_exist_id "^x,"keyword this"))

and modifquestneg env x l =
  if (Hashtbl.mem  (fst env) x) then
    begin
    let valeur = (Hashtbl.find (fst env) x) in
    match valeur with
    |Fonc t -> raise (Typing_error (l,"Var/Val","Function"))
    |Vari t -> t.quest_removable <- false
    |Clas t -> raise (Typing_error (l,"Var/Val","Class"))
    end
   else raise (Typing_error (l,"Non_exist_id "^x,"keyword this"))





and type_expr env e =
  match e.corp with
  | Ecst    c   -> ret_typed (TEcst c) e.loc (type_const env c e.loc)
  | Epar    exp -> (type_expr env exp)
  | Ebinop  (o,e1,e2) ->  let te1,te2, t = type_binop env o e1 e2 in
                          ret_typed (TEbinop (o,te1,te2)) e.loc t
  | Eunop   (eup,e) -> let te, t = type_unop env (eup,e) in
                       ret_typed (TEunop (eup,te)) e.loc t
  | Eif     (en,blxpr,None)  ->
            let l1,l2   =  whos_null env en  in
            let ten     = (type_expr env en) in
            let t1      =  ten.etyp           in
            if t1<>tbool then raise (Typing_error (e.loc, tp t1, tp tbool))
            else
            begin
               let tblxpr = type_blocexpr env blxpr in
               let ret    = ret_typed  (TEif (ten, tblxpr,None)) e.loc (extr_tblxpr tblxpr) in
               if  check_ret_blxpr env blxpr then
               List.iter (fun x -> modifquestpos env (fst x) (snd x)) l2;
               ret
            end

  |Eif     (en,blxpr,Some blxpr2)  ->
              let envi = copy_env env (snd env) in
              let l1,l2   =  whos_null envi en  in
              let ten     = (type_expr env en) in
              let t1      =  ten.etyp           in
              if t1<>tbool then raise (Typing_error (e.loc, tp tbool ,tp t1))
              else
              begin
                let tblxpr = type_blocexpr env blxpr in
                let t2 = extr_tblxpr tblxpr in
                List.iter (fun x -> modifquestpos env (fst x) (snd x)) l2;
                let tblxpr2 = type_blocexpr env blxpr2 in
                let t3 = extr_tblxpr tblxpr2 in
                if not(typ_castable t3 t2) then raise (Typing_error ((loc_blexpr blxpr2),tp t2, tp t3))
                else  ret_typed (TEif (ten, tblxpr,Some tblxpr2)) e.loc t2
              end
  | Ewhile  (en, blxpr) ->
     let envi = copy_env env (snd env) in
     let l1,l2   =  whos_null envi en  in
     let ten     = (type_expr env en) in
     let t1      =  ten.etyp           in
     if t1<>tbool then raise (Typing_error (en.loc, tp tbool, tp t1)) else
        let tblxpr = type_blocexpr env blxpr in
        let t2 = extr_tblxpr tblxpr in
        if  check_ret_blxpr env blxpr then
        List.iter (fun x -> modifquestpos env (fst x) (snd x)) l2;
        ret_typed (TEwhile  (ten, tblxpr)) e.loc t2

  | Ereturn None   -> (match snd env with
                        |None -> raise (Typing_error (e.loc, "Unxepected return" ,"keyword this"))
                        |Some tunit -> ret_typed (TEreturn None) e.loc tunit
                        |_    -> raise (Typing_error (e.loc, "Wrong return type" ,"keyword this")))

  | Ereturn Some e ->  let te     = (type_expr env e) in
                       let t1     =  te.etyp           in
                       (
                       match snd env with
                         |None -> print_endline("ici");raise (Typing_error (e.loc, "Unxepected return" ,"keyword this"))
                         |Some t when (typ_castable t t1) -> ret_typed (TEreturn (Some te)) e.loc tunit
                         |Some t   -> print_endline(tp(t));raise (Typing_error (e.loc, "Wrong return type" ,"keyword this"))
                       )

  | Eacc    acc    -> let tacc = type_acces env acc in
                      let t = extr_tacc tacc in
                      ret_typed (TEacc tacc) e.loc t
  | Eeg     (acc,em) ->
                        let tem     = (type_expr env em)       in
                        let t       =  tem.etyp                 in
                        let tacc    = type_eg env acc t em.loc in
                        ret_typed (TEeg (tacc,tem)) e.loc tunit
  | Ecall ("print", [x]) ->
                            let tx     = (type_expr env x) in
                            let t      = tx.etyp           in
                            if       t = tint        then ret_typed  (TEcall ("print", [tx])) e.loc tunit
                            else (if t = tstri       then ret_typed  (TEcall ("print", [tx])) e.loc tunit
                            else (if t = Twhat tstri then ret_typed  (TEcall ("print", [tx])) e.loc tunit
                            else raise (Typing_error (e.loc, "function print does not support type : "^tp(t),"keyword this"))))

  | Ecall   (s,l) ->  print_endline("call " ^ s);let tl,t = type_ecall env s l e.loc in
                      print_endline(tp(t));ret_typed (TEcall (s,tl)) e.loc t
  | Efun (pl,(Some ty),b) ->
      let l2 = extract_id_prmlist pl in
      dump (is_duplicate_idents l2);
      incr lvl;
      let new_env = copy_env env (Some ty) in
      List.iter (add_param new_env) pl;
      if not ((List.for_all (function Par(i, t, _) -> well_formed new_env t ) pl)&&(well_formed new_env ty))
      then raise (Typing_error (b.loc, "something is malformed 2", "keyword this"));
      let tb = (type_blocf new_env b) in
      decr lvl;
      ret_typed (TEfun (pl, (Some ty), tb)) e.loc (Tarot(type_of_prmlist pl,ty))


  | Efun (pl, None, b) ->
       let l2 = extract_id_prmlist pl in
       (is_duplicate_idents l2);
       incr lvl;
       let new_env = copy_env env (Some tunit) in
       List.iter (add_param new_env) pl;
       if not (List.for_all (function Par (i, t, _)-> well_formed new_env t ) pl)
       then raise (Typing_error (b.loc, "something is malformed 1", "keyword this"));
       let tb = (type_blocf new_env b) in
       decr lvl;
       ret_typed (TEfun (pl, None, tb)) e.loc (Tarot(type_of_prmlist pl,tunit))


and type_ecall env s l loc =
   (* Recheche dans l'environnment de la fonction/classe/ anything callable*)
   let valu =
      (
         if (Hashtbl.mem  (fst env) s) then
     begin
      let valeur = (Hashtbl.find (fst env) s) in
      match valeur with
      |Fonc t -> (if (t.lvl <= !lvl) then valeur else raise (Typing_error (loc,"Non_exist_id "^s,"keyword this")))
      |Vari t -> if t.lvl <= !lvl then
                 (
                   match t.typ with
                   |Tarot(_,_) -> valeur
                   |_ -> raise (Typing_error (loc,"Var/Val " ^ s ^  "  is not callable","keyword this"))
                 )
                 else raise (Typing_error (loc,"Var/Val " ^ s ^  "  is not callable","keyword this"))
      |Clas t -> valeur
      end
      else raise (Typing_error (loc,"Non_exist_id "^s,"keyword this"))
      )
   in




   match valu with
   (*Si on a pas de paramètres de type*)
   |Fonc t when t.idl = [] ->  fonc_aux_app env s l loc t.typ
   |Vari t -> fonc_aux_app env s l loc t.typ
   (*Avec les paramètres de type*)

   |Fonc t ->
      begin
         (*On se sert de h pour l'unification des paramètres de type*)
         let h = Hashtbl.create 5 in
         List.iter (fun x -> Hashtbl.add h x None) t.idl;
         let tprmlist,treturn =
            match t.typ with
            |Tarot (tl,t) -> tl,t
            |_ as a-> raise (Typing_error (loc,"unexpected func typ" ^ tp(a),"keyword this"))
         in
            (*On prend les types des expressions*)
          let tl_expr            = List.map (fun e -> (type_expr env e)) l        in
          let list_typ_expr      = List.map (fun e ->  e.etyp           ) tl_expr in
          (*Unification*)
          List.iter2 (unify loc t.idl h) tprmlist list_typ_expr;
          tl_expr,replace_typ3 loc t.idl h treturn
      end
   |Clas t ->
      begin
         if t.params = [] then raise (Typing_error (loc, "Uncallable Class", "keyword this"));
         (*On se sert de h pour l'unification des paramètres de type*)
         let h = Hashtbl.create 5 in
         List.iter (fun x -> Hashtbl.add h x None) t.idl;
         list_eq_length loc t.params l;
         let tl_expr            = List.map (fun e -> (type_expr env e)) l in
         let list_typ_expr      = List.map (fun e ->  e.etyp           ) tl_expr
         and list_typ_param = List.map (function Parvar (i, t, l) | Parval (i, t, l) -> t) t.params in
         List.iter2 (unify loc t.idl h) list_typ_param list_typ_expr;
         tl_expr,Ttype(s,List.map (replace_typ2 loc h) t.idl)
      end

and fonc_aux_app env s l loc arg =
   match arg with
    |Tarot (tl,t) ->
    begin
      let tl_expr = List.map (fun e -> (type_expr env e)) l in
      let l2      = List.map (fun e ->  e.etyp           ) tl_expr in
      if typ_castable  (Tarot(tl,t)) (Tarot(l2,t)) then tl_expr,t else raise (Typing_error (loc,"types uncastable","keyword this"))
    end
    |_ as a-> raise (Typing_error (loc,"unexpected func typ" ^ tp(a),"keyword this"))

and concord_paramc_typ p texpr =
   match p with
   |Parvar(x,t,loc) ->  if typ_castable t texpr then () else raise (Typing_error (loc,tp(t),tp(texpr)))
   |Parval(x,t,loc) ->  if typ_castable t texpr then () else raise (Typing_error (loc,tp(t),tp(texpr)))

and unify loc typlist tbl typ1 typ2=
   (*
      Ceci est expérimental
      Mais à un tel niveau
      Merci Maxime pour l'aide
      loc : Localisation de l'erreur
      typlist : Liste des paramètres de types
      tbl     : Hashtbl id -> type option (où on garde les types)
      typ1 : type paramètre (avec paramètres de Type)
      typ2 : type de l'expression
      print_endline ("I came here on " ^ t1 ^ " with " ^ tp(typ2));
      print_endline(tp(typ1)^" " ^ tp(typ2));

   *)
   match typ1, typ2 with
   |Ttype(t1,[]), _ when List.mem t1 typlist ->
      begin
         let valor = Hashtbl.find tbl t1 in
         match valor with
         |None    -> Hashtbl.replace tbl t1 (Some typ2)
         |Some Ttype(t,l) -> if not(typ_castable (Ttype(t,l)) typ2) then raise (Typing_error (loc, "Unable to unify arguments 1", "keyword this"))
         |Some Tnull       -> Hashtbl.replace tbl t1 (Some (Twhat typ2))
         |Some Twhat(t)    -> if not(typ_castable t typ2) then raise (Typing_error (loc, "Unable to unify arguments 2", "keyword this"))
         |_                -> raise (Typing_error (loc, "Unable to unify arguments 3", "keyword this"))
      end
   |Ttype(t1,l1) , Ttype(t2,l2)  when t1 = t2 && List.exists (fun x-> List.exists (fun y -> exist_id_typ x y) typlist) l1 ->
         List.iter2 (unify loc typlist tbl) l1 l2
   |Ttype(t1,l1) , Ttype(t2,l2)  -> if not(typ_castable typ1 typ2) then raise (Typing_error (loc, "Unable to unify arguments 4", "keyword this"))
   |Tarot(tl1,t1), Tarot(tl2,t2) -> unify loc typlist  tbl t1  t2 ;
                                             list_eq_length loc tl1 tl2;
                                             List.iter2 (unify loc typlist tbl) tl1 tl2
   |Twhat(t)     , Tnull         -> ()
   |Twhat(t1)    , Twhat(t2)     -> unify loc typlist tbl t1 t2;
   |Twhat(t1)    , Ttype(t2,l)   -> unify loc typlist tbl t1 typ2;
   | _           , _             -> if not(typ_castable typ1 typ2) then raise (Typing_error (loc, "Unable to unify arguments", "keyword this"))

and exist_id_typ typ id =
   match typ with
   |Ttype(iden,[]) when iden = id -> true
   |Ttype _ -> false
   |Tnull   -> false
   |Twhat(t) -> exist_id_typ t id
   |Tarot(tl,t) -> List.exists (fun x -> exist_id_typ x id) tl || exist_id_typ t id

and replace_typ2 loc tbl i=
     match Hashtbl.find tbl i with
     |None -> raise (Typing_error (loc, "1 Undefinable dangling type parameter "^ i, "keyword this"))
     |Some t -> t

and replace_typ3 loc idl tbl arg =
   match arg with
      |Tnull   -> Tnull
      |Twhat t -> Twhat (replace_typ3 loc idl tbl t)
      |Tarot (tl2, t) -> Tarot (List.map (replace_typ3 loc idl tbl) tl2, replace_typ3 loc idl tbl t)
      |Ttype (i, []) when List.mem i idl ->
        (
          let valu = Hashtbl.find tbl i in
          match valu with
          |None -> raise (Typing_error (loc, "2 Udefinable dangling type parameter "^ i, "keyword this"))
          |Some t -> t
        )
      |Ttype (i, l)  -> Ttype (i, List.map (replace_typ3 loc idl tbl)l)

and type_const env c l=
   match c with
    | Cthis       -> val_type env "this" l
    | Cnull       -> Tnull
    | Cbool (b)   -> tbool
    | Cstring (s) -> tstri
    | Cint (i)    -> tint

and type_acces env acc = match acc with
    |Aident(x,l) -> let t = vtype_complet env x l in
                     (
                     match t.typ,t.quest_removable with
                        |Twhat(tn),true -> TAident(x,l,tn)
                        |_              -> TAident(x,l,t.typ)
                     )
    |Adot(e,s,l) -> let te      = (type_expr env e) in
                    let t       =  te.etyp          in
                     (
                     match t with
                       |Ttype (c, tl) -> TAdot (te, s, l, fst (get_dot env c tl s l))
                       | _ as a       -> raise (Typing_error (l, "Not an accessible element", "keyword this"))
                     )
    |Awhat(e,s,l) -> let te      = (type_expr env e) in
                     let t       =  te.etyp          in
                        (
                        match t with
                           |Twhat (Ttype (c, tl))-> TAwhat (te, s, l, (Twhat (removewhat(fst (get_dot env c tl s l)))))
                           |Ttype (c, tl)        -> TAwhat (te, s, l, fst (get_dot env c tl s l))
                           | _ -> raise (Typing_error (l, "Not an accessible element", "keyword this"))
                        )

and type_eg env a t1 l  =
    match a with
    |Aident (x,l2)  -> if (is_var env x)  then
                      (let v= var_type env x l2 in
                      if (typ_castable v t1)  then TAident(x,l2,v) else  raise (Typing_error (l,tp(t1),tp(v))))
                      else raise (Typing_error (l2,"Non_exist_id : " ^ x,"keyword this"))
    |Adot  (e,x,l2) ->  let te      = (type_expr env e) in
                        let t       =  te.etyp          in
                        (match t with
                           |Ttype (c, tl) -> let v, m = get_dot env c tl x l2 in
                             if m then (if (typ_castable v t1) then TAdot (te, x, l2,v) else  raise (Typing_error (l,"17 "^tp(t1),tp(v))))
                             else raise (Typing_error (l2,  x ^ " is a non-mutable access" , "keyword this"))
                           | _ -> raise (Typing_error (l, "Not an accessible element", "keyword this"))
                        )
    |Awhat (e,x,l2) ->  let te      = (type_expr env e) in
                        let t       =  te.etyp          in
                        (match t with
                          |Twhat(Ttype (c, tl)) -> let v, m = get_dot env c tl x l2 in
                              if m then (if (typ_castable v t1) then TAwhat (te, x, l2,v) else  raise (Typing_error (l,"18 "^tp(t1),tp(v))))
                              else raise (Typing_error (l2,  x ^ " is a non-mutable access", "keyword this"))
                          |Ttype (c, tl) -> let v, m = get_dot env c tl x l2 in
                              if m then (if (typ_castable v t1) then TAwhat (te, x, l2,v) else  raise (Typing_error (l,"17 "^tp(t1),tp(v))))
                              else raise (Typing_error (l2,  x ^ " is a non-mutable access" , "keyword this"))
                          | _ -> raise (Typing_error (l, "Not an accessible element", "keyword this")))

and get_dot env c tl x l =
    try (
        match Hashtbl.find (fst env) c with
            |Clas cl ->(try replace_typ l cl.idl tl (Hashtbl.find cl.champs x), Hashtbl.find cl.mut_champs x
                with |Not_found -> raise (Typing_error (l, "field does not even exist lmao", "keyword this") ))
            | _ -> raise (Typing_error (l, "that's not even a class smh", "keyword this"))
        )
    with |Not_found -> raise (Typing_error (l, "class does not exist shrug", "keyword this"))

and replace_typ l idl tl = function
    |Tnull -> Tnull
    |Twhat t -> Twhat (replace_typ l idl tl t)
    |Tarot (tl2, t) -> Tarot (List.map (replace_typ l idl tl) tl2, replace_typ l idl tl t)
    |Ttype (i, []) when List.mem i idl -> (
        let rec aux x = function
            |(t::q),(a::b) when t = x -> a
            |(t::q),(a::b) -> aux x (q,b)
            |_,_ -> raise (Typing_error (l, "something's wrong with a class somewhere that should be fixed", "keyword this"))
        in (aux i (idl,tl)))
    |t -> t

and type_binop env o e1 e2 = match o with
   | Add | Sub | Mul | Div | Mod ->
     let te1 = (type_expr env e1) in
     let t1 = te1.etyp in
     if t1<>tint then raise (Typing_error (e1.loc, tp(tint), tp(t1))) else
     (
        let te2 = (type_expr env e2)in
        let t2 = te2.etyp in
        if t2<>tint then raise (Typing_error (e2.loc, tp(tint), tp(t2))) else
           te1,te2,tint
     )

  | Eeq | Neq | Lt | Le | Gt | Ge ->
     let te1 = (type_expr env e1) in
     let t1 = te1.etyp in
     if t1<>tint then raise (Typing_error (e1.loc, tp(tint), tp(t1))) else
     (
        let te2 = (type_expr env e2) in
        let t2  = te2.etyp in
         if t2<>tint then raise (Typing_error (e2.loc, tp(tint), tp(t2))) else
         te1,te2,tbool
     )
  | And  ->
      let te1 = (type_expr env e1) in
      let t1 = te1.etyp in
      if t1<>tbool then raise (Typing_error (e1.loc, tp(tbool), tp(t1))) else
      (*Non-Nullité*)
      (
         let l1, l2    =  whos_null env e1   in
         let te2 = (type_expr env e2) in
         let t2  = te2.etyp in
         if t2<>tbool then raise (Typing_error (e2.loc, tp(tbool), tp(t2))) else
         te1,te2,tbool
      )
   | Or   ->

       let te1 = (type_expr env e1) in
       let t1  = te1.etyp in
       if t1<>tbool then raise (Typing_error (e1.loc, tp(tbool), tp(t1))) else
      (
          (*Non-Nullité*)
          let envi = copy_env env (snd env)  in
          let l1,l2   =  whos_null envi e1   in
          List.iter (fun x -> modifquestpos env (fst x) (snd x)) l2;
          let te2 = (type_expr env e2)  in
          let t2  = te2.etyp in
          if t2<>tbool then raise (Typing_error (e2.loc, tp(tbool), tp(t2))) else
          te1,te2,tbool
      )
  | Eeeq | Neeq ->
     let te1 = (type_expr env e1) in
     let t1  = te1.etyp in
     if  (t1 = tbool || t1 = tunit || t1 = tint)  then raise (Typing_error (e1.loc, "not bool/unit/int", tp(t1))) else
     (
       let te2 = (type_expr env e2) in
       let t2  = te2.etyp in
       if (t2 = tbool || t2 = tunit || t2 = tint)  then raise (Typing_error (e2.loc, "not bool/unit/int", tp(t1))) else
          te1,te2,tbool
     )

and type_unop env e = match e with
  | Unot, en ->
      let ten = (type_expr env en) in
      let t   = ten.etyp in
      if  t <>tbool then  raise (Typing_error (en.loc, tp tbool , tp t)) else
      ten,tbool
  | Uneg, en ->
      let ten = (type_expr env en)in
      let t = ten.etyp in
      if  t <>tint  then  raise (Typing_error (en.loc, tp tint  , tp t)) else
         ten,tint

and check_ret_expr env e =
  match e.corp with
  | Ereturn (Some eu) ->  begin
                          if is_none (snd env) then raise (Typing_error (e.loc , "Unexpected return" , "keyword this"))
                          else
                            (let rettyp = (type_expr env eu).etyp in
                            if (typ_castable  (get (snd env)) rettyp) then true
                            else raise (Typing_error (e.loc , tp(get (snd env)) , tp(rettyp))))
                          end
  | Ereturn None -> begin
                        if is_none (snd env) then raise (Typing_error (e.loc , "Unexpected return" , "keyword this"))
                        else
                          (if  (get (snd env)) = tunit then true
                          else raise (Typing_error (e.loc , tp(get (snd env)),tp tunit)))
                        end


  | Eif     (en,blxpr,blxpr2)  ->   let l1,l2   =  whos_null env en  in
                                    if (check_ret_blxpr env blxpr) then
                                    (
                                       List.iter (fun x -> modifquestpos env (fst x) (snd x)) l2;
                                       match blxpr2 with
                                       |None   -> false
                                       |Some b -> (check_ret_blxpr env b)
                                    )
                                    else false
  | Ewhile  (en, blxpr) -> false
  | Epar    exp         -> check_ret_expr env exp
  | Ecst    c         -> false
  | Ebinop  (o,e1,e2) -> false
  | Eunop   (e1,e2)   -> false
  | Eacc    acc       -> false
  | Eeg     (a,em)    -> false
  | Ecall   (s,l)     -> false
  | Efun    (l1,l2,l3)-> false

and check_ret_blxpr env blxpr =
  match blxpr with
  |B bl -> check_ret_blc env bl
  |E e  -> check_ret_expr env e

and check_ret_blc env bl  =
   let res = ref false in
   incr lvl;
   let nenv = copy_env env (snd env) in
   let rec treatblc = function
    |[] -> ()
    |V(v) ::q -> type_var_d nenv v;treatblc q
    |E2(e)::q -> ((res := ((check_ret_expr nenv e) || !res));treatblc q)
    in
    treatblc bl.blc; decr lvl;
!res
and type_blocf env b  =
   (*
      A voir redondance avec check_ret_blc. Je propose qu'on fusionne les deux à un moment ?
   *)

    incr lvl;
    let nenv = copy_env env (snd env) in
    let typ  = ref tunit  in
    let l = ref [] in
    if not((snd nenv) = None || (snd nenv) = Some tunit) then  error_check (check_ret_blc nenv b) b.loc;
    let rec treat_list envi bl =
        match bl with
        |t::a ->  (match t with
                     |V  (v)->   typ := tunit;
                                 l := TV (type_var_d envi v) ::!l;
                                 treat_list envi a
                     |E2 (e)->   let te = (type_expr envi e) in
                                 typ := te.etyp;
                                 l := TE2 (te) :: !l;
                                 treat_list envi a
)
         |[]   -> ()
    in
    treat_list nenv b.blc;
    decr lvl;let a = {blc = List.rev !l ; btyp = !typ} in a

and type_varexpr env = function
    |V(v)  -> TV  (type_var_d env v)
    |E2(e) -> TE2 (type_expr env e)

and type_bloc env b =
    print_endline("Tlength is "^(string_of_int(List.length (b.blc))));
    incr lvl;
    let lis = ref [] in
    let typ = ref tunit in
    let nenv = copy_env env (snd env) in
    let rec aux envi l = match l with
    |[] -> decr lvl
    |[x]-> let res = (type_varexpr envi x) in (decr lvl; typ := extr_tvarexpr res; lis:=  res::(!lis) )
    |x::t -> (lis:= (type_varexpr envi x)::!lis);aux envi t
    in
    aux nenv b.blc; {blc = List.rev !lis; btyp = !typ}


and type_blocexpr env = function
  |B bl -> TB (type_bloc env bl)
  |E e  -> TE (type_expr env e)

and type_var_d env  = function
|Var (x, opt, e,l) -> begin print_endline("var entry" ^ x);
                        let te      = (type_expr env e) in
                        let t1      =  te.etyp           in
                        match opt with
                          |None -> (add_var env x t1 l); TVar(x,opt,te,l,t1)
                          |Some a -> if not(typ_castable  a t1) then raise (Typing_error (e.loc, tp a, tp t1 ))
                       else (add_var env x a l);print_endline("this is done"); TVar(x,opt,te,l,a)
                        end
  |Val (x, opt, e,l) -> begin
                          let te      = (type_expr env e) in
                          let t1      =  te.etyp           in
                          match opt with
                          |None -> (add_val env x t1 l); TVal(x,opt,te,l,t1)
                          |Some a -> if not(typ_castable  a t1) then raise (Typing_error (e.loc, tp a, tp t1 )) else
                          (add_val env x a l); TVal(x,opt,te,l,a)
                        end


and type_fun_d env f=
    match f with
    |Func(None,nom,p,None,b,l) ->
      print_endline nom;
      let l2 = extract_id_prmlist p in
      if (taken_id env nom) then (raise (Typing_error (l, "unc", "keyword this")))
      else
        dump (is_duplicate_idents l2);
        (*Traitement du typage de la fonction*)

        incr lvl;
        let new_env = copy_env env (Some tunit) in
        List.iter (add_param new_env) p;
        if not (List.for_all (function Par (i, t, _)-> well_formed new_env t ) p)
        then raise (Typing_error (l, "something is malformed", "keyword this"));
        let  typ_f = Tarot(type_of_prmlist p,tunit) in
        (add_fun new_env nom typ_f [] l);
        let tb = type_blocf new_env b in
        decr lvl;
        add_fun env nom typ_f [] l;
        TFunc(None,nom,p,None,tb,l,tunit)

    |Func(Some pt,nom,p,None,b,l)      ->
      print_endline nom;
      let l2 = extract_id_prmlist p in
      if (taken_id env nom) then (raise (Typing_error (l, "Taken id" ^ nom, "keyword this")))
      else begin
        if (is_duplicate pt) then (raise (Typing_error (l, "Duplicate type param", "keyword this")));
        dump (is_duplicate_idents l2);
        incr lvl;
        let new_env = copy_env env (Some tunit) in
        List.iter (function t -> add_class new_env t (Clas {lvl = !lvl; idl = []; params = []; champs = Hashtbl.create 0; mut_champs = Hashtbl.create 0}) l) pt;
        List.iter (add_param new_env) p;
        if not (List.for_all (function Par(i, t, _) -> well_formed new_env t ) p)
        then raise (Typing_error (l, "something is malformed", "keyword this"));
        let typ_f = Tarot(type_of_prmlist p,tunit) in
        (add_fun new_env nom typ_f pt l);
        let tb = type_blocf new_env b in
        decr lvl;(add_fun env nom typ_f pt l);
        TFunc(None,nom,p,None,tb,l,tunit)

      end

      |Func(None,nom,p,(Some ty),b,l) ->
        print_endline nom;
        let l2 = extract_id_prmlist p in
        if (taken_id env nom) then raise (Typing_error (l, "unc", "keyword this"))
        else begin
          dump (is_duplicate_idents l2);
          incr lvl;
          let new_env = copy_env env (Some ty) in
          List.iter (add_param new_env) p;
          if not (List.for_all (function Par(i, t, _) -> well_formed new_env t ) p)
          then raise (Typing_error (l, "something is malformed", "keyword this"));
          let typ_f = Tarot(type_of_prmlist p,ty) in
          (add_fun new_env nom typ_f [] l);
          let tb = type_blocf new_env b in
          decr lvl;(add_fun env nom typ_f [] l);
          TFunc(None,nom,p,(Some ty),tb,l,ty)
        end

    |Func(Some pt,nom,p,(Some ty),b,l) ->
      print_endline nom;
      let l2 = extract_id_prmlist p in
      if (taken_id env nom) then (raise (Typing_error (l, "unc", "keyword this")))
      else begin
        if (is_duplicate pt) then (raise (Typing_error (l, "unc", "keyword this")));
        dump (is_duplicate_idents l2);
        incr lvl;
        let new_env = copy_env env (Some ty) in
        List.iter (function t -> add_class new_env t (Clas {lvl = !lvl; idl = []; params = []; champs = Hashtbl.create 0; mut_champs = Hashtbl.create 0}) l) pt;
        List.iter (add_param new_env) p;
        if not (List.for_all (function Par(i, t, _)-> well_formed new_env t ) p)
        then raise (Typing_error (l, "something is malformed", "idk"));
        let typ_f = Tarot(type_of_prmlist p,ty) in
        (add_fun new_env nom typ_f pt l);
        let tb = type_blocf new_env b in
        decr lvl;(add_fun env nom typ_f pt l);
        TFunc(Some pt,nom,p,(Some ty),tb,l,ty)

      end

and type_var_pc env cl  = function
  |Parvar (x,t,l) -> Hashtbl.add cl.champs x t; Hashtbl.add cl.mut_champs x true; (add_var env x t l)

  |Parval (x,t,l) -> Hashtbl.add cl.champs x t; Hashtbl.add cl.mut_champs x false; (add_val env x t l)

and type_var_c env cl  = function
  |Var (x, opt, e,l) -> begin
                       let te      = (type_expr env e) in
                       let t1      =  te.etyp           in
                       match opt with
                         |None -> Hashtbl.add cl.champs x t1;
                                  Hashtbl.add cl.mut_champs x true;
                                  add_var env x t1 l;
                                  TVar(x,opt,te,l,t1)
                         |Some a -> if not(typ_castable  a t1) then
                                     raise (Typing_error (e.loc, "var", tp(t1)))
                                     else
                                       Hashtbl.add cl.champs x t1;
                                       Hashtbl.add cl.mut_champs x true;
                                       add_var env x a l;
                                       TVar(x,opt,te,l,a)
                       end
  |Val (x, opt, e,l) -> begin
                      let te      = (type_expr env e) in
                      let t1      =  te.etyp           in
                       match opt with
                         |None -> Hashtbl.add cl.champs x t1;
                                  Hashtbl.add cl.mut_champs x false;
                                  add_var env x t1 l;
                                  TVal(x,opt,te,l,t1)
                         |Some a -> if not(typ_castable  a t1) then
                             raise (Typing_error (e.loc, "var", tp(t1)))
                             else
                               Hashtbl.add cl.champs x t1;
                               Hashtbl.add cl.mut_champs x false;
                               add_var env x a l;
                               TVal(x,opt,te,l,a)
                       end

and type_class_d env d =
   match d with
   |Cls(c,None   ,l,vl,lo) ->

      (  (*On commence par vérifier si on a des répétitions *)
         let l2 = extract_id_prmclist l  in
         let l3 = extract_id_varllist vl in
         dump (is_duplicate_idents l2);dump(is_duplicate_idents l3);

         (*Etape 2*)
         let envi = copy_env env (snd env)
         and cl = {lvl = !lvl; idl = []; params = l; champs = Hashtbl.create 5; mut_champs = Hashtbl.create 5} in
         add_class envi c (Clas cl) lo;
         if List.for_all (function Parvar (i, t, _) | Parval (i, t, _) -> well_formed envi t ) l
         then
            begin
               (*On ajoute this et les paramètres à l'environnement*)
            add_val envi "this" (Ttype (c, [])) lo;
            List.iter (function x -> type_var_pc envi cl x) l ;
            let tvl = List.map  (function v -> type_var_c  envi cl v) vl in
            add_class env c (Clas cl) lo;
            TCls(c,None,l,tvl,lo)
            end
         else
            raise(Typing_error (lo, "something about malformed types", "keyword this"))
      )
   |Cls(c,Some tl,l,vl,lo) ->
      (  (*On commence par vérifier si on a des répétitions *)
         if (is_duplicate tl) then (raise (Typing_error (lo, "unc", "keyword this")));
         let l2 = extract_id_prmclist l  in
         let l3 = extract_id_varllist vl in
         dump (is_duplicate_idents l2);dump (is_duplicate_idents l3);

         let envi = copy_env env (snd env) in
         List.iter (function i -> add_class envi i (Clas {lvl = !lvl; idl = []; params = []; champs = Hashtbl.create 0; mut_champs = Hashtbl.create 0}) lo) tl;
         let cl = {lvl = !lvl; idl = tl; params = l; champs = Hashtbl.create 5; mut_champs = Hashtbl.create 5} in
         add_class envi c (Clas cl) lo;

        if List.for_all (function Parvar (i, t, _) | Parval (i, t, _) -> well_formed envi t ) l
         then
            begin
            List.iter (function x -> type_var_pc envi cl x) l ;
            add_val envi "this" (Ttype (c, List.map (function t -> Ttype (t, [])) tl )) lo;
            let tvl = List.map  (function v -> type_var_c  envi cl v) vl in
            add_class env c (Clas cl) lo;
            TCls(c,None,l,tvl,lo)
            end
         else
            raise(Typing_error (lo, "something about malformed types", "keyword this"))

      )

and type_decl env = function
    |Dvar   v -> TDvar   (type_var_d   env v)
    |Dclass c -> TDclass (type_class_d env c)
    |Dfun   f -> TDfun   (type_fun_d   env f)

and type_file  f =
    let env = Hashtbl.create 97, None in
    Hashtbl.replace (fst env) "Int" (Clas {lvl = 0; idl = []; params = []; champs = Hashtbl.create 0; mut_champs = Hashtbl.create 0});
    Hashtbl.replace (fst env) "Boolean" (Clas{lvl = 0; idl = []; params = []; champs = Hashtbl.create 0; mut_champs = Hashtbl.create 0});
    Hashtbl.replace (fst env) "Unit" (Clas {lvl = 0; idl = []; params = []; champs = Hashtbl.create 0; mut_champs = Hashtbl.create 0});
    Hashtbl.replace (fst env) "String" (Clas {lvl = 0; idl = []; params = []; champs = Hashtbl.create 0; mut_champs = Hashtbl.create 0});
    Hashtbl.replace (fst env) "Array" (Clas {lvl = 0; idl = ["T"]; params = []; champs = Hashtbl.create 0; mut_champs = Hashtbl.create 0});
    List.map (type_decl env) f



(*
-----------------------------------------------------------------TRASH---------------------------------------------------
let fun_type env v l=
  if (Hashtbl.mem  (fst env) v) then
    begin
     let valeur = (Hashtbl.find (fst env) v) in
     match valeur with
     |Fonc t -> (if (t.lvl <= !lvl) then t.typ else raise (Typing_error (l,"Non_exist_id "^v,"keyword this")))
     |Vari t -> raise (Typing_error (l,"Var is not callable","keyword this"))
     |Clas t -> raise (Typing_error (l,"Class is not callable","keyword this"))
    end
  else raise (Typing_error (l,"Non_exist_id "^v,"keyword this"))



*)
