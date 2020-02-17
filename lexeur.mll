
{
  open Lexing
  open Parser

 exception Lexing_error of string
    (*
    kwd_tbl est la liste des couples s,t tel que s représente le string et t le mot clé ou keyword dans la syntaxe abstraite (en miniscule)
    On les insérera dans h, la hashtable après.
    Cela nous permet d'avoir moins d'états sur l'automate.
    *)



    let rec etud_list st =
       match st with
       | [] -> []
       | '\\'::'n' ::q -> '\n'::(etud_list q)
       | '\\'::'t' ::q -> '\t'::(etud_list q)
       | '\\'::'\\'::q -> '\\'::(etud_list q)
       |  x::q         ->   x ::(etud_list q)

    let string_of_chars chars =
       let buf = Buffer.create 16 in
       List.iter (Buffer.add_char buf) chars;
       Buffer.contents buf

    let correct stri =
       let n = String.length stri      in
       let a = String.sub stri 1 (n-2) in
       let l = ref [] in
       String.iter (fun x -> l:= x::!l) a;
       l := List.rev !l;
       l := etud_list !l;
       string_of_chars !l

    let id_or_kwd st =
      (*
      Cette fonction prend un string comme argument et renvoie le mot clé SyntAbs s'il y'en a et le stirng Ident sinon
      *)
        let h = Hashtbl.create 23 in
        let kwd_tbl =
        [
        "class" , CLASS ;
        "data"  , DATA  ;
        "else"  , ELSE  ;
        "false" , FALSE ;
        "fun"   , FUNC  ;
        "if"    , IF    ;
        "null"  , NULL  ;
        "return", RETURN;
        "this"  , THIS  ;
        "true"  , TRUE  ;
        "val"   , VAL   ;
        "var"   , VAR   ;
        "while" , WHILE ;
        ] in
        List.iter (fun (n,t) -> Hashtbl.add h n t) kwd_tbl;
        try Hashtbl.find h st with _ -> IDENT st

}



(*

Choses à faire:
Vérifier que le lexeur marche
Comprendre le role des objets avec ????
Essayer de factoriser les caractères pour avoir moins d'états
Vérifier la définition de useless

*)









let chiffre     = ['0' - '9']
let alpha       = ['a' - 'z'  'A' - 'Z' '_']
let ident       = alpha (alpha|chiffre)*
let bit         = ['0' '1']
let hexa        = ['0' - '9' 'a'-'f' 'A'-'F']
let entier_b10  = chiffre|chiffre (chiffre| '_')* chiffre
let entier_b16  = ("0x"| "0X") (hexa|hexa (hexa|'_')*hexa)
let entier_b02  = ("0b"|"0B") (bit|bit(bit|'_')*bit )
let car         = [' '-'~']#['"' '\\'] | "\\\"" | "\\n" | "\\t" | "\\\\"


(*pas trop sur si c'est des chaines ou des char en syntaxe
  *)

let strng       = '"' car * '"'
let comment_li  = "//" [^ '\n' ] *
let useless     = [' '  '\t']



rule token = parse
  useless+                                     { token lexbuf }        (*gère les espaces*)
  |'\n'                                        { new_line lexbuf;token lexbuf}
  |"/*"                                        { comment lexbuf;token lexbuf }  (*gère les commentaires imbriqués*)
  |comment_li                                  { token lexbuf }
  |(entier_b02|entier_b10|entier_b16) as d     {
                                                try (INT (Int32.of_string d))
                                                with _ -> raise (Lexing_error  "entier trop grand")

                                                }

  |strng as s                                  { STRING (correct s) }
  |ident as i                                  { id_or_kwd i }
  |"->"       { ROBIN    }      (*????Affectation ? Type ? ??????*)
  |"||"       { OR       }      (*BoolOp: Or Logique*)
  |"&&"       { AND      }      (*BoolOp: AND Logique*)
  |"==="      { EEEQ     }      (*BoolOp: ???????????*)
  |"!=="      { NEEQ     }      (*BoolOp: ???????????*)
  |"=="       { EEQ      }      (*IntOP*)
  |"!="       { NEQ      }      (*IntOP*)
  |'='        { EQ       }      (*Affec*)
  |">="       { BIGGEQ   }      (*IntOP*)
  |"<="       { SMALEQ   }      (*IntOP*)
  |'<'        { SMALS    }      (*IntOP*)
  |'>'        { BIGGS    }      (*IntOP*)
  |'+'        { PLUS     }      (*IntOP*)
  |'-'        { MINUS    }      (*IntOP*)
  |'*'        { PROD     }      (*IntOP*)
  |'/'        { DIV      }      (*IntOP*)
  |'%'        { MOD      }      (*IntOP*)
  |'!'        { BANG     }      (*?????*)
  |'.'        { DOT      }      (*?????*)
  |"?."       { NANII    }      (*?????*)
  |'?'        { NANI     }      (*?????*)
  |'('        { LPAR     }
  |')'        { RPAR     }
  |','        { VIRG     }
  |':'        { DDOT     }
  |';'        { VDOT     }
  |'{'        { RACC     }
  |'}'        { LACC     }
  |_ as c     { raise
                  (Lexing_error
                    ("illegal character: "  ^ (Char.escaped c))
)}      (*Caractère*)
  | eof        { EOF      }      (*EndOfFile*)

and comment = parse
|"*/" {()}
|"/*" {comment lexbuf; comment lexbuf}
|'\n' {new_line lexbuf;comment lexbuf}
|_    {comment lexbuf}
|eof  {raise (Lexing_error "Missing terminating \"*/\" in comment")}
