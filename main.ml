(* Fichier principal de l'interprète mini-Turtle *)

open Format
open Lexing

(* Option de compilation, pour s'arrêter à l'issue du parser *)
let parse_only = ref false
let type_only  = ref false

(* Noms des fichiers source et cible *)
let ifile = ref ""
let ofile = ref ""

let set_file f s = f := s

(* Les options du compilateur que l'on affiche avec --help *)
let options =
  ["--parse-only", Arg.Set parse_only,
   "  Pour ne faire uniquement que la phase d'analyse syntaxique";
   "--type-only", Arg.Set type_only, "  stop after typing";]

let usage = "usage: mini-kotlin [option] file.kt"


(*get post et print_pos sont la pour indiquer ou est l'erreur ?*)

let get_pos pos = (pos.pos_lnum, pos.pos_cnum - pos.pos_bol + 1)
let print_pos (pos1, pos2) =
		let pos1 = get_pos pos1 and pos2 = get_pos pos2 in
		Printf.printf "File \"%s\", line %d, characters %d-%d:\n" !ifile (fst pos1) (snd pos1) (snd pos2)

(* localise une erreur en indiquant la ligne et la colonne *)
let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l (c-1) c

let () =
  Arg.parse options (set_file ifile) usage;

  if !ifile="" then begin eprintf "Aucun fichier à compiler\n@?"; exit 1 end;
  if not (Filename.check_suffix !ifile ".kt") then begin
    eprintf "Le fichier d'entrée doit avoir l'extension .kt\n@?";
    Arg.usage options usage;
    exit 1
  end;

  let f = open_in !ifile in
  let buf = Lexing.from_channel f in

  try
    let p = Parser.fichier Lexeur.token buf in
    close_in f;
    if !parse_only then exit 0;
    let typed_file = Typer.type_file p in
    if !type_only  then exit 0;
      ofile := (Filename.chop_suffix !ifile ".kt")^".s";
    Compile.compile_program typed_file !ofile
  with
    | Lexeur.Lexing_error c ->
	localisation (Lexing.lexeme_start_p buf);
	eprintf "Erreur lexicale: %s@." c;
	exit 1
    | Parser.Error ->
	localisation (Lexing.lexeme_start_p buf);
	eprintf "Erreur syntaxique@.";
	exit 1
    | Typer.Typing_error (loc,msg1,msg2) ->
   print_pos loc;
   (match msg2 with
   | "keyword this" -> 	Printf.printf "Typing error : %s\n" msg1;
   | _              ->	Printf.printf "Typing error : expected %s but expression type is %s\n" msg1 msg2;
);
  exit 1
