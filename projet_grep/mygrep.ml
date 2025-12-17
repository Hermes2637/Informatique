(* Lecture d'une regex lors de l'entrée ainsi que surveillance du flux éventuellement passé en paramètre *)
open Automate

(* Lecture de l'entrée et exécution ligne par ligne de la fonction k : string -> unit passée en paramètre *)
let process input k =
  try
    while true do
      let line = Stdlib.input_line input in
      k line
    done
  with End_of_file -> ()

(* Fonction string -> char list convertissant une chaîne de caractère en une liste contenant les mêmes caractères dans le même ordre *)
let string_to_char_list s =
  let n = String.length s in
  (* Fonction auxiliaire int -> char list -> char list qui ajoute les i premières lettres de s à l *)
  let rec split i l =
    if i < 0 then l
    else split (i-1) (s.[i]::l)
  in split (n-1) []

let char_list_to_regex c =
  let escaped = ref false in
  let rec aux c e1 e2 = 
    match c with
    | [] -> if e2 = None then begin
      match e1 with
      | Some e -> e
      | None -> Automate.Epsilon
      end
      else begin Printf.printf "Invalid syntax\n"; process (Stdlib.open_in "help.txt") (Printf.printf "%s\n%!"); exit 0 end
    | h::q -> if !escaped then begin 
        escaped := false;
        if e1 = None then
          aux q (Some (Automate.Lettre h)) e2
        else if e2 = None then
          aux q e1 (Some (Automate.Lettre h))
        else begin Printf.printf "Invalid syntax\n"; process (Stdlib.open_in "help.txt") (Printf.printf "%s\n%!"); exit 0 end
      end
      else if h = '\\' then begin escaped := true; aux q e1 e2 end
      else if h = '?' then begin match e1, e2 with
        | None, _ -> begin Printf.printf "Invalid syntax\n"; process (Stdlib.open_in "help.txt") (Printf.printf "%s\n%!"); exit 0 end
        | Some e, None -> aux q (Some (Automate.Union (e, Automate.Epsilon))) None
        | Some e01, Some e02 -> aux q e1 (Some (Automate.Union (e02, Automate.Epsilon)))
      end
      else if h = '*' then begin match e1, e2 with
        | None, _ -> begin Printf.printf "Invalid syntax\n"; process (Stdlib.open_in "help.txt") (Printf.printf "%s\n%!"); exit 0 end
        | Some e, None -> aux q (Some (Automate.Kleene e)) None
        | Some e01, Some e02 -> aux q e1 (Some (Automate.Kleene e02))
      end
      else if h = '+' then begin match e1, e2 with
        | None, _ -> begin Printf.printf "Invalid syntax\n"; process (Stdlib.open_in "help.txt") (Printf.printf "%s\n%!"); exit 0 end
        | Some e, None -> aux q (Some (Automate.Concat ((Automate.Kleene e), e))) None
        | Some e01, Some e02 -> aux q e1 (Some (Automate.Concat ((Automate.Kleene e02), e02)))
      end
      else if h = '|' then begin match e1, e2 with
        | None, _ | _, None -> begin Printf.printf "Invalid syntax\n"; process (Stdlib.open_in "help.txt") (Printf.printf "%s\n%!"); exit 0 end
        | Some e01, Some e02 -> aux q (Some (Automate.Union (e01, e02))) None
      end
      else if h = '@' then begin match e1, e2 with
        | None, _ | _, None -> begin Printf.printf "Invalid syntax\n"; process (Stdlib.open_in "help.txt") (Printf.printf "%s\n%!"); exit 0 end
        | Some e01, Some e02 -> aux q (Some (Automate.Concat (e01, e02))) None
      end
      else begin
        if e1 = None then
          aux q (Some (Automate.Lettre h)) e2
        else if e2 = None then
          aux q e1 (Some (Automate.Lettre h))
        else begin Printf.printf "Invalid syntax\n"; process (Stdlib.open_in "help.txt") (Printf.printf "%s\n%!"); exit 0 end
      end
  in aux c None None

let execute_automaton (a : Automate.automate) u =
  let rec dstar q v = match v with
  | [] -> q
  | e::t -> dstar (Hashtbl.find a.transitions (q, e)) t
  in let v = string_to_char_list u in
  try begin
    let f = dstar a.initial v in
    List.mem f a.terminaux
  end with Not_found -> false

let main () =
  (* Vérification de la présence de la regex *)
  let argc = Array.length Sys.argv in
  if argc < 2 || argc > 3 then begin
    Printf.printf "usage : %s regex [file]\n%!" Sys.argv.(0);
    exit 1
  end;
  (* Affichage du menu d'aide *)
  if Sys.argv.(1) = "-h" then begin
    let help = Stdlib.open_in "help.txt" in
    process help (Printf.printf "%s\n%!");
    exit 0
  end;
  (* Création de l'automate *)
  let reg = Sys.argv.(1) in
  let true_reg = char_list_to_regex (string_to_char_list reg) in
  let auto = Automate.determinise true_reg in
  (* Choix du flux d'entrée; entrée standard par défaut *)
  let input =
    if argc = 3 then begin
      Stdlib.open_in Sys.argv.(2)
    end else
      Stdlib.stdin
  in Printf.printf "Searching %s in %s\n\n%!" Sys.argv.(1) (if argc = 3 then Sys.argv.(2) else "stdin");
  (* Exécution de l'automate *)
  process input (fun s -> if execute_automaton auto s then Printf.printf "%s\n%!" s);

  if argc = 3 then Stdlib.close_in input

let () = main ()