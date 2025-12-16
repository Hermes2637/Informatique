type regexp =
 | Empty
 | Epsilon
 | Lettre of char
 | Union of regexp * regexp
 | Concat of regexp * regexp
 | Kleene of regexp;;

type char_lin = {
  id : int;
  lettre : char
}

type regexp_lin =
 | Emp
 | Eps
 | L of char_lin
 | U of regexp_lin * regexp_lin
 | C of regexp_lin * regexp_lin
 | K of regexp_lin;;

type automate = {
 nb_etats : int;
 initial : int ;
 terminaux : int list;
 transitions : ((int*char), int) Hashtbl.t
}

type automate_nd = {
 nb_etats : int;
 initiaux : bool array;
 terminaux : bool array;
 transitions : bool array array
}

let str_to_regexp str = 
  ();;

let rec est_vide expr =
  match expr with
  | Empty -> true
  | Epsilon -> false
  | Lettre _ -> false
  | Union (expr1, expr2) -> est_vide expr1 && est_vide expr2
  | Concat (expr1, expr2) -> est_vide expr1 || est_vide expr2
  | Kleene _ -> false

let rec suppr_vide expr = (* s'applique uniquement à des expr non vides !! *)
  match expr with
  | Empty -> failwith("")
  | Epsilon -> Epsilon
  | Lettre (a) -> Lettre (a)
  | Union (e1, e2) when est_vide e1 -> suppr_vide e2
  | Union (e1, e2) when est_vide e2 -> suppr_vide e1
  | Union (e1, e2) -> Union (e1,e2)
  | Concat (e1, e2) -> Concat(e1, e2)
  | Kleene e when est_vide e-> Epsilon
  | Kleene e -> Kleene (suppr_vide e)

let rec est_eps expr =
  match expr with
  | Empty -> false
  | Epsilon -> true
  | Lettre _ -> false
  | Union (expr1, expr2) ->
     (est_eps expr1 && est_eps expr2) ||
       (est_eps expr1 && est_vide expr2) ||
         (est_vide expr1 && est_eps expr2)
  | Concat (expr1, expr2) -> est_eps expr1 && est_eps expr2
  | Kleene expr -> est_vide expr || est_eps expr

let rec a_eps expr =
  match expr with
  | Emp -> false
  | Eps -> true
  | L _ -> false
  | U (expr1, expr2) -> a_eps expr1 || a_eps expr2
  | C (expr1, expr2) -> a_eps expr1 && a_eps expr2
  | K _ -> true

let rec suppr_eps expr = (* s'applique à une expr non vide et sans Empty *)
  match expr with
  | Empty -> failwith("")
  | Epsilon -> Epsilon
  | Lettre (a) -> Lettre (a)
  | Union (e1, e2) when est_eps e1 || est_eps e2 -> Epsilon
  | Union (e1,e2) -> Union(e1,e2)
  | Concat (e1, e2) when est_eps e1 -> suppr_eps e2 
  | Concat (e1, e2) when est_eps e2 -> suppr_eps e1
  | Concat (e1,e2) -> Concat(e1,e2)
  | Kleene e when est_eps e -> Epsilon
  | Kleene e -> Kleene e

let rec nb_lettre exp =
  match exp with
  | Empty -> 0
  | Epsilon -> 0
  | Lettre (a) -> 1
  | Union (e1,e2) -> nb_lettre e1 + nb_lettre e2
  | Concat (e1,e2) -> nb_lettre e1 + nb_lettre e2
  | Kleene (e) -> nb_lettre e

let linear_exp exp n =
  let int_to_char = Array.make (n+1) ' ' in
  let char_to_int = Hashtbl.create 10 in
  let i = ref(1) in
  let rec aux e =
    match e with
    |Empty -> Emp
    |Epsilon -> Eps
    |Lettre (a) -> int_to_char.(!i) <- a;
                  Hashtbl.add char_to_int a !i;
                  i := !i + 1;
                  L ({id = !i; lettre = a})
    |Union (e1,e2) -> U(aux e1, aux e2)
    |Concat (e1,e2) -> C(aux e1, aux e2)
    |Kleene (e) -> K(aux e) in
  (aux exp,int_to_char,char_to_int)

let rec calcul_P exp = (* pour une expr non vide et sans vide *)
  match exp with
  |Emp -> []
  |Eps -> []
  |L (a) -> [a]
  |U (e1,e2) -> (calcul_P e1) @ (calcul_P e2)
  |C (e1,e2) when a_eps e1 -> (calcul_P e1) @ (calcul_P e2)
  |C (e1,e2) -> (calcul_P e1)
  |K (e) -> (calcul_P e)

let rec calcul_S exp = (* pour une expr non vide et sans vide *)
  match exp with
  |Emp -> []
  |Eps -> []
  |L (a) -> [a]
  |U (e1,e2) -> (calcul_S e1) @ (calcul_S e2)
  |C (e1,e2) when a_eps e2 -> (calcul_S e1) @ (calcul_S e2)
  |C (e1,e2) -> (calcul_S e2)
  |K (e) -> (calcul_S e)

let rec produit_cart l1 l2 =
  match l1 with
  | [] -> []
  | e::t -> List.map (fun x -> (e,x)) l2 @ (produit_cart t l2)

let rec calcul_F exp =   (* pour une expr non vide et sans vide *)
  match exp with
  |Emp -> []
  |Eps -> []
  |L (a) -> []
  |U (e1,e2) -> calcul_F e1 @ (calcul_F e2)
  |C (e1,e2) -> produit_cart (calcul_S e1) (calcul_P e2) @ (calcul_F e1) @ (calcul_F e2)
  |K (e) -> produit_cart (calcul_S e) (calcul_P e) @ (calcul_F e)

let automate n exp_lin =
  let init = Array.make (n+1) false in
  init.(0) <- true;
  let ter = Array.make (n+1) false in
  ter.(0) <- a_eps exp_lin;
  List.iter (fun x -> ter.(x.id)<- true) (calcul_S exp_lin);
  let fact = Array.make (n+1) (Array.make (n+1) false) in
  List.iter (fun (x,y) -> fact.(x.id).(y.id) <- true) (calcul_F exp_lin);
  List.iter (fun x -> fact.(0).(x.id) <- true) (calcul_P exp_lin);

  let a = { nb_etats = n; 
            initiaux = init;
            terminaux = ter;
            transitions = fact } in
  a;;

let create_automate exp =
  let n = nb_lettre exp in
  if est_vide exp then begin ((automate 0 Emp),[||],Hashtbl.create 1);
  end
  else begin let e = suppr_eps (suppr_vide exp) in
           let (e_lin, int_to_char, char_to_int) = linear_exp e n in
           let a = automate n e_lin in
  (a, int_to_char, char_to_int) end ;;

let determinise exp =
  let n = nb_lettre exp in
  let (a, int_to_char, char_to_int) = create_automate exp in

  let rec est_final b =
    let res = ref false in
    for i=0 to (n+1) do
      if b.(i) && a.terminaux.(i) then res := true
      done;
    !res
  in


  let chercher_lettres b_sommet =
    let lettres = ref [] in
    let aux e =
      for j=0 to (n+1) do
        if a.transitions.(e).(j) then begin
          if not (List.mem (int_to_char.(j)) !lettres) then lettres := int_to_char.(j)::!lettres
          end
        done;
      in
    for i=0 to (n+1) do
      if b_sommet.(i) then aux i
      done;
    !lettres
    in

  let bool_to_int lst =
    let acc = ref 0 in
    for i=0 to (n+1) do
      if lst.(i) then acc := (1 lsl i) + !acc
      done;
    !acc
  in

  let bool_to_lst b =
    let lst = ref [] in
    for i=0 to (n+1) do
      if b.(i) then lst := i::!lst
      done;
    !lst
    in

  let a_traiter = Stack.create () in
  let deja_vu = Hashtbl.create 10 in
  let initial = Array.make (n+1) false in
  initial.(0) <- true;
  let transitions = Hashtbl.create 10 in
  let final = ref [] in
  Stack.push initial a_traiter;

  let delta_etoile etat lettre =
    let vu = Array.make (n+1) false in
    let lst_lettre = Hashtbl.find_all char_to_int lettre in
    let lst_etat = bool_to_lst etat in
    let rec aux l i_lettre =
      match l with
      | [] -> ()
      | e::t -> if a.transitions.(e).(i_lettre) then vu.(i_lettre) <- true;
                aux t i_lettre
    in
    List.iter (aux lst_etat) lst_lettre;
    Hashtbl.add transitions (bool_to_int etat, lettre) (bool_to_int vu)
  in
  
  let ajouter_sommet sommet =
    Hashtbl.add deja_vu (bool_to_int sommet) 0;
    if est_final sommet then final := (bool_to_int sommet) :: (!final);
    let sigma = chercher_lettres sommet in
    List.iter (delta_etoile sommet) sigma;
  in

  let construire () =
    while not (Stack.is_empty a_traiter) do
      let sommet = Stack.pop a_traiter in
      if not (Hashtbl.mem deja_vu (bool_to_int sommet)) then
        ajouter_sommet sommet
      done;
  in
  construire();
  
  {nb_etats = Hashtbl.length deja_vu;
  initial = 0;
  terminaux = !final;
  transitions = transitions}
;;





  


