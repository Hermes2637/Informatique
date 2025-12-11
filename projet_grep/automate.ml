type regexp =
 | Empty
 | Epsilon
 | Lettre of char
 | Union of regexp * regexp
 | Concat of regexp * regexp
 | Kleene of regexp;;

type regexp_int =
 | Emp
 | Eps
 | L of int
 | U of regexp_int * regexp_int
 | C of regexp_int * regexp_int
 | K of regexp_int;;

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
 transitions : (char list) array array
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

let linear_exp exp corres =
  let i = ref(0) in
  let rec aux e =
    match e with
    |Empty -> Emp
    |Epsilon -> Eps
    |Lettre (a) -> corres.(!i) <- a ;
                   i := !i + 1;
                  L (!i)
    |Union (e1,e2) -> U(aux e1, aux e2)
    |Concat (e1,e2) -> C(aux e1, aux e2)
    |Kleene (e) -> K(aux e) in
  aux exp

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

let automate p s f n corres_lin =
  let init = Array.make n false in
  List.iter (fun x -> init.(x)<- true) p;
  let ter = Array.make n false in
  List.iter (fun x -> ter.(x)<- true) s;

  let fact = Array.make n (Array.make n []) in
  List.iter (fun (x,y) -> fact.(x).(y) <- corres_lin.(y) :: fact.(x).(y)) f;

  let a = { nb_etats = n; 
            initiaux = init;
            terminaux = ter;
            transitions = fact } in
  a;;

let create_automate exp =
  let n = nb_lettre exp in
  let corres_lin = Array.make n ' ' in
  if est_vide exp then begin automate [] [] [] 0 corres_lin;
  end
  else begin let e = suppr_eps (suppr_vide exp) in
           let e_lin = linear_exp e corres_lin in
           let a = automate (calcul_P e_lin) (calcul_S e_lin) (calcul_F e_lin) n corres_lin in
  a end ;;

let determinise a =
  let a_det = {
    nb_etats = 1;
    initial = 0;
    terminaux = [];
    transitions = Hashtbl.create 10}
  in
  let rec sont_egales l1 l2 =
    match (l1,l2) with
    | ([],[]) -> true
    | (e1::t1,e2::t2) when e1 = e2 -> sont_egales t1 t2
    | _ -> false
  in
  let rec est_final l =
    match l with
    | [] -> false
    | e::t when a.terminaux.(e) -> true
    | _::t -> est_final t
  in
  let l_init a =
    let rec aux i =
      if i >= 0 then begin
        if a.initiaux.(i) then i :: (aux (i+1))
        else aux (i+1)
      end else []
    in aux (a.nb_etats-1)
  in

  let chercher_lettres l_sommet =
    let vu = ref([]) in
    let deja_vu char = if List.mem char !vu then None
      else begin vu := char :: !vu ;
                Some char
    end
    in
    let rec aux sommet i =
      if i >= 0 then begin
        List.filter_map deja_vu a.transitions.(sommet).(i) @ (aux sommet (i+1))
      end else []
    in
    let rec aux2 l_s =
      match l_s with
      | [] -> []
      | e::t -> aux e (a.nb_etats-1) @ (aux2 t)
    in aux2 l_sommet
  in

  let a_faire = Stack.create () in
  let corres_l_sommet_int = ref [l_init a] in
  Stack.push (l_init a) a_faire;
  let tab = Hashtbl.create 10 in
  let term = ref [] in 

  let new_states sigma e =
    let n = List.length (!corres_l_sommet_int) in
    corres_l_sommet_int := e :: (!corres_l_sommet_int);
    if est_final e then term := n :: (!term);
    let add_transi char =
      let i = ref (-1) in
      let appartient l_char =
        i := (i+1);
        if List.mem char l_char then Some(!i)
        else None
      in
      let n_etat = List.filter_map appartient (Array.to_list a.transitions.(e))
    in
    List.iter add_transi sigma


  
  let rec construire () =
    if Stack.is_empty a_faire then ()
    else begin
      let e = Stack.pop a_faire in
      let sigma = chercher_lettres e in
      new_states sigma e;
      construire ()



  


