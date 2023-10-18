(*Pablo Fernández Pérez. Grupo 3.3 TC*)

(**Ejercicio 1----------------------------------------------------------------------**)

let cumple_fnc = function
    (Regla_gic (a,[Terminal _]))-> true
  | (Regla_gic (a,[No_terminal _; No_terminal _]))-> true
  | (Regla_gic (a, l)) -> false
;;

let es_fnc (Gic (Conjunto nt, Conjunto t, Conjunto r, s)) =  
  let rec es_fnc_aux = function
      [] -> false
    | h::[] -> cumple_fnc h
    | h::t -> if (cumple_fnc h) then es_fnc_aux t else false
  in es_fnc_aux r
;;

let g1 = gic_of_string "S A B C; a b; S;
S -> A B | B C;
A -> B A | a;
B -> C C | b;
C -> A B | a;";;

let g2 = gic_of_string "S A B C; a b; S;
S -> A B | b C;
A -> a;
B -> a b;";;

(**Ejercicio 2----------------------------------------------------------------------**)

let fila1 cyk_table n cadena r =
  for i = 0 to n-1 do
    let c = List.nth cadena i in
    cyk_table.(0).(i) <- fila1_aux conjunto_vacio c r;
  done;
  cyk_table
;;

let rec fila1_aux acc h = function
    [] -> acc
  | (Regla_gic (a,[b]))::[] -> if (b = h) then (agregar a acc) else acc 
  | (Regla_gic (a, _))::[] -> acc
  | (Regla_gic (a,[b]))::t-> if (b = h) then fila1_aux (agregar a acc) h t else fila1_aux acc h t 
  | (Regla_gic (a, _))::t -> fila1_aux acc h t 
;;

let rec cyk_aux2 a b acc = function
    [] -> acc
  | (Regla_gic (c,[d; e]))::[] -> if ((d = a)&&(e = b)) then (agregar c acc) else acc 
  | (Regla_gic (c, _))::[] -> acc
  | (Regla_gic (c,[d; e]))::t-> if ((d = a)&&(e = b)) then cyk_aux2 a b (agregar c acc) t else cyk_aux2 a b acc t 
  | (Regla_gic (c, _))::t -> cyk_aux2 a b acc t 
;;

let rec cyk_aux acc r = function
    Conjunto [] -> acc
  | Conjunto ((a,b)::[]) -> (union (cyk_aux2 a b conjunto_vacio r) acc)
  | Conjunto ((a,b)::t) -> cyk_aux (union (cyk_aux2 a b conjunto_vacio r) acc) r (Conjunto t)
;;

let cyk cadena (Gic (nt, t, Conjunto r, s) as gic) =
  if not (es_fnc gic) then failwith "No_FNC"
  else 
  let n = List.length cadena in
  if (n = 0) then failwith "Cadena_vacía"
  else
  let cyk_table = Array.make_matrix n n conjunto_vacio in
  let cyk_table = fila1 cyk_table n cadena r in
  for i = 1 to n-1 do
    for j = 0 to n-1-i do
      for k = 0 to i-1 do
        let simbolos1 = cyk_table.(k).(j) in
        let simbolos2 = cyk_table.(i-k-1).(j+k+1) in
        cyk_table.(i).(j) <- union cyk_table.(i).(j) (cyk_aux conjunto_vacio r (cartesiano simbolos1 simbolos2)) 
      done;
    done;
  done;
  if (pertenece (No_terminal "S") cyk_table.(n-1).(0)) then true else false
;;

let c1 = cadena_of_string "b b a b";;

(*cyk c1 g1;;*)

(*cyk c1 g2;;*)

let c2 = cadena_of_string "b b b b";;

(*cyk c2 g1;;*)

let c3 = cadena_of_string "";;

(*cyk c3 g1;;*)

(**Ejercicio 3----------------------------------------------------------------------**)

let rec pertenece_plus a = function
    Conjunto [] -> false
  | Conjunto ((h,_)::t) -> if h = a then true else pertenece_plus a (Conjunto t)
;;

let fila1_plus cyk_table n cadena r =
  for i = 0 to n-1 do
    let c = List.nth cadena i in
    cyk_table.(0).(i) <- fila1_aux_plus conjunto_vacio c r;
  done;
  cyk_table
;;

let rec fila1_aux_plus acc h = function
    [] -> acc
  | (Regla_gic (a,[Terminal b]))::[] -> if ((Terminal b) = h) then (agregar (a, [(Terminal b,(0,0))]) acc) else acc 
  | (Regla_gic (a, _))::[] -> acc
  | (Regla_gic (a,[Terminal b]))::t-> if ((Terminal b) = h) then fila1_aux_plus (agregar (a, [(Terminal b,(0,0))]) acc) h t else fila1_aux_plus acc h t 
  | (Regla_gic (a, _))::t -> fila1_aux_plus acc h t 
;;

let rec cyk_aux2_plus a b acc p11 p12 p21 p22 = function
    [] -> acc
  | (Regla_gic (c,[No_terminal d; No_terminal e]))::[] -> if (((No_terminal d) = a)&&((No_terminal e) = b)) then (agregar (c, [((No_terminal d),(p11,p12)); ((No_terminal e),(p21,p22))]) acc) else acc 
  | (Regla_gic (c, _))::[] -> acc
  | (Regla_gic (c,[No_terminal d; No_terminal e]))::t-> if (((No_terminal d) = a)&&((No_terminal e) = b)) then cyk_aux2_plus a b (agregar (c, [((No_terminal d),(p11,p12)); ((No_terminal e),(p21,p22))]) acc) p11 p12 p21 p22 t else cyk_aux2_plus a b acc p11 p12 p21 p22 t 
  | (Regla_gic (c, _))::t -> cyk_aux2_plus a b acc p11 p12 p21 p22 t 
;;

let rec cyk_aux_plus acc r p11 p12 p21 p22 = function
    Conjunto [] -> acc
  | Conjunto (((a,_),(b,_))::[]) -> (union (cyk_aux2_plus a b conjunto_vacio p11 p12 p21 p22 r) acc)
  | Conjunto (((a,_),(b,_))::t) -> cyk_aux_plus (union (cyk_aux2_plus a b conjunto_vacio p11 p12 p21 p22 r) acc) r p11 p12 p21 p22 (Conjunto t)
;;

let cyk_plus cadena (Gic (nt, t, Conjunto r, s) as gic) =
  if not (es_fnc gic) then failwith "No_FNC"
  else 
  let n = List.length cadena in
  if (n = 0) then failwith "Cadena_vacía"
  else
  let cyk_table = Array.make_matrix n n conjunto_vacio in
  let cyk_table = fila1_plus cyk_table n cadena r in
  for i = 1 to n-1 do
    for j = 0 to n-1-i do
      for k = 0 to i-1 do
        let simbolos1 = cyk_table.(k).(j) in
        let simbolos2 = cyk_table.(i-k-1).(j+k+1) in
        cyk_table.(i).(j) <- union cyk_table.(i).(j) (cyk_aux_plus conjunto_vacio r k j (i-k-1) (j+k+1) (cartesiano simbolos1 simbolos2)) 
      done;
    done;
  done;
  if (pertenece_plus (No_terminal "S") cyk_table.(n-1).(0)) then (true,(construir_arboles cyk_table cyk_table.(n-1).(0) (No_terminal "S")) []) else (false,[])
;;

let rec concatenar_listas xs ys =
  match xs with
  | [] -> []
  | x::xs' ->
    List.map (fun y -> x ^" "^ y) ys @ concatenar_listas xs' ys
;;

let rec construir_arboles_aux a l = 
  match l with
  | [] -> []
  | hd::tl -> ("("^a^" "^hd^")") :: construir_arboles_aux a tl
;;

let rec construir_arboles cyk_table simbolos s l =
  match simbolos with
    (Conjunto []) -> l
  | (Conjunto ((No_terminal nt, [(No_terminal a,(a1,a2));(No_terminal b,(b1,b2))])::t)) -> 
      if not (No_terminal nt = s) then construir_arboles cyk_table (Conjunto t) s l
      else
      let arboles1 = (construir_arboles cyk_table cyk_table.(a1).(a2) (No_terminal a) []) in
      let arboles2 = (construir_arboles cyk_table cyk_table.(b1).(b2) (No_terminal b) []) in
      construir_arboles cyk_table (Conjunto t) s (construir_arboles_aux nt (concatenar_listas (arboles1) (arboles2)))@l
  | (Conjunto ((No_terminal nt, [(Terminal a,(a1,a2))])::t)) -> 
      if not (No_terminal nt = s) then construir_arboles cyk_table (Conjunto t) s l
      else
      let arbol = "("^nt^" "^a^")" in
      construir_arboles cyk_table (Conjunto t) s (arbol::l)
  | (Conjunto (_::t)) -> construir_arboles cyk_table (Conjunto t) s l
;;

let g_plus = gic_of_string "S A B C; a b; S;
S -> A B | B C;
A -> B A | a;
B -> C C | b;
C -> A B | a;";;

let c_plus = cadena_of_string "b b a b";;

(*cyk_plus c_plus g_plus;;*)

(**Ejercicio 4----------------------------------------------------------------------**)

type regla_gicp =
  Regla_gicp of (simbolo * simbolo list * float);;

type gicp = 
  Gicp of (simbolo conjunto * simbolo conjunto * regla_gicp conjunto * simbolo);;
   
let gicp_of_gic (Gic (vts, vns, Conjunto rs, s)) ps =
  let rs' = List.map2 (fun (Regla_gic (nt, rhs)) p -> Regla_gicp (nt, rhs, p)) (rs) ps in
  Gicp (vts, vns, Conjunto rs', s);;
  

let cumple_fnc2 = function
    (Regla_gicp (a,[Terminal _],_))-> true
  | (Regla_gicp (a,[No_terminal _; No_terminal _],_))-> true
  | (Regla_gicp (a, l, _)) -> false
;;

let es_fnc2 (Gicp (Conjunto nt, Conjunto t, Conjunto r, s)) =  
  let rec es_fnc2_aux = function
      [] -> false
    | h::[] -> cumple_fnc2 h
    | h::t -> if (cumple_fnc2 h) then es_fnc2_aux t else false
  in es_fnc2_aux r
;;

let rec pertenece_prob a = function
    Conjunto [] -> false
  | Conjunto ((h,_)::t) -> if h = a then true else pertenece_prob a (Conjunto t)
;;

let fila1_prob cyk_table n cadena r =
  for i = 0 to n-1 do
    let c = List.nth cadena i in
    cyk_table.(0).(i) <- fila1_aux_prob conjunto_vacio c r;
  done;
  cyk_table
;;

let rec fila1_aux_prob acc h = function
    [] -> acc
  | (Regla_gicp (a,[Terminal b],p))::[] -> if ((Terminal b) = h) then (agregar (a, [(Terminal b,(0,0),p)]) acc) else acc 
  | (Regla_gicp (a, _, _))::[] -> acc
  | (Regla_gicp (a,[Terminal b],p))::t-> if ((Terminal b) = h) then fila1_aux_prob (agregar (a, [(Terminal b,(0,0),p)]) acc) h t else fila1_aux_prob acc h t 
  | (Regla_gicp (a, _, _))::t -> fila1_aux_prob acc h t 
;;

let rec cyk_aux2_prob a b acc p11 p12 p21 p22 = function
    [] -> acc
  | (Regla_gicp (c,[No_terminal d; No_terminal e],p))::[] -> if (((No_terminal d) = a)&&((No_terminal e) = b)) then (agregar (c, [((No_terminal d),(p11,p12),p); ((No_terminal e),(p21,p22),p)]) acc) else acc 
  | (Regla_gicp (c, _, _))::[] -> acc
  | (Regla_gicp (c,[No_terminal d; No_terminal e],p))::t-> if (((No_terminal d) = a)&&((No_terminal e) = b)) then cyk_aux2_prob a b (agregar (c, [((No_terminal d),(p11,p12),p); ((No_terminal e),(p21,p22),p)]) acc) p11 p12 p21 p22 t else cyk_aux2_prob a b acc p11 p12 p21 p22 t 
  | (Regla_gicp (c, _, _))::t -> cyk_aux2_prob a b acc p11 p12 p21 p22 t 
;;

let rec cyk_aux_prob acc r p11 p12 p21 p22 = function
    Conjunto [] -> acc
  | Conjunto (((a,_),(b,_))::[]) -> (union (cyk_aux2_prob a b conjunto_vacio p11 p12 p21 p22 r) acc)
  | Conjunto (((a,_),(b,_))::t) -> cyk_aux_prob (union (cyk_aux2_prob a b conjunto_vacio p11 p12 p21 p22 r) acc) r p11 p12 p21 p22 (Conjunto t)
;;

let cyk_prob cadena (Gicp (nt, t, Conjunto r, s) as gicp) =
  if not (es_fnc2 gicp) then failwith "No_FNC"
  else 
  let n = List.length cadena in
  if (n = 0) then failwith "Cadena_vacía"
  else
  let cyk_table = Array.make_matrix n n conjunto_vacio in
  let cyk_table = fila1_prob cyk_table n cadena r in
  for i = 1 to n-1 do
    for j = 0 to n-1-i do
      for k = 0 to i-1 do
        let simbolos1 = cyk_table.(k).(j) in
        let simbolos2 = cyk_table.(i-k-1).(j+k+1) in
        cyk_table.(i).(j) <- union cyk_table.(i).(j) (cyk_aux_prob conjunto_vacio r k j (i-k-1) (j+k+1) (cartesiano simbolos1 simbolos2)) 
      done;
    done;
  done;
  if (pertenece_prob (No_terminal "S") cyk_table.(n-1).(0)) then (true,(construir_arboles_prob cyk_table cyk_table.(n-1).(0) (No_terminal "S")) []) else (false,[])
;;

let rec concatenar_listas_prob xs ys =
  match xs with
  | [] -> []
  | (x, px)::xs' ->
    List.map (fun (y, py) -> (x ^" "^ y, px *. py)) ys @ concatenar_listas_prob xs' ys
;;

let rec construir_arboles_prob_aux a p l = 
  match l with
  | [] -> []
  | (s,p1)::tl -> (("("^a^" "^s^")"),p1*.p) :: construir_arboles_prob_aux a p tl
;;
let multiplicar_lista numeros =
  List.fold_left (fun acumulador numero -> acumulador *. numero) 1.0 numeros;;

let rec construir_arboles_prob cyk_table simbolos s l =
  match simbolos with
    (Conjunto []) -> l
  | (Conjunto ((No_terminal nt, [(No_terminal a,(a1,a2),p);(No_terminal b,(b1,b2),p)])::t)) -> 
      if not (No_terminal nt = s) then construir_arboles_prob cyk_table (Conjunto t) s l
      else
      let arboles1 = (construir_arboles_prob cyk_table cyk_table.(a1).(a2) (No_terminal a) []) in
      let arboles2 = (construir_arboles_prob cyk_table cyk_table.(b1).(b2) (No_terminal b) []) in
      construir_arboles_prob cyk_table (Conjunto t) s (construir_arboles_prob_aux nt p (concatenar_listas_prob (arboles1) (arboles2)))@l
  | (Conjunto ((No_terminal nt, [(Terminal a,(a1,a2),p)])::t)) -> 
      if not (No_terminal nt = s) then construir_arboles_prob cyk_table (Conjunto t) s l
      else
      let arbol = ("("^nt^" "^a^")",p) in
      construir_arboles_prob cyk_table (Conjunto t) s (arbol::l)
  | (Conjunto (_::t)) -> construir_arboles_prob cyk_table (Conjunto t) s l
;;

(**Ejercicio 4----------------------------------------------------------------------**)

type regla_gicp =
  Regla_gicp of (simbolo * simbolo list * float);;

type gicp = 
  Gicp of (simbolo conjunto * simbolo conjunto * regla_gicp conjunto * simbolo);;
   
let gicp_of_gic (Gic (vts, vns, Conjunto rs, s)) ps =
  let rs' = List.map2 (fun (Regla_gic (nt, rhs)) p -> Regla_gicp (nt, rhs, p)) (rs) ps in
  Gicp (vts, vns, Conjunto rs', s);;
  

let cumple_fnc2 = function
    (Regla_gicp (a,[Terminal _],_))-> true
  | (Regla_gicp (a,[No_terminal _; No_terminal _],_))-> true
  | (Regla_gicp (a, l, _)) -> false
;;

let es_fnc2 (Gicp (Conjunto nt, Conjunto t, Conjunto r, s)) =  
  let rec es_fnc2_aux = function
      [] -> false
    | h::[] -> cumple_fnc2 h
    | h::t -> if (cumple_fnc2 h) then es_fnc2_aux t else false
  in es_fnc2_aux r
;;

let rec pertenece_prob a = function
    Conjunto [] -> false
  | Conjunto ((h,_,_)::t) -> if h = a then true else pertenece_prob a (Conjunto t)
;;

let fila1_prob cyk_table n cadena r =
  for i = 0 to n-1 do
    let c = List.nth cadena i in
    cyk_table.(0).(i) <- fila1_aux_prob conjunto_vacio c r;
  done;
  cyk_table
;;

let rec fila1_aux_prob acc h = function
    [] -> acc
  | (Regla_gicp (a,[Terminal b],p))::[] -> if ((Terminal b) = h) then (agregar (a, [(Terminal b,(0,0))], p) acc) else acc 
  | (Regla_gicp (a, _, _))::[] -> acc
  | (Regla_gicp (a,[Terminal b],p))::t-> if ((Terminal b) = h) then fila1_aux_prob (agregar (a, [(Terminal b,(0,0))], p) acc) h t else fila1_aux_prob acc h t 
  | (Regla_gicp (a, _, _))::t -> fila1_aux_prob acc h t 
;;

let rec cyk_aux2_prob a b acc p11 p12 p21 p22 = function
    [] -> acc
  | (Regla_gicp (c,[No_terminal d; No_terminal e],p))::[] -> if (((No_terminal d) = a)&&((No_terminal e) = b)) then (agregar (c, [((No_terminal d),(p11,p12)); ((No_terminal e),(p21,p22))], p) acc) else acc 
  | (Regla_gicp (c, _, _))::[] -> acc
  | (Regla_gicp (c,[No_terminal d; No_terminal e],p))::t-> if (((No_terminal d) = a)&&((No_terminal e) = b)) then cyk_aux2_prob a b (agregar (c, [((No_terminal d),(p11,p12)); ((No_terminal e),(p21,p22))], p) acc) p11 p12 p21 p22 t else cyk_aux2_prob a b acc p11 p12 p21 p22 t 
  | (Regla_gicp (c, _, _))::t -> cyk_aux2_prob a b acc p11 p12 p21 p22 t 
;;

let rec cyk_aux_prob acc r p11 p12 p21 p22 = function
    Conjunto [] -> acc
  | Conjunto (((a,_,_),(b,_,_))::[]) -> (union (cyk_aux2_prob a b conjunto_vacio p11 p12 p21 p22 r) acc)
  | Conjunto (((a,_,_),(b,_,_))::t) -> cyk_aux_prob (union (cyk_aux2_prob a b conjunto_vacio p11 p12 p21 p22 r) acc) r p11 p12 p21 p22 (Conjunto t)
;;

let cyk_prob cadena (Gicp (nt, t, Conjunto r, s) as gicp) =
  if not (es_fnc2 gicp) then failwith "No_FNC"
  else 
  let n = List.length cadena in
  if (n = 0) then failwith "Cadena_vacía"
  else
  let cyk_table = Array.make_matrix n n conjunto_vacio in
  let cyk_table = fila1_prob cyk_table n cadena r in
  for i = 1 to n-1 do
    for j = 0 to n-1-i do
      for k = 0 to i-1 do
        let simbolos1 = cyk_table.(k).(j) in
        let simbolos2 = cyk_table.(i-k-1).(j+k+1) in
        cyk_table.(i).(j) <- union cyk_table.(i).(j) (cyk_aux_prob conjunto_vacio r k j (i-k-1) (j+k+1) (cartesiano simbolos1 simbolos2)) 
      done;
    done;
  done;
  if (pertenece_prob (No_terminal "S") cyk_table.(n-1).(0)) then (true,(construir_arboles_prob cyk_table cyk_table.(n-1).(0) (No_terminal "S")) []) else (false,[])
;;

let rec concatenar_listas_prob xs ys =
  match xs with
  | [] -> []
  | (x, px)::xs' ->
    List.map (fun (y, py) -> (x ^" "^ y, px *. py)) ys @ concatenar_listas_prob xs' ys
;;

let rec construir_arboles_prob_aux a p l = 
  match l with
  | [] -> []
  | (s,p1)::tl -> (("("^a^" "^s^")"),p1*.p) :: construir_arboles_prob_aux a p tl
;;
let multiplicar_lista numeros =
  List.fold_left (fun acumulador numero -> acumulador *. numero) 1.0 numeros;;

let rec construir_arboles_prob cyk_table simbolos s l =
  match simbolos with
    (Conjunto []) -> l
  | (Conjunto ((No_terminal nt, [(No_terminal a,(a1,a2));(No_terminal b,(b1,b2))], p)::t)) -> 
      if not (No_terminal nt = s) then construir_arboles_prob cyk_table (Conjunto t) s l
      else
      let arboles1 = (construir_arboles_prob cyk_table cyk_table.(a1).(a2) (No_terminal a) []) in
      let arboles2 = (construir_arboles_prob cyk_table cyk_table.(b1).(b2) (No_terminal b) []) in
      construir_arboles_prob cyk_table (Conjunto t) s (construir_arboles_prob_aux nt p (concatenar_listas_prob (arboles1) (arboles2)))@l
  | (Conjunto ((No_terminal nt, [(Terminal a,(a1,a2))], p)::t)) -> 
      if not (No_terminal nt = s) then construir_arboles_prob cyk_table (Conjunto t) s l
      else
      let arbol = ("("^nt^" "^a^")",p) in
      construir_arboles_prob cyk_table (Conjunto t) s (arbol::l)
  | (Conjunto (_::t)) -> construir_arboles_prob cyk_table (Conjunto t) s l
;;
