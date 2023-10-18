(*Pablo Fernández Pérez. Grupo 3.3 TC*)

(**Ejercicio 1----------------------------------------------------------------------**)

(*AFN-ε -> presenta transiciones que no consumen ningún símbolo.*)
let es_afne (Af (_, _, _, Conjunto arcos, _)) =
  let rec aux = function
      [] -> false
    | (Arco_af (e1, e2, s))::t -> if s = (Terminal "") then true else aux t
  in
    aux arcos
;;

(*AFN -> presenta algún estado, el cual, ante un mismo símbolo de entrada, puede transitar a varios estados diferentes.*)
let es_afn (Af (_, _, _, Conjunto arcos, _)) =
  let aux acc = function
      [] -> false
    | (Arco_af (e1, e2, s))::t -> if s = (Terminal "") then false else if (pertenece (e1,s) acc) then true else aux (agregar (e1,s) acc) t
  in
    aux conjunto_vacio arcos
;;

(*AFD -> la función de transición está completamente especificada, para cada par (estado, símbolo) hay un único destino (si hubiese más no sería una función).*)
let es_afd (Af (q, a, _, Conjunto tr, _) as af) =
  if (es_afn af)
    then false
    else let rec aux acc qs = function
        [] -> igual acc qs
      | (Arco_af (e1, e2, s))::t -> if (((pertenece e2 q) = false) || (s = (Terminal ""))) then false else aux (agregar (e1,s) acc) qs t
    in
    aux conjunto_vacio (cartesiano q a) tr
;;

(*Ejemplos:*)
let afne = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
          Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "1", Estado "1", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "a");
                    Arco_af (Estado "2", Estado "0", Terminal "");
                    Arco_af (Estado "2", Estado "3", Terminal "");
                    Arco_af (Estado "2", Estado "3", Terminal "c")],
          Conjunto [Estado "1"; Estado "3"]);;
          
let afn = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
          Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "1", Estado "1", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "a");
                    Arco_af (Estado "2", Estado "0", Terminal "c");
                    Arco_af (Estado "2", Estado "3", Terminal "c")],
          Conjunto [Estado "1"; Estado "3"]);;
          
let afd = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
          Conjunto [Terminal "a"; Terminal "b"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "0", Estado "2", Terminal "b");
                    Arco_af (Estado "1", Estado "1", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "a");
                    Arco_af (Estado "2", Estado "3", Terminal "a");
                    Arco_af (Estado "2", Estado "3", Terminal "b");
                    Arco_af (Estado "3", Estado "3", Terminal "a");
                    Arco_af (Estado "3", Estado "3", Terminal "b")],
          Conjunto [Estado "1"; Estado "3"]);;

(*En el siguiente caso no está definida la transición del par (Estado "1", Terminal "b")*)
let af = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
          Conjunto [Terminal "a"; Terminal "b"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "0", Estado "2", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "a");
                    Arco_af (Estado "2", Estado "3", Terminal "a");
                    Arco_af (Estado "2", Estado "3", Terminal "b");
                    Arco_af (Estado "3", Estado "3", Terminal "a");
                    Arco_af (Estado "3", Estado "3", Terminal "b")],
          Conjunto [Estado "1"; Estado "3"]);;

(**Ejercicio 2----------------------------------------------------------------------**)

(*Dados los estados actuales en cada autómata se calculan los alcanzados con cada símbolo, que se van añadiendo a la cola*)
(*Además, es necesario aplicar epsilon cierre a los estados alcanzados mediante símbolos para obtener todos los nuevos estados*)
let rec nuevos_estados s c1 c2 af1 af2 cola = match s with
    [] -> List.rev cola
  | h::t -> nuevos_estados t c1 c2 af1 af2 (((epsilon_cierre (avanza h c1 af1) af1),(epsilon_cierre (avanza h c2 af2) af2))::cola)
;;
        
(*Comprueba si un conjunto contiene algún estado final*)
let rec contiene_final f = function
    Conjunto [] -> false
  | Conjunto (h::t) -> if (pertenece h f) then true else (contiene_final f (Conjunto t))
;;
   
let equivalentes (Af (q1, s1, i1, t1, f1) as af1) (Af (q2, s2, i2, t2, f2) as af2) =
  let rec aux (Conjunto s) cola visitados = match cola, visitados with
      [], _ -> true
    | (Conjunto [], Conjunto [])::t, visitados -> aux (Conjunto s) t visitados 
    | (c1,c2)::t, visitados -> if (pertenece (c1,c2) visitados) 
                                 then aux (Conjunto s) t visitados 
                                 else if ((contiene_final f1 c1)&&(not (contiene_final f2 c2))||((not (contiene_final f1 c1))&&(contiene_final f2 c2))) 
                                        then false (*Si uno de los conjuntos contiene un estado final y el otro no, podemos asegurar que los afs no son equivalentes*)
                                        else aux (Conjunto s) (nuevos_estados s c1 c2 af1 af2 (List.rev cola)) (agregar (c1,c2) visitados)
  in
    aux (union s1 s2) [((epsilon_cierre (Conjunto [i1]) af1),(epsilon_cierre (Conjunto [i2]) af2))] conjunto_vacio
;;

(*Ejemplos:*)

(*Equivalencia AFN - AFD diapositiva 29*)
let afn21 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
          Conjunto [Terminal "a"; Terminal "b"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "0", Estado "2", Terminal "a");
                    Arco_af (Estado "2", Estado "3", Terminal "b");
                    Arco_af (Estado "3", Estado "2", Terminal "a")],
          Conjunto [Estado "1"; Estado "3"]);;
          
let afd21 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"; Estado "4"],
          Conjunto [Terminal "a"; Terminal "b"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "0", Estado "4", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "b");
                    Arco_af (Estado "1", Estado "4", Terminal "a");
                    Arco_af (Estado "2", Estado "3", Terminal "a");
                    Arco_af (Estado "2", Estado "4", Terminal "b");
                    Arco_af (Estado "3", Estado "2", Terminal "b");
                    Arco_af (Estado "3", Estado "4", Terminal "a");
                    Arco_af (Estado "4", Estado "4", Terminal "a");
                    Arco_af (Estado "4", Estado "4", Terminal "b")],
          Conjunto [Estado "1"; Estado "2"]);;
          
(*Equivalencia AFN-ε - AFN - AFD diapositiva 40*)
let afne22 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"; Estado "4"],
          Conjunto [Terminal "a"; Terminal "b"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "");
                    Arco_af (Estado "0", Estado "3", Terminal "a");
                    Arco_af (Estado "1", Estado "2", Terminal "");
                    Arco_af (Estado "1", Estado "2", Terminal "a");
                    Arco_af (Estado "3", Estado "4", Terminal "b");
                    Arco_af (Estado "4", Estado "1", Terminal "");
                    Arco_af (Estado "4", Estado "0", Terminal "b")],
          Conjunto [Estado "2"]);;
          
let afn22 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"; Estado "4"],
          Conjunto [Terminal "a"; Terminal "b"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "2", Terminal "a");
                    Arco_af (Estado "0", Estado "3", Terminal "a");
                    Arco_af (Estado "3", Estado "2", Terminal "b");
                    Arco_af (Estado "3", Estado "4", Terminal "b");
                    Arco_af (Estado "3", Estado "1", Terminal "b");
                    Arco_af (Estado "4", Estado "2", Terminal "a");
                    Arco_af (Estado "4", Estado "2", Terminal "b");
                    Arco_af (Estado "4", Estado "1", Terminal "b");
                    Arco_af (Estado "4", Estado "0", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "a")],
          Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "4"]);;

let af22 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"; Estado "4"],
          Conjunto [Terminal "a"; Terminal "b"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "1", Estado "2", Terminal "b");
                    Arco_af (Estado "2", Estado "3", Terminal "a");
                    Arco_af (Estado "2", Estado "4", Terminal "b");
                    Arco_af (Estado "4", Estado "1", Terminal "a")],
          Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"; Estado "4"]);;

(*Incluyendo estado sumidero*)
let afd22 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"; Estado "4"; Estado "5"],
          Conjunto [Terminal "a"; Terminal "b"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "0", Estado "5", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "b");
                    Arco_af (Estado "1", Estado "5", Terminal "a");
                    Arco_af (Estado "2", Estado "3", Terminal "a");
                    Arco_af (Estado "2", Estado "4", Terminal "b");
                    Arco_af (Estado "3", Estado "5", Terminal "a");
                    Arco_af (Estado "3", Estado "5", Terminal "b");
                    Arco_af (Estado "4", Estado "1", Terminal "a");
                    Arco_af (Estado "4", Estado "5", Terminal "b");
                    Arco_af (Estado "5", Estado "5", Terminal "a");
                    Arco_af (Estado "5", Estado "5", Terminal "b")],
          Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"; Estado "4"]);;

(*Equivalencia AFN-ε - AFN - AFD diapositiva 42*)
let afne23 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"],
          Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "0", Terminal "a");
                    Arco_af (Estado "0", Estado "1", Terminal "");
                    Arco_af (Estado "1", Estado "1", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "");
                    Arco_af (Estado "2", Estado "2", Terminal "c")],
          Conjunto [Estado "2"]);;

let afn23 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"],
          Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "0", Terminal "a");
                    Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "0", Estado "1", Terminal "b");
                    Arco_af (Estado "0", Estado "2", Terminal "a");
                    Arco_af (Estado "0", Estado "2", Terminal "b");
                    Arco_af (Estado "0", Estado "2", Terminal "c");
                    Arco_af (Estado "1", Estado "1", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "b");
                    Arco_af (Estado "1", Estado "2", Terminal "c");
                    Arco_af (Estado "2", Estado "2", Terminal "c")],
          Conjunto [Estado "0"; Estado "1"; Estado "2"]);;

let af23 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
          Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "0", Estado "2", Terminal "b");
                    Arco_af (Estado "0", Estado "3", Terminal "c");
                    Arco_af (Estado "1", Estado "1", Terminal "a");
                    Arco_af (Estado "1", Estado "2", Terminal "b");
                    Arco_af (Estado "1", Estado "3", Terminal "c");
                    Arco_af (Estado "2", Estado "2", Terminal "b");
                    Arco_af (Estado "2", Estado "3", Terminal "c");
                    Arco_af (Estado "3", Estado "3", Terminal "c")],
          Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"]);;

(*Incluyendo estado sumidero*)
let afd23 = Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"; Estado "4"],
          Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
          Estado "0",
          Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
                    Arco_af (Estado "0", Estado "2", Terminal "b");
                    Arco_af (Estado "0", Estado "3", Terminal "c");
                    Arco_af (Estado "1", Estado "1", Terminal "a");
                    Arco_af (Estado "1", Estado "2", Terminal "b");
                    Arco_af (Estado "1", Estado "3", Terminal "c");
                    Arco_af (Estado "2", Estado "4", Terminal "a");
                    Arco_af (Estado "2", Estado "2", Terminal "b");
                    Arco_af (Estado "2", Estado "3", Terminal "c");
                    Arco_af (Estado "3", Estado "4", Terminal "a");
                    Arco_af (Estado "3", Estado "4", Terminal "b");
                    Arco_af (Estado "3", Estado "3", Terminal "c");
                    Arco_af (Estado "4", Estado "4", Terminal "a");
                    Arco_af (Estado "4", Estado "4", Terminal "b");
                    Arco_af (Estado "4", Estado "4", Terminal "c")],
          Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"]);;
          
(**Ejercicio 3----------------------------------------------------------------------**)

let escaner_afn cadena (Af (_, _, inicial, _, finales) as af) =
  if not (es_afn af) then failwith "Not_AFN"
  else
   let rec aux = function
        (Conjunto [], _) -> false
      | (actuales, []) -> not (es_vacio (interseccion actuales finales))
      | (actuales, simbolo :: t) -> aux ((avanza simbolo actuales af), t)
   in
      aux ((Conjunto [inicial]), cadena)
   ;;
   
let escaner_afd cadena (Af (_, _, inicial, Conjunto arcos, finales) as af) =
  if not (es_afd af) then failwith "Not_AFD"
  else
   let rec aux = function
        (actual, []) -> (pertenece actual finales)
      | (actual, simbolo :: t) ->
           let arco = List.find (fun (Arco_af(o, d, s)) -> o = actual && s = simbolo) arcos in
           let nuevo_estado = match arco with Arco_af(o, d, s) -> d in
           aux (nuevo_estado, t)
   in
      aux (inicial, cadena)
   ;;
   
(*Ejemplos:*)
(*
escaner_afn [Terminal "a"; Terminal "b"; Terminal "a"; Terminal "c"] afn;;
escaner_afn [Terminal "a"; Terminal "b"; Terminal "a"] afn;;

escaner_afd [Terminal "a"; Terminal "a"; Terminal "b"] afd;;
escaner_afd [Terminal "a"; Terminal "a"] afd;;
*)
