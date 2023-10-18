(*Pablo Fernández Pérez. Grupo 3.3 TC*)

(**Ejercicio 1----------------------------------------------------------------------**)
let rec mapdoble f1 f2 = function
    [] -> []
  | h::[] -> [f1 h]
  | h1::h2::t -> f1 h1 :: f2 h2 :: mapdoble f1 f2 t
;;

(*val mapdoble : ('a -> 'b) -> ('a -> 'b) -> 'a list -> 'b list = <fun>*)
(*La función mapdoble toma dos funciones que convierten un valor del tipo 'a en un valor del tipo 'b, seguidas por una lista de valores del tipo 'a. 
  La función devuelve una lista de valores del tipo 'b. 'a y 'b son tipos polimórficos, lo que significa que pueden representar cualquier tipo.*)

(*mapdoble (function x -> x) (function x -> -x) [1;1;1;1;1];;*)

(*mapdoble (function x -> x*2) (function x -> "x") [1;2;3;4;5];;*)
(*Error: This expression has type string but an expression was expected of type int*)
(*En OCaml tenemos a' lists que pueden ser de cualquier tipo de datos, pero todos sus elementos tienen que ser del mismo tipo. 
  No podemos tener por lo tanto una lista que contenga tanto elementos de tipo entero como de tipo string.*)
  
(*let y = function x -> 5 in mapdoble y;;*)
(*('_weak1 -> int) -> '_weak1 list -> int list = <fun>*)
(*Estamos haciendo una definición parcial de mapdoble. Hay cosas ya definidas y otras que quedan en el aire (para expresar esto último, OCaml utliza el tipo "weak").
  Tipo débil => Todavía no se sabe lo que es, pero cuando se use sí que se va a saber. Esto podemos observarlo si probamos, por ejemplo: 
  - En primer lugar -> mapdoble (function x -> x);;
  - Después         -> mapdoble (function x -> x) (function x -> -x);;*)
  
(*Más ejemplos:
mapdoble (function x -> x) (function x -> x*2) [1;2;3;4];;
mapdoble (function x -> x) (function x -> x*2) [];;
mapdoble (function x -> "impar") (function x -> "par") [1;2;3];;
*)

(**Ejercicio 2----------------------------------------------------------------------**)
let rec primero_que_cumple f = function
    [] -> raise Not_found
  | h::t -> if f h = true then h
                     else primero_que_cumple f t
;;

(*val primero_que_cumple : ('a -> bool) -> 'a list -> 'a = <fun>*)

(*Ejemplos
primero_que_cumple (function x -> x>2) [1;0;2;3;4];;
primero_que_cumple (function x -> x>2) [1;0;2];;
primero_que_cumple (function x -> (String.length x) = 4) ["s";"hola";"q";"casa"];;
*)

let existe f l =
  try
    (primero_que_cumple f l;
     true)
  with
  | Not_found -> false
;;

(*Ejemplos
existe (function x -> x>2) [1;0;2;3;4];;
existe (function x -> x>2) [1;0;2];;
existe (function x -> (String.length x) = 4) ["s";"hola";"q";"casa"];;
*)

let rec asociado l a = 
  snd(primero_que_cumple (function x,y -> x = a) l)
;;

(*Ejemplos
asociado [(1,"a");(2,"b");(3,"c");(4,"d")] 3;;
asociado [(1,"a");(2,"b");(3,"c");(4,"d");(3,"e")] 3;;
asociado [(1,"a");(2,"b");(3,"c");(4,"d")] 5;;
*)

(**Ejercicio 3----------------------------------------------------------------------**)
type 'a arbol_binario =
Vacio
| Nodo of 'a * 'a arbol_binario * 'a arbol_binario;;

(*Para ejemplos:
let t1 = Nodo(3, Nodo(2, Vacio, Vacio), Nodo(5, Nodo(4, Vacio, Vacio), Nodo(1, Vacio, Vacio)));;

let t2 = Nodo(3, Nodo(2,  Nodo(4, Vacio, Vacio), Nodo(1, Vacio, Vacio)), Nodo(5, Vacio, Vacio));;

let t3 = Nodo(1, Nodo(2,  Nodo(4, Nodo(8, Vacio, Vacio), Nodo(9, Vacio, Vacio)), Nodo(5, Nodo(10, Vacio, Vacio), Nodo(11, Vacio, Vacio))), Nodo(3, Nodo(6, Nodo(12, Vacio, Vacio), Nodo(13, Vacio, Vacio)), Nodo(7, Nodo(14, Vacio, Vacio), Nodo(15, Vacio, Vacio))));;
*)

let rec in_orden = function
    Vacio-> []
  | Nodo (x,i,d) -> (in_orden i) @ (x::(in_orden d))
;;

(*
in_orden t1;;
in_orden t2;;
in_orden t3;;
*)

let rec pre_orden = function
    Vacio-> []
  | Nodo (x,i,d) -> (x::(pre_orden i)) @ (pre_orden d)
;;

(*
pre_orden t1;;
pre_orden t2;;
pre_orden t3;;
*)

let rec post_orden = function
    Vacio-> []
  | Nodo (x,i,d) -> ((post_orden i) @ (post_orden d) @ [x])
;;

(*
post_orden t1;;
post_orden t2;;
post_orden t3;;
*)

let rec anchura t =
  let rec aux acc = function
      [] -> List.rev acc
    | Nodo (x, i, d)::tail ->
      aux (x::acc) (tail @ [i;d])
    | Vacio :: tail -> aux acc tail
  in
  aux [] [t]
;;

(*
anchura t1;;
anchura t2;;
anchura t3;;
*)

(**Ejercicio 4----------------------------------------------------------------------**)
type 'a conjunto = Conjunto of 'a list;;

let conjunto_vacio = Conjunto [];;

let rec pertenece a = function
    Conjunto [] -> false
  | Conjunto (h::t) -> if h = a then true else pertenece a (Conjunto t)
;;

(*  
pertenece 2 (Conjunto [1;2;3;4]);;
pertenece 2 (Conjunto [1;3;4]);;
*)

let agregar a (Conjunto c) = 
  if (pertenece a (Conjunto c)) then (Conjunto c) else (Conjunto (a::c))
;;

(*
agregar 2 (Conjunto [1;2;3;4]);;
agregar 2 (Conjunto [1;3;4]);;
*)

let conjunto_of_list l =
  let rec aux c = function
      [] -> c
    | h::t -> aux (agregar h c) t 
  in aux (Conjunto []) l
;;
    
(*
conjunto_of_list [1;2;2;4;3;4];;
conjunto_of_list [];;
*)

let suprimir a (Conjunto c) = 
  let rec aux a c acc = function
      [] -> Conjunto c
    | h::t -> if h = a then Conjunto (acc @ t) else aux a c (h::acc) t
  in aux a c [] c
;;

(*
suprimir 2 (Conjunto [1;2;3;4]);;
suprimir 2 (Conjunto [1;3;4]);;
suprimir 1 (Conjunto [1;3;4]);;
suprimir 4 (Conjunto [1;3;4]);;
*)

let rec cardinal c = 
  let rec aux acc = function
      Conjunto [] -> acc
    | Conjunto (h::t) -> aux (acc+1) (Conjunto t)
  in aux 0 c
;;

(*
cardinal (Conjunto [1;2;3;4;5]);;
cardinal (Conjunto []);;
*)

let union (Conjunto c1) (Conjunto c2) = 
  let rec aux c1 c2 acc = match c1, c2 with
      c1, [] -> Conjunto c1
    | [], c2 -> acc 
    | h1::t1, c2 -> aux t1 c2 (agregar h1 acc)
  in aux c1 c2 (Conjunto c2)
;;

(*
union (Conjunto [1;2;3;4;5]) (Conjunto [5;6;7]);;
union (Conjunto [1;2;3]) (Conjunto [3;4;5;6;7]);;
union (Conjunto []) (Conjunto [5;6;7]);;
union (Conjunto [1;2;3;4;5]) (Conjunto []);;
*)

let interseccion (Conjunto c1) (Conjunto c2) = 
  let rec aux c1 c2 acc = match c1, c2 with
      c1, [] -> Conjunto []
    | [], c2 -> Conjunto acc 
    | h1::t1, c2 -> if (pertenece h1 (Conjunto c2)) then aux t1 c2 (h1::acc) else aux t1 c2 acc
  in aux c1 c2 []
;;

(*
interseccion (Conjunto [1;2;3;4;5;6]) (Conjunto [5;6;7]);;
interseccion (Conjunto [1;2;3;4]) (Conjunto [3;4;5;6;7]);;
interseccion (Conjunto []) (Conjunto [5;6;7]);;
interseccion (Conjunto [1;2;3;4;5]) (Conjunto []);;
*)

let diferencia (Conjunto c1) (Conjunto c2) = 
  let rec aux c1 c2 acc = match c1, c2 with
      c1, [] -> acc
    | [], c2 -> acc 
    | c1, h::t -> aux c1 t (suprimir h acc)
  in aux c1 c2 (Conjunto c1)
;;

(*
diferencia (Conjunto [1;2;3;4;5;6]) (Conjunto [5;6;7]);;
diferencia (Conjunto [1;2;3;4]) (Conjunto [3;4;5;6;7]);;
diferencia (Conjunto []) (Conjunto [5;6;7]);;
diferencia (Conjunto [1;2;3;4;5]) (Conjunto []);;
*)

let incluido (Conjunto c1) (Conjunto c2) = 
  let rec aux c1 c2 = match c1, c2 with
      [], [] -> true
    | c1, [] -> false
    | [], c2 -> true 
    | h1::t1, c2 -> if (pertenece h1 (Conjunto c2)) then aux t1 c2 else false
  in aux c1 c2
;;

(*
incluido (Conjunto [1;2;3]) (Conjunto [1;2;3;4;5]);;
incluido (Conjunto [1;2;3]) (Conjunto [1;2;4;5;6]);;
incluido (Conjunto []) (Conjunto [5;6;7]);;
incluido (Conjunto [1;2;3]) (Conjunto []);;
*)

let igual c1 c2 =
  if ((cardinal c1)=(cardinal c2)) then (incluido c1 c2)
  else false
;;

(*
igual (Conjunto [1;2;3]) (Conjunto [2;1;3]);;
igual (Conjunto [1;2;3]) (Conjunto [1;2;3;4]);;
igual (Conjunto []) (Conjunto [5;6;7]);;
igual (Conjunto [1;2;3]) (Conjunto []);;
igual (Conjunto []) (Conjunto []);;
*)

let producto_cartesiano (Conjunto c1) (Conjunto c2) = 
  let rec aux c1 c2 acc1 acc2= match c1, c2 with
      [], c2 -> Conjunto acc1
    | h1::t1, [] -> aux t1 acc2 acc1 acc2
    | h1::t1, h2::t2 -> aux (h1::t1) t2 ((h1,h2)::acc1) acc2
  in aux c1 c2 [] c2
;;

(*
producto_cartesiano (Conjunto [1;2;3]) (Conjunto [4;5;6;7]);;
producto_cartesiano (Conjunto [1;2]) (Conjunto [1;2;3]);;
producto_cartesiano (Conjunto []) (Conjunto [5;6;7]);;
producto_cartesiano (Conjunto [1;2;3]) (Conjunto []);;
producto_cartesiano (Conjunto []) (Conjunto []);;
*)

let list_of_conjunto = function
    Conjunto x -> x
;;

(*
list_of_conjunto (Conjunto [1;2;3;4]);;
list_of_conjunto (Conjunto []);;
*)
