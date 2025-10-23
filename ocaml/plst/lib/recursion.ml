(* SCW note: SHIFT+ENTER sends a selection to utop in vscode *)

type nat = O | S of nat


let n1 : nat = S O
let n2 : nat = S n1
let n3 : nat = S n2
let n4 : nat = S n3
let n5 : nat = S n4

let succ : nat -> nat = fun x -> S x


(* begin double *)
let rec double : nat -> nat = fun x -> 
  match x with 
  | O -> O
  | S y -> succ (succ (double y))
(* end double *)
  

(* --------------------------------------------------- *)


type void

(*
let rec x : void = x
*)


(* begin loop *)
let rec f : int -> void = 
  fun x -> f x

let loop : void = f 0 
(* end loop *)


(* --------------------------------------------------- *)

(* mutual recursion *)
(* begin mutual *)
let rec even : nat -> bool = fun x -> 
  match x with 
  | O -> true
  | S y -> odd y
  and 
  odd : nat -> bool = fun x -> 
  match x with 
  | O -> false 
  | S y -> even y
(* end mutual *)

let b1 : bool = even n2
let b2 : bool = odd n2



(* begin single *)
let rec even : nat -> bool = fun x -> 
  match x with 
  | O -> true
  | S y -> match y with 
           | O -> false 
           | S z -> even z

let odd : nat -> bool = fun x -> 
  match x with 
  | O -> false 
  | S y -> even y
(* end single *)


(* recursive product definition *)
(* begin product *)
type oe = { odd : nat -> bool ; even : nat -> bool }

let rec obj : oe = { odd = (fun x -> 
                              match x with 
                              | O -> false 
                              | S y -> obj.even y) ;
                    even = (fun x -> 
                              match x with 
                              | O -> true
                              | S y -> obj.odd y
                           )
                    }
(* end product *)                          


(* begin stream *)
type stream = Cons of int * stream

let rec zeros : stream = Cons (0, zeros)
(* end stream *)

(* begin maps *)
let rec map_stream f = fun y -> 
  match y with 
  | Cons (x, s) -> Cons (f x, map_stream f s)
(* end maps *)

(* 
(* begin ones *)
let ones : stream = map_stream (fun x -> x + 1) zeros   
(* end ones *)
*)


let rec append : int list -> stream -> stream = 
  fun l s ->
    match l with 
    | [] -> s 
    | h :: t -> Cons (h, append t s) 

let example : stream = append [1;2;3;4;5] zeros

(* begin streamex *)
let rec take : nat -> stream -> int list * stream = fun n s -> 
  match n with
  | O -> ([],s)
  | S m -> match s with 
           | Cons (x, s') -> 
              let (tl, s'') = take m s' in (x :: tl, s'')

let (example,_)  = take n5 zeros
(* end streamex *)

(* begin takeomega *)
let rec omega : nat = S omega 
let example = take omega zeros 
(* end takeomega *)

(* ----------------------------------------- *)

(* Y-combinator: implementating recursive definitions via recursive types *)
(* Inspiration from: Felleisen, the Little Schemer *)

(* A simple recursive function *)

(* begin length *)
let rec length : int list -> int = fun l ->
    match l with 
    | [] -> 0
    | _ :: l' -> 1 + length l'
(* end length *)
let _ = length [1;2;3;4]

(* Can we implement length without using let rec? Yes! *)
(* begin length2 *)
let bottom : int list -> int = 
  fun _ -> failwith "<loops>"

let length0 : int list -> int = bottom

let length1 : int list -> int = fun l -> 
  match l with
  | [] -> 0
  | _ :: l' -> 1 + length0 l'

let length2 : int list -> int = fun l -> 
  match l with 
  | [] -> 0
  | _ :: l' -> 1 + length1 l'
(* end length2 *)
let _ = length2 [1]

(* or (self contained version) *)
let length2 : int list -> int = 
  ((fun length ->
     (fun l -> 
        match l with 
        | [] -> 0
        | _ :: l' -> 1 + length l'))
    ((fun length -> 
        (fun l -> 
           match l with
           | [] -> 0
           | _ :: l' -> 1 + length l'))
        bottom))

let _ = length2 [1]


(* refactored *)

(* begin refactored2 *)
let mk_length : (int list -> int) -> int list -> int = 
  fun length -> 
     (fun l -> 
        match l with 
        | [] -> 0
        | _ :: l' -> 1 + length l')

let length2 : int list -> int = 
  (fun f -> (f (f bottom)))
  mk_length
(* end refactored2 *)
let _ = length2 [1]

(* now it is easier to extend *)

(* works for all lists < 3 *)
let length3 : int list -> int = 
  (fun f -> (f (f (f bottom))))
  mk_length

let _ = length3 [1;2]

(* works for all lists < 4 *)
(* begin length4 *)
let length4 : int list -> int = 
  (fun f -> (f (f (f (f bottom)))))
  mk_length
(* end length4 *)

let _ = length4 [1;2;3]


(* We would like to say this in OCaml to get the full version of 
   the length function. But RHS must be a value *)

(*
let rec length : int list -> int = 
  (fun f -> f length)
  mk_length

OR:

let rec length : int list -> int = 
  mk_length length
*)

(* begin lengthrec *)
let rec length : int list -> int = 
  fun l -> 
    mk_length length
    l
(* end lengthrec *)

let _ = length [1;2;3]

(* What we really want: SELF APPLICATION *)

(* begin lengthrec2 *)
let rec length : int list -> int = 
  fun l -> 
    mk_length (fun l -> mk_length length l)
    l
(* end lengthrec2 *)
let _ = length [1;2;3]

let rec length : int list -> int = 
  fun l -> 
    mk_length (fun l -> mk_length (fun l -> mk_length length l) l)
    l
let _ = length [1;2;3]

(* BIG LEAP: SELF APPLICATION *)

(*
(* begin self *)
(* DOESN'T TYPE CHECK *)
let length : int list -> int = 
   fun l -> 
     (fun f -> f f)
     (fun g -> mk_length (fun l -> g g l))
     l 
(* end self *)
*)







(* Self application with recursive types *)

(* begin dom *)
type 'a dom = Abs of ('a dom -> 'a)

let app (f : 'a dom) (x : 'a dom) : 'a = 
  match f with 
  | Abs h -> h x
(* end dom *)

(*
(* begin loop *)
(*   (\x.x x)(\x.x x)  *)

let delta : 'a dom -> 'a = (fun f -> app f f)
let omega : 'a = app (Abs delta) (Abs delta)    (* DIVERGES! *)
(* end loop *)
*)

(* revise our definition of length above to use this type *)

(* begin lengthdom *)
let length : int list -> int = 
   fun l -> 
     (fun f -> app f f)
     (Abs (fun g -> 
         mk_length (fun l -> app g g l)))
     l 
(* end lengthdom *)
let _ = length [1;2;3;4]






(** factor out combinator *)

(* begin y *)
let y_combinator : (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b)
  = fun h -> 
   (fun f -> app f f)
   (Abs (fun g -> h (fun x -> (app g g) x)))

let length = y_combinator mk_length
(* end y *)

(* CHALLENGE: is there a version for products??? *)


let x = length [1;2;3;4]


