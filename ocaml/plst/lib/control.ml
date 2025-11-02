(* SCW note: SHIFT+ENTER sends a selection to utop in vscode *)
(* SHIFT+OPTION+F runs formatter *)
(* Cmd+K Cmd+I shows hover *)

(* Code examples from https://xavierleroy.org/CdF/2023-2024/4.pdf *)

(* This example demonstrates various ways of processing the values
   in some container. 
   - higher-order iterator
   - iterator/enumeration (directly)
   - generator (via exceptions)
   - enumeration (via effect handlers)

*)

open Printf
open Effect
open Effect.Deep

(* A sample container data structure: a binary tree *)
type 'a tree = Empty | Node of 'a tree * 'a * 'a tree

let leaf x = Node (Empty, x, Empty)
let t1 = Node (Node (leaf 0, 1, leaf 2), 3, Node (leaf 4, 5, leaf 6))
let t2 = Node (leaf 0, 1, (Node (leaf 2, 3, Node (leaf 4, 5, leaf 6))))

(* --------------------------------------------------------- *)

(* A simple higher-order function that does something 
   with every value in the tree *)
let rec tree_iter (f: 'a -> unit) (t: 'a tree) =
  match t with
  | Empty -> ()
  | Node(l, x, r) -> tree_iter f l; f x; tree_iter f r

(* 
   In the simplest version, an iteration function controls the pace of 
   the iteration.  The user of the iteration function can determine when 
   the iteration starts and what computation is applied to each element. 
   However, all elements are immediately processed in order.
*)

;; printf "tree_iter\n"
;; tree_iter print_int t1    (* All elements are printed at once *)
;; print_newline ()
;; tree_iter print_int t2
;; print_newline ()


(* --------------------------------------------------------- *)


(* An enumeration is either Done or has more elements to produce *)
type 'a enum = Done | More of 'a * (unit -> 'a enum)

let tree_iterator (t: 'a tree) : 'a enum =
  let rec loop (t: 'a tree) (k: unit -> 'a enum) =
    match t with
    | Empty -> k ()
    | Node(l, x, r) ->
      loop l (fun () -> More(x, fun () -> loop r k)) in
  loop t (fun () -> Done)

let rec print_enum k e =
  if k = 0 then e else
    match e with 
    | Done -> Done
    | More (x,next) -> print_int x ; print_enum (k-1) (next ())

;; printf "tree enumeration\n"
let iter = tree_iterator t1
let iter2 = print_enum 3 iter   (* print first three elements *)
;; printf "\n"
let _ = print_enum 2 iter2      (* print next two elements *)
;; printf "\n"

(* ------------------------------------------ *)
(* We can use exceptions to  *)

exception NoSuchElementException
let tree_generator (t: 'a tree) : unit -> 'a =
  let current = ref (fun () -> tree_iterator t) in
  fun () ->
    match !current () with
    | Done -> raise NoSuchElementException
    | More(x, k) -> current := k; x

let print_generator k (g : unit -> int) = 
  try 
    let rec loop k = if k = 0 then () else
        (print_int (g ()) ; loop (k-1)) in
    loop k
  with NoSuchElementException -> ()

;; printf "tree_generator (3 elements) \n"
;; print_generator 3 (tree_generator t1)
;; printf "\n"
  


(* ---------------------------------------------------- *)


(* Start with a simple tree iterator *)
let rec tree_iter (f: 'a -> unit) (t: 'a tree) =
  match t with
  | Empty -> ()
  | Node(l, x, r) -> tree_iter f l; f x; tree_iter f r

(* Use the iterator to make a generator for the elements in the tree 
   at every step, perform the "Next" effect, which is handled to 
   create an 'enum'
*)
let tree_enum (type a) : a tree -> a enum =
  let module Inv = struct
    type _ eff += Next : a -> unit eff
    let tree_enum (t: a tree) : a enum =
      match tree_iter (fun x -> perform (Next x)) t with
      | () -> Done
      | effect Next x, k -> More(x, fun () -> continue k ())
  end in
  Inv.tree_enum


 
;; printf "tree_enum from tree_iter\n"
;; let _ = print_enum 3 (tree_enum t1)
;; printf "\n"  

