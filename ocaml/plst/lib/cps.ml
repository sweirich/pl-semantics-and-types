

let print_int_list lst =
  let rec loop lst = 
      match lst with  
      | [] -> print_string "]"
      | [x] -> print_int x; print_string "]"
      | x :: t -> print_int x ; print_string "; " ; loop t
  in 
  print_string "["; loop lst


(* A sample container data structure: a binary tree *)
type 'a tree = Empty | Node of 'a tree * 'a * 'a tree

let leaf x = Node (Empty, x, Empty)
let t1 = Node (Node (leaf 0, 1, leaf 2), 3, Node (leaf 4, 5, leaf 6))
let t2 = Node (leaf 0, 1, (Node (leaf 2, 3, Node (leaf 4, 5, leaf 6))))

let rec inorder (t : 'a tree) : 'a list = 
  match t with 
  | Empty -> []
  | Node (l,x,r) -> inorder l @ (x :: inorder r)

;; print_int_list (inorder t1)
;; print_newline ()



(* ACCUMULATOR style  tree traversal *)
let rec inorder_acc (t : 'a tree) (k : 'a list) : 'a list = 
  match t with 
  | Empty -> k
  | Node (l,x,r) -> inorder_acc l (x :: inorder_acc r k)


;; print_int_list (inorder_acc t1 [])
;; print_newline ()







(* TAIL_RECURSIVE (CPS) style tree traversal *)
let rec inorder_tail (t : 'a tree) (k : 'a list -> 'b) : 'b =
   match t with 
   | Empty -> k []
   | Node(l,x,r) -> inorder_tail l (fun ll -> inorder_tail r (fun rl -> k (ll @ (x :: rl))))

;; print_int_list (inorder_tail t1 (fun x -> x))
;; print_newline ()
;; inorder_tail t1 print_int_list
;; print_newline ()







(** ACCUMULATOR & TAIL RECURSION: difference lists *)
type 'a dlist = 'a list -> 'a list
let nil = fun x -> x
let cons (x:'a) (t:'a dlist) : 'a dlist = fun (l : 'a list) -> (x :: t l)
let app (t1: 'a dlist) (t2 : 'a dlist) = fun l -> t1 (t2 l)
let to_list (t : 'a dlist) = t []

(** Difference LIST version *)
let rec inorder_dlist (t : 'a tree) (k : 'a dlist -> 'b) : 'b = 
  match t with 
  | Empty -> k nil
  | Node (l,x,r) -> inorder_dlist l (fun ld -> 
                          inorder_dlist r (fun rd -> k (app ld (cons x rd))))
 
;; print_int_list (to_list (inorder_dlist t1 nil))
;; print_newline ()

;; inorder_dlist t1 (fun d -> print_int_list (d []))
;; print_newline ()


