(** Effect Handlers: exploring what they can do *)

open Effect
open Effect.Deep
open Printf

(* Create a simple effect handler *)
type _ eff += Doit : int -> int eff 

let example = 
  match 1 + perform (Doit 2) with 
  | res -> res
  | effect Doit x, _k -> x
;; printf "Effect handler example1: %d\n" example    


(* --------------------------------------------------- *)

let example = 
  match 1 + perform (Doit 2) with 
  | res -> res
  | effect Doit _x, k -> (continue k 3)
(* ;; printf "Effect handler example2: %d\n" example   *)


(* --------------------------------------------------- *)

let example = 
  match 1 + perform (Doit 2) + perform (Doit 27) with 
  | res -> res
  | effect Doit _x, k -> (continue k 3)

(* ;; printf "Effect handler example3: %d\n" example  *)



(* We go back to the evaluation point each time, using '3' as 
   the value. So the result is 1 + 3 + 3 *)

(* --------------------------------------------------- *)


let r : (int , int) continuation option ref = ref None
let example = 47 + match 2 + perform (Doit 2) with 
  | res -> res
  | effect Doit x, k -> r := Some k ; x

let answer = match !r with
    Some k -> continue k 0
  | None -> failwith "no k"

(* ;; printf "Effect handler 4: example %d, answer %d\n" example answer *)





(* We save the continuation in a reference which we invoke
   **after** the match is off the stack. So we skip adding 47 to answer *)

(* --------------------------------------------------- *)



let r : (int , int) continuation option ref = ref None
let example = 47 + match 2 + perform (Doit 2) with 
  | res -> res
  | effect Doit x, k -> r := Some k ; x

let answer = match !r with
    Some k -> 
    let x1 = (continue k 0) in   (* returns 2 *)
    let x2 = (try match !r with 
          Some k' -> continue k' 1
        | None -> failwith "no k'"
       with Continuation_already_resumed -> 100)
    in x1 + x2 
  | None -> failwith "no k"


(* ;; printf "Effect handler 5: example %d, answer %d\n" example answer *)






(* In this example, we save the continuation in a reference which we invoke
   **after** the match is off the stack. But we can only use that 
   continuation once *)

(* --------------------------------------------------- *)

let r : ((int , int) continuation * int) option ref = ref None
let example = 47 + match let x1 = perform (Doit 7) in 
                let x2 = perform (Doit 13) in
                2 + x1 + x2 with
              | res -> res
              | effect Doit x, k ->  r := Some (k,x) ; x

let answer1 = match !r with
    Some (k,x) -> let v = x + 20 in continue k v
  | None -> failwith "no k"

let answer2 = match !r with
    Some (k,x) -> let v = x + 21 in continue k v
  | None -> failwith "no k"

(* ;; printf "Effect handler 6: example %d, answer1 %d, answer2 %d\n" example answer1 answer2 *)






(* NOTE: The first perform captures [match let x1 = _ in let x2 = perform (Doit 13) in 2 + x1 + x2 with ...] 
         but does not continue. so the result is 47 + 7.
         This is then invoked with x1 = 27. 
         The second perform captures
         [match let x2 = _ in 2 + 27 + x2 with ...] and saves it in the reference
         it then returns 13
         This saved continuation is invoked with x2 = 13 + 21 so it returns
         2 + 27 + 34 = 63
*)