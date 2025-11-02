(** * Motivating example for effect handlers *)

open Effect
open Effect.Deep
open Printf

module Exception = struct

type exn += Conversion_failure of string

let int_of_string (s : string) : int =
  match int_of_string_opt s with
  | Some n -> n
  | None -> raise (Conversion_failure s)

let sum_stringlist lst =
  lst |> List.map int_of_string |> List.fold_left (+) 0

(* ;; printf "%d\n" (sum_stringlist ["1"; "2"; "three"; "4"; "five" ]) *)

let safe_sum_stringlist lst =
  match sum_stringlist lst with
  | res -> res
  | exception Conversion_failure s ->
    printf "Bad input: %s\n" s; max_int

(* 
;; printf "%d\n" (safe_sum_stringlist ["1"; "2"; "three"; "4"; "five" ])
*)

end


(* --------------------------------------------------- *)
(* example with effect handlers instead *)

module Effect = struct

type _ eff += Conversion_failure : string -> int eff

let int_of_string s =
  match int_of_string_opt s with
  | Some n -> n
  | None -> perform (Conversion_failure s)

let sum_stringlist lst =
  lst |> List.map int_of_string |> List.fold_left (+) 0

(* ;; printf "%d\n" (sum_stringlist ["1"; "2"; "three"; "4"; "five" ]) *)

let safe_sum_stringlist lst =
  match sum_stringlist lst with
  | res -> res
  | effect Conversion_failure s, k ->
    printf "Bad input: %s, replaced with 0\n" s;
    continue k 0

(* 
;; printf "%d\n" (safe_sum_stringlist ["1"; "2"; "three"; "4"; "five" ])
*)

end