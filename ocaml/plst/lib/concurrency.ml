open Effect
open Effect.Deep
open Printf

(***** cooperative concurrency via effect handlers *)
type thread = unit -> unit

type _ eff +=
  | Spawn : thread -> unit eff
  | Yield : unit eff
  | Terminate : unit eff

(* While a thread is running, it can do some actions.... *)

(* ...such as spawn a new thread *)
let spawn (f : thread) = perform (Spawn f)
(* ...stop running for a bit, so that other threads can run *)
let yield () = perform Yield
(* ...stop running completely *)
let terminate () = perform Terminate

(* We need a place to store stopped threads. *)
let threads : thread Queue.t = Queue.create()
(* and a way to add new threads to it. *)
let schedule (f : thread) = 
  Queue.add f threads

(* Start executing the next thread in the queue. *)
let next () =
  match Queue.take_opt threads with
  | None -> ()
  | Some f -> f ()

type exn += Stop : exn

let rec run () =
  match Queue.take_opt threads with 
  | None -> ()
  | Some f -> 
    match f() with
    | () -> run ()
    | effect Terminate, k -> discontinue k Stop; run ()
    | effect Yield, k -> schedule (continue k); run ()
    | effect Spawn f, k -> schedule (continue k); schedule f; run ()

let task name n =
  for i = 1 to n do printf "%s%d " name i; yield() done

;; schedule (fun () ->
    spawn (fun () -> task "a" 6);
    spawn (fun () -> task "b" 3);
    task "c" 4)

;; run ()
