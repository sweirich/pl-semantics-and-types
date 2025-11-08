open Printf

(* This file is from: https://xavierleroy.org/control-structures/index.html *)
(* However, here we axiomatize call/cc so it doesn't depend on a specific version of OCaml.
   That means we cannot run any of these examples.
*)

type 'a cont 
let callcc (f: 'a cont -> 'a) : 'a = failwith "This file is not runnable"
let throw (k: 'a cont) (v: 'a) : 'b = failwith "This file is not runnable"
let run (f: unit -> unit) : unit = failwith "This file is not runnable"

(* Section 8.2 *)

(* Basic example: convoluted absolute value *)

let abs n =
    callcc (fun k -> - (if n >= 0 then throw k n else n))

let _ =
  run begin fun () ->
    printf "abs 10 = %d\n" (abs 10);
    printf "abs -5 = %d\n" (abs (-5))
  end

(* An iterator over trees *)

type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree

let rec tree_iter (f: 'a -> unit) (t: 'a tree) : unit =
  match t with
  | Leaf -> ()
  | Node(l, x, r) -> tree_iter f l; f x; tree_iter f r

let my_tree =
  Node(Node(Leaf, 1, Node(Leaf, 2, Leaf)), 3, Node(Node(Leaf, 4, Leaf), 5, Leaf))

(* Searching in a tree for the first element that satisfies a predicate *)

let tree_search (pred: 'a -> bool) (t: 'a tree) : 'a option =
  callcc (fun k ->
    tree_iter (fun x -> if pred x then throw k (Some x)) t;
    None)

let _ =
  run begin fun () ->
    match tree_search (fun n -> n mod 2 = 0) my_tree with
    | Some n -> printf "Found %d\n" n
    | None   -> printf "Not found\n"
  end

(* Same, with an exception *)

let tree_search (type a) (pred: a -> bool) (t: a tree) : a option =
  let exception Found of a in
  try
    tree_iter (fun x -> if pred x then raise (Found x)) t;
    None
  with Found x -> Some x

let _ =
  run begin fun () ->
    match tree_search (fun n -> n mod 2 = 0) my_tree with
    | Some n -> printf "Found %d\n" n
    | None   -> printf "Not found\n"
  end

(* Same, with backtracking *)

let tree_search (pred: 'a -> bool) (t: 'a tree) : ('a * unit cont) option =
  callcc (fun k ->
    tree_iter
      (fun x -> if pred x then callcc (fun k' -> throw k (Some(x, k'))))
      t;
    None)

let _ =
  run begin fun () ->
    match tree_search (fun n -> n mod 2 = 0) my_tree with
    | Some(n, k) -> printf "Found %d\n" n; throw k ()
    | None       -> printf "Not found\n"
  end

(* Section 8.3 *)

(* Implementing exceptions using callcc *)

let handlers : exn cont Stack.t = Stack.create()

let my_raise exn =
  if Stack.is_empty handlers then failwith "unhandled exception";
  throw (Stack.pop handlers) exn

let my_trywith body handler =
  callcc (fun k1 ->
    handler (
      callcc (fun k2 ->
        Stack.push k2 handlers;
        let res = body() in
        ignore (Stack.pop handlers);
        throw k1 res)))

let prodlist (l: int list) : int =
  let rec prod = function
    | [] -> 1
    | 0 :: l -> my_raise Exit
    | n :: l -> n * prod l in
  my_trywith
    (fun () -> prod l)
    (function Exit -> 0 | exn -> raise exn)

let _ =
  run begin fun () ->
    printf "prodlist [1;2;3] = %d\n" (prodlist [1;2;3]);
    printf "prodlist [4;0;6] = %d\n" (prodlist [4;0;6])
  end

(* Implementing cooperative threads using callcc *)

let ready : (unit -> unit) Queue.t = Queue.create ()

let schedule () : unit =
  match Queue.take_opt ready with
  | None -> ()
  | Some k -> k ()

let yield () : unit = 
  callcc (fun k ->
    Queue.add (fun () -> throw k ()) ready;
    schedule())

let terminate () : unit = schedule ()

let spawn (f: unit -> unit) : unit = Queue.add f ready

let process name count =
  for n = 1 to count do
    printf "%s%d " name n;
    yield ()
  done;
  terminate()

let _ =
  run begin fun () ->
    printf "Running 3 processes: ";
    spawn (fun () -> process "A" 5);
    spawn (fun () -> process "B" 3);
    process "C" 6;
    printf "done\n"
  end

(* Backtracking and choice points using callcc *)

let backtrack : unit cont Stack.t = Stack.create()

let fail () =
  throw (Stack.top backtrack) ()

let assert_ b =
  if not b then fail ()

let choose_aux l =
  callcc (fun k -> Stack.push k backtrack);
   match !l with
   | [] -> ignore (Stack.pop backtrack) ; fail ()
   | hd :: tl -> l := tl; hd

let choose l = choose_aux (ref l)

let _ =
  run begin fun () ->
    let a = choose [1;2;3;4;5;6;7] in
    let b = choose [1;2;3;4;5;6;7] in
    let c = choose [1;2;3;4;5;6;7] in
    (* Make sure that it is a right triangle *)
    assert_ (c * c = a * a + b * b);
    (* Force side a to be the shortest side *)
    assert_ (b < a);
    (* Print the solution found *)
    printf "Right triangle found: %d %d %d\n" a b c
  end


