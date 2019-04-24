(* References *)
let x = ref 42
let y = ref 42
let z = x
let () = x := 43 (* pay attention to syntax! *)
let w = (!y) + (!z)

(* study carefully the following example *)
let incr a = a := !a + 1
let new_val () = 
  let counter = ref 0 in 
  fun () -> incr counter; !counter

let new_val2 = 
  let counter = ref 0 in 
  fun () -> incr counter; !counter

let new_val3 = 
  fun () ->
  let counter = ref 0 in 
  incr counter; !counter

let f0 = ref (fun x -> x)
let f x = if x = 0 then 1 else x * (!f0) (x - 1)
let () = f0 := f (* f 5 = 120 *)

type point = {x: int; y:int; mutable c: string}
let p = {x = 3;y = 2; c= "red"}
let () = p.c <- "black"

type 'a ref = {mutable contents: 'a}
let ref x = {contents = x}
let (!) y = y.contents
let (:=) x z = x.contents <- z


module MutableRecordStack = struct
  exception Empty
  type 'a node = {value : 'a ; mutable next: 'a node option}
  type 'a t = {mutable top: 'a node option}
  let empty () = {top = None}
  let push x s = s.top <- Some{value = x; next = s.top}
  let peek s = match s.top with
    | None -> raise Empty
    | Some {value} -> value
  let pop s = match s.top with
    | None -> raise Empty
    | Some{next} -> s.top <- next
end

type student = {name: string; mutable gpa: float}
let alice = {name = "Alice"; gpa = 3.7}
let () = alice.gpa <- 4.0

let ( +:= ) x y = x := !x + y

let arr = [|0;1|]
let () = arr.(0) <- 4

type vector = float array
let norm v = Array.(map (fun x -> x *. x) v |> fold_left (fun x y -> x +. y) 0. |> sqrt)
let normalize_loop v = let len = norm v in for x = 0 to Array.length v - 1 do v.(x) <- v.(x) /. len done
let normalize v = let len = norm v in Array.iteri (fun i x -> v.(i) <- x /. len) v
let norm_loop v = let n = ref 0. in for i = 0 to Array.length v - 1 do n := !n +. v.(i) *. v.(i) done; sqrt (!n)

let init_matrix r c f = Array.(init r (fun i -> init c (fun j -> f i j)))

(* An ['a node] is a node of a mutable doubly-linked list.
 * It contains a value of type ['a] and optionally has 
 * pointers to previous and/or next nodes. *)
type 'a node = {
  mutable prev : 'a node option;
  mutable next : 'a node option;
  value : 'a
}

(* An ['a dlist] is a mutable doubly-linked list with elements 
 * of type ['a].  It is possible to access the first and 
 * last elements in constant time.  
 * RI: The list does not contain any cycles. *)
type 'a dlist = {
  mutable first : 'a node option;
  mutable last : 'a node option;
}

(* [create_node v] is a node containing value [v] with
 * no links to other nodes. *)
let create_node v = {prev=None; next=None; value=v}

(* [empty_dlist ()] is an empty doubly-linked list. *)
let empty_dlist () = {first=None; last=None}

(* [create_dlist n] is a doubly-linked list containing
 * exactly one node, [n]. *)
let create_dlist (n: 'a node) : 'a dlist = {first=Some n; last=Some n}

(* [insert_first d n] mutates dlist [d] by
 * inserting node [n] as the first node. *)
let insert_first (d: 'a dlist) (n: 'a node) : unit =
  n.next <- d.first;
  d.first <- Some n

(* [insert_last d n] mutates dlist [d] by
 * inserting node [n] as the last node. *)
let insert_last (d: 'a dlist) (n: 'a node) : unit =
  n.prev <- d.last;
  d.last <- Some n

(* [insert_after d n1 n2] mutates dlist [d] by
 * inserting node [n2] after node [n1]. *)
let insert_after (d: 'a dlist) (n1: 'a node) (n2: 'a node) : unit =
  let m = ref d.first in 
  while !m <> None do 
    match !m with 
    | None -> failwith "rep failed"
    | Some x -> if x = n1 then begin 
        match x.next with 
        | None -> x.next <- Some n2; d.last <- Some n2
        | Some y -> y.prev <- Some n2; x.next <- Some n2
      end
      else (); m := x.next
  done

(* [insert_before d n1 n2] mutates dlist [d] by
 * inserting node [n2] before node [n1]. *)
let insert_before (d: 'a dlist) (n1: 'a node) (n2: 'a node) : unit =
  let m = ref d.first in 
  while !m <> None do 
    match !m with 
    | None -> failwith "rep failed"
    | Some x -> if x = n1 then begin 
        match x.prev with 
        | None -> x.prev <- Some n2; d.first <- Some n2
        | Some y -> y.next <- Some n2; x.prev <- Some n2
      end
      else (); m := x.next
  done
(* [remove d n] mutates dlist [d] by removing node [n].
 * requires: [n] is a node of [d]. *)
let remove (d: 'a dlist) (n: 'a node) : unit =
  let m = ref d.first in 
  while !m <> None do 
    match !m with 
    | None -> failwith "rep failed"
    | Some x -> if x = n then begin 
        match x.prev, x.next with 
        | None, None -> d.first <- None; d.last <- None 
        | None, Some y -> d.first <- Some y; y.prev <- None
        | Some x, None -> d.last <- Some x; x.next <- None
        | Some x, Some y -> x.next <- Some y; y.prev <- Some x
      end
      else (); m := x.next
  done

(* [iter_forward d f] on a dlist [d] which has 
 * elements n1; n2; ... is (f n1); (f n2); ... *)
let iter_forward (d: 'a dlist) (f: 'a -> unit) : unit =
  let m = ref d.first in 
  while !m <> None do 
    match !m with 
    | None -> failwith "rep failed"
    | Some x -> f x.value; 
      m := x.next
  done

(* [iter_backward d f] on a dlist [d] which has 
 * elements n1; n2; ... is ...; (f n2); (f n1) *)
let iter_backward (d: 'a dlist) (f: 'a -> unit) : unit =
  let m = ref d.last in 
  while !m <> None do 
    match !m with 
    | None -> failwith "rep failed"
    | Some x -> f x.value; 
      m := x.prev
  done