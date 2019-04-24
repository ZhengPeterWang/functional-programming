(** [Poly] represents immutable polynomials with integer coefficients. *) 
module type Poly = sig
  (** [t] is the type of polynomials *) 
  type t
  (** [eval x p] is [p] evaluated at [x].
      Example: if [p] represents $3x^3 + x^2 + x$, then [eval 10 p] is [3110]. *)
  val eval : int -> t -> int 
  (** [plus x y] is [x + y]. 
      Example: if [p] is $x^3 + 3x^2$ and [q] is $x^2$ then [plus p q] is $x^3 + 4x^2$. *)
  val plus : t -> t -> t
  val create : int list -> t
  val query : t -> int list
end

module Polynomial: Poly = struct
  type t = int list
  let rec pow a = function
    | 0 -> 1
    | 1 -> a
    | n -> 
      let b = pow a (n / 2) in
      b * b * (if n mod 2 = 0 then 1 else a)
  let eval a p = 
    let rec eva a n acc = function 
      | [] -> acc
      | h::t -> eva a (n + 1) (acc + h * pow a n) t in 
    eva a 0 0 p
  let rec plus p1 p2 =
    match p1, p2 with
    | [], [] -> []
    | [], h::t -> h::(plus [] t)
    | h::t, [] -> h::(plus t [])
    | h1::t1, h2::t2 -> (h1 + h2)::(plus t1 t2)
  let create x = x
  let query x = x
end

module type MyMap = sig

  (** [('k,'v) t] is the type of a map containing bindings 
      from keys of type ['k] to values of type ['v]. *)
  type ('k,'v) t

  (** [empty] is the map containing no bindings. *)
  val empty : ('k,'v) t

  (** [mem k m] is true if [k] is bound in [m] and false otherwise. *)
  val mem : 'k -> ('k,'v) t -> bool

  (** [find k m] is [v] iff [k] is bound to [v] in [m]. 
      Raises: [Not_found] if [k] is not bound in [m]. *)
  val find : 'k -> ('k,'v) t -> 'v

  (** [add k v m] is the map [m'] that contains the same bindings
      as [m], and additionally binds [k] to [v]. If [k] was
      already bound in [m], its old binding is replaced by
      the new binding in [m']. *)
  val add : 'k -> 'v -> ('k,'v) t -> ('k,'v) t

  (** [remove k m] is the map [m'] that contains the same bindings
      as [m], except that [k] is unbound in [m']. *)
  val remove : 'k -> ('k,'v) t -> ('k,'v) t

end 

module FunMap : MyMap = struct
  type ('k, 'v) t = 'k -> 'v option
  let empty x = None
  let mem k m = m k <> None
  let find k m = match m k with
    | None -> raise Not_found
    | Some x -> x
  let add k v f = fun x -> if x = k then Some v else f k
  let remove k f = fun x -> if x = k then None else f k
end


(**********************************************************)
(*  WARNING:  The BuggyTwoListQueue module below          *)
(*            deliberately contains bugs!!!               *)
(**********************************************************)

module type Queue = sig
  (* An ['a t] is a queue whose elements have type ['a]. *)
  type 'a t

  (* The empty queue. *)
  val empty : 'a t

  (* Whether a queue is empty. *)
  val is_empty : 'a t -> bool

  (* [singleton x] is the queue containing just [x]. *)
  val singleton : 'a -> 'a t

  (* [enqueue x q] is the queue [q] with [x] added to the front. *)
  val enqueue : 'a -> 'a t -> 'a t

  (* [peek q] is [Some x], where [x] is the element at the front of the queue,
     or [None] if the queue is empty. *)
  val peek : 'a t -> 'a option

  (* [dequeue q] is [Some q'], where [q'] is the queue containing all the
     elements of [q] except the front of [q], or [None] if [q] is empty. *)
  val dequeue : 'a t -> 'a t option

  (* [to_list q] is [x1; x2; ...; xn], where [x1] is the element
     at the head of [q], ..., [xn] is the element at the end of [q]. *)
  val to_list : 'a t -> 'a list
end

module BuggyTwoListQueue : Queue = struct
  (* AF: [{front; back}] is a queue whose elements from top to bottom is the 
     same from traversing the list [front@(List.rev back)] from head to tail.
     RI: if [front] is empty then [back] is empty *)
  type 'a t = {front:'a list; back:'a list}

  let rep_ok a = if a.front = [] && a.back <> []
    then raise (Invalid_argument "rep failed") else a

  let empty = {front=[]; back=[]}

  let is_empty q =
    match q with
    | {front=[]; back=[]} -> true
    | _ -> false

  let singleton x = {front=[x]; back=[]}

  (* Helper function to ensure that a queue is in normal form. *)
  let norm = function
    | {front=[]; back} -> {front=List.rev back; back=[]}
    | q -> q

  let enqueue x q = norm {q with back=x::q.back}

  let peek q =
    match q with
    | {front=[]} -> None
    | {front=x::_} -> Some x

  let dequeue q =
    match q with
    | {front=[]; _} -> None
    | {front=_::xs; back} -> Some (norm {front=xs; back})

  let to_list q =
    let {front;back} = q
    in front @ List.rev back
end

