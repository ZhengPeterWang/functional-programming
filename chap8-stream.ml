(* p. 297 -  298 *)
(* let rec nats = 0::List.map (fun x -> x + 1) nats *)
type 'a stream = Cons of 'a * (unit -> 'a stream)
let rec from n = Cons(n, fun () -> from (n + 1))
let rec from_f n = Cons(n, fun () -> from_f (n +. 1.))
let nats = from 0
let hd (Cons (h, _)) = h
let tl (Cons (_, t)) = t()

let rec take n s = 
  if n = 0 then []
  else (hd s):: take (n - 1) (tl s)

let rec drop n s = 
  if n = 0 then s
  else Cons(hd s, fun () -> (drop n (tl s)))

let rec map f (Cons(h, tf)) = 
  Cons(f h, fun () -> map f (tf()))

let rec map2 f (Cons(h1, tf1)) (Cons(h2, tf2)) =
  Cons(f h1 h2, fun () -> map2 f (tf1()) (tf2()))

let sum = map2 (+)
let rec nats = Cons(0, fun () -> map (fun x -> x + 1) nats)
let rec fibs = Cons(1, fun () -> (Cons(1, fun () -> sum fibs (tl fibs))))

(* p. 302 - 303 *)
module LazyFibs = struct
  type 'a lazystream = 
    | Cons of 'a * 'a lazystream Lazy.t
  let hd : 'a lazystream -> 'a =
    fun (Cons (h, _)) -> h
  let tl : 'a lazystream -> 'a lazystream =
    fun (Cons (_, t)) -> Lazy.force t
  let rec map f ls = Cons(f (hd ls), lazy (map f (tl ls)))
  let rec filter p ls = 
    if (p (hd ls)) 
    then Cons(hd ls, lazy (filter p (tl ls))) 
    else filter p (tl ls)
  let rec take_aux n (Cons(h, t)) lst =
    if n = 0 then lst
    else take_aux (n - 1) (Lazy.force t) (h::lst)
  let take : int -> 'a lazystream -> 'a list = 
    fun n s -> List.rev (take_aux n s [])
  let nth : int -> 'a lazystream -> 'a = 
    fun n s -> List.hd (take_aux (n + 1) s [])
  let rec sum : int lazystream -> int lazystream -> int lazystream = 
    fun (Cons(h_a, t_a)) (Cons(h_b, t_b)) ->
    Cons(h_a + h_b, lazy(sum(Lazy.force t_a) (Lazy.force t_b)))
  let rec fibs = 
    Cons(1, lazy(Cons(1, lazy(sum (tl fibs) fibs))))
  let nth_fib n = nth n fibs
end

(* Textbook problems: p. 377 - 382 *)
let rec p n = if n = 0 then 1 else 2 * p (n - 1)
let rec pow n = Cons(p n, fun () -> (pow (n + 1)))
let pow2 = pow 0
let pow2 = map (fun x -> p x) (from 0)

let even_str = map (fun x -> x * 2) (from 1)
let infinite_char = map (fun x -> char_of_int ((x mod 26) + 97)) (from 0)
let go = map (fun _ -> Random.int 2) (from 0)

let rec nth s i = if i < 0 then failwith "invariant failed"
  else if i = 0 then hd s else nth (tl s) (i - 1)

let rec filter p s = 
  if (p (hd s)) then Cons(hd s, fun () -> filter p (tl s)) else filter p (tl s)

let rec interleave (Cons(hd, f)) s = 
  Cons(hd, fun () -> interleave s (f()))

let sift a s = filter (fun y -> (y mod a <> 0) || y = a) s
let rec primes ss x = 
  let sifted = sift (hd ss) ss in 
  Cons(hd sifted, fun () -> primes (tl sifted) (x + 1))
let p = primes (from 2) 1

let rec f k x = if k = 0. then 1. else (f (k -. 1.) x) *. x /. k
(* may be improved by laziness and memoization *)
let e_terms x = map (fun k -> f k x ) (from_f 0.)
let rec total (Cons(h, f)) acc = Cons(acc +. h, fun () -> total (f()) (acc +. h))
let rec within eps (Cons(h, f)) = 
  let h' = hd (f ()) in 
  if abs_float(h -. h') /. (abs_float(h +. h') /. 2. +. 1.)< eps then h' else within eps (f())
let e x eps = within eps (total (e_terms x) 0.)

(* the other type of stream *)
type 'a stream = Cons of (unit -> 'a * 'a stream)
let hd (Cons f) = fst (f())
let tl (Cons f) = snd (f())
let nats = let rec nats i = Cons(fun () -> i, nats (i + 1)) in nats 0
let rec map s f = Cons(fun () -> f (hd s), map (tl s) f)
(* TODO: why this representation is lazier than the one on line 3? *)

(* laziness p. 381 *)
let m = lazy (print_string "Hello Lazy World")
let () = Lazy.force m
let () = Lazy.force m

let (&&&) a b = if Lazy.force a = false then false else Lazy.force b
