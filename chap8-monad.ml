(* Monads, p. 354 - *)
module type Monad = sig 
  type 'a t
  val return: 'a -> 'a t
  val bind: 'a t -> ('a -> 'b t) -> 'b t
end

module Maybe : Monad = struct
  type 'a t = 'a option

  let return x = Some x

  let bind m f = 
    match m with
    | None -> None
    | Some x -> f x
end

let add (m1: int Maybe.t) (m2:int Maybe.t) : int Maybe.t = 
  Maybe.(bind m1 (fun x -> bind m2 (fun y -> return (x + y))))

module type ExtMonad = sig
  type 'a t
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val (>>|) : 'a t -> ('a -> 'b) -> 'b t
  val join : 'a t t -> 'a t
end
module NewMaybe: ExtMonad = struct
  type 'a t = 'a option
  let return x = Some x
  let (>>=) m f = match m with 
    | None -> None
    | Some x -> f x
  let (>>|) m f = match m with
    | None -> None
    | Some x -> Some (f x)
  let join m = match m with 
    | None -> None
    | Some x -> x
end

module GreatMaybe = struct
  type 'a t = 'a option
  let return x = Some x
  let (>>=) m f = match m with 
    | None -> None
    | Some x -> f x
  let (>>|) m f = m >>= (fun x -> Some (f x ))
  let join m = m >>= (fun x -> x)
end

module type FmapJoinMonad = sig
  type 'a t
  val (>>|) : 'a t -> ('a -> 'b) -> 'b t
  val join : 'a t t -> 'a t
  val return : 'a -> 'a t
end

module type BindMonad = sig
  type 'a t
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end

module MakeMonad (M : FmapJoinMonad) : BindMonad = struct
  type 'a t = 'a M.t
  let return = M.return
  let (>>=) m f = (M.(>>|) m f) |> M.join
end

module ListMonad : ExtMonad = struct
  type 'a t = 'a list
  let return x = [x]
  let (>>|) m f = List.map f m
  let join ls = List.concat ls
  let (>>=) m f = ( m >>| f) |> join
end

(* [op]: int -> int option *)
let bind (x: int option) (op: int -> int option): int option =
  match x with
  | None -> None
  | Some a -> op a

let return x = Some x

let (>>=) = bind

(* [upgrade op]: int option -> int option *)
let upgrade op x = x >>= op

let ( + ) (x: int option) (y: int option): int option =
  x >>= fun a -> 
  y >>= fun b ->
  return (Pervasives.(+) a b)

let (/) (x: int option) (y: int option): int option =
  x >>= fun a ->
  y >>= fun b ->
  if b = 0 then None else return (Pervasives.(/) a b)

let upgrade_binary op x y =
  x >>= fun a ->
  y >>= fun b ->
  op a b

let return_binary op x y = return (op x y)

let ( + ) = upgrade_binary (return_binary Pervasives.( + ))

(* Monad laws *)
let q x f = (return x) >>= f
let r x f = f x
let q m = m >>= return
let r m = m
let q m f g = (m >>= f) >>= g
let r m f g = m >>= (fun x -> f x >>= g)

let compose (f: int -> int option) (g: int -> int option) (x: int) = 
  (f x) >>= g
let (>=>) = compose
let q f = return >=> f (* f *)
let q f = f >=> return (* f *)
let q f g h = (f >=> g) >=> h (* f >=> (g >=> h) *)


let return (x : int) : int * string =
  (x, "")

let log (name : string) (f : int -> int) : int -> int * string = 
  fun x -> (f x, Printf.sprintf "Called %s on %i; " name x)

let (>>=) (m : int * string) (f : int -> int * string) : int * string =
  let (x, s1) = m in
  let (y, s2) = f x in
  (y, s1 ^ s2)

let loggable (name : string) (f : int -> int) : int * string -> int * string =
  fun m -> 
  m >>= fun x ->
  log name f x

module Writer : Monad = struct
  type 'a t = 'a * string

  let return x = (x, "")

  let bind m f =
    let (x, s1) = m in
    let (y, s2) = f x in
    (y, s1 ^ s2)
end

module Trivial : Monad = struct
  type 'a t = Wrap of 'a
  let return x = Wrap x
  let bind (Wrap x) f = f x
end