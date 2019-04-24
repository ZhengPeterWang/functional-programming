(*  p. 229 *)
module type Fraction = sig
  type t = int * int
  val make : int -> int -> t
  val numerator : t -> int 
  val denominator : t -> int 
  val toString : t -> string 
  val toReal : t -> float
  val add : t -> t -> t
  val mul : t -> t -> t 
end

module MyFraction:(Fraction) = struct
  type t = int * int
  let make a b = if b = 0 then failwith "divided by 0" else (a, b)
  let numerator a = fst a
  let denominator a = snd a
  let toString a = (string_of_int (fst a))^"/"^(string_of_int (snd a))
  let toReal a = (float_of_int (fst a))/.(float_of_int (snd a))
  let add a b = ((fst a)*(snd b)+(snd a)*(fst b), (snd a)*(snd b))
  let mul a b = ((fst a)*(fst b), (snd a)*(snd b))
end

let rec gcd x y =
  if x = 0 then y
  else if x < y then gcd (y - x) x
  else gcd y (x - y)

module FractionReduced:Fraction = struct
  include MyFraction
  let rec make a b = 
    if b = 0 then failwith "divided by 0" 
    else if b < 0 then make (~-a) (~-b)
    else let g = gcd (abs a) b in (a/g, b/g)
  let add a b = make ((fst a)*(snd b)+(snd a)*(fst b)) ((snd a)*(snd b))
  let mul a b = make ((fst a)*(fst b)) ((snd a)*(snd b))
end

module FractionFunctor = functor (F:Fraction) -> (struct
    include F
    let rec transform a = let c = fst a in let d = snd a in
      if d = 0 then failwith "divided by 0" 
      else if d < 0 then transform ((~-c) , (~-d))
      else let g = gcd (abs c) d in (c / g, d / g)
    let add a b = transform (F.add a b)
    let mul a b = transform (F.mul a b)
    let make a b = transform (F.make a b)
  end : Fraction)

module FrReduced = FractionFunctor(MyFraction)

(* p. 238 *)
module type Ring = sig
  type t
  val zero  : t
  val one   : t
  val (+)   : t -> t -> t
  val (~-)  : t -> t
  val ( * ) : t -> t -> t
  val to_string : t -> string
  val of_int : int -> t
end

module type Field = sig
  include Ring
  val (/) : t -> t -> t
end

module IntRing : (Ring with type t = int) = struct
  type t = int
  let zero = 0
  let one = 1
  let (+) = (+)
  let (~-) = (~-)
  let ( * ) = ( * )
  let to_string = string_of_int
  let of_int n = n
end

module IntField : Field = struct
  include IntRing
  let (/) = (/)
end

module FloatRing : (Ring with type t = float) = struct
  type t = float
  let zero = 0.
  let one = 1.
  let (+) = (+.)
  let (~-) = (~-.)
  let ( * ) = ( *. )
  let to_string = string_of_float
  let of_int n = float_of_int n
end

module FloatField : Field = struct
  include FloatRing
  let (/) = (/.)
end

module Rational(F:Field):Field = struct
  type t = F.t * F.t
  let zero = (F.zero, F.zero)
  let one = (F.one, F.one)
  let (+) (a, b) (c, d) = F.(a * d + c * b, b * d)
  let (~-) (a,b) = F.(-a,b)
  let (/) (a,b) (c,d) = F.(a*d, b*c)
  let ( * ) (a,b) (c,d) = F.(a*c, b*d)
  let to_string (a,b) = F.(to_string a ^ "/" ^ to_string b)
  let of_int n = F.(F.of_int n,one)
end

module IntRational = Rational(IntField)
module FloatRational = Rational(FloatField)