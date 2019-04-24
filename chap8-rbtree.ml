(* p. 306 *)
type color = Red | Black
type 'a rbtree = Node of color * 'a * 'a rbtree * 'a rbtree | Leaf

let rec mem x = function
  | Leaf -> false
  | Node(_, y, left, right) -> x = y || (x < y && mem x left) || mem x right

let balance = function
  | Black, z, Node(Red, y, Node(Red, x, a, b), c), d
  | Black, z, Node(Red, x, a, Node(Red, y, b, c)), d
  | Black, x, a, Node(Red, z, Node(Red, y, b, c), d)
  | Black, x, a, Node(Red, y, b, Node(Red, z, c, d))
    -> Node(Red, y, Node(Black, x, a, b), Node(Black, z,  c, d)) (* why? *)
  | a, b, c, d -> Node(a, b, c, d)

let insert x s = 
  let rec ins = function
    | Leaf -> Node(Red, x, Leaf, Leaf)
    | Node (color, y, a, b) as s ->
      if x < y then balance (color, y, ins a, b)
      else if x > y then balance (color, y, a, ins b)
      else s in
  match ins s with
  | Node(_, y, a, b) -> Node(Black, y, a, b)
  | Leaf -> failwith "RBT insert failed"

module type Comparable = sig
  type t
  val compare : t -> t -> int
end

module BstSet (C: Comparable) = struct
  type t = C.t rbtree
  let (=~) (c1: C.t) (c2: C.t) = C.compare c1 c2 = 0
  let (>~) (c1: C.t) (c2: C.t) = C.compare c1 c2 > 0
  let (<~) (c1: C.t) (c2: C.t) = C.compare c1 c2 < 0
  let rec mem (x: C.t) = function
    | Leaf -> false
    | Node(_, y, left, right) -> x =~ y || (x <~ y && mem x left) || mem x right
  let insert x s = 
    let rec ins = function
      | Leaf -> Node(Red, x, Leaf, Leaf)
      | Node (color, y, a, b) as s ->
        if x <~ y then balance (color, y, ins a, b)
        else if x >~ y then balance (color, y, a, ins b)
        else s in
    match ins s with
    | Node(_, y, a, b) -> Node(Black, y, a, b)
    | Leaf -> failwith "RBT insert failed"
end

type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree

let rec preord acc = function
  | Leaf -> acc
  | Node (l,v,r) -> let acc = preord (v::acc) l in preord acc r
let preorder t = List.rev (preord [] t)

let rec inord acc = function
  | Leaf -> acc
  | Node (l,v,r) -> let acc = inord acc l in inord (v::acc) r
let inorder t = List.rev (inord [] t)

let rec postord acc = function
  | Leaf -> acc
  | Node (l,v,r) -> let acc = postord acc l in v::(postord acc r)
let postorder t = List.rev (postord [] t)

let t =
  Node(Node(Node(Leaf, 1, Leaf), 2, Node(Leaf, 3, Leaf)),
       4,
       Node(Node(Leaf, 5, Leaf), 6, Node(Leaf, 7, Leaf)))

