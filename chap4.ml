(* p. 143 - starting from fold *)
let rec fold_right op lst init = 
  match lst with 
  | [] -> init
  | h::t -> op h (fold_right op t init)

let rec fold_left op acc = function
  | [] -> acc
  | h::t -> fold_left op (op acc h) t

let fold_right_tr f l accu =
  List.fold_left (fun acc elt -> f elt acc) accu (List.rev l)

let length l = List.fold_left (fun a _ -> a + 1) 0 l 

let rev l = List.fold_left (fun a x -> x::a) [] l

let my_map f l = List.fold_left (fun a x -> a@[f(x)]) [] l
let my_map f l = List.fold_right (fun x a -> f(x)::a) l []

let filter f l = List.fold_right (fun x a -> if (f x) then x::a else a) l []

let rec fold_tree init op = function
  | Leaf -> init
  | Node(a, l, r) -> op a (fold_tree init op l) (fold_tree init op r)

let size t = fold_tree 0 (fun _ l r -> 1 + l + r ) t

let depth t = fold_tree 0 (fun _ l r -> 1 + max l r) t

let preorder t = fold_tree [] (fun x l r -> [x]@l@r) t

(* p. 157 *)
let square x = x * x
let ($) f x = f x
let y = square $ 2 + 2 (* 16 *)
let y = square 2 + 2 (* 6? *)

(* p. 161 *)
let keys dict = fst (List.split dict) |> List.sort_uniq Pervasives.compare

let is_valid_matrix m = match m with
  |[] -> false
  |h::t -> 
    fst (List.fold_left 
           (fun acc elt -> 
              (fst acc && (snd acc = List.length elt), (snd acc))) 
           (true, List.length h) t)

let row_vector_add l1 l2 = List.map2 (+) l1 l2

let matrix_add m1 m2 = List.map2 (row_vector_add) m1 m2

(* p. 162 matrix multiplication *)
let rec empty n = if n = 0 then [] else []::(empty (n - 1))

let matrix_transpose m = List.fold_left 
    (fun mat_acc row -> List.map2 (fun r re -> r@[re]) mat_acc row) 
    (empty (List.length (List.hd m))) m

let inner_product l1 l2 = List.fold_left (+) 0 (List.map2 ( * ) l1 l2)

let dosomething v m = List.map (inner_product v) m
let pair_multiply m1 m2 = List.map (fun x -> dosomething x m2) m1
let matrix_multiply m1 m2 = pair_multiply m1 (matrix_transpose m2)

let pair_multiply m1 m2 = List.map (fun x -> List.map (inner_product x) m2) m1
let matrix_multiply m1 m2 = List.map (fun x -> 
    List.map (inner_product x) (matrix_transpose m2)) m1