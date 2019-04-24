(* Making Textbook Easy*)

(** p.55 *)
let rec h n pp p =
  if n = 1 then p
  else (h (n - 1) p (pp + p))

(* p.57 *)
let rec print_int_list = function 
  | [] -> ()
  | h::t -> print_endline h;
    print_int_list t

let print_int_list' lst =
  List.iter (fun x -> print_endline x;) lst

(* p. 118 - 120 *)
type 'a tree =
  | Leaf
  | Node of 'a * 'a tree * 'a tree

let rec size = function
  | Leaf -> 0
  | Node (_,l,r) -> 1 + size l + size r

let preorder_lin t =
  let rec pre_acc acc = function
    | Leaf -> acc
    | Node (value, left, right) -> value :: (pre_acc (pre_acc acc right) left) 
  in pre_acc [] t

(* p. 127 *)
let rec take n acc = function
  | h::t when n <> 0 -> take (n - 1) t (h::acc)
  | _ -> acc

let rec drop n = function
  | [] -> []
  | h::t as ls -> if n = 0 then ls else drop (n - 1) t

(* p. 128 *)
let is_unimodal ls =
  let rec is_unimodal_checked b = function
    | [] -> true
    | h::[] -> true
    | h::t -> 
      if b = false && List.hd t >= h then is_unimodal_checked false t 
      else if b = false then is_unimodal_checked true t
      else if b = true && List.hd t > h then false
      else (is_unimodal_checked b t) in
  is_unimodal_checked false ls

let rec powerset = function
  | [] -> [[]]
  | h::t -> let ls = powerset t in (List.map (fun x -> h::x) ls)@ls

(* p. 132 *)
let rec depth = function
  | Leaf -> 0
  | Node(_, l, r) -> 1 + max (depth l) (depth r)

let rec same_shape tr1 tr2 = 
  match (tr1, tr2) with
  | (Leaf, Leaf) -> true
  | (Node(_, l1, r1), Node(_, l2, r2)) -> 
    (same_shape l1 l2) && (same_shape r1 r2)
  | _ -> false

(* p. 132 - 133 *)
type bst = Legal of int  * int | Illegal | Empty

let is_bst (tr: int tree) =
  let rec is_bst_helper = function
    | Leaf -> Empty
    | Node(a, l, r) -> match is_bst_helper (l), is_bst_helper (r) with
      |(Legal (minl, maxl), Legal (minr, maxr)) -> if maxl < a && a < minr then
          Legal(minl, maxr) else Illegal
      | (Legal(minl, maxl), Empty) -> 
        if maxl < a then Legal(minl, a) else Illegal
      | (Empty, Legal(minr, maxr)) -> 
        if a < minr then Legal(a, maxr) else Illegal
      | _ -> Illegal
  in is_bst_helper tr