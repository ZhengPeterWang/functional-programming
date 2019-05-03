
module Compiler =
 struct
  type expr =
  | Const of int
  | Plus of expr * expr

  (** val eval_expr : expr -> int **)

  let rec eval_expr = function
  | Const i -> i
  | Plus (e1, e2) -> ( + ) (eval_expr e1) (eval_expr e2)

  type instr =
  | PUSH of int
  | ADD

  type prog = instr list

  type stack = int list

  (** val eval_prog : prog -> stack -> stack option **)

  let rec eval_prog p s =
    match p with
    | [] -> Some s
    | i::p' ->
      (match i with
       | PUSH n -> eval_prog p' (n::s)
       | ADD ->
         (match s with
          | [] -> None
          | x::l ->
            (match l with
             | [] -> None
             | y::s' -> eval_prog p' ((( + ) x y)::s'))))

  (** val compile : expr -> prog **)

  let rec compile = function
  | Const n -> (PUSH n)::[]
  | Plus (e1, e2) -> ( @ ) (compile e2) (( @ ) (compile e1) (ADD::[]))
 end
