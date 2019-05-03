
module Compiler :
 sig
  type expr =
  | Const of int
  | Plus of expr * expr

  val eval_expr : expr -> int

  type instr =
  | PUSH of int
  | ADD

  type prog = instr list

  type stack = int list

  val eval_prog : prog -> stack -> stack option

  val compile : expr -> prog
 end
