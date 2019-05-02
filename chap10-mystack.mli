
module MyStack :
 sig
  type 'a stack = 'a list

  val empty : 'a1 stack

  val is_empty : 'a1 stack -> bool

  val push : 'a1 -> 'a1 stack -> 'a1 stack

  val peek : 'a1 stack -> 'a1 option

  val pop : 'a1 stack -> 'a1 stack option

  val size : 'a1 stack -> int
 end
