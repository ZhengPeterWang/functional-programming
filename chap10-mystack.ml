
module MyStack =
 struct
  type 'a stack = 'a list

  (** val empty : 'a1 stack **)

  let empty =
    []

  (** val is_empty : 'a1 stack -> bool **)

  let is_empty = function
  | [] -> true
  | _::_ -> false

  (** val push : 'a1 -> 'a1 stack -> 'a1 stack **)

  let push x s =
    x::s

  (** val peek : 'a1 stack -> 'a1 option **)

  let peek = function
  | [] -> None
  | x::_ -> Some x

  (** val pop : 'a1 stack -> 'a1 stack option **)

  let pop = function
  | [] -> None
  | _::xs -> Some xs

  (** val size : 'a1 stack -> int **)

  let size =
    List.length
 end
