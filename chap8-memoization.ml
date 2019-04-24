(* Memoization *)
let fibm (n) = 
  let memo: int option array = Array.make (n + 1) None in 
  let rec f_mem n = 
    match memo.(n) with 
    | Some result -> result
    | None -> let result = if n < 2 then 1 else f_mem (n - 1) + f_mem (n - 2) in 
      memo.(n) <- Some result;
      result
  in 
  f_mem n

module Unmemoized = struct
  type tree = Empty | Node of int * tree * tree
  let rec party t = max (party_in t) (party_out t)
  and party_in t = match t with 
    | Empty -> 0
    | Node(v, l, r) -> v + party_out l + party_out r
  and party_out t = match t with
    | Empty -> 0
    | Node (v, l, r) -> party l + party r
end

module Memoized = struct
  type tree = Empty
            | Node of int * string * tree * tree * 
                      ((int * string list) option) ref
  let rec party t : int * string list = 
    match t with 
    | Empty -> 0, []
    | Node(v, n, l, r, memo) -> 
      begin
        match !memo with 
        | Some result -> result
        | None -> let result = 
                    let a,na = party_in t and b, nb = party_out t in 
                    if a > b then a + v, n :: na else b, nb
          in memo := Some result; result
      end

  and party_in t = match t with 
    | Empty -> 0, []
    | Node(v, n, l, r, _) -> let a, na = party_out l and b, nb = party_out r in 
      a + b, n :: na @ nb
  and party_out t = match t with 
    | Empty -> 0, []
    | Node(_, _, l, r, _) -> let a, na = party l and b, nb = party r in 
      a + b, na @ nb
end

type breakResult = string list * int

let cube x = x * x * x
let big = 1000000
let linebreak1 (words : string list) (target: int): string list = 
  let rec lb (clen: int) (words: string list) : breakResult = 
    match words with 
    | [] -> [""], 0
    | word::rest -> 
      begin 
        let wlen = String.length word in 
        let contlen = if clen = 0 then wlen else clen + 1 + wlen in 
        let l1, c1' = lb 0 rest in 
        let c1 = c1' + cube (target - contlen) in 
        if contlen <= target then 
          let h2::t2, c2 = lb contlen rest in
          if c1 < c2 then word::l1, c1 else 
            (if h2 = "" then word else word^" "^h2)::t2, c2
        else word::l1, c1 + big
      end
  in let result, cost = lb 0 words in result

let linebreak2 (words: string list) (target: int): string list = 
  let memo : breakResult option array = Array.make (List.length words + 1) None in 
  let rec lb_mem (words: string list): breakResult = 
    let n = List.length words in 
    match Array.get memo n with 
    | Some br -> br
    | None -> let br = lb 0 words in Array.set memo n (Some br); br
  and lb (clen : int) (words: string list): breakResult = 
    match words with 
    | [] -> [""], 0
    | word::rest -> let wlen = String.length word in 
      let contlen = if clen = 0 then wlen else clen + 1 + wlen in 
      let l1, c1' = lb_mem rest in 
      let c1 = c1' + cube (target - contlen) in 
      if contlen <= target then 
        let h2::t2, c2 = lb contlen rest in
        if c1 < c2 then word::l1, c1 else 
          (if h2 = "" then word else word^" "^h2)::t2, c2
      else word::l1, c1 + big
  in 
  let result, cost = lb 0 words in result

let memo f = 
  let h = Hashtbl.create 11 in 
  fun x -> try
      Hashtbl.find h x 
    with Not_found -> let y = f x in 
      Hashtbl.add h x y;
      y
let memo_rec f = 
  let h = Hashtbl.create 11 in 
  let rec g x = try (* [g] is a higher order function representing self *)
      Hashtbl.find h x 
    with Not_found -> 
      let y = f g x in 
      Hashtbl.add h x y;
      y
  in g

let fib_memo = 
  let fib self n = (* recursion symbol goes into [self] *)
    if n < 2 then 1 else self (n - 1) + self (n - 2) in 
  memo_rec fib (* using a "self" function to transfer recursion *)
