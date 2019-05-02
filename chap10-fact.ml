
(** val add : int -> int -> int **)

let rec add n m =
  (fun f0 fs -> if n = 0 then f0 () else fs (n - 1))
    (fun _ -> m)
    (fun p -> succ (add p m))
    n

(** val mul : int -> int -> int **)

let rec mul n m =
  (fun f0 fs -> if n = 0 then f0 () else fs (n - 1))
    (fun _ -> 0)
    (fun p -> add m (mul p m))
    n

(** val fact_tr_acc : int -> int -> int **)

let rec fact_tr_acc n acc =
  (fun f0 fs -> if n = 0 then f0 () else fs (n - 1))
    (fun _ -> acc)
    (fun k -> fact_tr_acc k (mul n acc))
    n

(** val fact_tr : int -> int **)

let fact_tr n =
  fact_tr_acc n (succ 0)
