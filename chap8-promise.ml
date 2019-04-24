

(* Concurrency, Promise, Callback *)
module type Promise = sig 
  type 'a state = Pending | Resolved of 'a | Rejected of exn
  type 'a promise
  type 'a resolver
  val make : unit -> 'a promise * 'a resolver
  val return : 'a -> 'a promise
  val state : 'a promise -> 'a state
  val resolve : 'a resolver -> 'a -> unit
  val reject : 'a resolver -> exn -> unit
  val (>>=): 'a promise -> ('a -> 'b promise) -> 'b promise
end

module LwtPromise:Promise = struct

  type 'a state = Pending | Resolved of 'a | Rejected of exn
  type 'a handler = 'a state -> unit
  type 'a promise = {mutable state : 'a state;
                     mutable handlers : 'a handler list
                    }
  type 'a resolver = 'a promise

  let enqueue (handler: 'a state -> unit) (promise: 'a promise): unit =
    promise.handlers <- handler :: promise.handlers

  let write_once p s = 
    if p.state = Pending then p.state <- s else invalid_arg "cannot write twice"
  let make () = 
    let p = {state = Pending; handlers = []} in p, p
  let return x = {state = Resolved x; handlers = []}
  let state p = p.state

  let resolve_or_reject (r: 'a resolver) (st: 'a state) = 
    assert (st <> Pending);
    let handlers = r.handlers in 
    r.handlers <- [];
    write_once r st;
    List.iter (fun f -> f st) handlers (* an imperative map *)
  let reject r x = resolve_or_reject r (Rejected x)
  let resolve r x = resolve_or_reject r (Resolved x)

  let handler (resolver: 'a resolver): 'a handler = function
    | Pending -> failwith "handler RI violated"
    | Rejected exc -> reject resolver exc
    | Resolved x -> resolve resolver x
  let handler_of_callback (callback : 'a -> 'b promise) (resolver: 'b resolver): 'a handler = function
    | Pending -> failwith "Handler RI violated"
    | Rejected exc -> reject resolver exc
    | Resolved x -> let promise = callback x in 
      match promise.state with
      | Resolved y -> resolve resolver y
      | Rejected exc -> reject resolver exc
      | Pending -> enqueue (handler resolver) promise
  let (>>=) (input_promise: 'a promise) (callback : 'a -> 'b promise) : 'b promise =
    match input_promise.state with
    | Resolved x -> callback x
    | Rejected exc -> {state = Rejected exc; handlers = []}
    | Pending -> let output_promise, output_resolver = make () in 
      enqueue (handler_of_callback callback output_resolver) input_promise;
      (* higher order thinking *)
      output_promise
end

open LwtPromise
let (u, v)  = make ()
let q = u >>= (fun x -> return (print_int x))
let () = resolve v 3 (* after this prints out 3 *)

open Lwt.Infix
open Lwt_io
open Lwt_unix

(** [log ()] is a promise for an [input_channel] that reads from
    the file named "log". *)
let log () : input_channel Lwt.t = 
  openfile "log" [O_RDONLY] 0 >>= fun fd ->
  Lwt.return (of_fd input fd)

(** [loop ic] reads one line from [ic], prints it to stdout,
    then calls itself recursively. It is an infinite loop. *)
let rec loop (ic : input_channel) = 
  ignore(Lwt_io.read_line ic >>= fun x -> Lwt_io.printlf "%s" x); loop ic  
(* hint: use [Lwt_io.read_line] and [Lwt_io.printlf] *)

(** [monitor ()] monitors the file named "log". *)
let monitor () : unit Lwt.t = 
  log () >>= loop

(** [handler] is a helper function for [main]. If its input is
    [End_of_file], it handles cleanly exiting the program by 
    returning the unit promise. Any other input is re-raised 
    with [Lwt.fail]. *)
let handler : exn -> unit Lwt.t = 
  fun _ -> Lwt.return ()

let main () : unit Lwt.t = 
  Lwt.catch monitor handler

let _ = Lwt_main.run (main ())