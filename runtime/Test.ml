open Colors
open Core
open Async

let foo n =
  let key = Cstruct.of_string "1-2" in
  let msg = Cstruct.of_string "foo" in
  Nocrypto.Hash.SHA256.hmac key msg;
  Deferred.never ()

(*
let foo num =
  print_endline ("[A]");
  print_endline ("[B]");
  within' ~monitor:(Monitor.create ()) (fun () -> Clock.after (Time.Span.of_sec 2.) >>= fun () -> Deferred.return (print_endline ("Kaboom1!")));
  within' ~monitor:(Monitor.create ()) (fun () -> Clock.after (Time.Span.of_sec 2.) >>= fun () -> Deferred.return (print_endline ("Kaboom2!")));
  print_endline ("[C]");
  Deferred.never ()*)

let command =
  Command.async
    ~summary:"Test"
    Command.Spec.(
      empty
      +> flag "-num" (optional_with_default 0 int)
        ~doc:" Num"
    )
    (fun num () -> foo num);;

let () = Rpc_parallel.start_app command;;
