open Async
open Crypto


(*let mk_secret n m =
  if n <= m then
    string_of_int n ^ "-" ^ string_of_int m
  else
    string_of_int m ^ "-" ^ string_of_int n*)

let mk_secret (n : int) (m : int) : string = "0"

let export_key (printb : bool) (symkeyfile : string) (n : int) (m : int) : unit Deferred.t =
  let () = Nocrypto_entropy_unix.initialize () in

  let secret  : string     = mk_secret n m in
  let key     : Crypto.key = Crypto.cstruct2key (Cstruct.of_string secret) in
  let sym_key : string     = Crypto.key2string key in

  Writer.open_file ~append:(false) symkeyfile
  >>= fun symw ->
  let _ = Writer.write symw (sym_key ^ "\n") in
  let _ =
    if printb
    then print_endline ("[symmetric key exported to " ^ symkeyfile ^ ": " ^ sym_key ^ "]")
    else print_endline ("[symmetric key exported to " ^ symkeyfile ^ "]") in

  Deferred.return ()


let read_key symkeyfile : unit Deferred.t =
  let sym     : Crypto.key = MacKeyFun.read_symmetric_key symkeyfile in
  let sym_key : string     = Crypto.key2string sym in
  print_endline ("[symmetric key read from " ^ symkeyfile ^ ": " ^ sym_key ^ "]");
  Deferred.return ()
