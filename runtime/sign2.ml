open Colors

external call_c_test           : int -> int                = "caml_test"
external call_c_newEC          : int -> Obj.t              = "newEC0"
external call_c_loadPrivateKey : int -> Obj.t -> int       = "loadPrivateKey0"
external call_c_loadPublicKey  : int -> Obj.t -> int       = "loadPublicKey0"
external call_c_signTextTest   : Obj.t -> string = "signTextTest0"

let test1 () =
  let time1 = SpPrelude.Time.get_time () in
  let i : int = call_c_test 33 in
  print_endline (kYEL ^ "[V=" ^ string_of_int i ^ ";T=" ^ SpPrelude.of_list (SpPrelude.Time.time2string (SpPrelude.Time.sub_time (SpPrelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);
  ()

let test2 () =
  let time1 = SpPrelude.Time.get_time () in
  let priv : Obj.t  = call_c_newEC 0 in
  let pub  : Obj.t  = call_c_newEC 0 in
  let _    : int    = call_c_loadPrivateKey 0 priv in
  let _    : int    = call_c_loadPublicKey 0 pub in
  let s    : string = call_c_signTextTest priv in
  (*print_endline ("----\n" ^ s ^ "\n----");*)
  print_endline (kYEL ^ "[T=" ^ SpPrelude.of_list (SpPrelude.Time.time2string (SpPrelude.Time.sub_time (SpPrelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);
  ()

let _ = test2 ()

(*

  ocamlc -c test.c
  ocamlfind ocamlc -custom -package batteries -a -o test2.cma Colors.ml SpPrelude.ml test2.ml
  ocamlfind ocamlc -custom -package batteries -o prog test2.cma test.o
  ./prog

 *)
