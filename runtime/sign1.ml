open Colors

external call_c_test : int -> int = "caml_test"

let test1 () =
  let time1 = SpPrelude.Time.get_time () in
  let i : int = call_c_test 33 in
  print_endline (kYEL ^ "[V=" ^ string_of_int i ^ ";T=" ^ SpPrelude.of_list (SpPrelude.Time.time2string (SpPrelude.Time.sub_time (SpPrelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);
  ()

let _ = print_endline ("------")

let _ = test1 ()

(*

  ocamlc -c test.c
  ocamlfind ocamlc -custom -package batteries -a -o test2.cma Colors.ml SpPrelude.ml test2.ml
  ocamlfind ocamlc -custom -package batteries -o prog test2.cma test.o
  ./prog

 *)
