let test (n : int) =
  print_endline (Batteries.String.of_list ['a'] ^ string_of_int n)
let _ = test 1
