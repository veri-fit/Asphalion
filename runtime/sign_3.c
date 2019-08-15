#include <stdio.h>
#include <caml/mlvalues.h>
#include <caml/callback.h>
#include <caml/memory.h>

int main(int argc , char **argv) {
  // Initialize OCaml code
  caml_startup(argv);

  static value * out = NULL;
  if (out == NULL) { out = caml_named_value("test3"); }
  value v = caml_callback(*out, Val_int(0));
  char * s = String_val(v);
  printf("string is: %s\n", s);
  return 0;
}
