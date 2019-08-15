#include <stdio.h>


#include <caml/mlvalues.h>
#include <caml/callback.h>
#include <caml/memory.h>


value caml_test(value v) {
  int i = Int_val(v);
  i++;
  printf("new_value: %i\n", i);
  return (Val_int(i));
}
