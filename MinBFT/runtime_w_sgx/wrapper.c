#include<stdio.h> //printf
#include<string.h>    //strlen
#include<sys/socket.h>    //socket
#include<arpa/inet.h> //inet_addr

#include <caml/mlvalues.h>
#include <caml/callback.h>
#include <caml/memory.h>

#include "tcp_client.c"



CAMLprim value
caml_connect_to_server(value unit)
{
  int res;
  res = connect_to_server();
  return Val_int(res);
}

CAMLprim value
caml_close_socket(value v)
{
  int sock = Int_val(v);
  close(sock);
  return Val_unit;
}


CAMLprim value
caml_tcp_client(value ml_tuple)
{
  char ** argv;
  int sock;
  value v;

  CAMLparam1(ml_tuple);

  argv = String_val(Field(ml_tuple, 0));
  sock = Int_val(Field(ml_tuple, 1));
  v    = Field(ml_tuple, 2);

  printf("CAML wrapper socket %d\n", Int_val(sock));

  value res;
  res = tcp_client(argv,sock,v);

  CAMLreturn(res);
}

