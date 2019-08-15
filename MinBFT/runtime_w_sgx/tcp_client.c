#define DEBUG 0


/*
    C ECHO client example using sockets
*/
#include<stdio.h> //printf
#include<string.h>    //strlen
#include<sys/socket.h>    //socket
#include<arpa/inet.h> //inet_addr

#include <caml/mlvalues.h>
#include <caml/callback.h>
#include <caml/memory.h>
#include <caml/alloc.h>


#define DLEN 256


int sock;
char ip_address[9] = "127.0.0.1";
int port_number = 8080;

typedef unsigned int SIGN;

enum header{
  HDR_CREATE_UI_IN,
  HDR_VERIFY_UI_IN,
  HDR_CREATE_UI_OUT,
  HDR_VERIFY_UI_OUT,
};

typedef struct __attribute__ ((packed)) pre_ui {
  unsigned int rep;
  unsigned int cid;
  unsigned int counter;
} PRE_UI;

typedef struct __attribute__ ((packed)) ui {
  PRE_UI pre;
  char dig[DLEN];
} UI;

typedef struct __attribute__ ((packed)) bare_request {
  unsigned int client;
  unsigned int timestamp;
  unsigned int operation;
} BARE_REQUEST;

typedef struct __attribute__ ((packed)) request {
  BARE_REQUEST breq;
  SIGN         sign;
} REQUEST;

typedef struct __attribute__((packed)) view_request{
  unsigned int view;
  REQUEST      req;
} VIEW_REQUEST;

typedef struct __attribute__((packed)) create_ui_in {
  VIEW_REQUEST view_req;
  unsigned int old_counter;
  unsigned int new_counter;
} CREATE_UI_IN;

typedef struct __attribute__((packed)) view_request_ui {
  VIEW_REQUEST view_req;
  UI           ui;
} VIEW_REQUEST_UI;

typedef struct __attribute__((packed)) verify_ui_in{
   VIEW_REQUEST_UI view_req_ui;
} VERIFY_UI_IN;

typedef struct __attribute__((packed)) create_ui_out{
  UI           ui;
  unsigned int set; /* 0 for true; 1 for false */
} CREATE_UI_OUT;

typedef struct __attribute__((packed)) verify_ui_out{
  unsigned int res;
} VERIFY_UI_OUT;

typedef struct __attribute__((packed)) interface_in{
  enum header hdr;
  CREATE_UI_IN create;
  VERIFY_UI_IN verify;
} INTERFACE_IN;

typedef struct __attribute__((packed)) interface_out{
  enum header hdr;
  CREATE_UI_OUT create;
  VERIFY_UI_OUT verify;
} INTERFACE_OUT;




void startup(char **argv) {
  caml_startup(argv);
}

void connect_to_trusted_server() {
  struct sockaddr_in server;

  //Create socket
  sock = socket(AF_INET , SOCK_STREAM, 0);
  if (sock == -1)
    {
      printf("Could not create socket");
    }
  puts("Socket created");

  server.sin_addr.s_addr = inet_addr(ip_address);
  server.sin_family = AF_INET;
  server.sin_port = htons( port_number );

  //Connect to remote server
  if (connect(sock, (struct sockaddr *)&server , sizeof(server)) < 0)
    {
      perror("connect failed. Error");
      //return 1;
    }

  printf("-------SOCKET number is %d\n", sock);
  puts("Connected\n");
}


void debug_create_ui_in(value v)
{
  value in_msg, in_v_r_o, in_v_r, in_old, in_new, in_view, in_req, in_b_req, in_sign, in_client, in_timestamp, in_operation, in_sign_sign;

    printf("***********DEBUG CREATE_UI_IN******************\n");
    if (Is_block(v))
      {
	printf ("create_ui_in is another block(%d,%ld)\n", Tag_val(v), Wosize_val(v));
	if (Is_block(v)) {
	  in_msg = Field(v,0);
	  if (Is_block(in_msg)) {
            in_v_r_o = Field(in_msg,0);
            in_new   = Field(in_msg,1);
	    if (Is_block(in_v_r_o)) {
              in_v_r = Field(in_v_r_o,0);
              in_old  = Field(in_v_r_o,1);
              if (Is_block(in_v_r)) {
                in_view = Field(in_v_r,0); printf ("view (%d)\n",Int_val(in_view));
                in_req  = Field(in_v_r,1);
                if (Is_block(in_req)) {
                  in_b_req = Field(in_req,0);
                  in_sign  = Field(in_req,1);
                  if (Is_block(in_b_req)) {
                    in_client    = Field(in_b_req,0);  printf ("client (%d)\n", Int_val(in_client));
                    in_timestamp = Field(in_b_req,1);  printf ("timestamp (%d)\n", Int_val(in_timestamp));
                    in_operation = Field(in_b_req,2);  printf ("operation (%d)\n", Int_val(in_operation));
                    if (Is_block(in_sign)){
                      in_sign_sign = Field(in_sign,0); printf ("signature (%d)\n",Int_val(in_sign));
                    }
                  }
                }
	      }
	    }
	  }
	}
      }
      printf("***********DEBUG END CREATE_UI_IN******************\n");
}

void debug_verify_ui_in(value v)
{
  value in_msg, in_old, in_new, in_view, in_req, in_b_req, in_sign, in_client, in_timestamp, in_operation, in_sign_sign;
  value in_v_r_ui, in_v_r, in_ui, in_ui_pre, in_dig, in_ui_rep, in_ui_cid, in_ui_count;


  printf("*********** test side DEBUG VERIFY_UI_IN ******************\n");
  if (Is_block(v))
    {
      printf ("verify_ui_in is another block(%d,%ld)\n", Tag_val(v), Wosize_val(v));
      if (Is_block(v)) {
	in_v_r_ui = Field(v,0);
	if (Is_block(in_v_r_ui)) {
	  in_v_r = Field(in_v_r_ui,0);
	  in_ui  = Field(in_v_r_ui,1);
	  if (Is_block(in_v_r)) {
	    in_view = Field(in_v_r,0); printf ("view (%d)\n",Int_val(in_view));
	    in_req = Field(in_v_r,1);
	    if (Is_block(in_req)) {
	      in_b_req = Field(in_req,0);
	      in_sign  = Field(in_req,1); printf ("tok (%d)\n",Int_val(in_sign));
	      if (Is_block(in_b_req)) {
		in_client    = Field(in_b_req,0); printf ("client (%d)\n",    Int_val(in_client));
		in_timestamp = Field(in_b_req,1); printf ("timestamp (%d)\n", Int_val(in_timestamp));
		in_operation = Field(in_b_req,2); printf ("operation (%d)\n", Int_val(in_operation));
	      }
	    }
	  }
	  if (Is_block(in_ui)){
	    in_ui_pre = Field(in_ui,0);
	    in_dig    = Field(in_ui,1); printf ("dig (%s)\n", String_val(in_dig));
	    if (Is_block(in_ui_pre)){
	      in_ui_rep   = Field(in_ui_pre,0); printf ("replica (%d)\n", Int_val(in_ui_rep));
              in_ui_cid   = Field(in_ui_pre,1); printf ("cid (%d)\n",     Int_val(in_ui_cid));
              in_ui_count = Field(in_ui_pre,2); printf ("count (%d)\n",   Int_val(in_ui_count));
	    }
	  }
	}
      }
    }
    printf("***********DEBUG VERIFY_UI_IN END******************\n");
}

void debug_verify_ui_out(value res)
{
  printf("***********DEBUG VERIFY_UI_OUT******************\n");
  if (Is_block(res)){
    printf ("verify_ui_out is another block(%d,%ld)\n", Tag_val(res), Wosize_val(res));
    value b_val = Field(res,0);
    printf(" FINAL RES IS %d\n", Bool_val(b_val));
  }
  printf("***********DEBUG VERIFY_UI_OUT END******************\n");
}

struct interface_in convert_create_ui_in_to_struct(value v)
{
  value in_msg, in_v_r_o, in_v_r, in_old, in_new, in_view, in_req, in_b_req, in_sign, in_client, in_timestamp, in_operation;

  struct bare_request br_par;
  struct request req_par;
  struct view_request v_req_par;
  struct create_ui_in create_ui_in_par;
  struct interface_in interface_in_par;

  if (DEBUG) { printf("client side : Create_UI_IN\n"); }
  if (Is_block(v))
    {
      if (DEBUG) { printf ("cu_ui_in is another block(%d,%ld)\n", Tag_val(v), Wosize_val(v)); }
      if (Is_block(v)) {
	in_msg = Field(v,0);
	if (Is_block(in_msg)) {
          in_v_r_o = Field(in_msg,0);
	  in_new   = Field(in_msg,1);
          if (Is_block(in_v_r_o)) {
            in_v_r = Field(in_v_r_o,0);
            in_old = Field(in_v_r_o,1);
            if (Is_block(in_v_r)) {
              in_view = Field(in_v_r,0); if (DEBUG) { printf ("view (%d)\n",Int_val(in_view)); }
              in_req  = Field(in_v_r,1);
              if (Is_block(in_req)) {
                in_b_req = Field(in_req,0);
                in_sign  = Field(in_req,1);  if (DEBUG) { printf ("signature (%d)\n",Int_val(in_sign)); }
                if (Is_block(in_b_req)) {
                  in_client    = Field(in_b_req,0);  if (DEBUG) { printf ("client (%d)\n",    Int_val(in_client));    }
                  in_timestamp = Field(in_b_req,1);  if (DEBUG) { printf ("timestamp (%d)\n", Int_val(in_timestamp)); }
                  in_operation = Field(in_b_req,2);  if (DEBUG) { printf ("operation (%d)\n", Int_val(in_operation)); }
                }
              }
            }
	  }
	}
      }
    }

  br_par = (BARE_REQUEST) { .client = Int_val(in_client), .timestamp = Int_val(in_timestamp), .operation = Int_val(in_operation)};

  req_par = (REQUEST) {.breq = br_par, .sign = 0/*Int_val(in_sign)*/};

  v_req_par = (VIEW_REQUEST) { .view = Int_val(in_view), .req  = req_par};

  create_ui_in_par = (CREATE_UI_IN){ .view_req = v_req_par, .old_counter = Int_val(in_old), .new_counter = Int_val(in_new) };

  interface_in_par = (INTERFACE_IN){ .hdr = HDR_CREATE_UI_IN, .create = create_ui_in_par};

  return interface_in_par;
}

struct interface_in convert_verify_ui_in_to_struct(value v)
{

  value in_msg, in_view, in_req, in_b_req, in_sign, in_client, in_timestamp, in_operation;
  value in_v_r_ui, in_v_r, in_ui, in_ui_pre, in_dig, in_ui_rep, in_ui_cid, in_ui_count;

  struct bare_request br_par;
  struct request req_par;
  struct view_request v_req_par;
  struct verify_ui_in verify_ui_in_par;
  struct interface_in interface_in_par;
  struct ui ui_par;
  struct pre_ui ui_pre_par;
  struct view_request_ui view_request_ui_par;

  if (DEBUG) { printf(" CLIENT side: VERIFY_UI_IN\n"); }

  if (Is_block(v))
    {
      if (DEBUG) { printf ("verify_ui_in is another block(%d,%ld)\n", Tag_val(v), Wosize_val(v)); }
      if (Is_block(v)) {
	in_v_r_ui = Field(v,0);
	if (Is_block(in_v_r_ui)) {
	  in_v_r = Field(in_v_r_ui,0);
	  in_ui = Field(in_v_r_ui,1);
	  if (Is_block(in_v_r)) {
	    in_view = Field(in_v_r,0); if (DEBUG) { printf ("view (%d)\n",Int_val(in_view)); }
	    in_req = Field(in_v_r,1);
	    if (Is_block(in_req)) {
	      in_b_req = Field(in_req,0);
	      in_sign  = Field(in_req,1);  if (DEBUG) { printf ("tok (%d)\n",Int_val(in_sign)); }
	      if (Is_block(in_b_req)) {
		in_client    = Field(in_b_req,0);  if (DEBUG) { printf ("client (%d)\n",    Int_val(in_client));    }
		in_timestamp = Field(in_b_req,1);  if (DEBUG) { printf ("timestamp (%d)\n", Int_val(in_timestamp)); }
		in_operation = Field(in_b_req,2);  if (DEBUG) { printf ("operation (%d)\n", Int_val(in_operation)); }
	      }
	    }
	  }
	  if (Is_block(in_ui)){
	    in_ui_pre = Field(in_ui,0);
	    in_dig    = Field(in_ui,1); if (DEBUG) { printf ("dig (%s)\n", String_val(in_dig)); }
	    if (Is_block(in_ui_pre)){
	      in_ui_rep   = Field(in_ui_pre,0); if (DEBUG) { printf ("replica (%d)\n", Int_val(in_ui_rep));   }
	      in_ui_cid   = Field(in_ui_pre,1); if (DEBUG) { printf ("cid (%d)\n",     Int_val(in_ui_cid));   }
	      in_ui_count = Field(in_ui_pre,2); if (DEBUG) { printf ("count (%d)\n",   Int_val(in_ui_count)); }
	    }
	  }
	}
      }
    }


  br_par = (BARE_REQUEST) { .client = Int_val(in_client), .timestamp = Int_val(in_timestamp), .operation = Int_val(in_operation)};

  req_par = (REQUEST) { .breq = br_par, .sign = 0/*Int_val(in_sign)*/};

  v_req_par = (VIEW_REQUEST) { .view = Int_val(in_view), .req  = req_par};

  ui_pre_par = (PRE_UI){ .rep = Int_val(in_ui_rep), .cid = Int_val(in_ui_cid), .counter = Int_val(in_ui_count)};

  ui_par.pre = ui_pre_par;
  char * s = String_val(in_dig);
  for (int i = 0; i < DLEN; i++) { ui_par.dig[i] = s[i]; }
  //strncpy(ui_par.dig,String_val(in_dig),DLEN);
  //ui_par = (UI){ .pre = ui_pre_par, .dig = String_val(in_dig)};

  view_request_ui_par = (VIEW_REQUEST_UI) { .view_req = v_req_par, .ui = ui_par};

  verify_ui_in_par = (VERIFY_UI_IN){ .view_req_ui = view_request_ui_par};

  interface_in_par = (INTERFACE_IN){ .hdr = HDR_VERIFY_UI_IN, .verify = verify_ui_in_par};

  return interface_in_par;
 }


void debug_create_ui_out(value res)
{
  value out_opui, out_ui, out_ui_pred, out_ui_dig, out_ui_count, out_ui_rep, out_ui_cid, out_res, out_dig;

  printf("***********DEBUG CREATE_UI_OUT******************\n");
    if (Is_block(res)){
      out_opui = Field(res,0);
      if (Is_block(out_opui)){
        if (Tag_val(out_opui) == 0) { // Then Some
          out_ui = Field(out_opui,0);
          if (Is_block(out_ui)){
            out_ui_pred = Field(out_ui,0);
            out_dig     = Field(out_ui,1); printf("dig %s\n",String_val(out_dig));
            if (Is_block(out_ui_pred)) {
              out_ui_rep   = Field(out_ui_pred,0); printf("REPLICA %d\n",Int_val(out_ui_rep));
              out_ui_cid   = Field(out_ui_pred,1); printf("cid %d\n",    Int_val(out_ui_cid));
              out_ui_count = Field(out_ui_pred,2); printf("counter %d\n",Int_val(out_ui_count));
            }
          }
        }
      }
    }
    printf("***********DEBUG CREATE_UI_OUT END******************\n");
}


value convert_interface_struct_to_create_ui_out(struct interface_out interface_out_par)
{
  value res;
  value gargs[3];

  if (DEBUG) { printf("CREATE_UI_OUT\n"); }

  // Only do this if:  interface_out_par.create.set == 0

  gargs[0] = Val_int(interface_out_par.create.ui.pre.rep); /* replica */
  // we ditch the counter id here because we use a dummy one is MinBFTinstance.
  //gargs[1] = Val_int(interface_out_par.create.ui.pre.cid); /* counter id */
  gargs[1] = Val_int(interface_out_par.create.ui.pre.counter);   /* counter */
  //if (DEBUG) { printf("\n(1)\n)"); }
  //if (DEBUG) { printf("string is: %s\n", interface_out_par.create.ui.dig); }
  //if (DEBUG) { printf("\n(2)\n)"); }
  gargs[2] = caml_copy_string(interface_out_par.create.ui.dig); /* dig */
  //if (DEBUG) { printf("\n(3)\n)"); }

  if (DEBUG) { printf("\n\nREPLICA %d\n", interface_out_par.create.ui.pre.rep); }
  if (DEBUG) { printf("counter %d\n", interface_out_par.create.ui.pre.counter); }
  if (DEBUG) { printf("digital %s\n", interface_out_par.create.ui.dig); }

  /* r c d */
  /***********************************/
  static value * mk_cui_out_c = NULL;
  if (mk_cui_out_c == NULL) mk_cui_out_c = caml_named_value("mk_create_ui_out");
  res = caml_callbackN(*mk_cui_out_c, 3, gargs);

  if (DEBUG) { printf("****************INTERFACE_OUT CONVERTED TO CREATE_UI_OUT\n"); }

  if (DEBUG) { debug_create_ui_out(res); }

  return res;
}

value convert_interface_struct_to_verify_ui_out(struct interface_out interface_out_par) {
  value gargs[1];

  if (DEBUG) { printf("VERIFY_UI_OUT\n"); }

  gargs[0] = Val_int(interface_out_par.verify.res); /* bool */

  /*********************************/
  static value * mk_cui_out_c = NULL;
  if (mk_cui_out_c == NULL) mk_cui_out_c = caml_named_value("mk_verify_ui_out");
  value res = caml_callbackN(*mk_cui_out_c, 1, gargs);

  if (DEBUG) { printf("****************INTERFACE BACK TO VALUE VERSION\n"); }

  if (DEBUG) { debug_verify_ui_out(res); }

  return res;
}



value tcp_client(value v) {
  struct interface_in interface_in_par;
  struct interface_out interface_out_par;
  value res;
  int read_size;

  // Initialize OCaml code
  //startup("");

  if (DEBUG) { printf("SOCKET is %d\n",sock); }

  /* convert value to the structures */

  /* check is it create_ui_in or verify_ui_in */
  if (Tag_val(v) == 0) {
    interface_in_par = convert_create_ui_in_to_struct(v); //create_ui_in
  } else {
    interface_in_par = convert_verify_ui_in_to_struct(v); //verify_ui_in
  }

  /* end of conversion of the value to the structures */

  //Send some data
  if (send(sock , &interface_in_par, sizeof(INTERFACE_IN), 0) < 0) {
    printf("SOCKET is %d\n",sock);
    puts("Send failed");
    return 1;
  }
  if (DEBUG) { printf("SENT: \n"); }


  /**********************************************************************************************************/

  if (read_size = recv(sock, &interface_out_par, sizeof(INTERFACE_OUT), 0) < 0) {
    puts("recv failed");
    return 1;
  }

  if (DEBUG) { printf("[READ INPUT %d/%ld]\n", read_size, sizeof(INTERFACE_IN)); }

  if (interface_out_par.hdr == HDR_CREATE_UI_OUT) {
    res = convert_interface_struct_to_create_ui_out(interface_out_par);
  } else {
    res = convert_interface_struct_to_verify_ui_out(interface_out_par);
  }

  return res;
}

void set_port_number(int port) {
  port_number = port;
}


value caml_connect_to_server(value unit) {
  connect_to_trusted_server();
  return Val_unit;
}

value caml_close_socket(value v) {
  close(Int_val(v));
  return Val_unit;
}

value caml_tcp_client(value v) {
  if (DEBUG) { printf("CAML wrapper socket %d\n", Int_val(sock)); }
  return (tcp_client(v));
}

value caml_set_port_number(value port) {
  set_port_number(Int_val(port));
  return Val_unit;
}
