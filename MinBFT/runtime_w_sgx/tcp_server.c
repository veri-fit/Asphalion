#define DEBUG 0


/*
    C socket server example
*/
#include<stdio.h>
#include<string.h>    //strlen
#include<sys/socket.h>
#include<arpa/inet.h> //inet_addr
#include<unistd.h>    //write

#include <caml/mlvalues.h>
#include <caml/callback.h>
#include <caml/memory.h>
#include <caml/alloc.h>


#define DLEN 256


int MAXLINE = 250;
int CONF_FILE_SIZE = 250;
int port_number = 8080;

typedef unsigned int SIGN;

enum header{
	    HDR_CREATE_UI_IN,
	    HDR_VERIFY_UI_IN,
	    HDR_CREATE_UI_OUT,
	    HDR_VERIFY_UI_OUT,
};

typedef struct __attribute__ ((packed)) pre_ui{
  unsigned int rep;
  unsigned int cid;
  unsigned int counter;
} PRE_UI;

typedef struct __attribute__ ((packed)) ui{
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

typedef struct __attribute__((packed)) view_request {
  unsigned int view;
  REQUEST      req;
} VIEW_REQUEST;

typedef struct __attribute__((packed)) create_ui_in {
  VIEW_REQUEST view_req;
  unsigned int old_counter;
  unsigned int new_counter;
} CREATE_UI_IN;

typedef struct __attribute__((packed)) view_request_ui{
  VIEW_REQUEST view_req;
  UI           ui;
} VIEW_REQUEST_UI;

typedef struct __attribute__((packed)) verify_ui_in{
  VIEW_REQUEST_UI view_req_ui;
} VERIFY_UI_IN;

typedef struct __attribute__((packed)) create_ui_out{
  UI           ui;
  unsigned int set; // 0 for true; 1 for false
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

value execute_request(value i) {
  static value * execute_request_closure = NULL;
  if (execute_request_closure == NULL)
    execute_request_closure = caml_named_value("execute_request");
  value cuiout = caml_callback(*execute_request_closure, i);
  return cuiout;
}

int connect_to_client() {
  int socket_desc, client_sock, c;
    struct sockaddr_in server, client;

    //Create socket
    socket_desc = socket(AF_INET , SOCK_STREAM , 0);
    if (socket_desc == -1) {
      printf("Could not create socket");
    }
    puts("Socket created");

    if (setsockopt(socket_desc, SOL_SOCKET, SO_REUSEADDR, &(int){ 1 }, sizeof(int)) < 0) {
      perror("setsockopt(SO_REUSEADDR) failed");
    }

    //Prepare the sockaddr_in structure
    server.sin_family = AF_INET;
    server.sin_addr.s_addr = INADDR_ANY;
    server.sin_port = htons( port_number );

    //Bind
    if( bind(socket_desc,(struct sockaddr *)&server , sizeof(server)) < 0)
      {
        //print the error message
        perror("bind failed. Error");
        return 1;
      }
    puts("bind done");

    //Listen
    listen(socket_desc , 3);

    //Accept and incoming connection
    puts("Waiting for incoming connections...");
    c = sizeof(struct sockaddr_in);

    //accept connection from an incoming client
    client_sock = accept(socket_desc, (struct sockaddr *)&client, (socklen_t*)&c);
    if (client_sock < 0)
    {
        perror("accept failed");
        return 1;
    }
    puts("Connection accepted");

    return client_sock;
}

void debug_create_ui_in(value v) {
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

value convert_interface_struct_to_create_ui_in(struct interface_in interface_in_par) {
  value targs[5];
  value v;

  if (DEBUG) { printf("CREATE UI IN\n "); }

  targs[0] = Val_int(interface_in_par.create.view_req.view); /* view */
  targs[1] = Val_int(interface_in_par.create.view_req.req.breq.client);   /* client */
  targs[2] = Val_int(interface_in_par.create.view_req.req.breq.timestamp); /* timestamp */
  targs[3] = Val_int(interface_in_par.create.view_req.req.breq.operation); /* operation */
  targs[4] = Val_int(0/*interface_in_par.create.view_req.req.sign*/); /* tok */
  // We ditch the old/new counters her because we use dummy ones in MinBFTinstance
  //targs[5] = Val_int(interface_in_par.create.old_counter); /* old counter */
  //targs[6] = Val_int(interface_in_par.create.new_counter); /* new counter */

  /* v c t op tok */
  static value * mk_cui_closure = NULL;
  if (mk_cui_closure == NULL) mk_cui_closure = caml_named_value("mk_create_ui_in");
  v = caml_callbackN(*mk_cui_closure, 5, targs);


  if (DEBUG) { printf("****************INTERFACE BACK TO VALUE VERSION\n"); }

  if (DEBUG) { debug_create_ui_in(v); }

  return v;
}

void debug_verify_ui_in(value v) {
  value in_msg, in_view, in_req, in_b_req, in_sign, in_client, in_timestamp, in_operation, in_sign_sign;
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
	      in_sign  = Field(in_req,1);  printf ("tok (%d)\n",Int_val(in_sign));
	      if (Is_block(in_b_req)) {
		in_client    = Field(in_b_req,0);  printf ("client (%d)\n", Int_val(in_client));
		in_timestamp = Field(in_b_req,1);  printf ("timestamp (%d)\n", Int_val(in_timestamp));
		in_operation = Field(in_b_req,2);  printf ("operation (%d)\n", Int_val(in_operation));
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



value convert_interface_struct_to_verify_ui_in(struct interface_in interface_in_par) {
  value gargs[8];

  if (DEBUG) { printf("VERIFY UI IN\n "); }

  gargs[0] = Val_int(interface_in_par.verify.view_req_ui.view_req.view); // view
  gargs[1] = Val_int(interface_in_par.verify.view_req_ui.view_req.req.breq.client); // client 
  gargs[2] = Val_int(interface_in_par.verify.view_req_ui.view_req.req.breq.timestamp); // timestamp 
  gargs[3] = Val_int(interface_in_par.verify.view_req_ui.view_req.req.breq.operation); // operation 
  gargs[4] = Val_int(0/*interface_in_par.verify.view_req_ui.view_req.req.sign*/); // tok
  gargs[5] = Val_int(interface_in_par.verify.view_req_ui.ui.pre.rep); // replica
  //gargs[6] = Val_int(interface_in_par.verify.view_req_ui.ui.pre.cid); // counter id
  // We ditch the counter id here because we use a dummy one in MinBFTinstance
  gargs[6] = Val_int(interface_in_par.verify.view_req_ui.ui.pre.counter); // counter
  gargs[7] = caml_copy_string(interface_in_par.verify.view_req_ui.ui.dig); // dig


  /*
    printf("\n \n REPLICA %d\n", interface_in_par.verify.view_req_ui.ui.pre.rep);
    printf("counter %d\n", interface_in_par.verify.view_req_ui.ui.pre.counter);
    printf("digital %d\n", interface_in_par.verify.view_req_ui.ui.dig);
    printf("view  %d\n", interface_in_par.verify.view_req_ui.view_req.view);
    printf("client %d\n", interface_in_par.verify.view_req_ui.view_req.req.breq.client); // client 
    printf("timestamp %d\n", interface_in_par.verify.view_req_ui.view_req.req.breq.timestamp); // timestamp 
    printf("operation %d\n", interface_in_par.verify.view_req_ui.view_req.req.breq.operation); // operation 
    printf("tok %d\n",interface_in_par.verify.view_req_ui.view_req.req.sign); // tok
  */

  static value * mk_vui_out_c = NULL;
  if (mk_vui_out_c == NULL) { mk_vui_out_c = caml_named_value("mk_verify_ui_in"); }
  value v = caml_callbackN(*mk_vui_out_c, 8, gargs);


  if (DEBUG) { printf("****************INTERFACE BACK TO VALUE VERSION VUI_IN\n"); }

  if (DEBUG) { debug_verify_ui_in(v); }

  return v;
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


struct interface_out convert_create_ui_out_to_struct(value res)
{
  value out_opui, out_ui, out_ui_pred, out_ui_dig, out_ui_count, out_ui_rep, out_ui_cid, out_res, out_dig;
  struct pre_ui ui_pre_par;
  struct ui ui_par;
  struct create_ui_out create_ui_out_par;
  struct interface_out interface_out_par;

  unsigned int ui_is_set;

  if (DEBUG) { printf("\n CREATE_UI_OUT \n"); }

  if (Is_block(res)){
    out_opui = Field(res,0);
    if (Is_block(out_opui)){
      if (Tag_val(out_opui) == 0) { // Then Some
        out_ui = Field(out_opui,0);
        if (Is_block(out_ui)){
          ui_is_set = 0;
          out_ui_pred = Field(out_ui,0);
          out_dig     = Field(out_ui,1); if (DEBUG) { printf("dig %s\n",String_val(out_dig)); }
          if (Is_block(out_ui_pred)) {
            out_ui_rep   = Field(out_ui_pred,0); if (DEBUG) { printf("REPLICA %d\n",Int_val(out_ui_rep));   }
            out_ui_cid   = Field(out_ui_pred,1); if (DEBUG) { printf("cid %d\n",Int_val(out_ui_cid));       }
            out_ui_count = Field(out_ui_pred,2); if (DEBUG) { printf("counter %d\n",Int_val(out_ui_count)); }

            ui_pre_par = (PRE_UI){ .rep = Int_val(out_ui_rep), .cid = Int_val(out_ui_cid), .counter = Int_val(out_ui_count)};
            ui_par.pre = ui_pre_par;
            char * s = String_val(out_dig);
            for (int i = 0; i < DLEN; i++) { ui_par.dig[i] = s[i]; }
            //strncpy(ui_par.dig,String_val(out_dig),DLEN);
            //ui_par = (UI){ .pre = ui_pre_par, .dig = String_val(out_dig)};
          }
        } else {
          ui_is_set = 1;
        }
      }
    }
  }

  create_ui_out_par = (CREATE_UI_OUT) { .ui  = ui_par, .set = ui_is_set };
  interface_out_par = (INTERFACE_OUT) { .hdr = HDR_CREATE_UI_OUT, .create = create_ui_out_par };

  //if (DEBUG) { printf("\n(1)\n)"); }
  //if (DEBUG) { printf("string is: %s\n", interface_out_par.create.ui.dig); }
  //if (DEBUG) { printf("\n(2)\n)"); }

  if (DEBUG) { debug_create_ui_out(res); }

  return interface_out_par;
}

void debug_verify_ui_out(value res) {
  printf("***********DEBUG VERIFY_UI_OUT******************\n");
  if (Is_block(res)){
    printf ("verify_ui_out is another block(%d,%ld)\n", Tag_val(res), Wosize_val(res));
    value b_val = Field(res,0);
    printf(" FINAL RES IS %d\n", Int_val(b_val));
  }
  printf("***********DEBUG VERIFY_UI_OUT END******************\n");
}


struct interface_out convert_verify_ui_out_to_struct(value res) {
  value out_res;
  struct interface_out interface_out_par;
  struct verify_ui_out verify_ui_out_par;

  if (DEBUG) { printf("\n VERIFY_UI_OUT \n"); }

  if (Is_block(res)){
    out_res = Field(res,0); if (DEBUG) { printf("result is %d\n", Bool_val(out_res)); }
  }

  verify_ui_out_par = (VERIFY_UI_OUT) { .res = Bool_val(out_res)};

  interface_out_par = (INTERFACE_OUT) { .hdr = HDR_VERIFY_UI_OUT, .verify = verify_ui_out_par};

  if (DEBUG) { debug_verify_ui_out(res); }

  return interface_out_par;
}



int getUsigPort(FILE* file, int id){
  char buffer[MAXLINE];
  char *linestatus=NULL;
  char *token=NULL;
  char *delimiter=" ";
  while((linestatus=fgets(buffer,MAXLINE,file))!=NULL){
    int len=strlen(buffer);
    buffer[len-2]='\0'; //removing \n from string

    // This is the 'id' part
    token=strtok(buffer,delimiter);

    if (atoi(token+3) == id) {
      printf("[read id: %d]\n", id);
      //host
      token=strtok(NULL,delimiter);
      //replica port
      token=strtok(NULL,delimiter);
      //usig port
      token=strtok(NULL,delimiter);

      int port = atoi(token+10);
      printf("[read usig port: %d]\n", port);
      return port;
    }
  }
}

int main(int argc , char **argv) {
  int client_sock, read_size;

  struct interface_in interface_in_par;
  struct interface_out interface_out_par;

  int myid = 0;
  if (argc > 1) { sscanf(argv[1], "%d", &myid); }
  printf ("[my id is: %d]\n", myid);

  char conf[CONF_FILE_SIZE];
  if (argc > 2) { sscanf(argv[2], "%s", conf); }
  printf ("[configuration file is: %s]\n", conf);

  FILE *file=fopen(conf,"r");
  int uport = getUsigPort(file,myid);
  port_number = uport;
  printf("[port is now: %d]\n", port_number);

  value res, v;

  // Initialize OCaml code
  caml_startup(argv);

  client_sock = connect_to_client();

  if (DEBUG) { printf("[WAITING FOR AN INPUT]\n"); }
  // !!! What if we haven't read the whole thing !!!
  while((read_size = recv(client_sock, &interface_in_par, sizeof(INTERFACE_IN), 0)) > 0)
    {

      if (DEBUG) { printf("[READ INPUT %d/%ld]\n", read_size, sizeof(INTERFACE_IN)); }

      /* convert interface to value */
      if (interface_in_par.hdr == HDR_CREATE_UI_IN) {
	v = convert_interface_struct_to_create_ui_in(interface_in_par);
      } else {
	v = convert_interface_struct_to_verify_ui_in(interface_in_par);
      }

      if (DEBUG) { printf("*********ABOUT TO EXECUTE-----------------\n"); }
      value res = execute_request(v);
      if (DEBUG) { printf("*********EXECUTED-----------------\n"); }

      /***************************************************************************************/

      /* convert value to C struct */
      if (interface_in_par.hdr == HDR_CREATE_UI_IN) {
      	interface_out_par = convert_create_ui_out_to_struct(res); //create_ui_in
      } else {
        interface_out_par = convert_verify_ui_out_to_struct(res); //verify_ui_in
      }

      /* /\* convert value to C struct *\/ */
      /* if (Tag_val(v) == 0) { */
      /*   if (interface_in_par.hdr == HDR_VERIFY_UI_IN) { */
      /*     printf("!!!!! verify input/create output\n"); */
      /*     while (1) { sleep (1000); } */
      /*   } */
      /*   interface_out_par = convert_create_ui_out_to_struct(res); //create_ui_in */
      /* } else if (Tag_val(v) == 1) { */
      /*   if (interface_in_par.hdr == HDR_CREATE_UI_IN) { */
      /*     printf("!!!!! create input/verify output\n"); */
      /*     while (1) { sleep (1000); } */
      /*   } */
      /*   interface_out_par = convert_verify_ui_out_to_struct(res); //verify_ui_in */
      /* } else { */
      /*   //printf("\n Default interface \n"); //default */
      /*   perror("bad interface"); */
      /* } */

      if (DEBUG) { printf("OUTPUT_INTERFACE_CALCULATED\n"); }
      if (DEBUG) {
        if (Tag_val(v) == 0)
          { printf("digest is: %s\n", interface_out_par.create.ui.dig); }
      }
      /* value is now a C structure */



      //Send the message back to client
      write(client_sock , &interface_out_par , sizeof(INTERFACE_OUT));
    }


    if(read_size == 0)
    {
        puts("Client disconnected");
        fflush(stdout);
    }
    else if(read_size == -1)
    {
        perror("recv failed");
    }

    return 0;
}
