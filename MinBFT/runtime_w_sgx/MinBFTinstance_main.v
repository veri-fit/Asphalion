Require Export MinBFTinstance.


Extraction "MinbftReplica.ml"
           log_new_prepare_gc1 log_new_prepare_gc2 (* this is only used when we want to GC the log for a fair evaluation *)
           lookup_table MUSIG MLOG MMAIN (*mtest*)
           DirectedMsgs2string bare_msg2string HashData2string
           mk_create_ui_in mk_verify_ui_in
           mk_create_ui_out mk_verify_ui_out
           execute_request
           u1 u2 u3 u4 u5.


(*
  Compile using: ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix MinbftReplica.native
 *)
