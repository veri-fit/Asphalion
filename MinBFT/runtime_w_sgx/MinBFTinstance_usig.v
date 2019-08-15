Require Export MinBFTinstance.


Extraction "USIG_extracted.ml"
           lookup_table MUSIG (*mtest*)
           DirectedMsgs2string bare_msg2string HashData2string
           mk_create_ui_in mk_verify_ui_in
           mk_create_ui_out mk_verify_ui_out
           execute_request
           u1 u2 u3 u4 u5.
