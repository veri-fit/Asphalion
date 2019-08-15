type view = int

type preUI = { pre_ui_rid     : int;
               pre_ui_cid     : int;
               pre_ui_counter : int }

type uI = { ui_pre    : preUI;
            ui_digest : string }

type bare_Request = { bare_request_c : int;
                      bare_request_t : int;
                      bare_request_m : int }

type token = string
type tokens = token list

type request = { request_b : bare_Request;
                 request_a : tokens }

type bare_Reply = { bare_reply_r      : request;
                    bare_reply_result : int;
                    bare_reply_rep    : int;
                    bare_reply_view   : view }

type bare_Prepare = { bare_prepare_v : view;
                      bare_prepare_m : request }

type bare_Commit = { bare_commit_v  : view;
                     bare_commit_m  : request;
                     bare_commit_ui : uI }

type minBFT_Bare_Msg =
  | MinBFT_msg_bare_request of bare_Request
  | MinBFT_msg_bare_reply   of bare_Reply
  | MinBFT_msg_bare_prepare of bare_Prepare * preUI
  | MinBFT_msg_bare_commit  of bare_Commit  * preUI

type hashData = { hd_view : view; hd_msg : request; hd_pre : preUI }


let client2string    c  = "CLIENT("    ^ string_of_int c  ^ ")"
let timestamp2string ts = "TIMESTAMP(" ^ string_of_int ts ^ ")"
let view2string      v  = "VIEW("      ^ string_of_int v  ^ ")"
let counter2string   c  = "COUNTER("   ^ string_of_int c  ^ ")"
let cid2string       c  = "CID("       ^ string_of_int c  ^ ")"
let replica2string   r  = "REP("       ^ string_of_int r  ^ ")"
let result2string    r  = "RES("       ^ string_of_int r  ^ ")"
let command2string   c  = "COM("       ^ string_of_int c  ^ ")"
let token2string     t  = "TOKEN("     ^ t ^ ")"
let digest2string    d  = "DIGEST("    ^ d ^ ")"

let bare_request2string (r : bare_Request) =
  let { bare_request_c = c;
        bare_request_t = ts;
        bare_request_m = m } = r in
  "BARE-REQUEST(" ^ client2string c ^ "," ^ timestamp2string ts ^ "," ^ command2string m ^ ")"

let rec tokens2string_aux a =
  match a with
  | [] -> ""
  | t :: ts -> token2string t ^ "," ^ tokens2string_aux ts

let tokens2string a = "TOKENS[" ^ tokens2string_aux a ^ "]"

let request2string r =
  let { request_b = br; request_a = a } = r in
  "REQUEST(" ^ bare_request2string br ^ "," ^ tokens2string a ^ ")"

let bare_prepare2string p =
  let { bare_prepare_v = v; bare_prepare_m = m } = p in
  "BARE-PREPARE(" ^ view2string v ^ "," ^ request2string m ^ ")"

let pre_ui2string pui =
  let { pre_ui_rid = rid; pre_ui_cid = cid; pre_ui_counter = counter } = pui in
  "PRE-UI(" ^ replica2string rid ^ "," ^ cid2string cid ^ "," ^ counter2string counter ^ ")"

let ui2string ui =
  let { ui_pre = pui; ui_digest = d } = ui in
  "UI(" ^ pre_ui2string pui ^ "," ^ digest2string d ^ ")"

let bare_commit2string c =
  let { bare_commit_v = v; bare_commit_m = m; bare_commit_ui = ui } = c in
  "BARE-COMMIT(" ^ view2string v ^ "," ^ request2string m ^ "," ^ ui2string ui ^ ")"

let bare_reply2string br =
  let { bare_reply_r = req; bare_reply_result = res; bare_reply_rep = i; bare_reply_view = v } = br in
  "BARE-REPLY(" ^ request2string req ^ "," ^ result2string res ^ "," ^ replica2string i ^ "," ^ view2string v ^ ")"

let bare_msg2string = function
| MinBFT_msg_bare_request r -> "BARE-MSG-REQUEST(" ^ bare_request2string r ^ ")"
| MinBFT_msg_bare_reply   r -> "BARE-MSG-REPLY("   ^ bare_reply2string   r ^ ")"
| MinBFT_msg_bare_prepare (p, pui) -> "BARE-MSG_PREPARE(" ^ bare_prepare2string p ^ "," ^ pre_ui2string pui ^ ")"
| MinBFT_msg_bare_commit  (c, pui) -> "BARE-MSG_COMMIT("  ^ bare_commit2string  c ^ "," ^ pre_ui2string pui ^ ")"

let hashData2string hd =
  let { hd_view = v; hd_msg = r; hd_pre = pui } = hd in
  "HASH-DATA(" ^ view2string v ^ "," ^ request2string r ^ "," ^ pre_ui2string pui ^ ")"

let hashData2rep (hd : hashData) : int = hd.hd_pre.pre_ui_rid
