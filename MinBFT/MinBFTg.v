Require Export DTimeQ.
Require Export MinBFTheader.
Require Export ComponentSM.
Require Export ComponentSM2.
Require Export toString.
Require Export List.
Require Export USIG.
Require Export TrIncUSIG.


Section MinBFTg.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : DTimeContext }.

  Context { minbft_context : MinBFT_context }.
  Context { m_initial_keys : MinBFT_initial_keys }.
  Context { u_initial_keys : USIG_initial_keys }.

  Context { usig_hash : USIG_hash }.


  (* ===============================================================
     Messages
     =============================================================== *)

  Record Prepare :=
    prepare
      {
        prepare_b  : Bare_Prepare;
        prepare_ui : UI;
      }.

  Record Bare_Commit :=
    bare_commit
      {
        bare_commit_v  : View;
        bare_commit_m  : Request;
        bare_commit_ui : UI;
      }.

  Record Commit :=
    commit
      {
        commit_b  : Bare_Commit;
        commit_uj : UI;
      }.



  (* ============ extract view ==============*)

  Definition prepare2view (p : Prepare) : View :=
    bare_prepare_v (prepare_b p).

  Definition commit2view (c : Commit) : View :=
    bare_commit_v (commit_b c).

  (* ============ extract timestamp ==============*)

    Definition bare_request2timestamp (r : Bare_Request) : Timestamp  :=
    match r with
    | bare_request m t c => t
    end.

  Definition request2timestamp (r : Request) : Timestamp :=
    match r with
    | request br a => bare_request2timestamp br
    end.

  (* ============ extract sender ==============*)

  Definition bare_request2sender (r : Bare_Request) :  Client :=
    match r with
    | bare_request c t m  => c
    end.

  Definition request2sender (r : Request) : Client :=
    match r with
    | request b _ => bare_request2sender b
    end.

  Definition prepare2sender (p : Prepare) : Rep :=
    pre_ui_rid (prepare_ui p).

  Definition bare_commit2sender_i (c : Bare_Commit) : Rep :=
    pre_ui_rid (bare_commit_ui c).

  Definition commit2sender_i (c : Commit) : Rep :=
    pre_ui_rid (bare_commit_ui (commit_b c)).

  Definition commit2sender_j (c : Commit) : Rep :=
    pre_ui_rid (commit_uj c).

  Definition commit2sender_i_j (c : Commit) : Rep * Rep :=
    (commit2sender_i c, commit2sender_j c).

  Definition bare_reply2sender (r : Bare_Reply) : Rep :=
    bare_reply_rep r.

  Definition reply2sender (r : Reply) : Rep :=
    bare_reply2sender (reply_b r).

  (* =========== extract receiver =========== *)

  Definition bare_reply2request (r : Bare_Reply) : Request :=
    bare_reply_r r.

  Definition bare_reply2client (r : Bare_Reply) : Client :=
    request2sender (bare_reply2request r).

  Definition reply2client (r : Reply) : Client :=
    bare_reply2client (reply_b r).

  (* ============  extract sequence number ============== *)

  Definition prepare2ui (p : Prepare) : UI :=
    prepare_ui p.

  Definition commit2ui_i (c : Commit) : UI :=
    bare_commit_ui (commit_b c).

  Definition commit2ui_j (c : Commit) : UI :=
    commit_uj c.

  Definition commit2ui_i_j (c : Commit) : UI * UI :=
    (commit2ui_i c, commit2ui_j c).

  Definition commit2counter_i (c : Commit) : nat :=
    pre_ui_counter (commit2ui_i c).

  Definition commit2counter_j (c : Commit) : nat :=
    pre_ui_counter (commit2ui_j c).


  (* ============ extract message ==============*)

  Definition bare_request2msg (r : Bare_Request) : MinBFT_data_message :=
    match r with
    | bare_request c t m => m
    end.

  Definition request2msg (r : Request) : MinBFT_data_message :=
    match r with
    | request br a => bare_request2msg br
    end.

  Definition prepare2request (p : Prepare) : Request :=
    bare_prepare_m (prepare_b p).

  Definition prepare2bare_request (p : Prepare) : Bare_Request :=
    request_b (prepare2request p).

  Definition prepare2msg (p : Prepare) : MinBFT_data_message :=
    match prepare2bare_request p with
    | bare_request c t m => m
    end.

  Definition commit2request (c : Commit) : Request :=
    bare_commit_m (commit_b c).

  Definition commit2bare_request (c : Commit) : Bare_Request :=
    request_b (commit2request c).

  Definition commit2msg (c : Commit) : MinBFT_data_message :=
    match commit2bare_request c with
    | bare_request c t m => m
    end.

  Definition commit2client (c : Commit) : Client :=
    request2sender (commit2request c).

  (* ===============================================================
     Bare message type
     =============================================================== *)

  Inductive MinBFT_Bare_Msg : Set :=
  | MinBFT_msg_bare_request (r : Bare_Request) (* (a : Token) *)
  | MinBFT_msg_bare_reply   (r : Bare_Reply)   (* (a : Token) *)
  | MinBFT_msg_bare_prepare (p : Bare_Prepare) (pui : preUI)
  | MinBFT_msg_bare_commit  (c : Bare_Commit)  (pui : preUI).

  (* =========== Msg type =========== *)

  Inductive MinBFT_msg :=
  | MinBFT_request (m : Request)
  | MinBFT_reply   (m : Reply)
  | MinBFT_prepare (p : Prepare)
  | MinBFT_commit  (c : Commit)
  | MinBFT_accept  (a : Accept)
  | MinBFT_debug   (s : String.string).

  Global Instance MinBFT_I_Msg : Msg := MkMsg MinBFT_msg.

  Definition MinBFTmsg2status (m : MinBFT_msg) : msg_status :=
    match m with
    | MinBFT_request _ => MSG_STATUS_EXTERNAL
    | MinBFT_reply   _ => MSG_STATUS_PROTOCOL
    | MinBFT_prepare _ => MSG_STATUS_PROTOCOL
    | MinBFT_commit  _ => MSG_STATUS_PROTOCOL
    | MinBFT_accept  _ => MSG_STATUS_INTERNAL
    | MinBFT_debug   _ => MSG_STATUS_INTERNAL
    end.

  Global Instance MinBFT_I_MsgStatus : MsgStatus := MkMsgStatus MinBFTmsg2status.


  (* ===============================================================
     Crypto
     =============================================================== *)

  Global Instance MinBFT_I_Data : Data := MkData MinBFT_Bare_Msg.

  Class MinBFT_auth :=
    MkMinBFT_auth
      {
        MinBFT_create : data -> sending_keys -> list MinBFT_digest;
        MinBFT_verify : data -> name -> receiving_key -> MinBFT_digest -> bool
      }.

  Context { minbft_auth : MinBFT_auth }.

  Global Instance MinBFT_I_AuthFun : AuthFun :=
    MkAuthFun
      MinBFT_create
      MinBFT_verify.


  (* ===============================================================
        Authenticated Messages
        =============================================================== *)

  Definition option_client2name (cop : option Client) (n : name) : name :=
    match cop with
    | Some c => MinBFT_client c
    | None => n
    end.

  (* we are here extracting the sender of the message *)
  Definition MinBFT_msg_auth (m : msg) : option  name :=
    match m with
    | MinBFT_request r => Some (MinBFT_client (request2sender r))
    | MinBFT_reply   r => Some (MinBFT_replica (reply2sender r))
    | MinBFT_prepare p => Some (MinBFT_replica (prepare2sender p))
    | MinBFT_commit  c => Some (MinBFT_replica (commit2sender_j c)) (* because j sent commit message *)
    | MinBFT_accept  a => None
    | MinBFT_debug   s => None
    end.

  (* FIX : Why do we need n here? *)
  Definition MinBFT_data_auth (n : name) (d : data) : option name :=
    match d with
    | MinBFT_msg_bare_request r     => Some (MinBFT_client (bare_request2sender r))
    | MinBFT_msg_bare_reply   r     => Some (MinBFT_replica (bare_reply2sender r))
    | MinBFT_msg_bare_prepare p pui => Some (MinBFT_replica (pre_ui_rid pui))
    | MinBFT_msg_bare_commit  c pui => Some (MinBFT_replica (pre_ui_rid pui))
    end.

  Global Instance MinBFT_I_DataAuth : DataAuth := MkDataAuth MinBFT_data_auth.

  Definition reply2auth_data (r : Reply) : AuthenticatedData :=
    MkAuthData (MinBFT_msg_bare_reply (reply_b r)) (reply_a r).

  Definition prepare2auth_data (p : Prepare) : AuthenticatedData :=
    match p with
    | prepare b ui => MkAuthData (MinBFT_msg_bare_prepare b ui) [ui_digest ui]
    end.

  Definition commit2auth_data (c : Commit) : AuthenticatedData :=
    match c with
    | commit b ui => MkAuthData (MinBFT_msg_bare_commit b ui) [ui_digest ui]
    end.

  Definition MinBFT_get_contained_auth_data (m : msg) : list AuthenticatedData :=
    match m with
    | MinBFT_request m => []
    | MinBFT_reply   r => [reply2auth_data r]
    | MinBFT_prepare p => [prepare2auth_data p]
    | MinBFT_commit  c => [commit2auth_data c]
    | MinBFT_accept  a => []
    | MinBFT_debug   s => []
    end.

  Global Instance MinBFT_I_ContainedAuthData : ContainedAuthData :=
    MkContainedAuthData MinBFT_get_contained_auth_data.


  (* ===============================================================
     Decidability for different types of messages
     =============================================================== *)

  Definition UI_dec : Deq UI.
  Proof.
    introv.
    destruct x as [p1 d1], y as [p2 d2], p1 as [i1 j1 c1], p2 as [i2 j2 c2].
    destruct (rep_deq i1 i2); subst; prove_dec.
    destruct (deq_nat j1 j2); subst; prove_dec.
    destruct (deq_nat c1 c2); subst; prove_dec.
    destruct (MinBFT_digestdeq d1 d2); subst; prove_dec.
  Defined.

  Definition request2tokens (r : Request) : Tokens :=
    match r with
    | request b a => a
    end.

  Definition request_deq (m :  Request) (m' : Request) : bool :=
    if MinBFT_data_message_deq (request2msg m) (request2msg m') then
      if client_deq (request2sender m) (request2sender m') then
        if Tokens_dec (request2tokens m) (request2tokens m') then true
        else false
      else false
    else false.

  Definition prepare_deq (m: Prepare) (m' : Prepare) : bool :=
    if ViewDeq (prepare2view m) (prepare2view m') then
      if request_deq (prepare2request m) (prepare2request m') then
          if UI_dec (prepare_ui m) (prepare_ui m') then true
          else false
      else false
    else false.


    Definition commit_deq (m: Commit) (m' : Commit) : bool :=
      if ViewDeq (commit2view m) (commit2view m') then
        if request_deq (commit2request m) (commit2request m') then
          if UI_dec (commit2ui_i m) (commit2ui_i m') then
            if UI_dec (commit_uj m) (commit_uj m') then true
            else false
          else false
        else false
      else false.

    (****************************************************************************)

  Definition other_replicas (r : Rep) : list Rep := remove_elt rep_deq r reps.

  Definition other_names (r : Rep) : list name := map MinBFT_replica (other_replicas r).

  Definition broadcast2others (slf : Rep) F : DirectedMsg :=
    F (other_names slf).

  Definition broadcast2all F : DirectedMsgs := map F (map MinBFT_replica reps).

  (* ===============================================================
     Sending functions
     =============================================================== *)

  Definition send_prepare (p : Prepare) (n : list name) : DirectedMsg :=
    MkDMsg (MinBFT_prepare p) n ('0).

  Definition send_commit (c : Commit) (n : list name) : DirectedMsg :=
    MkDMsg (MinBFT_commit c) n ('0).

(* do we really care about this one?
  Definition send_request (r : Bare_m) (n : list name) : DirectedMsg :=
    MkDMsg (MinBFT_bare_m r) n 0. *)

  Definition send_reply (r : Reply) : DirectedMsg :=
    MkDMsg (MinBFT_reply r) [MinBFT_client (reply2client r)] ('0).

  Definition send_accept (a : Accept) (n : list name) : DirectedMsg :=
    MkDMsg (MinBFT_accept a) n ('0).

  Definition send_debug (s : String.string) (n : name) : DirectedMsg :=
    MkDMsg (MinBFT_debug s) [n] ('0).

  Definition send_debugs (s : String.string) (n : name) : DirectedMsgs :=
    [send_debug s n].

  (* ===============================================================
     Creation of authenticated messages
     =============================================================== *)

  Definition mk_auth_prepare
             (v  : View)
             (m  : Request)
             (ui : UI) : Prepare :=
    let bpp  := bare_prepare v m in
    (* we create an authenticated prepare message *)
    prepare bpp ui.

    Definition mk_auth_commit
             (v    : View)
             (m    : Request)
             (ui_i : UI)
             (ui_j : UI) : Commit :=
    let bcomm  := bare_commit v m ui_i in
    (* we create an authenticated commit message *)
    commit bcomm  ui_j.

    Definition mk_auth_reply
             (req  : Request)
             (res  : nat)
             (i    : Rep)
             (v    : View)
             (keys : local_key_map) : Reply :=
    let brep := bare_reply req res i v in
    (* we authenticate the unsigned reply message *)
    let toks := authenticate (MinBFT_msg_bare_reply brep) keys in
    (* we create an authenticated reply message *)
    reply brep toks.

  (* ===============================================================
     Log
     =============================================================== *)

    (* =========== Request Data =========== *)

    (* This is essentially a prepare minus the signature *)
  Inductive RequestData :=
  | request_data (v : View) (r : Request) (ui : UI).

  Definition request_data2view (rd : RequestData) : View :=
    match rd with
    | request_data v _ _ => v
    end.

  Definition request_data2ui (rd : RequestData) : UI :=
    match rd with
    | request_data _ _ ui => ui
    end.

  Definition request_data2rep (rd : RequestData) : Rep :=
    ui2rep (request_data2ui rd).

  Definition request_data2data_message (rd : RequestData) : Bare_Request :=
    match rd with
    | request_data _ m _ => request_b m
    end.

  Definition request_data2request (rd : RequestData) : Request :=
    match rd with
    | request_data _ m _ => m
    end.

  Lemma timestamp_deq : Deq Timestamp.
  Proof.
    repeat introv.
    destruct x as [n1], y as [n2].
    unfold deceq.
    destruct (deq_nat n1 n2); subst; tcsp; [].
    right; intro xx; inversion xx; subst; tcsp.
  Defined.

  Lemma view_deq : Deq View.
  Proof.
    repeat introv.
    destruct x as [n1], y as [n2].
    unfold deceq.
    destruct (deq_nat n1 n2); subst; tcsp; [].
    right; intro xx; inversion xx; subst; tcsp.
  Defined.

  Lemma Bare_Request_Deq : Deq Bare_Request.
  Proof.
    repeat introv.
    destruct x as [c1 t1 m1], y as [c2 t2 m2].
    destruct (client_deq c1 c2); subst; prove_dec.
    destruct (MinBFT_data_message_deq m1 m2); subst; prove_dec.
    destruct (timestamp_deq t1 t2); subst; prove_dec.
  Defined.

  Lemma Request_Deq : Deq Request.
  Proof.
    repeat introv.
    destruct x as [r1 a1], y as [r2 a2].
    destruct (Bare_Request_Deq r1 r2); subst; prove_dec.
    destruct (Tokens_dec a1 a2); subst; prove_dec.
  Defined.

  Lemma RequestData_Deq : Deq RequestData.
  Proof.
    repeat introv.
    destruct x as [v1 m1 ui1], y as [v2 m2 ui2].
    destruct (ViewDeq v1 v2); subst; prove_dec.
    destruct (Request_Deq m1 m2); subst; prove_dec.

    destruct ui1 as [p1 d1], ui2 as [p2 d2].
    destruct p1 as [i1 j1 c1], p2 as [i2 j2 c2].

    destruct (rep_deq i1 i2); subst; prove_dec.
    destruct (deq_nat j1 j2); subst; prove_dec.
    destruct (deq_nat c1 c2); subst; prove_dec.
    destruct (MinBFT_digestdeq d1 d2); subst; prove_dec.
  Defined.

  Definition eq_request_data (rd1 rd2 : RequestData) : bool :=
    if RequestData_Deq rd1 rd2 then true else false.

  Definition prepare2request_data (p : Prepare) : RequestData :=
    match p with
    | prepare (bare_prepare v m) ui => request_data v m ui
    end.

  Definition commit2request_data_i (c : Commit) : RequestData :=
    match c with
    | commit (bare_commit v m ui) _ => request_data v m ui
    end.

  Definition commit2request_data_j (c : Commit) : RequestData :=
    match c with
    | commit (bare_commit v m _) uj => request_data v m uj
    end.

  (* =========== MinBFT log =========== *)

  Record LOG_state_entry :=
    Build_LOGStateEntry
      {
        log_entry_request_data     : RequestData;
        log_entry_commits          : UIs;
      }.

  Definition LOG_state := list LOG_state_entry.

  Definition LOG_initial : LOG_state := [].

  Definition is_committed_entry (entry : LOG_state_entry) : bool :=
    F <=? length (log_entry_commits entry).

  Fixpoint find_entry (rd : RequestData) (l : LOG_state) : option  LOG_state_entry :=
    match l with
    | [] =>  None
    | entry :: entries =>
      if RequestData_Deq rd (log_entry_request_data entry)
      then Some entry
      else find_entry rd entries
    end.

  (* is this enough; or we have to keep on searching in order to find all matching RequestData? *)
  Definition is_committed (c : Commit) (l : LOG_state) : bool :=
    match find_entry (commit2request_data_i c) l with
    | None => false
    | Some e => is_committed_entry e
    end.

  Definition MkNewLogEntryFromPrepare (p : Prepare) : LOG_state_entry :=
    Build_LOGStateEntry
      (prepare2request_data p)
      [].

  (* this is the case when replica received commit, without previously receiving prepare *)
  Definition MkNewLogEntryFromCommit (c : Commit) : LOG_state_entry :=
    Build_LOGStateEntry
      (commit2request_data_i c)
      [commit_uj c].

  Definition add_commit2commits (c : UI) (uis : UIs) : UIs :=
    if in_dec rep_deq (ui2rep c) (map ui2rep uis) then uis
    else c :: uis.

  Definition add_commit2entry (ui : UI) (entry : LOG_state_entry) : LOG_state_entry :=
    match entry with
    | Build_LOGStateEntry rd comms =>
      if rep_deq (ui2rep ui) (request_data2rep rd)
      then entry
      else Build_LOGStateEntry rd (add_commit2commits ui comms)
    end.

  Fixpoint prepare_already_in_log (p : Prepare) (l : LOG_state) : bool :=
    match l with
    | [] => false
    | entry :: entries =>
      if RequestData_Deq (prepare2request_data p) (log_entry_request_data entry)
      then true
      else prepare_already_in_log p entries
    end.

  Definition prepare2counter (p : Prepare) : nat :=
    ui2counter (prepare2ui p).


  (* *********************************** *)
  (*
    Those are only ever used when we want to fairly evaluate the code, and therefore GC.
    They're not used here.  We only bring [log_new_prepare_gc] in during extraction (and
    not by default!!).
   *)
  Fixpoint log_new_prepare_aux (p : Prepare) (l : LOG_state) : LOG_state :=
    match l with
    | [] => [MkNewLogEntryFromPrepare p]
    | entry :: entries =>
      if RequestData_Deq (log_entry_request_data entry) (prepare2request_data p)
      then (* the entry matches the prepare, so we don't do anything *) l
      else entry :: log_new_prepare_aux p entries
    end.

  (* This is what we used in PBFT*)
  Definition GC_period := 50.

  (* We keep the last 20 requests we handled *)
  Definition GC_keep := 20.

  Definition log_new_prepare_gc1 (p : Prepare) (l : LOG_state) : LOG_state :=
    if deq_nat (Nat.modulo (prepare2counter p) GC_period) 0
    then log_new_prepare_aux p []
    else log_new_prepare_aux p l.

  Definition log_new_prepare_gc2 (p : Prepare) (l : LOG_state) : LOG_state :=
    if deq_nat (Nat.modulo (prepare2counter p) GC_period) 0
    then log_new_prepare_aux p (skipn (length l - GC_keep) l)
    else log_new_prepare_aux p l.
  (* *********************************** *)


  Fixpoint log_new_prepare (p : Prepare) (l : LOG_state) : LOG_state :=
    match l with
    | [] => [MkNewLogEntryFromPrepare p]
    | entry :: entries =>
      if RequestData_Deq (log_entry_request_data entry) (prepare2request_data p)
      then (* the entry matches the prepare, so we don't do anything *) l
      else entry :: log_new_prepare p entries
    end.

  (* commit is added even in case when prepare doesn't exist; see pg 58. *)
  Fixpoint log_new_commit (c : Commit) (l : LOG_state) : LOG_state :=
    match l with
    | [] => [MkNewLogEntryFromCommit c]
    | entry :: entries =>
      (* log already contains entry with the same message m *)
      if RequestData_Deq (commit2request_data_i c) (log_entry_request_data entry)
      then add_commit2entry (commit2ui_j c) entry :: entries
      else entry :: log_new_commit c entries
    end.

  Inductive LOG_input_interface :=
  | log_new_prepare_log_in    (p : Prepare)
  | log_new_commit_log_in     (c : Commit)
  | prepare_already_in_log_in (p : Prepare)
  | is_committed_in           (c : Commit).

  Inductive LOG_output_interface :=
  | log_out (b : bool).

  Definition CIOlog : ComponentIO :=
    MkComponentIO LOG_input_interface LOG_output_interface (log_out true).



  (* ===============================================================
     State of some replica
     =============================================================== *)

  Definition latest_executed_request := list (Client * Timestamp).

  Definition initial_latest_executed_request : latest_executed_request := [].

  Fixpoint update_latest_executed_request (r : Request) (l : latest_executed_request) : latest_executed_request :=
    match l with
    | [] => [(request2sender r, request2timestamp r)]
    | (c,t) :: l =>
      if client_deq c (request2sender r)
      then
        if t <? request2timestamp r
        then (c, request2timestamp r) :: l
        else (c,t) :: l
      else (c,t) :: update_latest_executed_request r l
    end.


  Definition latest_executed_counter := nat.

  Definition initial_latest_executed_counter : latest_executed_counter := 0.


  Definition highest_received_counter_value := list (Rep * nat).

  Definition initial_highest_received_counter_value : highest_received_counter_value := [].

  Fixpoint update_highest_received_counter_value (ui : UI) (l : highest_received_counter_value) : highest_received_counter_value :=
    match l with
    | [] => [(ui2rep ui, ui2counter ui)]
    | (r,c) :: l =>
      if rep_deq r (ui2rep ui)
      then
        if c <? ui2counter ui
        then (r, ui2counter ui) :: l
        else (r,c) :: l
      else (r,c) :: update_highest_received_counter_value ui l
    end.


  Record MAIN_state :=
    Build_State
      {

        (* The keys that we're holding to communicate with the clients *)
        local_keys        : local_key_map;

        (* Current view *)
        current_view      : View;   (* currently not important *)

        (* Current counter *)
        current_counter   : nat;    (* a copy of the USIG/TrInc counter *)

        (* state of the local state machine *)
        sm_state          : MinBFT_sm_state;

        (* last executed counter *)
        cexec             : latest_executed_counter;

        (* the sequence/timestamp of the last executed request for each client *)
        vreq              : latest_executed_request;

        (* the highest sequence number received from each server *)
        vacc              : highest_received_counter_value;

        (* sequence/timestamp currently being processed *)
        current_seq       : option Timestamp;

      }.

  Definition initial_counter : nat := 0.

  Definition initial_state (r : Rep) : MAIN_state :=
    Build_State
      (minbft_initial_keys (MinBFT_replica r))
      initial_view
      initial_counter
      MinBFT_sm_initial_state
      initial_latest_executed_counter
      initial_latest_executed_request
      initial_highest_received_counter_value
      None.

  Definition replace_sm_state
             (s : MAIN_state)
             (x : MinBFT_sm_state) : MAIN_state :=
    Build_State
      (local_keys      s)
      (current_view    s)
      (current_counter s)
      x
      (cexec           s)
      (vreq            s)
      (vacc            s)
      (current_seq     s).


  (* ===============================================================
     Trusted info
     =============================================================== *)

  Definition preUSIGname : PreCompName := MkPreCompName "USIG" 0.

  Definition USIGname : CompName := MkCN "USIG" 0 true.

  Class TrustedInfo :=
    MkTrustedInfo
      {
        trusted_state : Type
      }.

  Context { ti : TrustedInfo }.


  (* ===============================================================
     Parameters
     =============================================================== *)

  Global Instance MinBFT_I_baseFunIO : baseFunIO :=
    MkBaseFunIO (fun (nm : CompName) =>
                   if CompNameKindDeq (comp_name_kind nm) "USIG" then CIOusig
                   else if CompNameKindDeq (comp_name_kind nm) "TRINC" then CIOusig
                        else if CompNameKindDeq (comp_name_kind nm) "LOG" then CIOlog
                             else CIOdef).

  Global Instance MinBFT_I_baseStateFun : baseStateFun :=
    MkBaseStateFun (fun (nm : CompName) =>
                      if CompNameKindDeq (comp_name_kind nm) "USIG" then USIG_state
                      else if CompNameKindDeq (comp_name_kind nm) "TRINC" then TRINC_state
                           else if CompNameKindDeq (comp_name_kind nm) "LOG" then LOG_state
                                else if CompNameKindDeq (comp_name_kind nm) msg_comp_name_kind
                                     then MAIN_state
                                     else unit).

  Global Instance MinBFT_I_IOTrustedFun : IOTrustedFun :=
    MkIOTrustedFun
      (fun _ =>
         MkIOTrusted
           USIG_input_interface
           USIG_output_interface
           verify_ui_out_def).

  (* This should be either USIG_state or TRINC_state *)
  Global Instance MinBFT_I_trustedStateFun : trustedStateFun :=
    MkTrustedStateFun (fun _ => trusted_state).


  (* ===============================================================
     Log component
     =============================================================== *)

  Definition LOGname : CompName := MkCN "LOG" 0 false.

  Definition LOG_update : M_Update 0 LOGname _ :=
    fun (l : LOG_state) (m : LOG_input_interface) =>
      interp_s_proc
        (match m with
         | log_new_prepare_log_in p =>
           let l' := log_new_prepare p l in
           [R] (l', log_out true)
         | log_new_commit_log_in c =>
           let l' := log_new_commit c l in
           [R] (l', log_out true)
         | prepare_already_in_log_in p =>
           let b := prepare_already_in_log p l in
           [R] (l, log_out b)
         | is_committed_in c =>
           let b := is_committed c l in
           [R] (l, log_out b)
         end).

  Definition LOG_comp : M_StateMachine 1 LOGname :=
    build_m_sm LOG_update LOG_initial.

  (******************************************************************************)




  Definition on_create_ui_out {A} (f : UI -> A) (d : unit -> A) (out : USIG_output_interface) : A :=
    match out with
    | create_ui_out (Some ui) => f ui
    | _ => d tt
    end.

  Definition call_create_ui {A} (m : View * Request * nat * nat) (d : unit -> Proc A) (f : UI -> Proc A) :=
    (USIGname [C] (create_ui_in m))
      [>>=] on_create_ui_out f d.

  Notation "a >>cui>>=( d ) f" := (call_create_ui a d f) (at level 80, right associativity).

  Definition if_true_verify_ui_out {A} (f d : unit -> A) (out : USIG_output_interface) : A :=
    match out with
    | verify_ui_out b => if b then f tt else d tt
    | _ => d tt
    end.

  Definition call_verify_ui {A} (mui : View * Request * UI) (d f : unit -> Proc A) :=
    (USIGname [C] (verify_ui_in mui))
      [>>=] if_true_verify_ui_out f d.

  Notation " a >>vui>>=( d ) f" := (call_verify_ui a d f) (at level 80, right associativity).

  Definition on_log_out {A} (d f : unit -> A) (out : LOG_output_interface) : A :=
    match out with
    | log_out true  => d tt
    | log_out false => f tt
    end.

  Definition call_prepare_already_in_log {A} (p : Prepare) (d f : unit -> Proc A) : Proc A :=
    (LOGname [C] (prepare_already_in_log_in p))
      [>>=] on_log_out d f.

  Notation " a >>pil>>=( d ) f" := (call_prepare_already_in_log a d f) (at level 80, right associativity).


  Definition on_log_out_bool {A} (f : bool -> A) (out : LOG_output_interface) : A :=
    match out with
    | log_out b  => f b
    end.

  Definition call_prepare_already_in_log_bool {A} (p : Prepare) (f : bool -> Proc A) : Proc A :=
    (LOGname [C] (prepare_already_in_log_in p))
      [>>=] on_log_out_bool f.

  Notation " a >>bpil>>= f" := (call_prepare_already_in_log_bool a f) (at level 80, right associativity).


  Definition call_is_committed {A} (c : Commit) (d f : unit -> Proc A) : Proc A :=
    (LOGname [C] (is_committed_in c))
      [>>=] on_log_out f d.

  Notation " a >>ic>>=( d ) f" := (call_is_committed a d f) (at level 80, right associativity).


  Definition call_log_prepare {A} (p : Prepare) (f : unit -> Proc A) : Proc A :=
    (LOGname [C] (log_new_prepare_log_in p))
      [>>=] fun _ => f tt.

  Notation " a >>lp>>= f" := (call_log_prepare a f) (at level 80, right associativity).

  Definition call_log_commit {A} (c : Commit) (f : unit -> Proc A) : Proc A :=
    (LOGname [C] (log_new_commit_log_in c))
      [>>=] fun _ => f tt.

  Notation " a >>lc>>= f" := (call_log_commit a f) (at level 80, right associativity).

  Definition on_data_message {A} (m : MinBFT_msg) (d : unit -> Proc A) (f : Request -> Proc A) : Proc A :=
    match m with
    | MinBFT_request m => f m
    | _ => d tt
    end.

  Notation "a >>odm>>=( d ) f" := (on_data_message a d f) (at level 80, right associativity).

  Definition on_prepare {A} (m : MinBFT_msg) (d : unit -> Proc A) (f : Prepare -> Proc A) : Proc A :=
    match m with
    | MinBFT_prepare p => f p
    | _ => d tt
    end.

  Notation "a >>op>>=( d ) f" := (on_prepare a d f) (at level 80, right associativity).

  Definition on_commit {A} (m : MinBFT_msg) (d : unit -> Proc A) (f : Commit -> Proc A) : Proc A :=
    match m with
    | MinBFT_commit c => f c
    | _ => d tt
    end.

  Notation "a >>oc>>=( d ) f" := (on_commit a d f) (at level 80, right associativity).

  Definition on_accept {A} (m : MinBFT_msg) (d : unit -> Proc A) (f : Accept -> Proc A) : Proc A :=
    match m with
    | MinBFT_accept a => f a
    | _ => d tt
    end.

  Notation "a >>oacc>>=( d ) f" := (on_accept a d f) (at level 80, right associativity).


  Definition MAINname := msg_comp_name 0.

  Eval compute in (cio_I (fio MAINname)).

  Definition processing (s : MAIN_state) : bool :=
    match current_seq s with
    | Some _ => true
    | None => false
    end.

  Definition maybe_processing (t : Timestamp) (s : MAIN_state) : bool :=
    match current_seq s with
    | Some seq => if timestamp_deq t seq then true else false
    | None => true
    end.

  Fixpoint new_request (r : Request) (l : latest_executed_request) : bool :=
    match l with
    | [] => true
    | (c,t) :: l =>
      if client_deq c (request2sender r)
      then t <? (request2timestamp r)
      else new_request r l
    end.

  Definition verify_request (slf : Rep) (km : local_key_map) (r : Request) : bool :=
    verify_authenticated_data
      (MinBFT_replica slf)
      (MkAuthData (MinBFT_msg_bare_request (request_b r)) (request_a r))
      km.


  Definition valid_request
             (slf : Rep)
             (km  : local_key_map)
             (r   : Request)
             (s   : MAIN_state) : bool :=
    (negb (processing s))
      && new_request r (vreq s)
      && verify_request slf km r.

  Definition invalid_request
             (slf : Rep)
             (km  : local_key_map)
             (r   : Request)
             (s   : MAIN_state) : bool :=
    negb (valid_request slf km r s).


  Definition prepare2timestamp (p : Prepare) : Timestamp :=
    request2timestamp (prepare2request p).

  Definition commit2timestamp (c : Commit) : Timestamp :=
    request2timestamp (commit2request c).


  Fixpoint highest_received_counter (r : Rep) (l : highest_received_counter_value) : option nat :=
    match l with
    | [] => None
    | (r',c') :: l =>
      if rep_deq r r'
      then Some c'
      else highest_received_counter r l
    end.

  Definition highest_received_counter_is (r : Rep) (c : nat) (l : highest_received_counter_value) : bool :=
    match highest_received_counter r l with
    | None => false
    | Some c' => if deq_nat c c' then true else false
    end.

  Definition received_prior_counter (ui : UI) (s : MAIN_state) : bool :=
    match ui2counter ui with
    | 0 => false (* 0 is not a valid counter *)
    | 1 => true (* 1st counter *)
    | S n => highest_received_counter_is (ui2rep ui) n (vacc s)
    end.

  Definition received_equal_counter (ui : UI) (s : MAIN_state) : bool :=
    match ui2counter ui with
    | 0 => false (* 0 is not a valid counter *)
    | n => highest_received_counter_is (ui2rep ui) n (vacc s)
    end.

  Definition received_prior_or_equal_counter (ui : UI) (pil : bool) (s : MAIN_state) : bool :=
    if pil then received_equal_counter ui s
    else received_prior_counter ui s.

  Definition executed_prior_counter (ui : UI) (s : MAIN_state) : bool :=
    match ui2counter ui with
    | 0 => false (* 0 is not a valid counter *)
    | S n => if deq_nat n (cexec s) then true else false
    end.

  (* we only use 1 counter with id 0 *)
  Definition cid0 : nat := 0.

  Definition is_counter0 (ui : UI) : bool :=
    if deq_nat (ui2cid ui) cid0 then true else false.

  Definition valid_prepare
             (slf : Rep)
             (km  : local_key_map)
             (v   : View)
             (p   : Prepare)
             (s   : MAIN_state) : bool :=
    (maybe_processing (prepare2timestamp p) s)
      && new_request (prepare2request p) (vreq s)
      && (if view_deq v (prepare2view p) then true else false)
      && is_primary v (prepare2sender p)
      && negb (is_primary v slf)
      && verify_request slf km (prepare2request p)
      && executed_prior_counter (prepare2ui p) s
      && received_prior_counter (prepare2ui p) s
      && is_counter0 (prepare2ui p).

  Definition invalid_prepare
             (slf : Rep)
             (km  : local_key_map)
             (v   : View)
             (p   : Prepare)
             (s   : MAIN_state) : bool :=
    negb (valid_prepare slf km v p s).


  (* [pil] stands for 'prepare in log' *)
  Definition primary_has_logged_its_prepare (slf : Rep) (v : View) (pil : bool) :=
    if is_primary v slf then pil else true.

  (* returning [0] means that the commit is valid *)
  Definition valid_commit
             (slf : Rep)
             (km  : local_key_map)
             (v   : View)
             (c   : Commit)
             (pil : bool)
             (s   : MAIN_state) : nat :=
    if (if view_deq v (commit2view c) then true else false) then
      if (if rep_deq slf (commit2sender_j c) then false else true) then
        if is_primary v (commit2sender_i c) then
          if negb (is_primary v (commit2sender_j c)) then
            if verify_request slf km (commit2request c) then
              if received_prior_counter (commit2ui_j c) s then
                if is_counter0 (commit2ui_i c) then
                  if is_counter0 (commit2ui_j c) then
                    if primary_has_logged_its_prepare slf v pil then 0
                    else 9
                  else 8
                else 7
              else 6
            else 5
          else 4
        else 3
      else 2
    else 1.

  Definition invalid_commit
             (slf : Rep)
             (km  : local_key_map)
             (v   : View)
             (c   : Commit)
             (pil : bool)
             (s   : MAIN_state) : bool :=
    if deq_nat (valid_commit slf km v c pil s) 0 then false else true.

  (* returning [0] means that the commit is valid *)
  Definition valid_commit2
             (slf : Rep)
             (km  : local_key_map)
             (v   : View)
             (c   : Commit)
             (pil : bool)
             (s   : MAIN_state) : nat :=
    if maybe_processing (commit2timestamp c) s then
      if new_request (commit2request c) (vreq s) then
        if executed_prior_counter (commit2ui_i c) s then
          if received_prior_or_equal_counter (commit2ui_i c) pil s then 0
          else 4
        else 3
      else 2
    else 1.

  Definition invalid_commit2
             (slf : Rep)
             (km  : local_key_map)
             (v   : View)
             (c   : Commit)
             (pil : bool)
             (s   : MAIN_state) : bool :=
    if deq_nat (valid_commit2 slf km v c pil s) 0 then false else true.

  Definition start_processing (r : Request) (s : MAIN_state) : MAIN_state :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (current_counter   s)
      (sm_state          s)
      (cexec             s)
      (vreq              s)
      (vacc              s)
      (Some (request2timestamp r)).

  Definition stop_processing (s : MAIN_state) : MAIN_state :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (current_counter   s)
      (sm_state          s)
      (cexec             s)
      (vreq              s)
      (vacc              s)
      None.

  Definition increment_current_counter (s : MAIN_state) : MAIN_state :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (S (current_counter s))
      (sm_state          s)
      (cexec             s)
      (vreq              s)
      (vacc              s)
      (current_seq       s).

  Definition update_latest_executed (r : Request) (s : MAIN_state) : MAIN_state :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (current_counter   s)
      (sm_state          s)
      (cexec             s)
      (update_latest_executed_request r (vreq s))
      (vacc              s)
      (current_seq       s).

  Definition update_highest_received_counter (ui : UI) (s : MAIN_state) : MAIN_state :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (current_counter   s)
      (sm_state          s)
      (cexec             s)
      (vreq              s)
      (update_highest_received_counter_value ui (vacc s))
      (current_seq       s).

  Definition increment_latest_executed_counter (s : MAIN_state) : MAIN_state :=
    Build_State
      (local_keys        s)
      (current_view      s)
      (current_counter   s)
      (sm_state          s)
      (S (cexec s))
      (vreq              s)
      (vacc              s)
      (current_seq       s).


  (* handle Request *)
  Definition handle_request (slf : Rep) : UProc MAINname _ :=
    (* in case M_Update 0 _ := is output type it complains that "The term "m" has type "cio_I" while it is expected to have type "data_message"." *)
    fun state m =>
      let keys  := local_keys state in
      let cview := current_view state in
      let cc    := current_counter state in

      if not_primary cview slf then [R] (state, send_debugs "not primary" slf) else

      m >>odm>>=(fun _ => [R] (state,send_debugs "not a request" slf)) fun m =>
      if invalid_request slf keys m state then [R] (state, send_debugs "invalid request" slf) else
      let state1 := start_processing m state in

      (* create_UI and update of the current state *)
      (cview,m,cid0,S cc) >>cui>>=(fun _ => [R](state1, send_debugs "could not create UI" slf)) fun ui =>

      (* create prepare *)
      let p := mk_auth_prepare cview m ui in

      (* we log this prepare *)
      (LOGname [C] (log_new_prepare_log_in p)) [>>=] fun _ =>

      (* increment local copy of counter *)
      let state2 := increment_current_counter state1 in
      (* we update our highest received counter (for ourself) *)
      let state3 := update_highest_received_counter ui state2 in

      (* we broadcast the prepare message to all replicas *)
      [R] (state3, [broadcast2others slf (send_prepare p)]).


  Definition handle_prepare (slf : Rep) : UProc MAINname _ :=
    (* this one compiles Update MAIN_state Prepare DirectedMsgs := *)
    fun state m =>
      let keys  := local_keys state in
      let cview := current_view state in
      let cc    := current_counter state in

      m >>op>>=(fun _ => [R] (state, send_debugs "not a prepare" slf)) fun p =>
      if invalid_prepare slf keys cview p state then [R] (state, send_debugs "invalid prepare" slf) else
      let state1 := start_processing (prepare2request p) state in
      let state2 := update_highest_received_counter (prepare2ui p) state1 in

      (* we check whether the ui is created by some usig *)
      let v  := prepare2view p in
      let r  := prepare2request p in
      let ui := prepare2ui p in
      (v,r,ui) >>vui>>=(fun _ => [R] (state2, send_debugs "could not verify UI" slf)) fun _ =>

      (* we check if we already received this prepare *)
      p >>pil>>=(fun _ => [R] (state2, send_debugs "already received this prepare" slf)) fun _ =>

      (* we log this prepare *)
      p >>lp>>= fun _ =>

      (* create_UI and update of the current state *)
      (v,r,cid0,S cc) >>cui>>=(fun _ => [R] (state2, send_debugs "could not create UI" slf)) fun ui =>

      (* increment local copy of counter *)
      let state3 := increment_current_counter state2 in

      (* store the commit we created in the log and update replica's state *)
      let comm := mk_auth_commit cview (prepare2request p) (prepare2ui p) ui in
      comm >>lc>>= fun _ =>

      let out := [broadcast2others slf (send_commit comm)] in

      (* is committed *)
      comm>>ic>>=(fun _ => [R] (state3, send_debugs "not committed" slf ++ out)) fun _ =>

      let acc := accept (commit2request comm) (commit2counter_i comm) in
      let state4 := update_latest_executed (commit2request comm) state3 in
      let state5 := increment_latest_executed_counter state4 in
      let state6 := stop_processing state5 in
      let (r,x)  := MinBFT_sm_update (commit2client comm) (sm_state state6) (commit2msg comm) in
      let state7 := replace_sm_state state6 x in
      [R] (state7, send_accept acc [MinBFT_replica slf] :: out).

(*
      (* we broadcast the commit message to all replicas *)
      [R] (state3, [broadcast2others slf (send_commit comm)]).
*)

  Definition commit2prepare (c: Commit) : Prepare :=
    mk_auth_prepare (commit2view c) (commit2request c) (commit2ui_i c).


  Definition mk_my_commit (c : Commit) (ui : UI) : Commit :=
    mk_auth_commit
      (commit2view c)
      (commit2request c)
      (commit2ui_i c)
      ui.

  Definition nat_n2string {m} (n : nat_n m) : string := nat2string (proj1_sig n).

  Definition send_debug_valid_commit slf keys cview c pil state :=
    let ui_i := commit2ui_i c in
    let ui_j := commit2ui_j c in
    send_debugs
      (str_concat ["|INVALID COMMIT",
                   "|error code(1):",
                   nat2string (valid_commit slf keys cview c pil state),
                   "|error code(2):",
                   nat2string (valid_commit2 slf keys cview c pil state),
                   "|received prior counter?",
                   bool2string (received_prior_or_equal_counter ui_i pil state),
                   "|pil?",
                   bool2string pil,
                   "|ui_i counter?",
                   nat2string (ui2counter ui_i),
                   "|ui_i highest?",
                   op2string nat2string (highest_received_counter (ui2rep ui_i) (vacc state)),
                   "|ui_j rep?",
                   nat_n2string (reps2nat (ui2rep ui_j)),
                   "|ui_j counter?",
                   nat2string (ui2counter ui_j),
                   "|ui_j highest?",
                   op2string nat2string (highest_received_counter (ui2rep ui_j) (vacc state))
      ])
      slf.

  Definition handle_commit (slf : Rep) : UProc MAINname _ :=
    fun state m =>
      let keys  := local_keys state in
      let cview := current_view state in
      let cc    := current_counter state in

      m >>oc>>=(fun _ => [R] (state,[])) fun c =>
      let p := commit2prepare c in
      p >>bpil>>= fun pil =>
      if invalid_commit slf keys cview c pil state then [R] (state, send_debug_valid_commit slf keys cview c pil state) else

      let v  := commit2view c in
      let r  := commit2request c in
      let ui := commit2ui_i c in
      let uj := commit2ui_j c in

      (* we verify ui_i *)
      (v,r,ui) >>vui>>=(fun _ => [R] (state, send_debugs "bad primary ui" slf)) fun _ =>

      (* we verify ui_j *)
      (v,r,uj) >>vui>>=(fun _ => [R] (state, send_debugs "bad self ui" slf)) fun _ =>

      let state1 := update_highest_received_counter (commit2ui_j c) state in

      if invalid_commit2 slf keys cview c pil state then [R] (state1, send_debug_valid_commit slf keys cview c pil state) else

      let state2 := start_processing (commit2request c) state1 in
      let state3 := update_highest_received_counter (commit2ui_i c) state2 in

      (* if the received commit doesn't match an entry in the log we have to send our commit *)
      (p >>pil>>=(fun _ => [R] (state3, [(*send_debug "prepare corresponding to commit already in log" slf*)]))
      (fun _ =>
        (* create_UI and update of the current state *)
        (v,r,cid0,S cc) >>cui>>=(fun _ => [R] (state3, send_debugs "couldn't generate commit ui" slf)) fun ui =>

        (* increment local copy of counter *)
        let state4 := increment_current_counter state3 in

        (* store the commit we created in the log and update replica's state *)
        let comm := mk_my_commit c ui in
        comm >>lc>>= fun _ =>

        (* we broadcast the commit message to all replicas *)
        [R] (state4, [broadcast2others slf (send_commit comm)])
      )) [>>>=] fun state4 out =>

      (* we log this commit *)
      c >>lc>>= fun _ =>

      (* is committed *)
      c>>ic>>=(fun _ => [R] (state4, send_debugs "not committed" slf ++ out)) fun _ =>

      let acc := accept (commit2request c) (commit2counter_i c) in
      let state5 := update_latest_executed (commit2request c) state4 in
      let state6 := increment_latest_executed_counter state5 in
      let state7 := stop_processing state6 in
      let (r,x)  := MinBFT_sm_update (commit2client c) (sm_state state7) (commit2msg c) in
      let state8 := replace_sm_state state7 x in
      [R] (state8, send_accept acc [MinBFT_replica slf] :: out).


  Definition handle_accept (slf : Rep) : UProc MAINname MAIN_state :=
    fun state m =>
      let keys  := local_keys state in
      let cview := current_view state in
      m >>oacc>>=(fun _ => [R] (state,[]))  fun a =>
      let rep := mk_auth_reply (accept_r a) (accept_c a) slf cview keys in
      [R] (state, [send_reply rep]).


  Definition handle_reply (slf : Rep) : UProc MAINname MAIN_state :=
    fun state m =>
      [R] (state, []).

  Definition handle_debug (slf : Rep) : UProc MAINname MAIN_state :=
    fun state m =>
      [R] (state, []).


  Definition MAIN_update (slf : Rep) : M_Update 1 MAINname _ :=
    fun (s : MAIN_state) m =>
      interp_s_proc
        (match m with
         | MinBFT_request _ => handle_request slf s m
         | MinBFT_prepare _ => handle_prepare slf s m
         | MinBFT_commit  _ => handle_commit  slf s m
         | MinBFT_accept  _ => handle_accept  slf s m
         | MinBFT_reply   _ => handle_reply   slf s m
         | MinBFT_debug   _ => handle_debug   slf s m
         end).

  Definition MAIN_comp (r : Rep) : n_proc 2 MAINname :=
    build_m_sm (MAIN_update r) (initial_state r).


  (*Definition MinBFT_nstate (n : name) :=
    match n with
    | MinBFT_replica _ => MAIN_state
    | _ => unit
    end.*)

  Definition MinBFT_replicaSM_new (r : Rep) (s : MAIN_state) : n_proc 2 MAINname :=
    build_m_sm (MAIN_update r) s.

  Notation MinBFTls := (LocalSystem 2 0).

  (* Parameterized version of [MinBFTlocalSys] *)
  Definition MinBFTlocalSysP (n : Rep) (subs : n_procs 1) : MinBFTls :=
    MkPProc _ (MAIN_comp n) :: incr_n_procs subs.

  Definition MinBFTlocalSys_newP
             (n    : Rep)
             (s    : MAIN_state)
             (subs : n_procs 1) : MinBFTls :=
    MkPProc _ (MinBFT_replicaSM_new n s) :: incr_n_procs subs.

  Definition MinBFTfunLevelSpace :=
    MkFunLevelSpace
      (fun n =>
         match n with
         | MinBFT_replica _ => 2
         | _ => 0
         end)
      (fun n =>
         match n with
         | MinBFT_replica _ => 0
         | _ => 0
         end).

  (* Parameterized version of [MinBFTsys] *)
  Definition MinBFTsysP (subs : Rep -> n_procs _) : M_USystem MinBFTfunLevelSpace (*name -> M_StateMachine 2 msg_comp_name*) :=
    fun name =>
      match name with
      | MinBFT_replica n => MinBFTlocalSysP n (subs n)
      | _ => empty_ls _ _
      end.

  Definition LOGlocalSys (s : LOG_state) : LocalSystem 1 0 :=
    [MkPProc _ (build_m_sm LOG_update s)].

End MinBFTg.


Hint Rewrite @verify_create_hash_usig : minbft.

Notation MinBFTls := (LocalSystem 2 0).
