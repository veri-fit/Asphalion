Require Export DTimeQ.
Require Export MicroBFTheader.
Require Export ComponentSM.
Require Export ComponentSM2.
Require Export toString.


Section MicroBFT.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : DTimeContext }.

  Context { microbft_context : MicroBFT_context }.
  Context { m_initial_keys   : MicroBFT_initial_keys }.
  Context { u_initial_keys   : USIG_initial_keys }.

  (* ===============================================================
     USIG
     =============================================================== *)

  Record USIG_state :=
    Build_USIG
      {
        usig_id            : MicroBFT_node;
        usig_counter       : nat;
        usig_local_keys    : local_key_map;
      }.

  Record preUI :=
    Build_preUI
      {
        pre_ui_id      : MicroBFT_node;
        pre_ui_counter : nat;
      }.

  Record UI :=
    Build_UI
      {
        ui_pre     :> preUI;
        ui_digest  : MicroBFT_digest;
      }.

  Definition UIs := list UI.

  Definition ui2rep     (ui : UI) : MicroBFT_node := pre_ui_id (ui_pre ui).
  Definition ui2counter (ui : UI) : nat := pre_ui_counter (ui_pre ui).
  Definition ui2digest  (ui : UI) : MicroBFT_digest := ui_digest ui.


  (* ===============================================================
     Bare messages
     =============================================================== *)

  Record Commit :=
    commit
      {
        commit_n  : nat;
        commit_ui : UI
      }.

  Record Accept :=
    accept
      {
        accept_r : nat;
        accept_c : nat;
      }.

  Definition commit2sender (c : Commit) : MicroBFT_node :=
    pre_ui_id (commit_ui c).

  (* ===============================================================
     Bare message type
     =============================================================== *)

  Inductive MicroBFT_Bare_Msg : Set :=
  | MicroBFT_msg_bare_request (n : nat) (pui : preUI).

  (* =========== Msg type =========== *)

  Inductive MicroBFT_msg :=
  | MicroBFT_request (n : nat)
  | MicroBFT_commit  (c : Commit)
  | MicroBFT_accept  (a : Accept).

  Global Instance MicroBFT_I_Msg : Msg := MkMsg MicroBFT_msg.

  Definition MicroBFTmsg2status (m : MicroBFT_msg) : msg_status :=
    match m with
    | MicroBFT_request _ => MSG_STATUS_EXTERNAL
    | MicroBFT_commit  _ => MSG_STATUS_PROTOCOL
    | MicroBFT_accept  _ => MSG_STATUS_INTERNAL
    end.

  Global Instance MicroBFT_I_MsgStatus : MsgStatus := MkMsgStatus MicroBFTmsg2status.

  (* back to the definition of usig *)

  Record HashData :=
    Build_HashData
      {
        hd_msg : nat;
        hd_pre : preUI;
      }.

  (* hash of the whole usig *)
  Class USIG_hash :=
    MkMicroBFThash
      {
        create_hash_usig  : HashData -> local_key_map -> MicroBFT_digest;
        verify_hash_usig  : HashData -> MicroBFT_digest -> local_key_map -> bool;
        verify_create_hash_usig :
          forall (hd : HashData) (keys : local_key_map),
            verify_hash_usig hd (create_hash_usig hd keys) keys = true;
      }.
  Context { usig_hash : USIG_hash }.
  Hint Rewrite verify_create_hash_usig : microbft.

  Definition USIG_initial (r : MicroBFT_node) : USIG_state :=
    Build_USIG
      r
      0
      (usig_initial_keys r).

  Definition getReplicaId (u : USIG_state) : MicroBFT_node := usig_id u.

  Definition increment_USIG (u : USIG_state) : USIG_state :=
    Build_USIG
      (usig_id         u)
      (S               (usig_counter u))
      (usig_local_keys u).

  (* 1st USIG counter will be [1] *)
  Definition create_UI (msg : nat) (u : USIG_state) : USIG_state * UI :=
    (* increment current counter of the usig *)
    let u' := increment_USIG u in
    (* creates the data to hash *)
    let pre := Build_preUI (usig_id u') (usig_counter u') in
    let hd := Build_HashData msg pre in
    (* hashes the data *)
    let d  := create_hash_usig hd (usig_local_keys u') in
    (* builds UI *)
    let ui := Build_UI pre d in
    (u', ui).

  Definition verify_UI (msg : nat) (ui : UI) (u : USIG_state) : bool :=
    (* creates the data to hash *)
    let hd  := Build_HashData msg (ui_pre ui) in
    (* the keys are supposed to be the receiving keys for [ui_id ui] *)
    verify_hash_usig hd (ui2digest ui) (usig_local_keys u).

  Inductive USIG_input_interface :=
  | create_ui_in (msg   : nat)
  | verify_ui_in (msgui : nat * UI).

  Inductive USIG_output_interface :=
  | create_ui_out (ui : UI)
  | verify_ui_out (b  : bool)
  (* default output *)
  | verify_ui_out_def.

  Definition CIOusig : ComponentIO :=
    MkComponentIO USIG_input_interface USIG_output_interface verify_ui_out_def.


  (* ===============================================================
     Crypto
     =============================================================== *)

  Global Instance MicroBFT_I_Data : Data := MkData MicroBFT_Bare_Msg.

  Class MicroBFT_auth :=
    MkMicroBFT_auth
      {
        MicroBFT_create : data -> sending_keys -> list MicroBFT_digest;
        MicroBFT_verify : data -> name -> receiving_key -> MicroBFT_digest -> bool
      }.

  Context { microbft_auth : MicroBFT_auth }.

  Global Instance MicroBFT_I_AuthFun : AuthFun :=
    MkAuthFun
      MicroBFT_create
      MicroBFT_verify.


  (* ===============================================================
        Authenticated Messages
        =============================================================== *)

  (* we are here extracting the sender of the message *)
  Definition MicroBFT_msg_auth (m : msg) : option  name :=
    match m with
    | MicroBFT_request _ => None
    | MicroBFT_commit  c => Some (commit2sender c)
    | MicroBFT_accept  a => None
    end.

  (* FIX : Why do we need n here? *)
  Definition MicroBFT_data_auth (n : name) (d : data) : option name :=
    match d with
    | MicroBFT_msg_bare_request n pui => Some (pre_ui_id pui)
    end.

  Global Instance MicroBFT_I_DataAuth : DataAuth := MkDataAuth MicroBFT_data_auth.

  Definition commit2auth_data (c : Commit) : AuthenticatedData :=
    match c with
    | commit n ui => MkAuthData (MicroBFT_msg_bare_request n ui) [ui_digest ui]
    end.

  Definition MicroBFT_get_contained_auth_data (m : msg) : list AuthenticatedData :=
    match m with
    | MicroBFT_request _ => []
    | MicroBFT_commit  c => [commit2auth_data c]
    | MicroBFT_accept  a => []
    end.

  Global Instance MicroBFT_I_ContainedAuthData : ContainedAuthData :=
    MkContainedAuthData MicroBFT_get_contained_auth_data.


  (* ===============================================================
     Decidability for different types of messages
     =============================================================== *)

  Definition UI_dec : Deq UI.
  Proof.
    introv.
    destruct x as [p1 d1], y as [p2 d2], p1 as [i1 c1], p2 as [i2 c2].
    destruct (MicroBFT_nodeDeq i1 i2); subst; prove_dec.
    destruct (deq_nat c1 c2); subst; prove_dec.
    destruct (MicroBFT_digestdeq d1 d2); subst; prove_dec.
  Defined.

  (****************************************************************************)

  Definition broadcast2others F : DirectedMsg :=
    F [MicroBFT_backup1, MicroBFT_backup2].

  (* ===============================================================
     Sending functions
     =============================================================== *)

  Definition send_commit (c : Commit) (n : list name) : DirectedMsg :=
    MkDMsg (MicroBFT_commit c) n ('0).

  Definition send_accept (a : Accept) (n : list name) : DirectedMsg :=
    MkDMsg (MicroBFT_accept a) n ('0).


  (* ===============================================================
     Log
     =============================================================== *)

  Definition LOG_state := list Commit.

  Definition LOG_initial : LOG_state := [].

  Inductive LOG_input_interface :=
  | log_new (c : Commit).

  Inductive LOG_output_interface :=
  | log_out (b : bool).

  Definition CIOlog : ComponentIO :=
    MkComponentIO LOG_input_interface LOG_output_interface (log_out true).



  (* ===============================================================
     State of some replica
     =============================================================== *)

  Definition update_highest_received_counter_value (ui : UI) (n : nat) : nat :=
    if n <? ui2counter ui
    then ui2counter ui
    else n.


  Record MAIN_state :=
    Build_State
      {

        (* state of the local state machine *)
        sm_state : nat;

        (* the highest sequence number received from the primary *)
        prim     : nat;

      }.

  Definition initial_state : MAIN_state :=
    Build_State 0 0.

  Definition update_sm_state
             (s : MAIN_state)
             (x : nat) : MAIN_state :=
    Build_State (sm_state s + x) (prim s).

  Global Instance MicroBFT_I_baseFunIO : baseFunIO :=
    MkBaseFunIO (fun nm =>
                   if CompNameKindDeq (comp_name_kind nm) "USIG" then CIOusig
                   else if CompNameKindDeq (comp_name_kind nm) "LOG" then CIOlog
                        else CIOdef).

  Definition preUSIGname : PreCompName := MkPreCompName "USIG" 0.
  Definition USIGname : CompName := MkCN "USIG" 0 true.

  Global Instance MicroBFT_I_baseStateFun : baseStateFun :=
    MkBaseStateFun (fun nm =>
                      if CompNameKindDeq (comp_name_kind nm) "USIG" then USIG_state
                      else if CompNameKindDeq (comp_name_kind nm) "LOG" then LOG_state
                           else if CompNameKindDeq (comp_name_kind nm) msg_comp_name_kind
                                then MAIN_state
                                else unit).

  Global Instance MicroBFT_I_IOTrustedFun : IOTrustedFun :=
    MkIOTrustedFun
      (fun _ =>
         MkIOTrusted
           USIG_input_interface
           USIG_output_interface
           verify_ui_out_def).

  Global Instance MicroBFT_I_trustedStateFun : trustedStateFun :=
    MkTrustedStateFun (fun _ => USIG_state).

  Definition USIG_update : M_Update 0 USIGname _ :=
    fun (s : USIG_state) (m : USIG_input_interface) =>
      interp_s_proc
        (match m with
         | create_ui_in r =>
           let (s', ui) := create_UI r s in
           [R] (s', create_ui_out ui)
         | verify_ui_in (r,ui) =>
           let b := verify_UI r ui s in
           [R] (s, verify_ui_out b)
         end).

  Definition USIG_comp (n : MicroBFT_node) : M_StateMachine 1 USIGname :=
    build_m_sm USIG_update (USIG_initial n).

  Definition LOGname : CompName := MkCN "LOG" 0 false.

  Definition LOG_update : M_Update 0 LOGname _ :=
    fun (l : LOG_state) (m : LOG_input_interface) =>
      interp_s_proc
        (match m with
         | log_new r =>
           let l' := r :: l in
           [R] (l', log_out true)
         end).

  Definition LOG_comp : M_StateMachine 1 LOGname :=
    build_m_sm LOG_update LOG_initial.

  (******************************************************************************)


  Definition on_create_ui_out {A} (f : UI -> A) (d : unit -> A) (out : USIG_output_interface) : A :=
    match out with
    | create_ui_out ui => f ui
    | _ => d tt
    end.

  Definition call_create_ui {A} (m : nat) (d : unit -> Proc A) (f : UI -> Proc A) :=
    (USIGname [C] (create_ui_in m))
      [>>=] on_create_ui_out f d.

  Notation "a >>cui>>=( d ) f" := (call_create_ui a d f) (at level 80, right associativity).

  Definition if_true_verify_ui_out {A} (f d : unit -> A) (out : USIG_output_interface) : A :=
    match out with
    | verify_ui_out b => if b then f tt else d tt
    | _ => d tt
    end.

  Definition call_verify_ui {A} (mui : nat * UI) (d f : unit -> Proc A) :=
    (USIGname [C] (verify_ui_in mui))
      [>>=] if_true_verify_ui_out f d.

  Notation " a >>vui>>=( d ) f" := (call_verify_ui a d f) (at level 80, right associativity).

  Definition on_data_message {A} (m : MicroBFT_msg) (d : unit -> Proc A) (f : nat -> Proc A) : Proc A :=
    match m with
    | MicroBFT_request m => f m
    | _ => d tt
    end.

  Notation "a >>odm>>=( d ) f" := (on_data_message a d f) (at level 80, right associativity).

  Definition on_commit {A} (m : MicroBFT_msg) (d : unit -> Proc A) (f : Commit -> Proc A) : Proc A :=
    match m with
    | MicroBFT_commit c => f c
    | _ => d tt
    end.

  Notation "a >>oc>>=( d ) f" := (on_commit a d f) (at level 80, right associativity).


  Definition MAINname := msg_comp_name 0.

  Definition received_prior_counter (ui : UI) (s : MAIN_state) : bool :=
    match ui2counter ui with
    | 0 => false (* 0 is not a valid counter *)
    | 1 => true (* 1st counter *)
    | S n => if deq_nat n (prim s) then true else false
    end.

  Definition is_primary (n : MicroBFT_node) : bool :=
    if MicroBFT_nodeDeq n MicroBFT_primary then true else false.

  Definition not_primary (n : MicroBFT_node) : bool :=
    negb (is_primary n).

  Definition valid_commit
             (slf : MicroBFT_node)
             (c   : Commit)
             (s   : MAIN_state) : bool :=
    is_primary (commit2sender c)
      && not_primary slf
      && received_prior_counter (commit_ui c) s.

  Definition invalid_commit
             (slf : MicroBFT_node)
             (c   : Commit)
             (s   : MAIN_state) : bool :=
    negb (valid_commit slf c s).

  Definition update_highest_received_counter (ui : UI) (s : MAIN_state) : MAIN_state :=
    Build_State
      (sm_state          s)
      (update_highest_received_counter_value ui (prim s)).

  Definition handle_request (slf : MicroBFT_node) : UProc MAINname _ :=
    (* in case M_Update 0 _ := is output type it complains that "The term "m" has type "cio_I" while it is expected to have type "data_message"." *)
    fun state m =>
      if not_primary slf then [R] (state, []) else

      m >>odm>>=(fun _ => [R] (state,[])) fun m =>

      let state1 := update_sm_state state m in
      let m' := sm_state state1 in

      (* create_UI and update of the current state *)
      m' >>cui>>=(fun _ => [R](state1, [])) fun ui =>

      (* create request *)
      let c := commit m' ui in

      (* we log this request *)
      (LOGname [C] (log_new c)) [>>=] fun _ =>

      (* we broadcast the request message to all replicas *)
      [R] (state1, [broadcast2others (send_commit c)]).

  Definition handle_commit (slf : MicroBFT_node) : UProc MAINname _ :=
    fun state m =>
      m >>oc>>=(fun _ => [R] (state,[])) fun c =>
      if invalid_commit slf c state then [R] (state, []) else

      (* we check whether the ui is created by some usig *)
      let n  := commit_n c in
      let ui := commit_ui c in
      (n,ui) >>vui>>=(fun _ => [R] (state, [])) fun _ =>

      let state1 := update_highest_received_counter (commit_ui c) state in

      (* we log this request *)
      (LOGname [C] (log_new c)) [>>=] fun _ =>

      (* we broadcast the commit message to all replicas *)
      let acc := accept n (ui2counter ui) in
      [R] (state1, [send_accept acc [slf]]).

  Definition handle_accept (slf : MicroBFT_node) : UProc MAINname _ :=
    fun (state : MAIN_state) m => [R](state,[]).


  Definition MAIN_update (slf : MicroBFT_node) : M_Update 1 MAINname _ :=
    fun (s : MAIN_state) m =>
      interp_s_proc
        (match m with
         | MicroBFT_request _ => handle_request slf s m
         | MicroBFT_commit  _ => handle_commit  slf s m
         | MicroBFT_accept  _ => handle_accept  slf s m
         end).

  Definition MAIN_comp (slf : MicroBFT_node) : n_proc 2 MAINname :=
    build_m_sm (MAIN_update slf) initial_state.


  (*Definition MicroBFT_nstate (n : name) :=
    match n with
    | MicroBFT_replica _ => MAIN_state
    | _ => unit
    end.*)

  Definition MicroBFTsubs (n : MicroBFT_node) : n_procs _ :=
    [
      MkPProc USIGname (USIG_comp n),
      MkPProc LOGname LOG_comp
    ].

  Definition MicroBFTsubs_new (s1 : USIG_state) (s2 : LOG_state) : n_procs _ :=
    [
      MkPProc USIGname (build_m_sm USIG_update s1),
      MkPProc LOGname  (build_m_sm LOG_update s2)
    ].

  Definition MicroBFTsubs_new_u (u : USIG_state) : n_procs _ :=
    [
      MkPProc USIGname (build_m_sm USIG_update u),
      MkPProc LOGname  LOG_comp
    ].

  Definition MicroBFTsubs_new_l n (l : LOG_state) : n_procs _ :=
    [
      MkPProc USIGname (USIG_comp n),
      MkPProc LOGname  (build_m_sm LOG_update l)
    ].

  Definition MicroBFT_replicaSM_new (r : MicroBFT_node) (s : MAIN_state) : n_proc 2 MAINname :=
    build_m_sm (MAIN_update r) s.

  Notation MicroBFTls := (LocalSystem 2 0).

  Definition MicroBFTlocalSys (slf : MicroBFT_node) : MicroBFTls :=
    MkPProc _ (MAIN_comp slf) :: incr_n_procs (MicroBFTsubs slf).

  Definition MicroBFTlocalSys_new
             (n  : MicroBFT_node)
             (s  : MAIN_state)
             (s1 : USIG_state)
             (s2 : LOG_state) : MicroBFTls :=
    MkPProc _ (MicroBFT_replicaSM_new n s) :: incr_n_procs (MicroBFTsubs_new s1 s2).

  Definition MicroBFTfunLevelSpace :=
    MkFunLevelSpace
      (fun n => 2)
      (fun n => 0).

  Definition MicroBFTsys : M_USystem MicroBFTfunLevelSpace (*name -> M_StateMachine 2 msg_comp_name*) :=
    MicroBFTlocalSys.

  Lemma eq_cons :
    forall {T} (x1 x2 : T) l1 l2,
      x1 :: l1 = x2 :: l2 -> x1 = x2 /\ l1 = l2.
  Proof.
    introv h; inversion h; auto.
  Qed.

  Lemma MicroBFTsubs_new_inj :
    forall a b c d,
      MicroBFTsubs_new a b = MicroBFTsubs_new c d
      -> a = c /\ b = d.
  Proof.
    introv h.
    repeat (apply eq_cons in h; repnd); GC.
    apply decomp_p_nproc in h0.
    apply decomp_p_nproc in h1.
    inversion h0; inversion h1; subst; simpl in *; auto.
  Qed.

  Lemma MicroBFTlocalSys_new_inj :
    forall a1 a2 b1 b2 c1 c2 d1 d2,
      MicroBFTlocalSys_new a1 b1 c1 d1 = MicroBFTlocalSys_new a2 b2 c2 d2
      -> b1 = b2 /\ c1 = c2 /\ d1 = d2.
  Proof.
    introv h.
    apply eq_cons in h; repnd.
    apply decomp_p_nproc in h0.
    inversion h0; subst.
    apply incr_n_procs_inj in h.
    apply MicroBFTsubs_new_inj in h; repnd; subst; tcsp.
  Qed.

  Lemma MicroBFTlocalSys_as_new :
    forall (r  : MicroBFT_node),
      MicroBFTlocalSys r
      = MicroBFTlocalSys_new
          r
          initial_state
          (USIG_initial r)
          LOG_initial.
  Proof.
    introv; eauto.
  Qed.

  Definition USIGlocalSys (s : USIG_state) : LocalSystem 1 0 :=
    [MkPProc _ (build_m_sm USIG_update s)].

  Definition LOGlocalSys (s : LOG_state) : LocalSystem 1 0 :=
    [MkPProc _ (build_m_sm LOG_update s)].

End MicroBFT.


Hint Rewrite @verify_create_hash_usig : microbft.

Notation MicroBFTls := (LocalSystem 2 0).
