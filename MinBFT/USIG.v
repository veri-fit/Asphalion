Require Export DTimeN.
Require Export MinBFTheader.
Require Export ComponentSM.
Require Export ComponentSM2.
Require Export toString.
Require Export List.


Section USIG.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : DTimeContext }.

  Context { minbft_context : MinBFT_context }.
  Context { m_initial_keys : MinBFT_initial_keys }.
  Context { u_initial_keys : USIG_initial_keys }.



  (* ===============================================================
     USIG STATE
     =============================================================== *)

  Record USIG_state :=
    Build_USIG
      {
        usig_id            : Rep;
        usig_counter       : nat;
        usig_local_keys    : local_key_map;
      }.

  Definition USIG_initial (r : Rep) : USIG_state :=
    Build_USIG
      r
      0
      (usig_initial_keys (MinBFT_replica r)).

  Definition getReplicaId (u : USIG_state) : Rep := usig_id u.

  Definition increment_USIG (u : USIG_state) : USIG_state :=
    Build_USIG
      (usig_id         u)
      (S               (usig_counter u))
      (usig_local_keys u).



  (* ===============================================================
     UIs
     =============================================================== *)

  Record preUI :=
    Build_preUI
      {
        pre_ui_rid     : Rep;
        pre_ui_cid     : nat;
        pre_ui_counter : nat;
      }.

  Definition MkPreUI (r : Rep) (c : nat) := Build_preUI r 0 c.

  Record UI :=
    Build_UI
      {
        ui_pre     :> preUI;
        ui_digest  : MinBFT_digest;
      }.

  Definition UIs := list UI.

  Definition ui2rep     (ui : UI) : Rep := pre_ui_rid (ui_pre ui).
  Definition ui2cid     (ui : UI) : nat := pre_ui_cid (ui_pre ui).
  Definition ui2counter (ui : UI) : nat := pre_ui_counter (ui_pre ui).
  Definition ui2digest  (ui : UI) : MinBFT_digest := ui_digest ui.



  (* ===============================================================
     HASH DATA
     =============================================================== *)

  Record HashData :=
    Build_HashData
      {
        hd_view : View;
        hd_msg  : Request;
        hd_pre  : preUI;
      }.

  (* hash of the whole usig *)
  Class USIG_hash :=
    MkMinBFThash
      {
        create_hash_usig  : HashData -> local_key_map -> MinBFT_digest;
        verify_hash_usig  : HashData -> MinBFT_digest -> local_key_map -> bool;
        verify_create_hash_usig :
          forall (hd : HashData) (keys : local_key_map),
            verify_hash_usig hd (create_hash_usig hd keys) keys = true;
      }.
  Context { usig_hash : USIG_hash }.
  Hint Rewrite verify_create_hash_usig : minbft.



  (* ===============================================================
     USIG INTERFACE
     =============================================================== *)

  (* 1st USIG counter will be [1] *)
  Definition create_UI (v : View) (msg : Request) (u : USIG_state) : USIG_state * UI :=
    (* increment current counter of the usig *)
    let u' := increment_USIG u in
    (* creates the data to hash *)
    let pre := MkPreUI (usig_id u') (usig_counter u') in
    let hd := Build_HashData v msg pre in
    (* hashes the data *)
    let d  := create_hash_usig hd (usig_local_keys u') in
    (* builds UI *)
    let ui := Build_UI pre d in
    (u', ui).

  Definition verify_UI_000 (v : View) (msg : Request) (ui : UI) (u : USIG_state) : bool :=
    (* creates the data to hash *)
    let hd  := Build_HashData v msg (ui_pre ui) in
    (* the keys are supposed to be the receiving keys for [ui_id ui] *)
    let d  := create_hash_usig hd (usig_local_keys u) in
    if MinBFT_digestdeq d (ui_digest ui)
    then true
    else false.

  Definition verify_UI (v : View) (msg : Request) (ui : UI) (u : USIG_state) : bool :=
    (* creates the data to hash *)
    let hd  := Build_HashData v msg (ui_pre ui) in
    (* the keys are supposed to be the receiving keys for [ui_id ui] *)
    verify_hash_usig hd (ui2digest ui) (usig_local_keys u).

(*  Definition verify_prepare (msg : Prepare) (ui : UI) (u : USIG_state) : bool :=
    (* creates the data to hash *)
    let pre := Build_preUI (pre_ui_id (ui_pre ui)) (pre_ui_counter (ui_pre ui)) in
    let hd  := Build_HashData (prepare2request msg) pre in
    (* the keys are supposed to be the receiving keys for [ui_id ui] *)
    let d  := create_hash_usig hd (usig_local_keys u) in
    if MinBFT_digestdeq d (ui_digest ui)
    then true
    else false.

  Definition verify_commit (msg : Commit) (ui : UI) (u : USIG_state) : bool :=
    (* creates the data to hash *)
    let pre := Build_preUI (pre_ui_id (ui_pre ui)) (pre_ui_counter (ui_pre ui)) in
    let hd  := Build_HashData (commit2request msg) pre in
    (* the keys are supposed to be the receiving keys for [ui_id ui] *)
    let d  := create_hash_usig hd (usig_local_keys u) in
    if MinBFT_digestdeq d (ui_digest ui)
    then true
    else false.*)

  Inductive USIG_input_interface :=
  | create_ui_in       (msg   : View * Request * nat (* current counter id *) * nat (* new counter id *))
  | verify_ui_in       (msgui : View * Request * UI).

  Inductive USIG_output_interface :=
  | create_ui_out        (ui : option UI)
  | verify_ui_out        (b  : bool)
  (* default output *)
  | verify_ui_out_def.

  Definition CIOusig : ComponentIO :=
    MkComponentIO USIG_input_interface USIG_output_interface verify_ui_out_def.



(*
  (* ===============================================================
     PARAMETERS
     =============================================================== *)

  Context { trusted_state_fun : trustedStateFun }.
  Context { base_fun_io : baseFunIO }.
  Context { base_state_io : baseStateFun }.
  Context { pm : @Msg }.

  Global Instance MinBFT_I_IOTrusted : IOTrusted :=
    Build_IOTrusted
      USIG_input_interface
      USIG_output_interface
      verify_ui_out_def.



  (* ===============================================================
     USIG UPDATE & SM
     =============================================================== *)

  Definition USIGname : CompName := MkCN "USIG" 0 true 0.

  Definition USIG_update : M_Update 0 USIGname _ :=
    fun (s : USIG_state) (m : USIG_input_interface) =>
      interp_s_proc
        (match m with
         | create_ui_in (v,r) =>
           let (s', ui) := create_UI v r s in
           [R] (s', create_ui_out ui)
         | verify_ui_in (v,r,ui) =>
           let b := verify_UI v r ui s in
           [R] (s, verify_ui_out b)
         end).

  (* (1) USIG and TrInc will have the same IO interface, but different states
     (2) add a new field to CompName to allow differentiating those states
     (3) call_proc will only look at the old CompName, without the new field
     (4) write a wrapper around TrInc's interface, which is slightly different
     (5) Parametrize UI in MinBFT
     (6) Move this elsewhere (to where all interfaces and states have been defined)
   *)
  Definition USIG_comp (r : Rep) : M_StateMachine 1 USIGname :=
    build_m_sm USIG_update (USIG_initial r).
*)

End USIG.


Hint Rewrite @verify_create_hash_usig : minbft.
