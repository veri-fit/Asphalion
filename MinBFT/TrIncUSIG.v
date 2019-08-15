Require Export USIG.


Section TrIncUSIG.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : DTimeContext }.

  Context { minbft_context : MinBFT_context }.
  Context { m_initial_keys : MinBFT_initial_keys }.
  Context { u_initial_keys : USIG_initial_keys }.

  Context { usig_hash : USIG_hash }.



  (* ===============================================================
     USIG STATE
     =============================================================== *)

  (* As opposed to the fully-fledged TrInc, a counter doesn't have its own set of keys *)
  Record TRINC_state :=
    Build_TRINC
      {
        trinc_id            : Rep;
        trinc_counters      : list nat;
        trinc_local_keys    : local_key_map;
        trinc_attestations  : list MinBFT_digest;
      }.

  Definition TRINC_initial (r : Rep) : TRINC_state :=
    Build_TRINC
      r
      []
      (usig_initial_keys (MinBFT_replica r))
      [].

  Definition getReplicaId (u : TRINC_state) : Rep := trinc_id u.

  (* This creates new counters if cid is greater than the numbers of counter
     already in use *)
  Fixpoint update_counter (cid : nat) (c : nat) (counters : list nat) : list nat :=
    match cid with
    | 0 =>
      match counters with
      | [] => [c]
      | counter :: counters => max c counter :: counters
      end
    | S n =>
      match counters with
      | [] => 0 :: update_counter n c []
      | counter :: counters => counter :: update_counter n c counters
      end
    end.

  Definition update_TRINC (cid : nat) (c : nat) (u : TRINC_state) : TRINC_state :=
    Build_TRINC
      (trinc_id           u)
      (update_counter cid c (trinc_counters u))
      (trinc_local_keys   u)
      (trinc_attestations u).

  Definition try_update_TRINC
             (cid : nat)
             (old : nat)
             (new : nat)
             (u   : TRINC_state) : TRINC_state :=
    if old <? new then update_TRINC cid new u
    else u.



(*
  (* ===============================================================
     UIs
     =============================================================== *)

  Record preTrIncUI :=
    Build_preTrIncUI
      {
        pre_trinc_ui_rid     : Rep; (* replica id *)
        pre_trinc_ui_cid     : nat; (* counter id *)
        pre_trinc_ui_counter : nat; (* counter value *)
      }.

  Record TrIncUI :=
    Build_TrIncUI
      {
        trinc_ui_pre     :> preTrIncUI;
        trinc_ui_digest  : MinBFT_digest;
      }.

  Definition TrIncUIs := list TrIncUI.

  Definition trinc_ui2rep     (ui : TrIncUI) : Rep := pre_trinc_ui_rid (trinc_ui_pre ui).
  Definition trinc_ui2cid     (ui : TrIncUI) : nat := pre_trinc_ui_cid (trinc_ui_pre ui).
  Definition trinc_ui2counter (ui : TrIncUI) : nat := pre_trinc_ui_counter (trinc_ui_pre ui).
  Definition trinc_ui2digest  (ui : TrIncUI) : MinBFT_digest := trinc_ui_digest ui.



  (* ===============================================================
     HASH DATA
     =============================================================== *)

  Record TrIncHashData :=
    Build_TrIncHashData
      {
        trinc_hd_view : View;
        trinc_hd_msg  : Request;
        trinc_hd_pre  : preTrIncUI;
      }.

  (* hash of the whole trinc *)
  Class TRINC_hash :=
    MkMinBFThash
      {
        create_hash_trinc  : TrIncHashData -> local_key_map -> MinBFT_digest;
        verify_hash_trinc  : TrIncHashData -> MinBFT_digest -> local_key_map -> bool;
        verify_create_hash_trinc :
          forall (hd : TrIncHashData) (keys : local_key_map),
            verify_hash_trinc hd (create_hash_trinc hd keys) keys = true;
      }.
  Context { trinc_hash : TRINC_hash }.
  Hint Rewrite verify_create_hash_trinc : minbft.
*)



  (* ===============================================================
     TRINC INTERFACE
     =============================================================== *)

  Definition getCounter (cid : nat) (l : list nat) : nat := nth cid l 0.

  Definition try_create_trinc_ui
             (v    : View)
             (msg  : Request)
             (keys : local_key_map)
             (rid  : Rep)
             (cid  : nat)
             (old  : nat)
             (new  : nat) : option UI :=
    (* TrInc allows [old <= c].  For this it also adds the old counters
       to attestations (UIs) *)
    if old <? new then
      (* creates the data to hash *)
      let pre := Build_preUI rid cid new in
      let hd  := Build_HashData v msg pre in
      (* hashes the data *)
      let d   := create_hash_usig hd keys in
      (* builds UI *)
      let ui  := Build_UI pre d in
      (* TODO: update the list of generated attestations *)
      Some ui
    else None.

  (* 1st TRINC counter will be [1] *)
  Definition create_TrIncUI
             (v   : View)
             (msg : Request)
             (cid : nat)
             (new : nat)
             (u   : TRINC_state) : TRINC_state * option UI :=
    (* increment current counter of the trinc *)
    let rid  := trinc_id u in
    let keys := trinc_local_keys u in
    let old  := getCounter cid (trinc_counters u) in
    let u'   := try_update_TRINC cid old new u in
    let ui   := try_create_trinc_ui v msg keys rid cid old new in
    (u', ui).

  Definition verify_TrIncUI
             (v   : View)
             (msg : Request)
             (ui  : UI)
             (u   : TRINC_state) : bool :=
    (* creates the data to hash *)
    let hd := Build_HashData v msg (ui_pre ui) in
    (* the keys are supposed to be the receiving keys for [ui_id ui] *)
    verify_hash_usig hd (ui2digest ui) (trinc_local_keys u).

(*  Definition verify_prepare (msg : Prepare) (ui : UI) (u : TRINC_state) : bool :=
    (* creates the data to hash *)
    let pre := Build_preUI (pre_ui_id (ui_pre ui)) (pre_ui_counter (ui_pre ui)) in
    let hd  := Build_HashData (prepare2request msg) pre in
    (* the keys are supposed to be the receiving keys for [ui_id ui] *)
    let d  := create_hash_trinc hd (trinc_local_keys u) in
    if MinBFT_digestdeq d (ui_digest ui)
    then true
    else false.

  Definition verify_commit (msg : Commit) (ui : UI) (u : TRINC_state) : bool :=
    (* creates the data to hash *)
    let pre := Build_preUI (pre_ui_id (ui_pre ui)) (pre_ui_counter (ui_pre ui)) in
    let hd  := Build_HashData (commit2request msg) pre in
    (* the keys are supposed to be the receiving keys for [ui_id ui] *)
    let d  := create_hash_trinc hd (trinc_local_keys u) in
    if MinBFT_digestdeq d (ui_digest ui)
    then true
    else false.*)

(*
  Inductive TRINC_input_interface :=
  | create_trinc_ui_in (msg   : View * Request * nat (* counter id *) * nat (* new counter value *))
  | verify_trinc_ui_in (msgui : View * Request * TrIncUI).

  Inductive TRINC_output_interface :=
  | create_trinc_ui_out        (ui : option TrIncUI)
  | verify_trinc_ui_out        (b  : bool)
  (* default output *)
  | verify_trinc_ui_out_def.

  Definition CIOtrinc : ComponentIO :=
    MkComponentIO TRINC_input_interface TRINC_output_interface verify_trinc_ui_out_def.
*)


End TrIncUSIG.
