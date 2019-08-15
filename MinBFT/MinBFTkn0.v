Require Export MinBFTg.
Require Export ComponentAxiom.


Section MinBFTkn0.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  (* ===============================================================
     Some useful lemmas/definitions
     =============================================================== *)

  Lemma eq_cons :
    forall {T} (x1 x2 : T) l1 l2,
      x1 :: l1 = x2 :: l2 -> x1 = x2 /\ l1 = l2.
  Proof.
    introv h; inversion h; auto.
  Qed.

  Definition ui_in_log_entry (ui : UI) (e : LOG_state_entry) : bool :=
    if UI_dec ui (request_data2ui (log_entry_request_data e))
    then true
    else if in_dec UI_dec ui (log_entry_commits e) then true else false.

  Definition ui_in_log ui l : bool :=
    existsb (ui_in_log_entry ui) l.

  Definition RequestData2HashData (r : RequestData) : HashData :=
    Build_HashData
      (request_data2view r)
      (request_data2request r)
      (ui_pre (request_data2ui r)).

  Lemma HashData_Deq : Deq HashData.
  Proof.
    repeat introv.
    destruct x as [v1 m1 ui1], y as [v2 m2 ui2].
    destruct (ViewDeq v1 v2); subst; prove_dec.
    destruct (Request_Deq m1 m2); subst; prove_dec.

    destruct ui1 as [i1 j1 c1], ui2 as [i2 j2 c2].

    destruct (rep_deq i1 i2); subst; prove_dec.
    destruct (deq_nat j1 j2); subst; prove_dec.
    destruct (deq_nat c1 c2); subst; prove_dec.
  Defined.

  Definition RequestDataAndUI2HashData (r : RequestData) (ui : UI) : HashData :=
    Build_HashData
      (request_data2view r)
      (request_data2request r)
      (ui_pre ui).

  Fixpoint hash_data_in_log_commits (hd : HashData) (rd : RequestData) (l : list UI) : bool :=
    match l with
    | [] => false
    | ui :: uis =>
      if HashData_Deq hd (RequestDataAndUI2HashData rd ui) then true
      else hash_data_in_log_commits hd rd uis
    end.

  Definition hash_data_in_log_entry (hd : HashData) (e : LOG_state_entry) : bool :=
    if HashData_Deq hd (RequestData2HashData (log_entry_request_data e))
    then true
    else hash_data_in_log_commits hd (log_entry_request_data e) (log_entry_commits e).

  Definition hash_data_in_log (hd : HashData) (l : LOG_state) : bool :=
    existsb (hash_data_in_log_entry hd) l.

  Inductive MinBFT_data :=
(*  | minbft_data_prepare (p  : Prepare)
  | minbft_data_commit  (c  : Commit)
  | minbft_data_hdata   (hd : HashData)*)
  | minbft_data_rdata   (rd : RequestData)
  | minbft_data_ui      (ui : UI).

  Definition MinBFT_auth2data (a : AuthenticatedData) : list MinBFT_data :=
    match a with
    | MkAuthData (MinBFT_msg_bare_prepare bp pui) [d] =>
      let ui := Build_UI pui d in
      [minbft_data_rdata (prepare2request_data (prepare bp ui)),
       minbft_data_ui ui]

    | MkAuthData (MinBFT_msg_bare_commit bc pui) [d] =>
      let uj  := Build_UI pui d in
      let com := commit bc uj in
      [minbft_data_rdata (commit2request_data_i com),
       (*minbft_data_rdata (commit2request_data_j com),*)
       minbft_data_ui (bare_commit_ui bc),
       minbft_data_ui uj]

    | _ => []
    end.

  Definition request_data_in_log (rd : RequestData) (l : LOG_state) : bool :=
    match find_entry rd l with
    | Some _ => true
    | None => false
    end.

  Lemma equal_hash_data_implies_equal_request_data :
    forall r1 r2,
      request_data2ui r1 = request_data2ui r2
      -> RequestData2HashData r1 = RequestData2HashData r2
      -> minbft_data_rdata r1 = minbft_data_rdata r2.
  Proof.
    introv h q.
    destruct r1 as [v1 r1 ui1], r2 as [v2 r2 ui2]; simpl in *; subst.
    unfold RequestData2HashData in *; ginv; auto.
  Qed.



  (* === INSTANTIATION OF ComponentTrust === *)

  Definition auth_data2ui (a : AuthenticatedData) : list UI :=
    match a with
    | MkAuthData (MinBFT_msg_bare_prepare _ pui) [d] => [Build_UI pui d]
    | MkAuthData (MinBFT_msg_bare_commit  c pui) [d] => [bare_commit_ui c, Build_UI pui d]
    | _ => []
    end.

  Definition USIG_output_interface2ui (o : USIG_output_interface) : option UI :=
    match o with
    | create_ui_out ui => ui
    | verify_ui_out b => None
    | verify_ui_out_def => None
    end.

  Global Instance MinBFT_I_ComponentTrust : ComponentTrust :=
    MkComponentTrust
      UI
      auth_data2ui
      USIG_output_interface2ui
      ui2rep.

  (* === ======================== === *)

End MinBFTkn0.
