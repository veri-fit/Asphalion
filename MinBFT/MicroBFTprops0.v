Require Export MicroBFTkn.


Hint Rewrite orb_false_r : bool.



Section MicroBFTprops0.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { microbft_context      : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { microbft_auth         : MicroBFT_auth         }.



  Lemma same_request_deq :
    forall {T} r (a b : T),
      (if Request_dec r r then a else b) = a.
  Proof.
    introv; smash_microbft.
  Qed.
  Hint Rewrite @same_request_deq : microbft.

  Lemma find_ui_implies_ui_in_log :
    forall r l,
      in_log r l
      -> ui_in_log (commit_ui r) l = true.
  Proof.
    induction l; introv h; simpl in *; ginv; smash_microbft.
    repndors; subst; tcsp;[].
    clear IHl.
    left.

    unfold ui_in_log_entry in *. simpl in *; smash_microbft.
  Qed.
  Hint Resolve find_ui_implies_ui_in_log : microbft.


  Lemma ui_in_log_log_new_request :
    forall (ui : UI) (r : Commit) (l : LOG_state),
      ui_in_log ui (r :: l)
      = if UI_dec ui (commit_ui r) then true
        else ui_in_log ui l.
  Proof.
    induction l; simpl; autorewrite with bool; tcsp;[].

    smash_microbft;[ destruct IHl;[|]; dands; eauto|].

    pose proof (orb_comm (ui_in_log_entry ui a) (ui_in_log ui l)) as xx.
    rewrite xx. clear xx.

    rewrite orb_assoc.
    rewrite IHl. eauto.
  Qed.


  Lemma hash_data_in_log_log_new_request :
    forall (hd : HashData) (r : Commit) (l : LOG_state),
      hash_data_in_log hd (r :: l)
      = if HashData_Deq hd (Request2HashData r) then true
        else hash_data_in_log hd l.
  Proof.
    induction l; simpl; autorewrite with bool; tcsp;[].

    smash_microbft;[destruct IHl; dands; eauto|].

    pose proof (orb_comm (hash_data_in_log_entry hd a) (hash_data_in_log hd  l)) as xx.
    rewrite xx. clear xx.

    rewrite orb_assoc.
    rewrite IHl. eauto.
  Qed.

  Lemma not_over_or: forall a b : Prop, ~ (a \/ b) <-> ~ a /\ ~ b.
  Proof.
    introv; split; intro h; repnd; tcsp.
  Qed.

  Lemma Build_HashData_eq_request2hash_data :
    forall r,
      Build_HashData (commit_n r) (commit_ui r)
      = Request2HashData r.
  Proof.
    destruct r as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite Build_HashData_eq_request2hash_data : microbft.

  (*
  Lemma find_entry_log_new_prepare :
    forall (rd : RequestData) (p : Prepare) (l : LOG_state),
      find_entry rd (log_new_prepare p l)
      = match find_entry rd l with
        | Some e => Some e
        | None =>
          if RequestData_Deq rd (prepare2request_data p)
          then Some (MkNewLogEntryFromPrepare p)
          else None
        end.
  Proof.
    induction l; simpl; smash_minbft.
  Qed.
   *)

  Lemma in_microbft_data_ui_request2ui_MicroBFT_auth2data_request2auth_data :
    forall r,
      In (microbft_data_ui (commit_ui r))
         (MicroBFT_auth2data (commit2auth_data r)).
  Proof.
    introv.
    destruct r. simpl in *.
    destruct commit_ui. simpl in *.
    right. left. eauto.
  Qed.
  Hint Resolve in_microbft_data_ui_request2ui_MicroBFT_auth2data_request2auth_data : microbft.

  Definition request2digest (r : Commit) : MicroBFT_digest :=
    ui2digest (commit_ui r).

  Definition request2pre_ui (p : Commit) : preUI :=
    ui_pre (commit_ui p).

  Lemma request2auth_data_eq :
    forall r,
      commit2auth_data r
      = MkAuthData
          (MicroBFT_msg_bare_request (commit_n r) (request2pre_ui r))
          [request2digest r].
  Proof.
    introv.
    destruct r as [b ui]; simpl; tcsp.
  Qed.

  Lemma build_ui_decomp_request_eq :
    forall r,
      Build_UI (request2pre_ui r) (request2digest r) = commit_ui r.
  Proof.
    destruct r as [b ui], ui; simpl; auto.
  Qed.
  Hint Rewrite build_ui_decomp_request_eq : microbft.

  Lemma const_opTrust :
    forall {t a},
      In (microbft_data_ui t) (MicroBFT_auth2data a)
      -> opTrust a.
  Proof.
    introv i.
    exists (Some t); simpl.
    pose proof (kc_auth2trust_correct a t) as q; apply q.
    exists (microbft_data_ui t); simpl; tcsp.
  Defined.
  Hint Resolve const_opTrust : microbft.

  Lemma in_MicroBFT_get_contained_auth_data_implies_is_protocol :
    forall a m,
      In a (MicroBFT_get_contained_auth_data m)
      -> is_protocol_message m = true.
  Proof.
    introv i; simpl in *.
    unfold is_protocol_message.
    destruct m; simpl in *; eauto.
  Qed.
  Hint Resolve in_MicroBFT_get_contained_auth_data_implies_is_protocol : microbft.

  Lemma request2ui_in_request2auth_data :
    forall r,
      In (microbft_data_ui (commit_ui r)) (MicroBFT_auth2data (commit2auth_data r)).
  Proof.
    destruct r as [b ui], ui as [pui d]; simpl; tcsp.
  Qed.
  Hint Resolve request2ui_in_request2auth_data : microbft.


  Lemma ui2rep_request2ui_eq :
    forall r,
      ui2rep (commit_ui r) = pre_ui_id (commit_ui r).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite ui2rep_request2ui_eq : microbft.


  Lemma upd_ls_main_state_and_subs_MicroBFTlocalSys_new :
    forall n s u l s' u' l',
      upd_ls_main_state_and_subs (MicroBFTlocalSys_new n s u l) s' (MicroBFTsubs_new u' l')
      = MicroBFTlocalSys_new n s' u' l'.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite upd_ls_main_state_and_subs_MicroBFTlocalSys_new : microbft.

  Lemma state_of_subcomponents_MicroBFTsubs_USIGname :
    forall r,
      state_of_subcomponents (MicroBFTsubs r) USIGname
      = Some (USIG_initial r).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MicroBFTsubs_USIGname : microbft.

  Lemma state_of_subcomponents_MicroBFTsubs_new_USIGname :
    forall s l,
      state_of_subcomponents (MicroBFTsubs_new s l) USIGname
      = Some s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MicroBFTsubs_new_USIGname : microbft.

  Lemma state_of_subcomponents_MicroBFTsubs_LOGname :
    forall r,
      state_of_subcomponents (MicroBFTsubs r) LOGname
      = Some LOG_initial.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MicroBFTsubs_LOGname : microbft.

  Lemma state_of_subcomponents_MicroBFTsubs_new_LOGname :
    forall s l,
      state_of_subcomponents (MicroBFTsubs_new s l) LOGname
      = Some l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MicroBFTsubs_new_LOGname : microbft.

  Lemma state_of_subcomponents_MicroBFTsubs_new_u_LOGname :
    forall u,
      state_of_subcomponents (MicroBFTsubs_new_u u) LOGname
      = Some LOG_initial.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MicroBFTsubs_new_u_LOGname : microbft.

  Lemma state_of_subcomponents_MicroBFTsubs_new_u_USIGname :
    forall u,
      state_of_subcomponents (MicroBFTsubs_new_u u) USIGname
      = Some u.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MicroBFTsubs_new_u_USIGname : microbft.

  Lemma upd_ls_main_state_and_subs_MicroBFTlocalSys :
    forall n s u l,
      upd_ls_main_state_and_subs (MicroBFTlocalSys n) s (MicroBFTsubs_new u l)
      = MicroBFTlocalSys_new n s u l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite upd_ls_main_state_and_subs_MicroBFTlocalSys : microbft.

  Lemma state_of_component_MicroBFTlocalSys_new_LOGname :
    forall n s u l,
      state_of_component LOGname (MicroBFTlocalSys_new n s u l)
      = Some l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_component_MicroBFTlocalSys_new_LOGname : microbft.

  Lemma state_of_component_MicroBFTlocalSys_new_USIGname :
    forall n s u l,
      state_of_component USIGname (MicroBFTlocalSys_new n s u l)
      = Some u.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_component_MicroBFTlocalSys_new_USIGname : microbft.

  Lemma request_in_log_log_new :
    forall rd r l,
      request_in_log rd (r :: l)
      = if Request_dec rd r
        then true
        else request_in_log rd l.
  Proof.
    introv.
    unfold request_in_log; smash_microbft.
    repndors; subst; tcsp.
  Qed.
  Hint Rewrite request_in_log_log_new : microbft.

  Lemma ui2rep_Build_UI :
    forall pui d,
      ui2rep (Build_UI pui d) = pre_ui_id pui.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite ui2rep_Build_UI : microbft.


  Lemma request_in_log_cons :
    forall rd entry entries,
      request_in_log rd (entry :: entries)
      = if Request_dec rd entry
        then true
        else request_in_log rd entries.
  Proof.
    introv; unfold request_in_log; simpl; smash_microbft.
    repndors; subst; tcsp.
  Qed.
  Hint Rewrite request_in_log_cons : microbft.


  Lemma send_by_primary_implies_MicroBFT_primary:
    forall r,
      is_primary (commit2sender r) = true
      -> pre_ui_id (commit_ui r) = MicroBFT_primary.
  Proof.
    introv H.
    unfold is_primary in *. smash_microbft.
  Qed.
  Hint Resolve send_by_primary_implies_MicroBFT_primary : minbft.

End MicroBFTprops0.


Hint Resolve find_ui_implies_ui_in_log : microbft.
Hint Resolve in_microbft_data_ui_request2ui_MicroBFT_auth2data_request2auth_data : microbft.
Hint Resolve const_opTrust : microbft.
Hint Resolve in_MicroBFT_get_contained_auth_data_implies_is_protocol : microbft.
Hint Resolve request2ui_in_request2auth_data : microbft.
Hint Resolve send_by_primary_implies_MicroBFT_primary : minbft.



Hint Rewrite @same_request_deq : microbft.
Hint Rewrite @Build_HashData_eq_request2hash_data : microbft.
Hint Rewrite @build_ui_decomp_request_eq : microbft.
Hint Rewrite @ui2rep_request2ui_eq : microbft.
Hint Rewrite @upd_ls_main_state_and_subs_MicroBFTlocalSys_new : microbft.
Hint Rewrite @state_of_subcomponents_MicroBFTsubs_USIGname : microbft.
Hint Rewrite @state_of_subcomponents_MicroBFTsubs_new_USIGname : microbft.
Hint Rewrite @state_of_subcomponents_MicroBFTsubs_LOGname : microbft.
Hint Rewrite @state_of_subcomponents_MicroBFTsubs_new_LOGname : microbft.
Hint Rewrite @state_of_subcomponents_MicroBFTsubs_new_u_LOGname : microbft.
Hint Rewrite @state_of_subcomponents_MicroBFTsubs_new_u_USIGname : microbft.
Hint Rewrite @upd_ls_main_state_and_subs_MicroBFTlocalSys : microbft.
Hint Rewrite @state_of_component_MicroBFTlocalSys_new_LOGname : microbft.
Hint Rewrite @state_of_component_MicroBFTlocalSys_new_USIGname : microbft.
Hint Rewrite @request_in_log_log_new : microbft.
Hint Rewrite @ui2rep_Build_UI : microbft.
Hint Rewrite @request_in_log_cons : microbft.
