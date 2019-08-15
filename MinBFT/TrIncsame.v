Require Export TrIncprops2.
Require Export TrInctacs.


Section TrIncsame.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { microbft_context    : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { microbft_auth       : MinBFT_auth         }.


  Lemma usig_step_same_id :
    forall {eo : EventOrdering} (e : Event) r t s s1 s2 u u1 u2,
      M_run_ls_on_this_one_event (MinBFTlocalSys_new r s s1 s2) e
      = Some (MinBFTlocalSys_new t u u1 u2)
      -> trinc_id s1 = trinc_id u1.
  Proof.
    introv h.
    apply map_option_Some in h; exrepnd; rev_Some; simpl in *.

    Time minbft_dest_msg Case;
      repeat(simpl in *; autorewrite with minbft in *; smash_minbft2).
  Qed.

  Lemma trinc_local_keys_try_update_TRINC :
    forall cid c1 c2 s,
      trinc_local_keys (try_update_TRINC cid c1 c2 s)
      = trinc_local_keys s.
  Proof.
    introv; unfold try_update_TRINC; smash_minbft2.
  Qed.
  Hint Resolve trinc_local_keys_try_update_TRINC : minbft.

  Lemma usig_step_same_keys :
    forall {eo : EventOrdering} (e : Event) r t s s1 s2 u u1 u2,
      M_run_ls_on_this_one_event (MinBFTlocalSys_new r s s1 s2) e
      = Some (MinBFTlocalSys_new t u u1 u2)
      -> trinc_local_keys s1 = trinc_local_keys u1.
  Proof.
    introv h.
    apply map_option_Some in h; exrepnd; rev_Some; simpl in *.

    Time minbft_dest_msg Case;
      repeat(simpl in *; autorewrite with minbft in *; smash_minbft2).
  Qed.

  Lemma usig_same_keys :
    forall {eo : EventOrdering} (e : Event) r t s s1 s2,
      M_run_ls_before_event (MinBFTlocalSys r) e
      = Some (MinBFTlocalSys_new t s s1 s2)
      -> trinc_local_keys s1 = usig_initial_keys (trinc_id s1).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_run_ls_before_event_unroll in h.
    destruct (dec_isFirst e); ginv; auto; smash_minbft2;[].

    apply map_option_Some in h; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbft in h1; exrepnd; subst.
    eapply ind in h1; eauto 3 with eo;[].
    applydup usig_step_same_keys in h0.
    applydup usig_step_same_id in h0.
    try congruence.
  Qed.

  Lemma usig_same_id :
    forall {eo : EventOrdering} (e : Event) r t s s1 s2,
      M_run_ls_before_event (MinBFTlocalSys r) e
      = Some (MinBFTlocalSys_new t s s1 s2)
      -> trinc_id s1 = r.
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_run_ls_before_event_unroll in h.
    destruct (dec_isFirst e); ginv; auto; smash_minbft2;[].

    apply map_option_Some in h; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbft in h1; exrepnd; subst.
    eapply ind in h1; eauto 3 with eo;[].
    applydup usig_step_same_id in h0.
    try congruence.
  Qed.

  Lemma usig_same_keys_on :
    forall {eo : EventOrdering} (e : Event) r t s s1 s2,
      M_run_ls_on_event (MinBFTlocalSys r) e
      = Some (MinBFTlocalSys_new t s s1 s2)
      -> trinc_local_keys s1 = usig_initial_keys (trinc_id s1).
  Proof.
    introv h.
    rewrite M_run_ls_on_event_unroll2 in h.
    apply map_option_Some in h; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbft in h1; exrepnd; subst.
    apply usig_same_keys in h1.
    applydup usig_step_same_keys in h0.
    apply usig_step_same_id in h0; try congruence.
  Qed.

  Lemma usig_same_id_on :
    forall {eo : EventOrdering} (e : Event) r t s s1 s2,
      M_run_ls_on_event (MinBFTlocalSys r) e
      = Some (MinBFTlocalSys_new t s s1 s2)
      -> trinc_id s1 = r.
  Proof.
    introv h.
    rewrite M_run_ls_on_event_unroll2 in h.
    apply map_option_Some in h; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbft in h1; exrepnd; subst.
    apply usig_same_id in h1.
    apply usig_step_same_id in h0; try congruence.
  Qed.

  Lemma state_usig_same_keys :
    forall {eo : EventOrdering} (e : Event) s,
      M_state_sys_on_event MinBFTsys e USIGname = Some s
      -> trinc_local_keys s = usig_initial_keys (loc e).
  Proof.
    introv h.
    apply map_option_Some in h; exrepnd; rev_Some.
    remember (loc e) as x; destruct x; simpl in *; tcsp;
      [|apply M_run_ls_on_event_unit_ls in h1; subst; simpl in *; inversion h0];[].
    applydup M_run_ls_on_event_ls_is_minbft in h1; exrepnd; subst.
    applydup usig_same_id_on in h1.
    apply usig_same_keys_on in h1.
    simpl in *.
    unfold state_of_subcomponents in h0; simpl in *; ginv.
  Qed.

End TrIncsame.

Hint Resolve trinc_local_keys_try_update_TRINC : minbft.
