Require Export MinBFTprops2.
Require Export MinBFTtacts2.


Section MinBFTsame.

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
      -> usig_id s1 = usig_id u1.
  Proof.
    introv h.
    apply map_option_Some in h; exrepnd; rev_Some; simpl in *; minbft_simp.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input in *; simpl in *; autorewrite with minbft in *.

    Time minbft_dest_msg Case;
      repeat(simpl in *; autorewrite with minbft in *; smash_minbft2).
  Qed.

  Lemma usig_step_same_keys :
    forall {eo : EventOrdering} (e : Event) r t s s1 s2 u u1 u2,
      M_run_ls_on_this_one_event (MinBFTlocalSys_new r s s1 s2) e
      = Some (MinBFTlocalSys_new t u u1 u2)
      -> usig_local_keys s1 = usig_local_keys u1.
  Proof.
    introv h.
    apply map_option_Some in h; exrepnd; rev_Some; simpl in *; minbft_simp.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input in *; simpl in *; autorewrite with minbft in *.

    Time minbft_dest_msg Case;
      repeat(simpl in *; autorewrite with minbft in *; smash_minbft2).
  Qed.

  Lemma usig_same_keys :
    forall {eo : EventOrdering} (e : Event) r t s s1 s2,
      M_run_ls_before_event (MinBFTlocalSys r) e
      = Some (MinBFTlocalSys_new t s s1 s2)
      -> usig_local_keys s1 = usig_initial_keys (usig_id s1).
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
      -> usig_id s1 = r.
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
      -> usig_local_keys s1 = usig_initial_keys (usig_id s1).
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
      -> usig_id s1 = r.
  Proof.
    introv h.
    rewrite M_run_ls_on_event_unroll2 in h.
    apply map_option_Some in h; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbft in h1; exrepnd; subst.
    apply usig_same_id in h1.
    apply usig_step_same_id in h0; try congruence.
  Qed.

  (* MOVE to ComponentSM2 *)
  Lemma M_run_ls_on_event_empty_ls :
    forall {eo : EventOrdering} (e : Event) l s ls,
      M_run_ls_on_event (empty_ls l s) e = Some ls
      -> ls = empty_ls l s.
  Proof.
    introv h.
    rewrite M_run_ls_on_event_unroll2 in h.
    apply map_option_Some in h; exrepnd; rev_Some.
    apply M_run_ls_before_event_empty_ls in h1; subst; simpl in *.
    apply map_option_Some in h0; exrepnd; rev_Some; ginv.
    inversion h1; subst; simpl in *; tcsp.
  Qed.

  Lemma state_usig_same_keys :
    forall {eo : EventOrdering} (e : Event) s,
      M_state_sys_on_event MinBFTsys e USIGname = Some s
      -> usig_local_keys s = usig_initial_keys (loc e).
  Proof.
    introv h.
    apply map_option_Some in h; exrepnd; rev_Some.
    remember (loc e) as x; destruct x; simpl in *; tcsp;
      [|apply M_run_ls_on_event_empty_ls in h1; subst; simpl in *; inversion h0];[].
    applydup M_run_ls_on_event_ls_is_minbft in h1; exrepnd; subst.
    applydup usig_same_id_on in h1.
    apply usig_same_keys_on in h1.
    simpl in *.
    unfold state_of_component in h0; simpl in *; ginv.
  Qed.

End MinBFTsame.
