Require Export TrIncprops1.
Require Export TrIncview.
Require Export MinBFTkn0.
Require Export TrInckn.


Section TrIncprops2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.



  Lemma new_bare_request_implies2 :
    forall r l t,
      new_bare_request (request_b r) l = true
      -> find_latest_executed_request (request2sender r) l = Some t
      -> t < request2timestamp r.
  Proof.
    introv.
    pose proof (new_bare_request_implies (request_b r) l t) as q.
    autorewrite with minbft in *; auto.
  Qed.

  Definition MkMinBFTtrustedSM (u : TRINC_state) : trustedSM :=
    MktrustedSM
      _ _ _
      (build_mp_sm USIG_update u).

  Lemma ex_M_byz_run_ls_on_event_MinBFTlocalSys :
    forall {eo : EventOrdering} (e : Event) n,
      (exists u, M_byz_run_ls_on_event (MinBFTlocalSys n) e = Some (M_t (MkMinBFTtrustedSM u)))
      \/ (exists s u l, M_byz_run_ls_on_event (MinBFTlocalSys n) e = Some (M_nt (MinBFTlocalSys_new n s u l))).
  Proof.
    introv.
    remember (M_byz_run_ls_on_event (MinBFTlocalSys n) e) as run; symmetry in Heqrun.

    pose proof (M_byz_compose_step2 e (MinBFTlocalSys n) (USIG_comp n)) as q.
    repeat (autodimp q hyp); eauto 3 with minbft comp;[].
    exrepnd.
    clear l q1 q0.
    unfold M_byz_state_ls_on_event in *.
    rewrite Heqrun in q2; simpl in *.
    apply map_option_Some in q2; exrepnd; subst; simpl in *.
    symmetry in q0.
    rewrite q1.

    destruct a; simpl in *; ginv.

    { right.
      apply option_map_Some in q0; exrepnd; subst; simpl in *.
      apply M_byz_run_ls_on_event_M_run_ls_on_event in q1.
      apply M_run_ls_on_event_ls_is_minbft in q1.
      exrepnd; subst.
      eexists; eexists; eexists; reflexivity. }

    { left.
      eapply M_byz_run_ls_on_event_some_M_t_implies in q1; simpl; eauto; eauto 3 with minbft.
      simpl in *; repnd.
      rewrite q0.
      exists (state_of_trusted t); auto. }
  Qed.

  Lemma ex_M_byz_state_sys_on_event_of_trusted_MinBFT :
    forall {eo : EventOrdering} (e : Event),
      ex_node_e e
      ->
      exists (u : TRINC_state),
        M_byz_state_sys_on_event_of_trusted MinBFTsys e = Some u.
  Proof.
    introv exe.
    unfold M_byz_state_sys_on_event_of_trusted; simpl.
    dup exe as exeb.
    unfold ex_node_e in exe; exrepnd; simpl in *.
    assert (loc e = MinBFT_replica n) as eqloc by (destruct (loc e); ginv; auto).
    rewrite eqloc; simpl.
    unfold M_byz_state_ls_on_event_of_trusted; simpl.

    pose proof (ex_M_byz_run_ls_on_event_MinBFTlocalSys e n) as q.
    repndors; exrepnd; rewrite q0; simpl; eauto.
    unfold state_of_trusted_in_ls; simpl; eauto.
  Qed.

  Lemma ex_M_byz_run_ls_before_event_MinBFTlocalSys :
    forall {eo : EventOrdering} (e : Event) n,
      (exists (u : TRINC_state),
          M_byz_run_ls_before_event (MinBFTlocalSys n) e = Some (M_t (MkMinBFTtrustedSM u)))
      \/
      (exists s u l,
          M_byz_run_ls_before_event (MinBFTlocalSys n) e = Some (M_nt (MinBFTlocalSys_new n s u l))).
  Proof.
    introv.
    rewrite M_byz_run_ls_before_event_unroll_on.
    destruct (dec_isFirst e) as [d|d].

    { right.
      rewrite MinBFTlocalSys_as_new.
      eexists; eexists; eexists; eauto. }

    apply ex_M_byz_run_ls_on_event_MinBFTlocalSys.
  Qed.

  Lemma MinBFT_M_byz_run_ls_on_event_unroll_sp :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : Rep),
      (exists s u l,
          M_byz_run_ls_on_event (MinBFTlocalSys r) e
          = M_byz_run_ls_on_this_one_event (MinBFTlocalSys_new r s u l) e
          /\ M_byz_run_ls_before_event (MinBFTlocalSys r) e
             = Some (M_nt ((MinBFTlocalSys_new r s u l))))
      \/
      (exists u,
          M_byz_run_ls_on_event (MinBFTlocalSys r) e
          = Some (M_t (fst (run_trustedSM_on_trigger_info (MkMinBFTtrustedSM u) (trigger e))))
          /\ M_byz_run_ls_before_event (MinBFTlocalSys r) e
             = Some (M_t (MkMinBFTtrustedSM u))).
  Proof.
    introv.
    rewrite M_byz_run_ls_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl.

    { left.
      rewrite MinBFTlocalSys_as_new.
      eexists; eexists; eexists; dands; eauto.
      rewrite M_byz_run_ls_before_event_unroll_on.
      destruct (dec_isFirst e); tcsp. }

    pose proof (ex_M_byz_run_ls_before_event_MinBFTlocalSys e r) as w.
    repndors; exrepnd; allrw; simpl.

    { right; eexists; eauto. }

    left.
    eexists; eexists; eexists; eauto.
  Qed.

  Lemma USIG_preserves_id :
    forall {eo : EventOrdering} (e : Event) n l s1 s2,
      loc e = MinBFT_replica n
      -> trinc_id s1 = n
      -> run_sm_on_inputs_trusted (USIG_sm_new s1) l = s2
      -> trinc_id s2 = n.
  Proof.
    induction l; introv eqloc eqid run; simpl in *; tcsp.

    { autorewrite with minbft in *; simpl in *; subst; tcsp. }

    pose proof (run_sm_on_inputs_trusted_cons
                  _ _ _ (USIG_sm_new s1) a l) as w.
    simpl in *; rewrite w in run; auto; clear w;[].

    unfold USIG_update in run; destruct a; repnd; simpl in *;
      [|apply IHl in run; auto];[].
    apply IHl in run; autorewrite with minbft; auto.
  Qed.

  Lemma preserves_usig_id :
    forall {eo : EventOrdering} (e : Event) n u,
      loc e = MinBFT_replica n
      -> M_byz_state_ls_on_event_of_trusted (MinBFTlocalSys n) e = Some u
      -> trinc_id u = n.
  Proof.
    intros eo; induction e as [e ind] using predHappenedBeforeInd;[]; introv eqloc eqst.

    pose proof (M_byz_compose_step_trusted e (MinBFTlocalSys n) (USIG_comp n)) as h.
    repeat (autodimp h hyp); eauto 3 with comp minbft;[].
    exrepnd.
    rewrite eqst in h2; ginv; simpl.

    pose proof (USIG_preserves_id
                  e n l s1
                  (run_sm_on_inputs_trusted (USIG_sm_new s1) l)) as q.
    repeat (autodimp q hyp).

    rewrite unroll_M_byz_state_ls_before_event_of_trusted in h1.
    destruct (dec_isFirst e) as [d|d].

    { apply option_map_Some in h1; exrepnd; subst; simpl in *.
      unfold find_trusted_sub in h1; simpl in h1; ginv. }

    apply ind in h1; autorewrite with eo; eauto 2 with eo.
  Qed.

  Lemma preserves_usig_id2 :
    forall {eo : EventOrdering} (e : Event) n ls u,
      loc e = MinBFT_replica n
      -> M_run_ls_on_event (MinBFTlocalSys n) e = Some ls
      -> state_of_component USIGname ls = Some u
      -> trinc_id u = n.
  Proof.
    introv eqloc run eqst.
    apply (preserves_usig_id e n u); auto.
    unfold M_byz_state_ls_on_event_of_trusted; simpl.
    applydup @M_run_ls_on_event_M_byz_run_ls_on_event in run as z; rewrite z; simpl.
    apply M_run_ls_on_event_ls_is_minbft in run; exrepnd; subst; simpl in *; tcsp.
  Qed.

  Lemma implies_learns_prepare2ui :
    forall {eo : EventOrdering} (e : Event) p n s u l,
      loc e = MinBFT_replica n
      -> trigger_op e = Some (MinBFT_prepare p)
      -> M_run_ls_before_event (MinBFTlocalSys n) e = Some (MinBFTlocalSys_new n s u l)
      -> verify_TrIncUI (prepare2view p) (prepare2request p) (prepare2ui p) u = true
      -> learns_data e (minbft_data_ui (prepare2ui p)).
  Proof.
    introv eqloc eqtrig runBef verif.
    exists n (prepare2auth_data p).
    simpl; allrw; simpl; dands; eauto 3 with minbft;[].
    unfold MinBFT_ca_verify.
    rewrite prepare2auth_data_eq.
    unfold M_byz_state_sys_before_event_of_trusted; simpl.
    allrw; simpl.
    unfold M_byz_state_ls_before_event_of_trusted.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    allrw; simpl.
    unfold state_of_trusted; simpl.
    autorewrite with minbft; smash_minbft.
  Qed.
  Hint Resolve implies_learns_prepare2ui : minbft.

  Lemma implies_learns_commit2ui_i :
    forall {eo : EventOrdering} (e : Event) c n s u l,
      loc e = MinBFT_replica n
      -> trigger_op e = Some (MinBFT_commit c)
      -> M_run_ls_before_event (MinBFTlocalSys n) e = Some (MinBFTlocalSys_new n s u l)
      -> verify_TrIncUI (commit2view c) (commit2request c) (commit2ui_j c) u = true
      -> verify_TrIncUI (commit2view c) (commit2request c) (commit2ui_i c) u = true
      -> learns_data e (minbft_data_ui (commit2ui_i c)).
  Proof.
    introv eqloc eqtrig runBef verifj verifi.
    exists n (commit2auth_data c).
    simpl; allrw; simpl; dands; eauto 3 with minbft;[].
    unfold MinBFT_ca_verify.
    rewrite commit2auth_data_eq.
    unfold M_byz_state_sys_before_event_of_trusted; simpl.
    allrw; simpl.
    unfold M_byz_state_ls_before_event_of_trusted.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    allrw; simpl.
    unfold state_of_trusted; simpl.
    autorewrite with minbft; smash_minbft.
  Qed.
  Hint Resolve implies_learns_commit2ui_i : minbft.

  Lemma implies_learns_commit2ui_j :
    forall {eo : EventOrdering} (e : Event) c n s u l,
      loc e = MinBFT_replica n
      -> trigger_op e = Some (MinBFT_commit c)
      -> M_run_ls_before_event (MinBFTlocalSys n) e = Some (MinBFTlocalSys_new n s u l)
      -> verify_TrIncUI (commit2view c) (commit2request c) (commit2ui_j c) u = true
      -> verify_TrIncUI (commit2view c) (commit2request c) (commit2ui_i c) u = true
      -> learns_data e (minbft_data_ui (commit2ui_j c)).
  Proof.
    introv eqloc eqtrig runBef verifj verifi.
    exists n (commit2auth_data c).
    simpl; allrw; simpl; dands; eauto 3 with minbft;[].
    unfold MinBFT_ca_verify.
    rewrite commit2auth_data_eq.
    unfold M_byz_state_sys_before_event_of_trusted; simpl.
    allrw; simpl.
    unfold M_byz_state_ls_before_event_of_trusted.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    allrw; simpl.
    unfold state_of_trusted; simpl.
    autorewrite with minbft; smash_minbft.
  Qed.
  Hint Resolve implies_learns_commit2ui_j : minbft.

End TrIncprops2.


Hint Resolve implies_learns_prepare2ui : minbft.
Hint Resolve implies_learns_commit2ui_i : minbft.
Hint Resolve implies_learns_commit2ui_j : minbft.
