Require Export MicroBFT.
(*
Require Export MicroBFTtacts.
Require Export MicroBFTbreak. *)
Require Export ComponentAxiom.
Require Export ComponentSM3.


Section MicroBFTsubs.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context      : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth         : MicroBFT_auth         }.



  (* this is the same as [is_replica] for Microbft *)
  Definition is_backup {eo : EventOrdering} (e : Event) :=
    (loc e = MicroBFT_backup1) \/ (loc e = MicroBFT_backup2).


  Lemma local_pred_preserves_is_replica :
    forall {eo : EventOrdering} (e1 e2 : Event),
      e1 ⊂ e2
      -> is_backup e2
      -> is_backup e1.
  Proof.
    introv lte isrep.
    unfold is_backup in *; destruct isrep as [H|H]; try(complete (rewrite <- H; eauto 3 with eo)).
  Qed.
  Hint Resolve local_pred_preserves_is_replica : microbft.

  Lemma are_procs_MicroBFTls : forall n, are_procs_ls (MicroBFTlocalSys n).
  Proof.
    introv; simpl; split; simpl;
      try (complete (eexists; introv; unfold proc2upd; simpl; try reflexivity));
      try (complete (introv i; simpl in *; repndors; subst; tcsp; simpl;
                     eexists; introv; unfold proc2upd;  reflexivity)).
  Qed.
  Hint Resolve are_procs_MicroBFTls : microbft.

  Lemma wf_MicroBFTls : forall n, wf_ls (MicroBFTlocalSys n).
  Proof.
    repeat introv; unfold wf_ls, wf_procs; simpl;
      dands; try (complete (introv xx; repndors; tcsp; ginv));
        repeat constructor; simpl; tcsp;
          try (complete (introv xx; repndors; tcsp; ginv)).
  Qed.
  Hint Resolve wf_MicroBFTls : microbft.

  Lemma are_procs_MicroBFTsys : are_procs_sys MicroBFTsys.
  Proof.
    introv; destruct n; simpl; eauto 3 with comp microbft.
  Qed.
  Hint Resolve are_procs_MicroBFTsys : microbft.

  Lemma wf_MicroBFTsys : wf_sys MicroBFTsys.
  Proof.
    introv; destruct n; simpl; eauto 3 with comp microbft.
  Qed.
  Hint Resolve wf_MicroBFTsys : microbft.

  Lemma MicroBFTsys_preserves_subs :
    sys_preserves_subs MicroBFTsys.
  Proof.
    introv; eauto 3 with comp microbft.
  Qed.
  Hint Resolve MicroBFTsys_preserves_subs : microbft.

  Lemma similar_microbft_implies_subs :
    forall (subs : n_procs 1) r,
      similar_subs subs (MicroBFTsubs r)
      -> exists (s1 : USIG_state) (s2 : LOG_state),
        subs = MicroBFTsubs_new s1 s2.
  Proof.
    introv sim.
    inversion sim; subst; clear sim.
    inversion sims; subst; clear sims.
    inversion sims0; subst; clear sims0.
    applydup @similar_procs_implies_same_name in simp; simpl in *.
    applydup @similar_procs_implies_same_name in simp0; simpl in *.
    destruct p1, p0; simpl in *; subst; simpl in *.
    destruct pp_proc, pp_proc0; simpl in *; tcsp;[].
    apply @similar_procs_implies_same_proc in simp.
    apply @similar_procs_implies_same_proc in simp0.
    simpl in *; repnd; subst.
    destruct a, a0; simpl in *; subst; simpl in *; tcsp;[].
    unfold similar_sms_at in *; repnd; simpl in *; subst; tcsp.
    unfold MicroBFTsubs_new, build_m_sm, build_mp_sm, at2sm; simpl; eauto.
  Qed.

  Lemma similar_sms_at_microbft_replica :
    forall r (p : n_proc_at 1 _),
      similar_sms_at p (MAIN_comp r)
      -> exists s, p = MicroBFT_replicaSM_new r s.
  Proof.
    introv sim.
    unfold similar_sms_at in *; repnd; simpl in *; subst.
    destruct p as [h upd st]; simpl in *; subst; simpl in *.
    exists st; auto.
  Qed.

  (* We can also prove some preservation lemmas:
       for example that the replica field in the USIG does not change *)
  Lemma M_run_ls_before_event_ls_is_microbft :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : MicroBFT_node)
           (ls : MicroBFTls),
      M_run_ls_before_event (MicroBFTlocalSys r) e = Some ls
      ->
      exists (s : MAIN_state) (s1 : USIG_state) (s2 : LOG_state),
        ls = MicroBFTlocalSys_new r s s1 s2.
  Proof.
    introv run.
    apply M_run_ls_before_event_preserves_subs in run; eauto 3 with comp microbft.
    repnd; simpl in *.
    destruct ls as [main subs]; simpl in *.

    apply similar_subs_sym in run3.
    apply similar_microbft_implies_subs in run3; exrepnd; subst.
    apply similar_sms_at_sym in run2.
    apply similar_sms_at_microbft_replica in run2; exrepnd; subst.
    eexists; eexists; eexists; try reflexivity.
  Qed.

  Lemma M_run_ls_on_event_ls_is_microbft :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : MicroBFT_node)
           (ls : MicroBFTls),
      M_run_ls_on_event (MicroBFTlocalSys r) e = Some ls
      ->
      exists (s : MAIN_state) (s1 : USIG_state) (s2 : LOG_state),
        ls = MicroBFTlocalSys_new r s s1 s2.
  Proof.
    introv run.
    apply M_run_ls_on_event_preserves_subs in run; eauto 3 with comp microbft.
    repnd; simpl in *.
    destruct ls as [main subs]; simpl in *.

    apply similar_subs_sym in run3.
    apply similar_microbft_implies_subs in run3; exrepnd; subst.
    apply similar_sms_at_sym in run2.
    apply similar_sms_at_microbft_replica in run2; exrepnd; subst.
    eexists; eexists; eexists; try reflexivity.
  Qed.

  Lemma similar_microbft_implies_level :
    forall r {n} (subs : n_procs n),
      similar_subs subs (MicroBFTsubs r)
      -> n = 1.
  Proof.
    introv sim.
    applydup @similar_subs_implies_same_level in sim; auto.
    destruct subs; simpl in *; auto; try omega.
    inversion sim.
  Qed.

  Lemma implies_similar_subs_MicroBFTsubs_new :
    forall s1 s2 s3 s4,
      similar_subs (MicroBFTsubs_new s1 s2) (MicroBFTsubs_new s3 s4).
  Proof.
    introv.
    repeat constructor.
  Qed.
  Hint Resolve implies_similar_subs_MicroBFTsubs_new : microbft.

  Lemma is_trusted_ls_usig :
    forall n, is_trusted_ls USIGname (MicroBFTlocalSys n).
  Proof.
    introv; tcsp.
  Qed.
  Hint Resolve is_trusted_ls_usig : microbft.

  Definition USIG_sm_new s :=
    build_m_sm USIG_update s.

  Lemma trusted_run_sm_on_inputs_usig :
    forall s n l,
      trusted_run_sm_on_inputs s (USIG_comp n) l
      = Some (run_sm_on_inputs_trusted (USIG_sm_new s) l).
  Proof.
    tcsp.
  Qed.

  Lemma run_sm_on_inputs_trusted_usig_preserves_id :
    forall l s,
      usig_id (run_sm_on_inputs_trusted (USIG_sm_new s) l) = usig_id s.
  Proof.
    induction l; introv; simpl in *; tcsp;[].
    pose proof (run_sm_on_inputs_trusted_cons _ _ _ (USIG_sm_new s) a l) as xx.
    simpl in *; rewrite xx; auto; clear xx.
    remember (fst (snd (USIG_update s a []))) as w; symmetry in Heqw.
    unfold update_state_op_m; dest_cases z; symmetry in Heqz.
    rewrite IHl.

    unfold USIG_update in Heqz.
    destruct a; simpl in *; repnd; simpl in *; inversion Heqz; simpl in *; auto.
  Qed.

  Lemma similar_sms_at_log :
    forall s p,
      similar_sms_at (build_mp_sm LOG_update s) p
      <-> exists s', p = build_mp_sm LOG_update s'.
  Proof.
    introv; split; intro h; exrepnd; subst; eauto.

    { inversion h; subst.
      destruct p as [ha up st]; simpl in *; subst; eauto.
      exists st; auto. }

    { constructor; auto. }
  Qed.
  Hint Rewrite similar_sms_at_log : microbft.

  Lemma similar_sms_at_usig :
    forall s p,
      similar_sms_at (build_mp_sm USIG_update s) p
      <-> exists s', p = build_mp_sm USIG_update s'.
  Proof.
    introv; split; intro h; exrepnd; subst; eauto.

    { inversion h; subst.
      destruct p as [ha up st]; simpl in *; subst; eauto.
      exists st; auto. }

    { constructor; auto. }
  Qed.
  Hint Rewrite similar_sms_at_usig : microbft.

End MicroBFTsubs.


Hint Resolve local_pred_preserves_is_replica : microbft.
Hint Resolve are_procs_MicroBFTls : microbft.
Hint Resolve wf_MicroBFTls : microbft.
Hint Resolve are_procs_MicroBFTsys : microbft.
Hint Resolve wf_MicroBFTsys : microbft.
Hint Resolve MicroBFTsys_preserves_subs : microbft.
Hint Resolve implies_similar_subs_MicroBFTsubs_new : microbft.
Hint Resolve is_trusted_ls_usig : microbft.


Hint Rewrite @similar_sms_at_log : microbft.
Hint Rewrite @similar_sms_at_usig : microbft.
