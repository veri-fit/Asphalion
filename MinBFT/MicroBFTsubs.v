Require Export MicroBFT.
(*Require Export MicroBFTtacts.*)
(*Require Export MicroBFTbreak. *)
Require Export ComponentAxiom.
Require Export ComponentSM3.
Require Export ComponentSM6.
Require Export ComponentSM9.


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

  Lemma are_procs_MicroBFTls : forall n, are_procs_n_procs (MicroBFTlocalSys n).
  Proof.
    introv; simpl;
      try (complete (eexists; introv; unfold proc2upd; simpl; try reflexivity));
      try (complete (introv i; simpl in *; repndors; subst; tcsp; simpl;
                     eexists; introv; unfold proc2upd;  reflexivity)).
  Qed.
  Hint Resolve are_procs_MicroBFTls : microbft.

  Lemma wf_MicroBFTls : forall n, wf_procs (MicroBFTlocalSys n).
  Proof.
    repeat introv; unfold wf_procs; simpl;
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

  Lemma similar_microbft_subs_new_implies_subs :
    forall (subs : n_procs 1) a b,
      similar_subs subs (MicroBFTsubs_new a b)
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
    destruct a1; simpl in *; subst; tcsp.
    unfold MicroBFTsubs_new, build_m_sm, build_mp_sm, at2sm; simpl; eauto.
  Qed.

  Lemma similar_sms_at_microbft_replica :
    forall r (p : n_proc 2 _),
      similar_sms p (MAIN_comp r)
      -> exists s, p = MicroBFT_replicaSM_new r s.
  Proof.
    introv sim.
    destruct p; simpl in *; tcsp.
    unfold similar_sms_at in *; repnd; simpl in *; subst.
    destruct a as [upd st]; simpl in *; subst; simpl in *.
    exists st; auto.
  Qed.

  Lemma similar_procs_MAIN :
    forall r p,
      similar_procs (MkPProc MAINname (MAIN_comp r)) p
      -> exists s, p = MkPProc MAINname (MicroBFT_replicaSM_new r s).
  Proof.
    introv sim.
    inversion sim as [? ? ? ? sims]; clear sim; subst.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
    apply similar_sms_sym in sims.
    apply similar_sms_at_microbft_replica in sims; exrepnd; subst; eauto.
  Qed.

  Lemma similar_subs_MicroBFTlocalSys_implies :
    forall r (ls : n_procs 2),
      similar_subs (MicroBFTlocalSys r) ls
      -> exists s s1 s2, ls = MicroBFTlocalSys_new r s s1 s2.
  Proof.
    introv sim.
    inversion sim; clear sim; subst; simpl in *.
    pose proof (similar_subs_incr_n_procs_left_implies (MicroBFTsubs r) ps2) as q.
    simpl in *; apply q in sims; clear q; exrepnd; subst.
    apply similar_subs_sym in sims0; apply similar_microbft_implies_subs in sims0; exrepnd; subst.
    apply similar_procs_MAIN in simp; exrepnd; subst; simpl in *.
    exists s s1 s2; auto.
  Qed.

  (* We can also prove some preservation lemmas:
       for example that the replica field in the USIG does not change *)
  Lemma M_run_ls_before_event_ls_is_microbft :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : MicroBFT_node)
           (ls : LocalSystem 2 0),
      M_run_ls_before_event (MicroBFTlocalSys r) e = Some ls
      ->
      exists (s : MAIN_state) (s1 : USIG_state) (s2 : LOG_state),
        ls = MicroBFTlocalSys_new r s s1 s2.
  Proof.
    introv run.
    apply M_run_ls_before_event_preserves_subs in run; eauto 3 with comp microbft.
    repnd; simpl in *.
    apply similar_subs_MicroBFTlocalSys_implies in run2; auto.
  Qed.

  Lemma M_run_ls_on_event_ls_is_microbft :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : MicroBFT_node)
           (ls : LocalSystem 2 0),
      M_run_ls_on_event (MicroBFTlocalSys r) e = Some ls
      ->
      exists (s : MAIN_state) (s1 : USIG_state) (s2 : LOG_state),
        ls = MicroBFTlocalSys_new r s s1 s2.
  Proof.
    introv run.
    apply M_run_ls_on_event_preserves_subs in run; eauto 3 with comp microbft.
    repnd; simpl in *.
    apply similar_subs_MicroBFTlocalSys_implies in run2; auto.
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

  (*Lemma trusted_run_sm_on_inputs_usig :
    forall s n l,
      trusted_run_sm_on_inputs s (USIG_comp n) l
      = Some (run_sm_on_inputs_trusted (USIG_sm_new s) l).
  Proof.
    tcsp.
  Qed.*)

  (*Lemma run_sm_on_inputs_trusted_usig_preserves_id :
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
  Qed.*)

  Lemma similar_sms_at_log :
    forall s p,
      similar_sms_at (build_mp_sm LOG_update s) p
      <-> exists s', p = build_mp_sm LOG_update s'.
  Proof.
    introv; split; intro h; exrepnd; subst; eauto; tcsp;[].
    inversion h; subst.
    destruct p as [up st]; simpl in *; subst; eauto.
    exists st; auto.
  Qed.
  Hint Rewrite similar_sms_at_log : microbft.

  Lemma similar_sms_at_usig :
    forall s p,
      similar_sms_at (build_mp_sm USIG_update s) p
      <-> exists s', p = build_mp_sm USIG_update s'.
  Proof.
    introv; split; intro h; exrepnd; subst; eauto; tcsp.
    inversion h; subst.
    destruct p as [up st]; simpl in *; subst; eauto.
    exists st; auto.
  Qed.
  Hint Rewrite similar_sms_at_usig : microbft.

  Lemma procs2byz_MicroBFTlocalSys :
    forall r, procs2byz (MicroBFTlocalSys r) = [MkPProc USIGname (incr_n_proc (USIG_comp r))].
  Proof.
    tcsp.
  Qed.
  Hint Rewrite procs2byz_MicroBFTlocalSys : microbft.

  Lemma M_byz_run_ls_before_event_ls_is_microbft :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : MicroBFT_node)
           (ls : LocalSystem 2 0),
      M_byz_run_ls_before_event (MicroBFTlocalSys r) e = ls
      ->
      (
        (exists (s : MAIN_state) (u : USIG_state) (l : LOG_state),
            ls = MicroBFTlocalSys_new r s u l)
        \/
        (exists (u : USIG_state),
            ls = [MkPProc USIGname (incr_n_proc (build_m_sm USIG_update u))])
      ).
  Proof.
    introv run.
    apply M_byz_run_ls_before_event_preserves_subs_byz2 in run; eauto 3 with microbft comp;[].
    repnd; autorewrite with microbft in *.
    repndors.

    { apply similar_subs_MicroBFTlocalSys_implies in run; exrepnd; subst; eauto. }

    { inversion run; subst; clear run.
      inversion sims; subst; clear sims.
      applydup @similar_procs_implies_same_name in simp; simpl in *.
      destruct p2; simpl in *; subst; simpl in *.
      apply @similar_procs_implies_same_proc in simp.
      destruct pp_proc; simpl in *; tcsp;[].
      destruct b; simpl in *; subst; simpl in *; tcsp;[].
      unfold similar_sms_at in *; repnd; simpl in *; subst; tcsp.
      destruct a; simpl in *; subst; tcsp.
      right.
      exists sm_state; auto. }
  Qed.

  Lemma on_comp_sing_eq :
    forall {n} {cn} (p : n_proc n cn) {cn'} {A} (F : n_proc n cn' -> A) (a : A),
      on_comp [MkPProc cn p] F a
      = match CompNameDeq cn cn' with
        | left x => F (eq_rect _ _ p _ x)
        | right _ => a
        end.
  Proof.
    introv; unfold on_comp; simpl; repeat dest_cases w.
  Qed.

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
Hint Rewrite @procs2byz_MicroBFTlocalSys : microbft.
