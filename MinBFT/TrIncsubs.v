(* TRINC instance *)

Require Export TrInc.
Require Export TrInctacs.
Require Export TrIncbreak.
Require Export MinBFTrep.
Require Export MinBFTsim1.
Require Export ComponentAxiom.
Require Export ComponentSM3.



(* Move to ComponentSM2 *)
Hint Resolve are_procs_empty_ls : comp.
Hint Resolve wf_empty_ls : comp.


Section TrIncsubs.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.



  Definition is_replica {eo : EventOrdering} (e : Event) :=
    exists r, loc e = MinBFT_replica r.

  Lemma in_output_implies_is_replica :
    forall {eo : EventOrdering} (e : Event) o,
      In o (M_output_sys_on_event MinBFTsys e)
      -> is_replica e.
  Proof.
    introv h.
    unfold M_output_sys_on_event in *.
    unfold is_replica.
    remember (loc e) as w; destruct w; simpl in *; tcsp; eauto.
    apply not_in_M_output_ls_on_event_empty_ls in h; tcsp.
  Qed.
  Hint Resolve in_output_implies_is_replica : minbft.

  Lemma local_pred_preserves_is_replica :
    forall {eo : EventOrdering} (e1 e2 : Event),
      e1 ⊂ e2
      -> is_replica e2
      -> is_replica e1.
  Proof.
    introv lte isrep.
    unfold is_replica in *; exrepnd; exists r; rewrite <- isrep0; eauto 3 with eo.
  Qed.
  Hint Resolve local_pred_preserves_is_replica : minbft.

  Lemma are_procs_MinBFTls : forall n, are_procs_n_procs (MinBFTlocalSys n).
  Proof.
    introv; simpl;
      try (complete (eexists; introv; unfold proc2upd; simpl; try reflexivity));
      try (complete (introv i; simpl in *; repndors; subst; tcsp; simpl;
                     eexists; introv; unfold proc2upd;  reflexivity)).
  Qed.
  Hint Resolve are_procs_MinBFTls : minbft.

  Lemma wf_MinBFTls : forall n, wf_procs (MinBFTlocalSys n).
  Proof.
    repeat introv; unfold wf_procs; simpl;
      dands; try (complete (introv xx; repndors; tcsp; ginv));
        repeat constructor; simpl; tcsp;
          try (complete (introv xx; repndors; tcsp; ginv)).
  Qed.
  Hint Resolve wf_MinBFTls : minbft.

  Lemma are_procs_MinBFTsys : are_procs_sys MinBFTsys.
  Proof.
    introv; destruct n; simpl; eauto 3 with comp minbft.
  Qed.
  Hint Resolve are_procs_MinBFTsys : minbft.

  Lemma wf_MinBFTsys : wf_sys MinBFTsys.
  Proof.
    introv; destruct n; simpl; eauto 3 with comp minbft.
  Qed.
  Hint Resolve wf_MinBFTsys : minbft.

  Lemma MinBFTsys_preserves_subs :
    sys_preserves_subs MinBFTsys.
  Proof.
    introv; eauto 3 with comp minbft.
  Qed.
  Hint Resolve MinBFTsys_preserves_subs : minbft.

  Lemma similar_minbft_implies_subs :
    forall (subs : n_procs 1) r,
      similar_subs subs (MinBFTsubs r)
      -> exists (s1 : TRINC_state) (s2 : LOG_state),
        subs = MinBFTsubs_new s1 s2.
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
    unfold MinBFTsubs_new, build_m_sm, build_mp_sm, at2sm; simpl; eauto.
  Qed.

  Lemma similar_subs_MinBFTlocalSys_implies :
    forall r (ls : n_procs 2),
      similar_subs (MinBFTlocalSys r) ls
      -> exists s s1 s2, ls = MinBFTlocalSys_new r s s1 s2.
  Proof.
    introv sim.
    apply similar_subs_MinBFTlocalSysP  in sim; exrepnd; subst.
    apply similar_subs_sym in sim1; apply similar_minbft_implies_subs in sim1; exrepnd; subst.
    exists s s1 s2; auto.
  Qed.

  (* We can also prove some preservation lemmas:
       for example that the replica field in the USIG does not change *)
  Lemma M_run_ls_before_event_ls_is_minbft :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : Rep)
           (ls : MinBFTls),
      M_run_ls_before_event (MinBFTlocalSys r) e = Some ls
      ->
      exists (s : MAIN_state) (s1 : TRINC_state) (s2 : LOG_state),
        ls = MinBFTlocalSys_new r s s1 s2.
  Proof.
    introv run.
    apply M_run_ls_before_event_preserves_subs in run; eauto 3 with comp minbft.
    repnd; simpl in *.
    apply similar_subs_MinBFTlocalSys_implies in run2; auto.
  Qed.

  Lemma M_run_ls_on_event_ls_is_minbft :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : Rep)
           (ls : MinBFTls),
      M_run_ls_on_event (MinBFTlocalSys r) e = Some ls
      ->
      exists (s : MAIN_state) (s1 : TRINC_state) (s2 : LOG_state),
        ls = MinBFTlocalSys_new r s s1 s2.
  Proof.
    introv run.
    apply M_run_ls_on_event_preserves_subs in run; eauto 3 with comp minbft.
    repnd; simpl in *.
    apply similar_subs_MinBFTlocalSys_implies in run2; auto.
  Qed.

  Lemma similar_minbft_implies_level :
    forall r {n} (subs : n_procs n),
      similar_subs subs (MinBFTsubs r)
      -> n = 1.
  Proof.
    introv sim.
    applydup @similar_subs_implies_same_level in sim; auto.
    destruct subs; simpl in *; auto; try omega.
    inversion sim.
  Qed.

(*  Lemma call_usig_preserves_subs :
    forall r i o {n} (subs1 subs2 : n_procs n),
      call_proc USIGname i subs1 = (subs2, o)
      -> similar_subs subs1 (MinBFTsubs r)
      -> similar_subs subs1 subs2.
  Proof.
    introv c sim.
    unfold call_proc in c; smash_minbft; eauto 3 with comp;[].
    applydup similar_minbft_implies_level in sim; subst n.
    applydup similar_minbft_implies_subs in sim; exrepnd; subst; simpl in *.
    repndors; subst; tcsp; ginv.
    inversion Heqx; subst; simpl in *; clear Heqx.
    unfold USIG_update in *; simpl in *.
    destruct i; simpl in *; smash_minbft; simpl in *;
      unfold build_mp_sm, decr_n_procs, sm_s_to_sm, bind, lift_M_O in Heqx1; simpl in *;
        inversion Heqx1; substs; simpl in *; repeat constructor.
  Qed.
  Hint Resolve call_usig_preserves_subs : minbft.

  Lemma call_log_preserves_subs :
    forall r i o {n} (subs1 subs2 : n_procs n),
      call_proc LOGname i subs1 = (subs2, o)
      -> similar_subs subs1 (MinBFTsubs r)
      -> similar_subs subs1 subs2.
  Proof.
    introv c sim.
    unfold call_proc in c; smash_minbft; eauto 3 with comp;[].
    applydup similar_minbft_implies_level in sim; subst n.
    applydup similar_minbft_implies_subs in sim; exrepnd; subst; simpl in *.
    repndors; subst; tcsp; ginv.
    inversion Heqx; subst; simpl in *; clear Heqx.
    unfold USIG_update in *; simpl in *.
    destruct i; simpl in *; smash_minbft; simpl in *;
      unfold build_mp_sm, decr_n_procs, sm_s_to_sm, bind, lift_M_O in Heqx1; simpl in *;
        inversion Heqx1; substs; simpl in *; repeat constructor.
  Qed.
  Hint Resolve call_log_preserves_subs : minbft.*)

  Lemma implies_similar_subs_MinBFTsubs_new :
    forall s1 s2 s3 s4,
      similar_subs (MinBFTsubs_new s1 s2) (MinBFTsubs_new s3 s4).
  Proof.
    introv.
    repeat constructor.
  Qed.
  Hint Resolve implies_similar_subs_MinBFTsubs_new : minbft.

  Lemma is_trusted_ls_usig :
    forall n, is_trusted_ls USIGname (MinBFTlocalSys n).
  Proof.
    introv; tcsp.
  Qed.
  Hint Resolve is_trusted_ls_usig : minbft.

  Definition USIG_sm_new s :=
    build_m_sm USIG_update s.

(*  Lemma trusted_run_sm_on_inputs_usig :
    forall s n l,
      trusted_run_sm_on_inputs s (USIG_comp n) l
      = Some (run_sm_on_inputs_trusted (USIG_sm_new s) l).
  Proof.
    tcsp.
  Qed.*)

  Lemma usig_id_try_update_USIG :
    forall cid old new s,
      trinc_id (try_update_TRINC cid old new s) = trinc_id s.
  Proof.
    introv; unfold try_update_TRINC; smash_minbft.
  Qed.
  Hint Rewrite usig_id_try_update_USIG : minbft.

(*  Lemma run_sm_on_inputs_trusted_usig_preserves_id :
    forall l s,
      trinc_id (run_sm_on_inputs_trusted (USIG_sm_new s) l) = trinc_id s.
  Proof.
    induction l; introv; simpl in *; tcsp;[].
    pose proof (run_sm_on_inputs_trusted_cons _ _ _ (USIG_sm_new s) a l) as xx.
    simpl in *; rewrite xx; auto; clear xx.
    match goal with
    | [ |- context[fst ?x]] => remember (fst x) as w; symmetry in Heqw
    end.
    unfold update_state_op_m; dest_cases z; symmetry in Heqz.
    subst.
    rewrite IHl.

    unfold USIG_update in Heqw.
    destruct a; simpl in *; repnd; simpl in *; inversion Heqw; simpl in *;
      autorewrite with minbft; auto.
  Qed.*)

  Lemma similar_sms_at_log :
    forall s p,
      similar_sms_at (build_mp_sm LOG_update s) p
      <-> exists s', p = build_mp_sm LOG_update s'.
  Proof.
    introv; split; intro h; exrepnd; subst; eauto.

    { inversion h; subst.
      destruct p as [up st]; simpl in *; subst; eauto.
      exists st; auto. }

    { constructor; auto. }
  Qed.
  Hint Rewrite similar_sms_at_log : minbft.

  Lemma similar_sms_at_usig :
    forall s p,
      similar_sms_at (build_mp_sm USIG_update s) p
      <-> exists s', p = build_mp_sm USIG_update s'.
  Proof.
    introv; split; intro h; exrepnd; subst; eauto.

    { inversion h; subst.
      destruct p as [up st]; simpl in *; subst; eauto.
      exists st; auto. }

    { constructor; auto. }
  Qed.
  Hint Rewrite similar_sms_at_usig : minbft.

End TrIncsubs.


Hint Resolve in_output_implies_is_replica : minbft.
Hint Resolve local_pred_preserves_is_replica : minbft.
Hint Resolve are_procs_MinBFTls : minbft.
Hint Resolve wf_MinBFTls : minbft.
Hint Resolve are_procs_MinBFTsys : minbft.
Hint Resolve wf_MinBFTsys : minbft.
(*Hint Resolve call_usig_preserves_subs : minbft.
Hint Resolve call_log_preserves_subs : minbft.*)
Hint Resolve MinBFTsys_preserves_subs : minbft.
Hint Resolve implies_similar_subs_MinBFTsubs_new : minbft.
Hint Resolve is_trusted_ls_usig : minbft.


Hint Rewrite @similar_sms_at_log : minbft.
Hint Rewrite @similar_sms_at_usig : minbft.
Hint Rewrite @usig_id_try_update_USIG : minbft.
