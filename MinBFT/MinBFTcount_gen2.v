(* GENERIC *)

Require Export MinBFTcount_gen2_request.
Require Export MinBFTcount_gen2_reply.
Require Export MinBFTcount_gen2_prepare.
Require Export MinBFTcount_gen2_commit.
Require Export MinBFTcount_gen2_accept.
Require Export MinBFTcount_gen2_debug.


Section MinBFTcount_gen2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma cexec_increases :
    forall {eo     : EventOrdering}
           (e      : Event)
           (s      : Rep)
           (s1     : _)
           (s2     : _)
           (subs1  : n_procs _)
           (subs2  : n_procs _),
      ~ In MAINname (get_names subs1)
      -> wf_procs subs1
      -> are_procs_n_procs subs1
      -> M_run_ls_on_this_one_event (MinBFTlocalSys_newP s s1 subs1) e
         = Some (MinBFTlocalSys_newP s s2 subs2)
      -> cexec s1 = cexec s2
         \/
         exists r l,
           cexec s2 = S (cexec s1)
           /\ In (send_accept (accept r (cexec s2)) l)
                 (M_output_ls_on_this_one_event (MinBFTlocalSys_newP s s1 subs1) e).
  Proof.
    introv ni wf aps h.
    remember (trigger e) as trig; symmetry in Heqtrig; destruct trig.
    { destruct d; simpl in *.
      { eapply cexec_increases_request; eauto. }
      { eapply cexec_increases_reply; eauto. }
      { eapply cexec_increases_prepare; eauto. }
      { eapply cexec_increases_commit; eauto. }
      { eapply cexec_increases_accept; eauto. }
      { eapply cexec_increases_debug; eauto. } }
    { apply map_option_Some in h; exrepnd; rev_Some; minbft_simp.
      unfold trigger_op in *; rewrite Heqtrig in *; simpl in *; ginv. }
    { apply map_option_Some in h; exrepnd; rev_Some; minbft_simp.
      unfold trigger_op in *; rewrite Heqtrig in *; simpl in *; ginv. }
  Qed.

  Lemma operation_inc_counter_ls_step :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i     : nat)
           (l     : list name)
           (s     : Rep)
           (ls    : MinBFTls)
           (subs  : n_procs _),
      lower_head 1 subs = true
      -> ~ In MAINname (get_names subs)
      -> wf_procs subs
      -> are_procs_n_procs subs
      -> M_run_ls_before_event (MinBFTlocalSysP s subs) e = Some ls
      -> In (send_accept (accept r (S i)) l) (M_output_ls_on_this_one_event ls e)
      -> i = 0
         \/
         exists r' l' e' ls',
           e' ⊏ e
           /\ M_run_ls_before_event (MinBFTlocalSysP s subs) e' = Some ls'
           /\ In (send_accept (accept r' i) l') (M_output_ls_on_this_one_event ls' e').
  Proof.
    introv low ni wf aps eqls out.
    applydup M_run_ls_before_event_ls_is_minbftP in eqls; exrepnd; subst; auto.
    applydup accepted_if_executed_previous_step in out; ginv.

    clear r l out eqls0.
    revert s s0 subs subs' low ni wf aps eqls.

    induction e as [e ind] using predHappenedBeforeInd;[]; introv low ni wf aps eqls.
    rewrite M_run_ls_before_event_unroll in eqls.
    destruct (dec_isFirst e) as [d|d]; ginv; minbft_simp.

    { apply eq_MinBFTlocalSys_newP_implies in eqls; repnd; subst; tcsp. }

    apply map_option_Some in eqls; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbftP in eqls1; exrepnd; subst; auto.

    dup eqls1 as eqBef.
    eapply ind in eqls1; eauto 3 with eo; clear ind;[].
    applydup similar_subs_preserves_get_names in eqls2.
    apply cexec_increases in eqls0; eauto 3 with comp minbft;
      try (complete (rewrite <- eqls3; auto));[].
    repndors; exrepnd; tcsp;
      try (complete (left; congruence));
      try (complete (right; minbft_finish_eexists));[].

    right.
    exists r' l' e' ls'; dands; auto; eauto 3 with eo; try congruence.
  Qed.

  Lemma operation_inc_counter_ls :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i1 i2 : nat)
           (l     : list name)
           (s     : Rep)
           (ls    : MinBFTls)
           (subs  : n_procs _),
      lower_head 1 subs = true
      -> ~ In MAINname (get_names subs)
      -> wf_procs subs
      -> are_procs_n_procs subs
      -> M_run_ls_before_event (MinBFTlocalSysP s subs) e = Some ls
      -> In (send_accept (accept r i2) l) (M_output_ls_on_this_one_event ls e)
      -> i1 < i2
      -> 0 < i1
      -> exists r' l' e' ls',
          e' ⊏ e
          /\ M_run_ls_before_event (MinBFTlocalSysP s subs) e' = Some ls'
          /\ In (send_accept (accept r' i1) l') (M_output_ls_on_this_one_event ls' e').
  Proof.
    intros eo e r i1 i2; revert e r.
    induction i2; introv low ni wf aps eqls out lti lti0; try omega;[].
    apply lt_n_Sm_le in lti.

    eapply operation_inc_counter_ls_step in out; eauto;[].
    repndors; subst; try omega.
    exrepnd.

    apply le_lt_or_eq in lti; repndors; subst; try (complete minbft_finish_eexists);[].

    eapply IHi2 in out1; eauto; try omega.
    exrepnd.
    exists r'0 l'0 e'0 ls'0; dands; auto; eauto 3 with eo.
  Qed.

  Definition lower_headF k {n} (f : Rep -> n_procs n) :=
    forall r, lower_head k (f r) = true.

  Definition not_in_namesF (cn : CompName) {n} (f : Rep -> n_procs n) :=
    forall r, ~ In MAINname (get_names (f r)).

  Definition wf_procsF {n} (f : Rep -> n_procs n) :=
    forall r, wf_procs (f r).

  Definition are_procs_n_procsF {n} (f : Rep -> n_procs n) :=
    forall r, are_procs_n_procs (f r).

  Lemma operation_inc_counter :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i1 i2 : nat)
           (l     : list name)
           (subs  : Rep -> n_procs _),
      lower_headF 1 subs
      -> not_in_namesF MAINname subs
      -> wf_procsF subs
      -> are_procs_n_procsF subs
      -> is_replica e
      -> In (send_accept (accept r i2) l) (M_output_sys_on_event (MinBFTsysP subs) e)
      -> i1 < i2
      -> 0 < i1
      -> exists r' l' e',
          e' ⊏ e
          /\ In (send_accept (accept r' i1) l') (M_output_sys_on_event (MinBFTsysP subs) e').
  Proof.
    introv low ni wf aps isr h lti lti0.
    unfold M_output_sys_on_event in *.
    unfold MinBFTsysP, is_replica in *; exrepnd.
    rewrite isr0 in *; simpl in *.

    apply M_output_ls_on_event_as_run in h; exrepnd.
    eapply operation_inc_counter_ls in h0; eauto.
    exrepnd.
    applydup local_implies_loc in h2 as eqloc.
    exists r' l' e'; dands; auto.
    rewrite eqloc.
    rewrite isr0.

    apply M_output_ls_on_event_as_run.
    eexists; dands; eauto.
  Qed.

  Lemma accepted_counter_positive :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i     : nat)
           (l     : list name)
           (subs  : Rep -> n_procs _),
      lower_headF 1 subs
      -> not_in_namesF MAINname subs
      -> wf_procsF subs
      -> are_procs_n_procsF subs
      -> is_replica e
      -> In (send_accept (accept r i) l) (M_output_sys_on_event (MinBFTsysP subs) e)
      -> 0 < i.
  Proof.
    introv low ni wf aps isrep out.
    unfold M_output_sys_on_event in *.
    unfold MinBFTsysP, is_replica in *; exrepnd.
    rewrite isrep0 in *; simpl in *.
    apply M_output_ls_on_event_implies_run in out; exrepnd.
    applydup M_run_ls_before_event_ls_is_minbftP in out1; exrepnd; subst; eauto.
    eapply accepted_if_executed_previous_step in out0; subst; omega.
  Qed.
  Hint Resolve accepted_counter_positive : minbft.

  Lemma M_output_ls_on_input_is_committed_implies :
    forall u c ls,
      M_run_ls_on_input (LOGlocalSys u) LOGname (is_committed_in c) = (ls, Some (log_out true))
      -> is_committed c u = true
         /\ ls = LOGlocalSys u.
  Proof.
    introv out.
    unfold M_run_ls_on_input, on_comp in out; simpl in *.
    unfold M_run_sm_on_input in out; simpl in *.
    unfold M_on_decr, M_break in out; simpl in *; minbft_simp.
    inversion out; auto.
  Qed.

End MinBFTcount_gen2.
