Require Export MinBFTcount_gen1.
Require Export MinBFTrep.
Require Export MinBFTprep.


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

  Lemma invalid_commit2_false_implies :
    forall slf km v c pil s,
      invalid_commit2 slf km v c pil s = false
      -> valid_commit2 slf km v c pil s = 0.
  Proof.
    introv h.
    unfold invalid_commit2 in *; smash_minbft.
  Qed.
  Hint Resolve invalid_commit2_false_implies : minbft.

  Ltac smash_minbft1_ :=
    let atac := fun _ => (eauto 1  with minbft) in
    let stac := fun _ => minbft_simplifier_step in
    let ftac := fun _ => try (fold DirectedMsgs in * ) in
    let rtac := fun _ => repeat (minbft_rw;simpl) in
    let x := fresh "x" in
    simpl in *;
    dest_all x stac ftac;
    rtac ();
    simplifier stac;
    atac ().

  Ltac sp_minbft_rw :=
    progress rewrite_strat try outermost (choice
                                            (choice
                                               (choice
                                                  (choice
                                                     M_break_call_proc_LOGname
                                                     M_break_call_proc_USIGname)
                                                  M_break_MinBFT_state_update)
                                               M_break_bind)
                                            (choice
                                               (hints minbft)
                                               (hints comp))).

  Ltac sp_break :=
    match goal with
    | [ H : is_M_break_out ?x ?y _, J : is_M_break_out ?x ?y _ |- _ ] =>
      unfold is_M_break_out in H, J; rewrite H in J; repeat hide_break; subst; ginv; GC
    | [ H : is_M_break_mon ?x ?y _, J : is_M_break_mon ?x ?y _ |- _ ] =>
      unfold is_M_break_mon in H, J; rewrite H in J; repeat hide_break; subst; ginv; GC
    end.

  Lemma commit2request_mk_auth_commit :
    forall v r ui1 ui2,
      commit2request (mk_auth_commit v r ui1 ui2) = r.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite commit2request_mk_auth_commit : minbft.

  Ltac invalid_prep_imp_count h :=
    match goal with
    | [ H : invalid_prepare _ _ _ _ _ = false |- _ ] =>
      applydup invalid_prepare_false_implies_prepare2counter_eq in H as h
    | [ H : invalid_commit2 _ _ _ _ _ _ = false |- _ ] =>
      applydup invalid_commit2_false_implies_commit2counter_i_eq in H as h
    end.


  Lemma cexec_increases :
    forall {eo     : EventOrdering}
           (e      : Event)
           (s      : Rep)
           (s1     : _)
           (s2     : _)
           (subs1  : n_procs _)
           (subs2  : n_procs _),
      M_run_ls_on_this_one_event (MinBFTlocalSys_newP s s1 subs1) e
      = Some (MinBFTlocalSys_newP s s2 subs2)
      -> cexec s1 = cexec s2
         \/
         exists r l,
           cexec s2 = S (cexec s1)
           /\ In (send_accept (accept r (cexec s2)) l)
                 (M_output_ls_on_this_one_event (MinBFTlocalSys_newP s s1 subs1) e).
  Proof.
    introv run.
    apply map_option_Some in run; exrepnd; rev_Some.
    unfold M_output_ls_on_this_one_event.
    rewrite run1.
    simpl in *.
    autorewrite with minbft in *.

    Time minbft_dest_msg Case;
      repeat (autorewrite with minbft comp in *; simpl in *; smash_minbft2);
      try (complete (apply upd_ls_main_state_and_subs_eq_MinBFTlocalSys_newP_implies in run0;
                       repnd; subst; tcsp));
      repeat (gdest;
                repeat smash_minbft1_at_ run0;
                repeat smash_minbft1_;
                repeat hide_break;
                repnd; simpl in *; repndors; ginv; tcsp; eauto 2 with minbft;
                  repeat sp_break;
                  repeat (first [progress rw_is_M_break
                                |progress allrw
                                |progress minbft_rw]; simpl in *;auto);
                try (complete (apply upd_ls_main_state_and_subs_eq_MinBFTlocalSys_newP_implies in run0;
                               repnd; subst; tcsp;
                               simpl; right; autorewrite with minbft;
                               try (invalid_prep_imp_count xx; rewrite xx);
                               eexists; eexists; dands; tcsp; eauto))).
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
      M_run_ls_before_event (MinBFTlocalSysP s subs) e = Some ls
      -> In (send_accept (accept r (S i)) l) (M_output_ls_on_this_one_event ls e)
      -> i = 0
         \/
         exists r' l' e' ls',
           e' ⊏ e
           /\ M_run_ls_before_event (MinBFTlocalSysP s subs) e' = Some ls'
           /\ In (send_accept (accept r' i) l') (M_output_ls_on_this_one_event ls' e').
  Proof.
    introv eqls out.
    applydup M_run_ls_before_event_ls_is_minbftP in eqls; exrepnd; subst.
    applydup accepted_if_executed_previous_step in out; ginv.

    clear r l out.
    revert s s0 subs' eqls.

    induction e as [e ind] using predHappenedBeforeInd;[]; introv eqls.
    rewrite M_run_ls_before_event_unroll in eqls.
    destruct (dec_isFirst e) as [d|d]; ginv.

    { inversion eqls; subst; GC; simpl; tcsp. }

    apply map_option_Some in eqls; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbftP in eqls1; exrepnd; subst.

    dup eqls1 as eqBef.
    eapply ind in eqls1; eauto 3 with eo; clear ind;[].
    apply cexec_increases in eqls0.
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
      M_run_ls_before_event (MinBFTlocalSysP s subs) e = Some ls
      -> In (send_accept (accept r i2) l) (M_output_ls_on_this_one_event ls e)
      -> i1 < i2
      -> 0 < i1
      -> exists r' l' e' ls',
          e' ⊏ e
          /\ M_run_ls_before_event (MinBFTlocalSysP s subs) e' = Some ls'
          /\ In (send_accept (accept r' i1) l') (M_output_ls_on_this_one_event ls' e').
  Proof.
    intros eo e r i1 i2; revert e r.
    induction i2; introv eqls out lti lti0; try omega;[].
    apply lt_n_Sm_le in lti.

    eapply operation_inc_counter_ls_step in out; eauto.
    repndors; subst; try omega.
    exrepnd.

    apply le_lt_or_eq in lti; repndors; subst; try (complete minbft_finish_eexists);[].

    eapply IHi2 in out1; eauto; try omega.
    exrepnd.
    exists r'0 l'0 e'0 ls'0; dands; auto; eauto 3 with eo.
  Qed.

  Lemma operation_inc_counter :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i1 i2 : nat)
           (l     : list name)
           (subs  : Rep -> n_procs _),
      is_replica e
      -> In (send_accept (accept r i2) l) (M_output_sys_on_event (MinBFTsysP subs) e)
      -> i1 < i2
      -> 0 < i1
      -> exists r' l' e',
          e' ⊏ e
          /\ In (send_accept (accept r' i1) l') (M_output_sys_on_event (MinBFTsysP subs) e').
  Proof.
    introv isr h lti lti0.
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
      is_replica e
      -> In (send_accept (accept r i) l) (M_output_sys_on_event (MinBFTsysP subs) e)
      -> 0 < i.
  Proof.
    introv isrep out.
    unfold M_output_sys_on_event in *.
    unfold MinBFTsysP, is_replica in *; exrepnd.
    rewrite isrep0 in *; simpl in *.
    apply M_output_ls_on_event_implies_run in out; exrepnd.
    applydup M_run_ls_before_event_ls_is_minbftP in out1; exrepnd; subst.
    eapply accepted_if_executed_previous_step in out0; subst; omega.
  Qed.
  Hint Resolve accepted_counter_positive : minbft.

  Lemma M_output_ls_on_input_is_committed_implies :
    forall u c ls,
      M_output_ls_on_input (LOGlocalSys u) (is_committed_in c) = (ls, log_out true)
      -> is_committed c u = true
         /\ ls = LOGlocalSys u.
  Proof.
    introv out.
    unfold M_output_ls_on_input in out; simpl in *.
    unfold M_run_smat_on_inputs in out; simpl in *.
    unfold M_run_update_on_inputs in out; simpl in *.
    unfold M_break in *; simpl in *; ginv.
    inversion out; auto.
  Qed.

End MinBFTcount_gen2.
