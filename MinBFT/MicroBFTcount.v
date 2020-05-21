Require Export MicroBFTprops0.
Require Export MicroBFTsubs.
Require Export MicroBFTbreak.
Require Export ComponentSM6.


Section MicroBFTcount.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.

(*
  Lemma accepted_if_executed_previous_step :
    forall {eo  : EventOrdering}
           (e   : Event)
           (req : Request)
           (i   : nat)
           (l   : list name)
           (r   : Rep)
           (s   : MAIN_state)
           (s1  : USIG_state)
           (s2  : LOG_state),
      In (send_accept (accept req i) l)
         (M_output_ls_on_this_one_event (MicroBFTlocalSys_new r s s1 s2) e)
      -> i = S (cexec s).
  Proof.
    introv h.
    apply in_M_output_ls_on_this_one_event_implies in h; exrepnd; simpl in *.
    autorewrite with microbft comp in *.
    Time microbft_dest_msg Case; simpl in *; tcsp; ginv; repeat smash_microbft2;
      repndors; tcsp; inversion h0; subst; GC; eauto 4 with microbft.
  Qed.

  Lemma operation_inc_counter_ls_step :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i     : nat)
           (l     : list name)
           (s     : Rep)
           (ls    : MicroBFTls),
      M_run_ls_before_event (MicroBFTlocalSys s) e = Some ls
      -> In (send_accept (accept r (S i)) l) (M_output_ls_on_this_one_event ls e)
      -> i = 0
         \/
         exists r' l' e' ls',
           e' ⊏ e
           /\ M_run_ls_before_event (MicroBFTlocalSys s) e' = Some ls'
           /\ In (send_accept (accept r' i) l') (M_output_ls_on_this_one_event ls' e').
  Proof.
    introv eqls out.
    applydup M_run_ls_before_event_ls_is_microbft in eqls; exrepnd; subst.
    applydup accepted_if_executed_previous_step in out; ginv.
    clear r l out.
    revert s s0 s1 s2 eqls.

    induction e as [e ind] using predHappenedBeforeInd;[]; introv eqls.
    rewrite M_run_ls_before_event_unroll in eqls.
    destruct (dec_isFirst e) as [d|d]; ginv.

    { inversion eqls; subst; GC; simpl; tcsp. }

    apply map_option_Some in eqls; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_microbft in eqls1; exrepnd; subst.

    dup eqls1 as eqbef.
    rename eqls1 into eqbef_backup.
    eapply ind in eqbef; eauto 3 with eo;[].

    apply map_option_Some in eqls0; exrepnd; simpl in *; rev_Some.
    autorewrite with microbft comp in *.
    Time microbft_dest_msg Case;
      repeat (autorewrite with microbft comp in *; simpl in *; smash_microbft2);
      try (complete (clear eqbef_backup; repndors; tcsp; [];
                       right; exrepnd; microbft_finish_eexists));
      [|].

    { Case "Commit".

      right.

      applydup invalid_commit_false_implies in Heqx as w.
      apply valid_commit_implies_executed_prior in w.
      apply executed_prior_counter_implies_eq_S in w.

      exists (commit2request c) [MicroBFT_replica s] (local_pred e) (MicroBFTlocalSys_new s s3 s1 s5).
      dands; eauto 3 with eo.

      Time unfold M_output_ls_on_this_one_event; simpl; repeat (allrw; simpl);
        repeat (autorewrite with microbft comp in *; simpl in *; smash_microbft2);
        try (complete (left; try congruence)).
    }

    { Case "Commit".

      right.

      applydup invalid_commit_false_implies in Heqx as w.
      apply valid_commit_implies_executed_prior in w.
      apply executed_prior_counter_implies_eq_S in w.

      exists (commit2request c) [MicroBFT_replica s] (local_pred e) (MicroBFTlocalSys_new s s3 s4 s5).
      dands; eauto 3 with eo.

      Time unfold M_output_ls_on_this_one_event; simpl; repeat (allrw; simpl);
        repeat (autorewrite with microbft comp in *; simpl in *; smash_microbft2);
        try (complete (left; try congruence)).
    }
  Qed.

  Lemma operation_inc_counter_ls :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i1 i2 : nat)
           (l     : list name)
           (s     : Rep)
           (ls    : MicroBFTls),
      M_run_ls_before_event (MicroBFTlocalSys s) e = Some ls
      -> In (send_accept (accept r i2) l) (M_output_ls_on_this_one_event ls e)
      -> i1 < i2
      -> 0 < i1
      -> exists r' l' e' ls',
          e' ⊏ e
          /\ M_run_ls_before_event (MicroBFTlocalSys s) e' = Some ls'
          /\ In (send_accept (accept r' i1) l') (M_output_ls_on_this_one_event ls' e').
  Proof.
    intros eo e r i1 i2; revert e r.
    induction i2; introv eqls out lti lti0; try omega;[].
    apply lt_n_Sm_le in lti.

    eapply operation_inc_counter_ls_step in out; eauto.
    repndors; subst; try omega.
    exrepnd.

    apply le_lt_or_eq in lti; repndors; subst; try (complete microbft_finish_eexists);[].

    eapply IHi2 in out1; eauto; try omega.
    exrepnd.
    exists r'0 l'0 e'0 ls'0; dands; auto; eauto 3 with eo.
  Qed.

  Lemma operation_inc_counter :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i1 i2 : nat)
           (l     : list name),
      is_replica e
      -> In (send_accept (accept r i2) l) (M_output_sys_on_event MicroBFTsys e)
      -> i1 < i2
      -> 0 < i1
      -> exists r' l' e',
          e' ⊏ e
          /\ In (send_accept (accept r' i1) l') (M_output_sys_on_event MicroBFTsys e').
  Proof.
    introv isr h lti lti0.
    unfold M_output_sys_on_event in *.
    unfold MicroBFTsys, is_replica in *; exrepnd.
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
           (l     : list name),
      is_replica e
      -> In (send_accept (accept r i) l) (M_output_sys_on_event MicroBFTsys e)
      -> 0 < i.
  Proof.
    introv isrep out.
    unfold M_output_sys_on_event in *.
    unfold MicroBFTsys, is_replica in *; exrepnd.
    rewrite isrep0 in *; simpl in *.
    apply M_output_ls_on_event_implies_run in out; exrepnd.
    applydup M_run_ls_before_event_ls_is_microbft in out1; exrepnd; subst.
    eapply accepted_if_executed_previous_step in out0; subst; omega.
  Qed.
  Hint Resolve accepted_counter_positive : microbft.
*)

  (*Lemma M_output_ls_on_input_is_log_new_implies :
    forall u r v o,
      M_output_ls_on_input (LOGlocalSys u) (log_new r) = (LOGlocalSys v, o)
      -> in_log r v.
  Proof.
    introv out.
    unfold M_output_ls_on_input in out; simpl in *.
    unfold M_run_smat_on_inputs in out; simpl in *.
    unfold M_run_update_on_inputs in out; simpl in *.
    unfold M_break in *; simpl in *; ginv.
    inversion out; auto; simpl; tcsp.
  Qed.*)

  Lemma invalid_request_false_implies_ui2rep_eq :
    forall R r s,
      invalid_commit R r s = false
      -> ui2rep (commit_ui r) = MicroBFT_primary.
  Proof.
    introv inv; unfold invalid_commit, valid_commit, is_primary in *; smash_microbft_2.
  Qed.
  Hint Resolve invalid_request_false_implies_ui2rep_eq : microbft.

  Lemma invalid_request_false_implies_not_primary :
    forall R r s,
      invalid_commit R r s = false
      -> not_primary R = true.
  Proof.
    introv inv; unfold invalid_commit, valid_commit, is_primary in *; smash_microbft_2.
  Qed.
  Hint Resolve invalid_request_false_implies_not_primary : microbft.

  (* This uses compositional reasoning, but using [LOG_comp]'s spec defined in
     [M_output_ls_on_input_is_committed_implies] *)
  Lemma accepted_counter_if_received_UI_primary :
    forall {eo : EventOrdering}
           (e  : Event)
           (R  : MicroBFT_node)
           (r  : nat)
           (i  : nat)
           (l  : list name),
      In (send_accept (accept r i) l) (M_output_ls_on_event (MicroBFTlocalSys R) e)
      ->
      exists (s  : MAIN_state)
             (s1 : USIG_state)
             (s2 : LOG_state)
             (ui : UI)
             (rq : Commit),
        M_run_ls_on_event (MicroBFTlocalSys R) e = Some (MicroBFTlocalSys_new R s s1 s2)
        /\ in_log rq s2
        /\ commit_n rq = r
        /\ commit_ui rq = ui
        /\ ui2counter ui = i
        /\ ui2rep ui = MicroBFT_primary
        /\ not_primary R = true.
  Proof.
    introv h.
    apply M_output_ls_on_event_as_run in h; exrepnd.
    rename ls' into ls.
    rewrite M_run_ls_on_event_unroll2; allrw; simpl.
    applydup M_run_ls_before_event_ls_is_microbft in h1; exrepnd; subst.
    apply in_M_output_ls_on_this_one_event_implies in h0; exrepnd; simpl in *; microbft_simp.
    unfold M_run_ls_on_this_one_event; simpl; allrw; simpl.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input.
    unfold statefund_nm in *; simpl in *.
    autorewrite with microbft comp in *.

    Time microbft_dest_msg Case; simpl in *; tcsp; ginv; repeat smash_microbft_2; ginv.
    eexists; eexists; eexists; eexists; eexists; dands; try reflexivity; eauto 3 with microbft; tcsp.
  Qed.

End MicroBFTcount.


(*
Hint Resolve accepted_counter_positive : microbft.
 *)
