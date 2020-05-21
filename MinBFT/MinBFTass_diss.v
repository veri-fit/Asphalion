Require Export CalculusSM_derived4.
Require Export MinBFTprops2.
Require Export MinBFTtacts2.
Require Export MinBFTinv.
Require Export MinBFTsame.


Section MinBFTass_diss.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Hint Rewrite ui_in_log_log_new_prepare : minbft.
  Hint Rewrite ui_in_log_log_new_commit : minbft.

  Lemma commit2sender_j_mk_auth_commit:
    forall v r ui1 ui2,
      commit2sender_j (mk_auth_commit v r ui1 ui2) = ui2rep ui2.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite commit2sender_j_mk_auth_commit : minbft.

  Lemma commit2sender_j_mk_my_commit :
    forall c ui,
      commit2sender_j (mk_my_commit c ui) = ui2rep ui.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite commit2sender_j_mk_my_commit : minbft.

  Lemma log_state_entry2rep_add_commit2entry :
    forall ui e,
      log_state_entry2rep (add_commit2entry ui e)
      = log_state_entry2rep e.
  Proof.
    introv; unfold log_state_entry2rep; autorewrite with minbft; auto.
  Qed.
  Hint Rewrite log_state_entry2rep_add_commit2entry : minbft.

  Lemma log_entry_commits_add_commit2entry :
    forall ui e,
      log_entry_commits (add_commit2entry ui e)
      = if rep_deq (ui2rep ui) (log_state_entry2rep e)
        then log_entry_commits e
        else add_commit2commits ui (log_entry_commits e).
  Proof.
    introv; destruct e; unfold log_state_entry2rep; simpl; smash_minbft2.
  Qed.
  Hint Rewrite log_entry_commits_add_commit2entry : minbft.

  Lemma find_entry_some_implies_eq_log_state_entry2rep :
    forall rd s e,
      find_entry rd s = Some e
      -> log_state_entry2rep e = request_data2rep rd.
  Proof.
    induction s; introv h; simpl in *; tcsp; smash_minbft2.
  Qed.

  Lemma find_entry_implies_prepare_already_in_log :
    forall c s e,
      find_entry (commit2request_data_i c) s = Some e
      -> prepare_already_in_log (commit2prepare c) s = true.
  Proof.
    induction s; introv h; simpl in *; ginv; smash_minbft2.
  Qed.


  Lemma ASSUMPTION_diss_correct_implies_knows_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_diss_correct_implies_knows.
  Proof.
    Opaque KE_CORRECT_TRACE_BEFORE.
    introv diss cor; simpl in *; exrepnd.
    unfold disseminate_data in *; simpl in *; exrepnd.
    unfold M_byz_output_sys_on_event in *.
    revert dependent o.
    rewrite diss1 in *; simpl in *; introv run out.
    apply interp_KE_CORRECT_TRACE_BEFORE in cor.

    eapply correct_byz_output_implies in cor; eauto; exrepnd; subst; simpl in *.
    eapply data_is_in_out_and_dmsgs_are_out_implies in cor2; eauto.
    clear dependent o.
    apply in_flat_map in cor2; exrepnd; simpl in *.

    unfold M_output_ls_on_event in *.
    apply in_olist2list in cor2; exrepnd; simpl in *.
    apply option_map_Some in cor2; exrepnd; subst; simpl in *.
    applydup M_run_ls_before_event_ls_is_minbft in cor2; exrepnd; subst; simpl in *.

    unfold knows_after,  state_after; simpl.
    unfold M_state_sys_on_event; simpl.
    allrw; simpl.
    unfold M_state_ls_on_event; simpl.
    rewrite M_run_ls_on_event_unroll2.
    allrw; simpl.

    applydup usig_same_id in cor2 as eqid; subst; simpl in *.
    hide_hyp cor2.

    unfold M_output_ls_on_this_one_event, trigger_op in *; simpl in *.
    unfold M_run_ls_on_this_one_event, trigger_op; simpl.
    rewrite cor0 in *; simpl in *.
    unfold M_run_ls_on_input_out, M_run_ls_on_input_ls in *; simpl in *.

    remember (M_run_ls_on_input (MinBFTlocalSys_new (usig_id s1) s s1 s2) (msg_comp_name 0) i) as run.
    symmetry in Heqrun; repnd; simpl in *.
    apply in_olist2list in cor3; exrepnd; subst; simpl in *.
    applydup (M_run_ls_on_input_ls_is_minbft_new (msg_comp_name 0)) in Heqrun.
    exrepnd; subst; simpl in *.
    unfold state_of_component; simpl.
    exists l'.

    unfold M_run_ls_on_input in *; simpl in *.
    autorewrite with minbft in *; simpl in *.

    Time minbft_dest_msg Case;
      repeat (autorewrite with minbft comp in *; simpl in *; smash_minbft2);
      repeat (repndors; subst; simpl in *; tcsp);
      unfold state_of_component in *; simpl in *;
      dands; try (complete (eexists;dands;try reflexivity));
      unfold MinBFT_data_knows; simpl; repeat smash_minbft2;
      unfold lower_out_break in *; simpl in *; minbft_simp;
      repeat (repndors; subst; simpl in *; tcsp);
      repeat smash_minbft2;
      try (complete (rename_hyp_with invalid_prepare invp;
                     applydup invalid_prepare_false_implies_eq_prepare2view in invp as eqv; rewrite <- eqv in *;
                     applydup invalid_prepare_false_implies_eq_prepare2sender in invp as eqs;
                     applydup invalid_prepare_false_implies_diff_prepare2sender in invp as dp;
                     autorewrite with minbft in *;
                     unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft2;
                     rename_hyp_with find_entry fe;
                     rewrite prepare_not_already_in_log_implies_find_entry in fe; ginv; simpl in *; repndors; tcsp;
                     unfold log_state_entry2rep in *; simpl in *; autorewrite with minbft in *; try congruence));
      try (complete (rename_hyp_with invalid_commit invc;
                     applydup invalid_commit_false_implies_eq_commit2view in invc as eqv; rewrite <- eqv in *;
                     applydup invalid_commit_false_implies_eq_commit2sender_i in invc as eqs;
                     autorewrite with minbft in *;
                     unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft2;
                     rename_hyp_with find_entry fe;
                     rewrite find_entry_log_new_commit in fe; simpl in *; smash_minbft2;
                     rename_hyp_with find_entry fe;
                     apply find_entry_implies_prepare_already_in_log in fe; tcsp)).
  Qed.

End MinBFTass_diss.

Hint Resolve ASSUMPTION_diss_correct_implies_knows_true : minbft.
