Require Export MicroBFTprops2.
Require Export MicroBFTsame.
Require Export MicroBFTprim.

Require Export MicroBFTass_mon.
Require Export MicroBFTass_tlearn.
Require Export MicroBFTass_uniq.
Require Export MicroBFTass_new.
Require Export MicroBFTass_knew.

Require Export ComponentAxiom.
Require Export CalculusSM_derived.


Section MicroBFTvalidity.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Lemma implies_disseminate_accept :
    forall a l {eo : EventOrdering} (e : Event) n,
      loc e = n
      -> In (send_accept a l) (M_output_ls_on_event (MicroBFTsys n) e)
      -> disseminate_data e (microbft_data_acc a).
  Proof.
    introv eqloc send.
    unfold disseminate_data; simpl.
    unfold M_byz_output_sys_on_event; simpl.
    subst; simpl in *.
    applydup in_M_output_ls_on_event_implies_byz_eq in send; allrw; simpl.
    apply in_flat_map; eexists; dands; eauto.
    simpl; tcsp.
  Qed.
  Hint Resolve implies_disseminate_accept : microbft.

  Lemma eq_preUI :
    forall ui,
      Build_preUI (ui2rep ui) (ui2counter ui) = ui_pre ui.
  Proof.
    destruct ui as [p d], p as [i c]; simpl; auto.
  Qed.

  Lemma ASSUMPTION_disseminate_if_knows_trusted_true :
    forall (eo : EventOrdering),
      assume_eo eo (KE_ALL_DATA ASSUMPTION_disseminate_if_knows_trusted).
  Proof.
    Opaque KE_CORRECT_TRACE_BEFORE.
    introv h; simpl in *; exrepnd; GC.
    unfold KE_LOCAL_CORRECT_TRACE_BEFORE in *.
    allrw @interp_KE_CORRECT_TRACE_BEFORE.
    Transparent KE_CORRECT_TRACE_BEFORE.
    unfold disseminate_data in h0; simpl in *.
    unfold M_byz_output_sys_on_event in *; simpl in *.
    rewrite correct_implies_byz_output_eq in h0; auto; simpl in *.
    apply in_flat_map in h0; exrepnd.
    apply M_output_ls_on_event_implies_run in h0; exrepnd.

    unfold knows_after, state_after, M_state_sys_on_event; simpl.
    unfold M_state_ls_on_event.
    unfold MicroBFTsys in *; simpl in *.
    rewrite M_run_ls_on_event_unroll2.
    rewrite h0; simpl.

    unfold MicroBFTheader.node2name in *; simpl in *.
    rewrite h3 in *; simpl in *.
    applydup M_run_ls_before_event_ls_is_microbft in h0; exrepnd; subst; simpl in *.
    apply in_M_output_ls_on_this_one_event_implies in h4; exrepnd; simpl in *.
    unfold M_run_ls_on_this_one_event; allrw; simpl.

    Time microbft_dest_msg Case;
      repeat(simpl in *; autorewrite with microbft in *; smash_microbft2).

    { unfold state_of_subcomponents in *; simpl in *.
      repndors; subst; simpl in *; tcsp.
      { eexists;dands;[eexists;dands;[eexists;dands;eauto|]| |]; simpl; tcsp.
        { unfold MicroBFT_data_knows; simpl.
          unfold ui_in_log_entry; simpl.
          apply orb_true_iff;left; dest_cases w. }
        { simpl.
          unfold Request2HashData, ui2rep; simpl.
          apply usig_same_keys in h0; allrw.
          eexists; rewrite verify_create_hash_usig; eauto. } }
      eexists; dands;[eexists;dands;[eexists;dands;eauto|] |]; simpl; auto;
        unfold MicroBFT_data_knows; simpl;
          unfold ui_in_log_entry; simpl;
            apply orb_true_iff;left; dest_cases w. }

    { unfold state_of_subcomponents in *; simpl in *.
      eexists;dands;[eexists;dands;[eexists;dands;eauto|] |]; simpl;
        [unfold MicroBFT_data_knows; simpl;
         unfold ui_in_log_entry; simpl;
         apply orb_true_iff;left; dest_cases w|].
      unfold generated_for; simpl.
      rename_hyp_with invalid_commit inv.
      applydup invalid_request_false_implies_ui2rep_eq in inv; tcsp.
      unfold verify_UI in *.
      unfold accept2hdata; simpl.
      rewrite <- inv0.
      rewrite eq_preUI; eauto.
      apply usig_same_keys in h0; rewrite h0 in *.
      eexists; eauto. }
  Qed.

  Lemma validity0 :
    forall (eo : EventOrdering) (e : Event) (r : nat) i l1,
      AXIOM_authenticated_messages_were_sent_or_byz eo MicroBFTsys
      -> has_correct_trace_before e (loc e)
      -> loc e = MicroBFT_backup1
      -> In (send_accept (accept r i) l1) (M_output_sys_on_event MicroBFTsys e)
      -> exists e' ui ks,
          disseminate_data e' (microbft_data_ui ui)
          /\ loc e' = MicroBFT_primary
          /\ ui2rep ui = MicroBFT_primary
          /\ verify_hash_usig (accept2hdata (accept r i)) (ui2digest ui) ks = true.
  Proof.
    introv sendbyz cor isrep send.

    unfold M_output_sys_on_event in send; rewrite isrep in send; simpl in send.

    assert (ex_node_e e) as ex by (unfold ex_node_e; allrw; simpl; eauto).

    applydup accepted_counter_if_know_UI_primary in send as senda; exrepnd.

    pose proof (DERIVED_RULE_disseminate_if_learned_and_disseminated2_true
                  (MkEventN e ex)
                  [] []
                  (microbft_data_acc (accept r i))) as knc.

    unfold rule_true in knc; simpl in knc.
    repeat (autodimp knc hyp); eauto 2 with microbft;[|].

    { simseqs j; try apply interpret_implies_sequent_true;
        try (complete (simpl; auto));
        try (complete (apply ASSUMPTION_knew_or_learns_or_gen_true; auto));
        try (complete (apply ASSUMPTION_trusted_learns_if_gen_true; auto));
        try (complete (apply ASSUMPTION_disseminate_if_knows_trusted_true; auto));
        try (complete (simpl; eapply implies_disseminate_accept; eauto));
        try (complete (unfold KE_LOCAL_CORRECT_TRACE_BEFORE; allrw interp_KE_CORRECT_TRACE_BEFORE; simpl; eauto 3 with eo)). }

    simpl in *.
    allrw @sequent_true_iff_interpret; simpl in *.
    exrepnd; repndors; exrepnd; GC.

    { assert (c0 = MicroBFT_primary) as eqp; subst.
      { apply uis_from_primary in knc2.
        unfold data_is_owned_by in *; simpl in *; try congruence. }
      exists (en_event e') c; simpl; dands; eauto. }

    { unfold generated_for in *; simpl in *; exrepnd; ginv.
      unfold data_is_owned_by in *; simpl in *; subst; simpl in *.
      rewrite isrep in *; simpl in *.
      apply uis_from_primary in knc2; rewrite knc2 in *; simpl in *.
      unfold MicroBFTheader.node2name in *; ginv. }
  Qed.

End MicroBFTvalidity.
