Require Export MinBFTprops2.
Require Export MinBFTsame.
Require Export MinBFTass_mon.
Require Export MinBFTass_tlearn.
Require Export MinBFTass_uniq.
Require Export MinBFTass_new2.
Require Export MinBFTass_tknew.
Require Export ComponentAxiom.


Section MinBFTagreement.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma agreement :
    forall (eo : EventOrdering) (e1 e2 : Event) r1 r2 i l1 l2,
      AXIOM_authenticated_messages_were_sent_or_byz eo MinBFTsys
      -> In (send_accept (accept r1 i) l1) (M_output_sys_on_event MinBFTsys e1)
      -> In (send_accept (accept r2 i) l2) (M_output_sys_on_event MinBFTsys e2)
      -> r1 = r2.
  Proof.
    introv sendbyz send1 send2.
    applydup in_output_implies_is_replica in send1 as isrep1.
    applydup in_output_implies_is_replica in send2 as isrep2.

    unfold is_replica in *.
    destruct isrep1 as [i1 isrep1].
    destruct isrep2 as [i2 isrep2].
    unfold M_output_sys_on_event in send1; rewrite isrep1 in send1; simpl in send1.
    unfold M_output_sys_on_event in send2; rewrite isrep2 in send2; simpl in send2.

    applydup @accepted_counter_if_know_UI_primary in send1 as statea.
    applydup @accepted_counter_if_know_UI_primary in send2 as stateb.
    exrepnd.

    applydup preserves_view_init_ls in statea0 as eqv1; auto.
    applydup preserves_view_init_ls in stateb0 as eqv2; auto.
    rewrite eqv1, eqv2 in *.
    clear eqv1 eqv2.

    applydup M_run_ls_on_event_MinBFT_to_components in statea0; repnd; auto;[].
    applydup M_run_ls_on_event_MinBFT_to_components in stateb0; repnd; auto;[].

    pose proof (request_data_was_verified e1 s4 s3 initial_view r1 ui0) as ka.
    repeat (autodimp ka hyp); try (complete (eexists; eauto)); exrepnd;[].

    pose proof (request_data_was_verified e2 s2 s1 initial_view r2 ui) as kb.
    repeat (autodimp kb hyp); try (complete (eexists; eauto)); exrepnd;[].

    assert (ex_node_e e1) as ex1 by (unfold ex_node_e; allrw; simpl; eauto).
    assert (ex_node_e e2) as ex2 by (unfold ex_node_e; allrw; simpl; eauto).

    pose proof (DERIVED_RULE_trusted_knowledge_unique3_true
                  (MkEventN e1 ex1) (MkEventN e2 ex2) (MkEventN e2 ex2)
                  [] []
                  (MinBFTprimary initial_view)
                  ui0
                  ui
                  (ui2counter ui0)
                  (ui2counter ui)
                  (minbft_data_rdata (request_data initial_view r1 ui0))
                  (minbft_data_rdata (request_data initial_view r2 ui))) as knc.
    unfold rule_true in knc; simpl in knc.
    repeat (autodimp knc hyp); eauto 2 with minbft;[|].

    { Opaque ASSUMPTION_trusted_learns_if_gen.
      Opaque ASSUMPTION_trusted_knew_or_learns_or_gen.
      Opaque ASSUMPTION_monotonicity.
      Opaque ASSUMPTION_generates_new.
      Opaque ASSUMPTION_disseminate_unique.
      introv vt vd vc vn xx yy zz.
      induction es using Vector.caseS'; simpl in *.
      clear vt vd vc vn es.
      repndors; subst; unfold seq_concl, seq_event in *;
        simpl in *; introv; simpl in *; tcsp;
          try (complete (apply ASSUMPTION_trusted_learns_if_gen_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_trusted_knew_or_learns_or_gen_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_monotonicity_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_disseminate_unique_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_generates_new_true; auto; destruct h0; auto));
          try (complete (eexists; simpl;allrw; simpl; eauto));
          try (complete (repeat (eexists; dands; eauto)));
          try (complete (allrw; auto));
          try (complete (rewrite (state_usig_same_keys e1) in ka; auto; rewrite isrep1 in ka;
                         unfold generated_for; simpl; dands; auto; introv xx; ginv; eexists; eauto));
          try (complete (rewrite (state_usig_same_keys e2) in kb; auto; rewrite isrep2 in kb;
                         unfold generated_for; simpl; dands; auto; introv xx; ginv; eexists; eauto)). }

    unfold sequent_true in knc; simpl in knc; repeat (autodimp knc hyp); tcsp;[].
    inversion knc; subst; subst; auto.
  Qed.

End MinBFTagreement.
