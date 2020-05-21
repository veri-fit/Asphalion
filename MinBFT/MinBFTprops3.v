Require Export MinBFTprops2.
Require Export MinBFTsame.
Require Export MinBFTass_mon.
Require Export MinBFTass_tlearn.
Require Export MinBFTass_uniq.
Require Export MinBFTass_new.
Require Export MinBFTass_tknew.
Require Export ComponentAxiom.
(*Require Export MinBFTass_learn.
Require Export MinBFTass_tknows.*)


Section MinBFTprops3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma unique_counter1 :
    forall {eo : EventOrdering}
           (e1 e2 : Event)
           (r     : Request)
           (i1 i2 : nat)
           (l1 l2 : list name),
      AXIOM_authenticated_messages_were_sent_or_byz eo MinBFTsys
      -> In (send_accept (accept r i1) l1) (M_output_sys_on_event MinBFTsys e1)
      -> In (send_accept (accept r i2) l2) (M_output_sys_on_event MinBFTsys e2)
      -> i1 < i2
      -> False.
  Proof.
    introv sendbyz h q lti.
    applydup in_output_implies_is_replica in h as isr1.
    applydup in_output_implies_is_replica in q as isr2.

    (* === replica at [e2] has accepted [i1] in the past === *)
    applydup (operation_inc_counter e2 r i1 i2) in q; auto; eauto 3 with minbft;[].
    exrepnd.

    unfold is_replica in *.
    destruct isr1 as [i isr1].
    destruct isr2 as [i' isr2].
    assert (loc e' = loc e2) as eqloc by eauto 2 with eo.
    assert (loc e' = MinBFT_replica i') as eqi' by congruence.

    unfold M_output_sys_on_event in h; rewrite isr1  in h;  simpl in h.
    unfold M_output_sys_on_event in q; rewrite isr2  in q;  simpl in q.
    unfold M_output_sys_on_event in q1; rewrite eqi' in q1; simpl in q1.

    applydup @accepted_counter_if_know_UI_primary in h  as state1a.
    applydup @accepted_counter_if_know_UI_primary in q  as state2b.
    applydup @accepted_counter_if_know_UI_primary in q1 as state2a.
    exrepnd.

    applydup preserves_view_init_ls in state2a0 as eqv1; auto.
    applydup preserves_view_init_ls in state2b0 as eqv2; auto.
    applydup preserves_view_init_ls in state1a0 as eqv3; auto.
    rewrite eqv1, eqv2, eqv3 in *.
    clear eqv1 eqv2 eqv3.

    applydup M_run_ls_on_event_MinBFT_to_components in state1a0; repnd; auto;[].
    applydup M_run_ls_on_event_MinBFT_to_components in state2a0; repnd; auto;[].

    pose proof (request_data_was_verified e1 s7 s6 initial_view r ui1) as ka.
    repeat (autodimp ka hyp); try (complete (eexists; eauto)); exrepnd;[].

    pose proof (request_data_was_verified e' s2 s1 initial_view r' ui) as kb.
    repeat (autodimp kb hyp); try (complete (eexists; eauto)); exrepnd;[].

    assert (ex_node_e e1) as ex1 by (unfold ex_node_e; allrw; simpl; eauto).
    assert (ex_node_e e') as ex2 by (unfold ex_node_e; allrw; simpl; eauto).

    pose proof (DERIVED_RULE_trusted_knowledge_unique3_ex_true
                  (MkEventN e1 ex1) (MkEventN e' ex2) (MkEventN e' ex2)
                  [] []
                  (MinBFTprimary initial_view)
                  ui1
                  ui
                  (ui2counter ui1)
                  (ui2counter ui)
                  (minbft_data_rdata (request_data initial_view r ui1))
                  (minbft_data_rdata (request_data initial_view r' ui))) as knc.
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
          try (complete (unfold data_is_owned_by; minbft_simp; allrw; auto));
          try (complete (apply ASSUMPTION_trusted_learns_if_gen_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_trusted_knew_or_learns_or_gen_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_monotonicity_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_disseminate_unique_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_generates_new_true; auto; destruct h0; auto));
          try (complete (eexists; simpl;allrw; simpl; eauto));
          try (complete (repeat (eexists; dands; eauto)));
          try (complete (allrw; auto));
          try (complete (rewrite (state_usig_same_keys e1) in ka; auto; rewrite isr1 in ka;
                         unfold generated_for; simpl; dands; auto; introv x; ginv; eexists; eauto));
          try (complete (rewrite (state_usig_same_keys e') in kb; auto; rewrite eqi' in kb;
                         unfold generated_for; simpl; dands; auto; introv x; ginv; eexists; eauto)). }

    unfold sequent_true in knc; simpl in knc; repeat (autodimp knc hyp); tcsp;[].
    inversion knc; subst; subst.

    pose proof (accepted_implies_latest_executed e' r' i1 l' s) as proga.
    repeat (autodimp proga hyp);
      try (complete (eexists; eauto));
      try (complete (unfold M_output_sys_on_event; allrw; simpl; auto));[].
    exrepnd.

    applydup M_run_ls_on_event_MinBFT_to_components in state2b0; repnd; auto;[].

    pose proof (M_state_sys_on_event_some_between (local_pred e2) e2 MinBFTsys MAINname s0) as between.
    repeat (autodimp between hyp); eauto 3 with eo minbft comp;[].
    exrepnd.
    rewrite <- M_state_sys_before_event_as_M_state_sys_on_event_pred in between0; eauto 3 with eo;[].

    pose proof (accepted_implies_new_request e2 r' i2 l2 s') as progb.
    repeat (autodimp progb hyp);
      try (complete (eexists; eauto));
      try (complete (unfold M_output_sys_on_event; allrw; simpl; auto));[].

    pose proof (vreq_monotonic e' e2 s s' (request2sender r') t) as mon.
    repeat (autodimp mon hyp);
      try (complete (eexists; eauto));[].
    exrepnd.

    apply new_bare_request_implies2 in mon1; auto; try omega.
  Qed.

  Lemma unique_counter :
    forall {eo : EventOrdering}
           (e1 e2 : Event)
           (r     : Request)
           (i1 i2 : nat)
           (l1 l2 : list name),
      AXIOM_authenticated_messages_were_sent_or_byz eo MinBFTsys
      -> In (send_accept (accept r i1) l1) (M_output_sys_on_event MinBFTsys e1)
      -> In (send_accept (accept r i2) l2) (M_output_sys_on_event MinBFTsys e2)
      -> i1 = i2.
  Proof.
    introv sendbyz h q.
    applydup in_output_implies_is_replica in h as isr1.
    applydup in_output_implies_is_replica in q as isr2.

    destruct (lt_dec i1 i2) as [d|d].

    {
      assert False; tcsp.
      apply (unique_counter1 e1 e2 r i1 i2 l1 l2); auto.
    }

    destruct (lt_dec i2 i1) as [d'|d']; try omega;[].

    assert False; tcsp.
    apply (unique_counter1 e2 e1 r i2 i1 l2 l1); auto.
  Qed.

End MinBFTprops3.
