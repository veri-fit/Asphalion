Require Export MicroBFTprops2.
Require Export MicroBFTsame.
Require Export MicroBFTass_mon.
Require Export MicroBFTass_tlearn.
Require Export MicroBFTass_uniq.
Require Export MicroBFTass_new.
Require Export MicroBFTass_tknew.
Require Export ComponentAxiom.


Section MicroBFTagreement.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Lemma not_primary_implies :
    forall {eo : EventOrdering} (e : Event),
      not_primary (loc e) = true
      -> loc e = MicroBFT_backup1 \/ loc e = MicroBFT_backup2.
  Proof.
    introv h; unfold not_primary, is_primary in h; smash_microbft.
    remember (loc e) as q; destruct q; tcsp.
  Qed.
  Hint Resolve not_primary_implies : microbft.

  Lemma agreement :
    forall (eo : EventOrdering) (e1 e2 : Event) (r1 r2 : nat) i l1 l2,
      AXIOM_authenticated_messages_were_sent_or_byz eo MicroBFTsys
      -> In (send_accept (accept r1 i) l1) (M_output_sys_on_event MicroBFTsys e1)
      -> In (send_accept (accept r2 i) l2) (M_output_sys_on_event MicroBFTsys e2)
      -> r1 = r2.
  Proof.
    introv sendbyz send1 send2.

    unfold M_output_sys_on_event in send1.
    unfold M_output_sys_on_event in send2.

    applydup @accepted_counter_if_know_UI_primary in send1 as statea.
    applydup @accepted_counter_if_know_UI_primary in send2 as stateb.
    exrepnd.

    applydup M_run_ls_on_event_MicroBFT_to_compoments in statea1; repnd; auto;[].
    applydup M_run_ls_on_event_MicroBFT_to_compoments in stateb1; repnd; auto;[].

    pose proof (request_was_verified e1 s4 s3 rq0) as ka.
    repeat (autodimp ka hyp); try (complete (eexists; eauto)); exrepnd; eauto 3 with microbft;[].

    pose proof (request_was_verified e2 s2 s1 rq) as kb.
    repeat (autodimp kb hyp); try (complete (eexists; eauto)); exrepnd; eauto 3 with microbft;[].

    assert (ex_node_e e1) as ex1 by (unfold ex_node_e; allrw; simpl; eauto).
    assert (ex_node_e e2) as ex2 by (unfold ex_node_e; allrw; simpl; eauto).

    pose proof (DERIVED_RULE_trusted_knowledge_unique3_ex_true
                  (MkEventN e1 ex1) (MkEventN e2 ex2) (MkEventN e2 ex2)
                  [] []
                  (MicroBFT_primary)
                  ui0
                  ui
                  (ui2counter ui0)
                  (ui2counter ui)
                  (microbft_data_rdata rq0)
                  (microbft_data_rdata rq)) as knc.
    unfold rule_true in knc; simpl in knc.
    repeat (autodimp knc hyp); eauto 2 with microbft;[|].

    { Opaque ASSUMPTION_trusted_learns_if_gen.
      Opaque ASSUMPTION_trusted_knew_or_learns_or_gen.
      Opaque ASSUMPTION_monotonicity.
      Opaque ASSUMPTION_generates_new_ex.
      Opaque ASSUMPTION_disseminate_unique.
      introv vt vd vc vn vz vv xx yy zz.
      induction es using Vector.caseS'; simpl in *.
      clear vt vd vc vn es.
      repndors; subst; unfold seq_concl, seq_event in *;
        simpl in *; introv; simpl in *; microbft_simp; tcsp;
          try (complete (apply ASSUMPTION_trusted_learns_if_gen_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_trusted_knew_or_learns_or_gen_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_monotonicity_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_disseminate_unique_true; auto; destruct h0; auto));
          try (complete (apply ASSUMPTION_generates_new_true; auto; destruct h0; auto));
          try (complete (unfold ui_has_counter in *; subst; simpl in *; auto));
          try (complete (eexists; simpl;allrw; simpl; eauto));
          try (complete (repeat (eexists; dands; eauto)));
          try (complete (dands; tcsp; erewrite state_usig_same_keys in ka; eauto));
          try (complete (dands; tcsp; erewrite state_usig_same_keys in kb; eauto)). }

    unfold sequent_true in knc; simpl in knc; repeat (autodimp knc hyp); tcsp;[].
    inversion knc; subst; subst; auto.
  Qed.

End MicroBFTagreement.
