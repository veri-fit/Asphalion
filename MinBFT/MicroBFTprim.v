Require Export MicroBFTprops2.


Section MicroBFTprim.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Lemma not_primary_false_implies :
    forall n,
      not_primary n = false
      -> n = MicroBFT_primary.
  Proof.
    introv h.
    apply negb_false_iff in h.
    unfold is_primary in *; smash_microbft2.
  Qed.
  Hint Resolve not_primary_false_implies : microbft.

  Lemma uis_from_primary :
    forall {eo : EventOrdering} (e : Event) ui,
      knows_after e (microbft_data_ui ui)
      -> ui2rep ui = MicroBFT_primary.
  Proof.
    introv kn.
    unfold knows_after, state_after in kn; exrepnd; simpl in *.
    unfold MicroBFT_data_knows in *; simpl in *.
    rewrite M_state_sys_on_event_unfold in kn2; apply map_option_Some in kn2; exrepnd; rev_Some.
    unfold MicroBFTheader.node2name in *; simpl in *.
    rewrite kn1 in *; simpl in *.
    unfold MicroBFTsys in *; simpl in *.
    applydup M_run_ls_on_event_ls_is_microbft in kn2; exrepnd; subst; simpl in *.

    apply option_map_Some in kn3; exrepnd; subst; simpl in *; microbft_simp.

    remember (loc e) as n; symmetry in Heqn.
    revert dependent s2.
    revert dependent s1.
    revert dependent s.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv run i.

    rewrite M_run_ls_on_event_unroll2 in run.
    apply map_option_Some in run; exrepnd; rev_Some.
    apply map_option_Some in run0; exrepnd; rev_Some.
    simpl in *.
    applydup M_run_ls_before_event_ls_is_microbft in run1; exrepnd; subst; simpl in *.

    unfold M_run_ls_on_input_ls, M_run_ls_on_input in *.
    autorewrite with microbft in *.

    rewrite M_run_ls_before_event_unroll_on in run1.

    Time microbft_dest_msg Case;
      try (destruct (dec_isFirst e));
      repeat(simpl in *; autorewrite with microbft in *; smash_microbft2);
      try (complete (apply ind in run1; autorewrite with eo; eauto 3 with eo));
      try (dup run1 as w; eapply preserves_usig_id2 in w);
      autorewrite with microbft eo in *; eauto;
        repndors; ginv;
          try (complete (apply ind in run1; autorewrite with eo; eauto 3 with eo));
          try (complete (unfold ui_in_log_entry in *;
                           simpl in *; smash_microbft2;
                             allrw; eauto 3 with microbft));
          try (complete (unfold ui_in_log_entry in *; simpl in *; smash_microbft2;
                           apply invalid_request_false_implies_ui2rep_eq in Heqx; auto)).
  Qed.

End MicroBFTprim.


Hint Resolve not_primary_false_implies : microbft.
