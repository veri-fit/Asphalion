Require Export MinBFTprops2.
Require Export MinBFTinv.


Section MinBFTass_uniq.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma ASSUMPTION_disseminate_unique_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_disseminate_unique.
  Proof.
    introv h; simpl in *; exrepnd; subst; GC; f_equal.
    rewrite h0 in h1; ginv.

    unfold disseminate_data in *; simpl in *.
    unfold M_byz_output_sys_on_event in *; simpl in *.
    rewrite M_byz_output_ls_on_event_as_run in h5, h6.
    rewrite h0 in *; simpl in *.

    pose proof (ex_M_byz_run_ls_before_event_MinBFTlocalSys e c3) as run.
    repndors; exrepnd; rewrite run0 in h5, h6; simpl in *.

    { remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; ginv; tcsp;[].
      unfold state_of_trusted in *; simpl in *.
      unfold USIG_update in *; destruct i; simpl in *;
        repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
        try (complete (inversion Heqx; clear Heqx; subst; simpl in *; repndors;
                       tcsp; subst; simpl in *; tcsp; ginv)). }

    remember (trigger e) as trig; symmetry in Heqtrig.
    destruct trig; simpl in *; ginv; tcsp;[|].

    { autorewrite with minbft in *.
      Time minbft_dest_msg Case;
        repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
        try (complete (repndors; smash_minbft2; ginv; simpl in *;
                         try (rename_hyp_with invalid_prepare invp);
                         try (rename_hyp_with invalid_commit invc);
                         try (complete (eapply data_is_owned_by_invalid_prepare_implies_false in invp; eauto; tcsp));
                         try (complete (unfold commit2ui_i in *; simpl in *;
                                          unfold ui_has_counter in *; simpl in *;
                                            unfold ui2counter in *; simpl in *; subst; simpl in *;
                                              eapply data_is_owned_by_invalid_commit_not_pil_implies_false in invc; eauto; tcsp)))). }

    { unfold state_of_trusted in *; simpl in *.
      unfold USIG_update in *; destruct i; simpl in *;
        repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
        try (complete (inversion Heqx; clear Heqx; subst; simpl in *; repndors;
                       tcsp; subst; simpl in *; tcsp; ginv)). }
  Qed.
  Hint Resolve ASSUMPTION_disseminate_unique_true : minbft.

End MinBFTass_uniq.


Hint Resolve ASSUMPTION_disseminate_unique_true : minbft.
