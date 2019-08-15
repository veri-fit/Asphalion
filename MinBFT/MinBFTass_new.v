Require Export MinBFTinv.
Require Export MinBFTprops2.


Section MinBFTass_new.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Opaque KE_TOWNS.
  Opaque KE_ID_BEFORE.

  Lemma ASSUMPTION_generates_new_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_generates_new_ex.
  Proof.
    introv h; simpl in *.
    allrw interp_KE_ID_BEFORE.
    unfold ui_has_counter in h.
    repnd; GC; subst.

    unfold id_before, id_after in *; simpl; exrepnd; subst.
    rename mem0 into mem1.
    rename mem into mem2.
    simpl in *.
    unfold trusted_state_before, trusted_state_after in *; simpl in *.
    exrepnd.
    rewrite h2 in h1; ginv.
    rewrite h2 in h0; ginv.
    unfold disseminate_data in *.

    unfold M_byz_state_sys_on_event_of_trusted in *; simpl in *.
    unfold M_byz_state_sys_before_event_of_trusted in *; simpl in *.
    unfold M_byz_output_sys_on_event in *.
    rewrite h2 in *; simpl in *.

    applydup preserves_usig_id in h4 as eqid; auto;[].

    apply map_option_Some in h4; exrepnd; rev_Some; simpl in *.
    apply map_option_Some in h5; exrepnd; rev_Some; simpl in *.
    rewrite M_byz_output_ls_on_event_as_run in h3.
    rewrite h5 in h3; simpl in *.

    pose proof (MinBFT_M_byz_run_ls_on_event_unroll_sp e c2) as w.
    rewrite h5 in w.
    rewrite h1 in w.

    clear h1 h5.

    apply on_M_trusted_implies_or in h4.
    apply on_M_trusted_implies_or in h0.
    repndors; exrepnd; subst; simpl in *; ginv;
      try (inversion w0; subst; simpl in *; clear w0);
      ginv; simpl in *;
        unfold state_of_trusted; simpl; rev_Some; [| |].

    { apply option_map_Some in h1; exrepnd; subst; simpl in *.
      unfold M_byz_run_ls_on_this_one_event in w1; simpl in *.

      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; ginv;[].

      (* XXXXXXXXXXXX *)
      autorewrite with minbft in *.
      Time minbft_dest_msg Case;
        repeat (simpl in *; autorewrite with minbft in *; smash_minbft2); repndors; smash_minbft2;
        try (complete (unfold state_of_trusted_in_ls, find_trusted_sub in *; simpl in *; ginv;
                       simpl in *; tcsp;
                       unfold ui_has_counter, ui2counter, state_of_trusted in *; simpl in *;
                       eexists; dands;[| | |right;eauto|]; simpl; auto; try omega;
                       try (rename_hyp_with invalid_prepare inv);
                       try (complete (eapply data_is_owned_by_invalid_prepare_implies_false in inv; eauto; tcsp));
                       remember (usig_counters u) as K; destruct K; simpl in *; tcsp;
                       destruct n; simpl in *; tcsp; try omega;
                         try (complete (f_equal; apply Max.max_l; try omega));
                         try (complete (left; dands; try omega; apply les_reflexive));
                         try (complete (left; dands; try apply les_reflexive; apply lt_n_S; apply Nat.max_lt_iff; left; try omega))));
        try (complete (ginv; simpl in *; autorewrite with minbft in *;
                         rename_hyp_with invalid_commit invc;
                         eapply data_is_owned_by_invalid_commit_not_pil_implies_false in invc; eauto; tcsp)). }

    { unfold M_byz_run_ls_on_this_one_event in *; simpl in *.
      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig in *; simpl in *; tcsp;[|].

      { unfold M_break in *; simpl in *; smash_minbft;[].
        repnd; simpl in *.
        apply option_map_Some in w1; exrepnd; subst; simpl in *; ginv. }

      { ginv; simpl in *.
        unfold state_of_trusted_in_ls, state_of_trusted in *; simpl in *.
        destruct i; simpl in *; repnd; tcsp; simpl in *; repndors; tcsp; ginv.

        unfold ui_has_counter, ui2counter, state_of_trusted in *; simpl in *.
        eexists; dands;[| | |right;eauto|]; simpl; auto; try omega; eauto 3 with minbft. } }

    { unfold state_of_trusted_in_ls, state_of_trusted in *; simpl in *.

      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig in *; simpl in *; tcsp;[].
      destruct i; simpl in *; repnd; tcsp; simpl in *; tcsp.
      repndors; subst; simpl in *; tcsp; ginv.

      unfold ui_has_counter, ui2counter, state_of_trusted in *; simpl in *.
      eexists; dands;[| | |right;eauto|]; simpl; auto; try omega; eauto 3 with minbft. }
  Qed.
  Hint Resolve ASSUMPTION_generates_new_true : minbft.

End MinBFTass_new.


Hint Resolve ASSUMPTION_generates_new_true : minbft.
