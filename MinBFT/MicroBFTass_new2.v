Require Export MicroBFTprops2.


Section MicroBFTass_new.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Opaque KE_TOWNS.
  Opaque KE_ID_BEFORE.

  Lemma ASSUMPTION_generates_new_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_generates_new.
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
    rewrite h2 in h3; ginv.
    unfold disseminate_data in *.

    unfold M_byz_state_sys_on_event in *; simpl in *.
    unfold M_byz_state_sys_before_event in *; simpl in *.
    unfold M_byz_output_sys_on_event in *.
    unfold M_byz_output_ls_on_event in *.
    rewrite h2 in *; simpl in *.

    applydup preserves_usig_id in h1 as eqid; auto;[].

    apply map_option_Some in h1; exrepnd; rev_Some; simpl in *; microbft_simp.
    apply map_option_Some in h5; exrepnd; rev_Some; simpl in *; microbft_simp.
    rewrite M_byz_run_ls_on_event_unroll2 in h1; simpl in *.

    remember (M_byz_run_ls_before_event (MicroBFTsys (MicroBFTheader.node2name n0)) e) as ls; symmetry in Heqls.
    simpl in *.
    rewrite Heqls in *.
    unfold MicroBFTsys in *; simpl in *.

    apply M_byz_run_ls_before_event_ls_is_microbft in Heqls.
    repndors; exrepnd; subst; simpl in *; microbft_simp.

    { unfold M_byz_run_ls_on_this_one_event in *; simpl in *.
      unfold M_byz_run_ls_on_one_event in *; simpl in *.
      revert dependent o.
      unfold data_is_in_out, event2out in *.
      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; ginv; tcsp; introv run j.

      { allrw in_flat_map; exrepnd.
        unfold M_run_ls_on_input in *.
        autorewrite with microbft in *.
        Time microbft_dest_msg Case;
          repeat (simpl in *; autorewrite with microbft in *; smash_microbft2);
          try (complete (repndors; ginv; simpl in *;
                           unfold ui_has_counter, ui2counter, state_of_trusted in *; simpl in *;
                             eexists; dands; try reflexivity; try omega; tcsp)). }

      { unfold M_run_ls_on_trusted, M_run_ls_on_input in *; simpl in *.
        autorewrite with microbft in *.
        rewrite @on_comp_sing_eq in run.
        rewrite @on_comp_sing_eq in h1.
        dest_cases w; simpl in *;[].
        destruct i, o; simpl in *; repndors; ginv; tcsp;[].
        inversion w; subst; simpl in *.
        rewrite (UIP_refl_CompName _ w) in *; auto; simpl in *.
        destruct it_input; simpl in *; repnd; simpl in *; tcsp; microbft_simp; ginv;
          unfold ui_has_counter, ui2counter, state_of_trusted in *; simpl in *;
            eexists; dands; try reflexivity; try omega; tcsp. } }

    { unfold M_byz_run_ls_on_this_one_event in *; simpl in *.
      unfold M_byz_run_ls_on_one_event in *; simpl in *.
      revert dependent o.
      unfold data_is_in_out, event2out in *.
      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; ginv; tcsp; introv run j.

      unfold M_run_ls_on_trusted, M_run_ls_on_input in *; simpl in *.
      autorewrite with microbft in *.
      rewrite @on_comp_sing_eq in run.
      rewrite @on_comp_sing_eq in h1.
      dest_cases w; simpl in *;[].
      destruct i, o; simpl in *; repndors; ginv; tcsp;[].
      inversion w; subst; simpl in *.
      rewrite (UIP_refl_CompName _ w) in *; auto; simpl in *.
      destruct it_input; simpl in *; repnd; simpl in *; tcsp; microbft_simp; ginv;
        unfold ui_has_counter, ui2counter, state_of_trusted in *; simpl in *;
          eexists; dands; try reflexivity; try omega; tcsp. }
  Qed.
  Hint Resolve ASSUMPTION_generates_new_true : microbft.

End MicroBFTass_new.


Hint Resolve ASSUMPTION_generates_new_true : microbft.
