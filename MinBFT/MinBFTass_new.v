Require Export MinBFTinv.
Require Export MinBFTprops2.
Require Export MinBFTrun.


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
    unfold disseminate_data in *; exrepnd; simpl in *.

    unfold M_byz_state_sys_on_event in *; simpl in *.
    unfold M_byz_state_sys_before_event in *; simpl in *.
    unfold M_byz_output_sys_on_event in *.
    revert dependent o.
    rewrite h2 in *; simpl in *.
    introv out dout.

    applydup preserves_usig_id in h4 as eqid; auto;[].

    (*pose proof (M_byz_compose_step_trusted e (MinBFTlocalSys c2) (incr_n_proc (USIG_comp c2))) as h.
    repeat (autodimp h hyp); eauto 3 with minbft.
    exrepnd; simpl in *.*)

    rewrite M_byz_output_ls_on_event_as_run in out; simpl in *.

    apply map_option_Some in h4; exrepnd; rev_Some; simpl in *; minbft_simp.
    apply map_option_Some in h5; exrepnd; rev_Some; simpl in *; minbft_simp.

    rewrite M_byz_run_ls_on_event_unroll2 in h1; simpl in *.

    match goal with
    | [ H : context[M_byz_run_ls_before_event ?ls ?e] |- _ ] =>
      remember (M_byz_run_ls_before_event ls e) as run; symmetry in Heqrun
    end.
    apply M_byz_run_ls_before_event_ls_is_minbft in Heqrun.
    repndors; exrepnd; subst; simpl in *.

    { unfold M_byz_output_ls_on_this_one_event in *; simpl in *.
      unfold M_byz_run_ls_on_this_one_event in *; simpl in *.
      unfold M_byz_run_ls_on_one_event in *; simpl in *.
      unfold M_byz_run_ls_on_input in *; simpl in *.
      unfold data_is_in_out, event2out in *; simpl in *.

      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; tcsp.

      { match goal with
        | [ H : context[M_run_ls_on_input ?ls ?cn ?i] |- _ ] =>
          remember (M_run_ls_on_input ls cn i) as oni; symmetry in Heqoni
        end.
        repnd; simpl in *; subst; simpl in *; minbft_simp.
        applydup (M_run_ls_on_input_ls_is_minbft_new (msg_comp_name 0)) in Heqoni.
        exrepnd; subst; simpl in *; ginv; simpl in *.
        apply in_flat_map in dout; exrepnd; simpl in *.

        unfold M_run_ls_on_input in *; simpl in *.
        autorewrite with minbft in *; simpl in *.

        Time minbft_dest_msg Case;
          repeat (simpl in *; autorewrite with minbft in *; smash_minbft2); repndors; smash_minbft2;
            unfold lower_out_break in *; simpl in *; minbft_simp;
            repeat (repndors; ginv; subst; tcsp; simpl in *; tcsp);
            unfold ui_has_counter, ui2counter, state_of_trusted in *; simpl in *;
              try (eexists; dands;[| | |right;eauto|]; simpl; auto; try omega);
              try (rename_hyp_with invalid_prepare inv);
              try (complete (eapply data_is_owned_by_invalid_prepare_implies_false in inv; eauto; tcsp));
              try (rename_hyp_with invalid_commit invc);
              try (eapply data_is_owned_by_invalid_commit_not_pil_implies_false in invc; eauto; tcsp);
              remember (usig_counters u) as K; destruct K; simpl in *; tcsp;
                destruct n; simpl in *; tcsp; try omega;
                  try (complete (f_equal; apply Max.max_l; try omega));
                  try (complete (left; dands; try omega; apply les_reflexive));
                  try (complete (left; dands; try apply les_reflexive; apply lt_n_S; apply Nat.max_lt_iff; left; try omega)). }

      { pose proof (snd_M_run_ls_on_trusted_incr_n_procs_eq (USIGlocalSys u) i) as z.
        unfold LocalSystem in *; simpl in *; rewrite z in out; clear z.
        rewrite rw_M_run_ls_on_trusted_USIGlocalSys in out.
        destruct i as [cn i]; simpl in *; dest_cases w;[].
        subst; simpl in *.
        destruct i; repnd; repeat (simpl in *; repndors; ginv; tcsp).
        unfold ui_has_counter, ui2counter, state_of_trusted in *; simpl in *.
        eexists; dands;[| | |right;eauto|]; simpl; auto; try omega; eauto 3 with minbft. } }

    { unfold M_byz_output_ls_on_this_one_event in *; simpl in *.
      unfold M_byz_run_ls_on_this_one_event in *; simpl in *.
      unfold M_byz_run_ls_on_one_event in *; simpl in *.
      unfold M_byz_run_ls_on_input in *; simpl in *.
      unfold data_is_in_out, event2out in *; simpl in *.

      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; tcsp;[].

      pose proof (snd_M_run_ls_on_trusted_incr_n_procs_eq (USIGlocalSys u) i) as z.
      unfold LocalSystem in *; simpl in *; rewrite z in out; clear z.
      rewrite rw_M_run_ls_on_trusted_USIGlocalSys in out.
      destruct i as [cn i]; simpl in *; dest_cases w;[].
      subst; simpl in *.
      destruct i; repnd; repeat (simpl in *; repndors; ginv; tcsp).
      unfold ui_has_counter, ui2counter, state_of_trusted in *; simpl in *.
      eexists; dands;[| | |right;eauto|]; simpl; auto; try omega; eauto 3 with minbft. }
  Qed.
  Hint Resolve ASSUMPTION_generates_new_true : minbft.

End MinBFTass_new.


Hint Resolve ASSUMPTION_generates_new_true : minbft.
