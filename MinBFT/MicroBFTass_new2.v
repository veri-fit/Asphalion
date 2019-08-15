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

    unfold M_byz_state_sys_on_event_of_trusted in *; simpl in *.
    unfold M_byz_state_sys_before_event_of_trusted in *; simpl in *.
    unfold M_byz_output_sys_on_event in *.
    rewrite h2 in *; simpl in *.

    applydup preserves_usig_id in h1 as eqid; auto;[].

    apply map_option_Some in h1; exrepnd; rev_Some; simpl in *.
    apply map_option_Some in h5; exrepnd; rev_Some; simpl in *.
    rewrite M_byz_output_ls_on_event_as_run in h4.
    rewrite h5 in h4; simpl in *.

    pose proof (MicroBFT_M_byz_run_ls_on_event_unroll_sp e n) as w.
    unfold MicroBFTheader.node2name in *; ginv; subst.
    unfold MicroBFTsys in *; simpl in *.
    rewrite h5 in w.
    rewrite h1 in w.

    clear h1 h5.

    apply on_M_trusted_implies_or in h7.
    apply on_M_trusted_implies_or in h8.
    repndors; exrepnd; subst; simpl in *; ginv;
      try (inversion w0; subst; simpl in *; clear w0);
      ginv; simpl in *;
        unfold state_of_trusted; simpl; rev_Some; [| |].

    { apply option_map_Some in h2; exrepnd; subst; simpl in *.
      unfold M_byz_run_ls_on_this_one_event in w1; simpl in *.

      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; ginv;[].

      (* XXXXXXXXXXXX *)
      autorewrite with microbft in *.
      Time microbft_dest_msg Case;
        repeat (simpl in *; autorewrite with microbft in *; smash_microbft2);
        try (complete (repndors; ginv; tcsp;
                         unfold state_of_trusted_in_ls, find_trusted_sub in *;
                         simpl in *; ginv; simpl in * )). }

    { unfold M_byz_run_ls_on_this_one_event in *; simpl in *.
      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig in *; simpl in *; tcsp;[|].

      { unfold M_break in *; simpl in *; smash_microbft;[].
        repnd; simpl in *.
        apply option_map_Some in w1; exrepnd; subst; simpl in *; ginv. }

      { ginv; simpl in *.
        unfold state_of_trusted_in_ls, state_of_trusted in *; simpl in *.
        destruct i; simpl in *; repnd; tcsp; simpl in *; repndors; tcsp; ginv. } }

    { unfold state_of_trusted_in_ls, state_of_trusted in *; simpl in *.

      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig in *; simpl in *; tcsp;[].
      destruct i; simpl in *; repnd; tcsp; simpl in *; tcsp.
      repndors; subst; simpl in *; tcsp; ginv. }
  Qed.
  Hint Resolve ASSUMPTION_generates_new_true : microbft.

End MicroBFTass_new.


Hint Resolve ASSUMPTION_generates_new_true : microbft.
