Require Export MicroBFTprops2.


Section MicroBFTass_uniq.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Lemma ASSUMPTION_disseminate_unique_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_disseminate_unique.
  Proof.
    introv h; simpl in *; exrepnd; subst; GC.
    rewrite h0 in h1; ginv.

    unfold disseminate_data in *; simpl in *.
    unfold M_byz_output_sys_on_event in *; simpl in *.
    rewrite M_byz_output_ls_on_event_as_run in h5, h6.
    rewrite h0 in *; simpl in *.
    unfold MicroBFTheader.node2name in *; simpl in *; subst.
    unfold MicroBFTsys in *; simpl in *.

    remember (M_byz_run_ls_before_event (MicroBFTlocalSys (loc e)) e) as ls; symmetry in Heqls.
    apply M_byz_run_ls_before_event_ls_is_microbft in Heqls.
    repndors; exrepnd; subst.

    { rewrite h5 in *; ginv.
      unfold M_byz_output_ls_on_this_one_event in h5.
      unfold M_byz_run_ls_on_one_event in h5.
      revert dependent o.
      unfold data_is_in_out, event2out in *.
      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; ginv; tcsp; introv a run b.

      { allrw in_flat_map; exrepnd.
        unfold M_run_ls_on_input in *.
        autorewrite with microbft in *.
        Time microbft_dest_msg Case;
          repeat (simpl in *; autorewrite with microbft in *; smash_microbft2);
          try (complete (repndors; ginv; tcsp)). }

      { unfold M_run_ls_on_trusted, M_run_ls_on_input in *; simpl in *.
        destruct i, o; simpl in *; repndors; ginv; tcsp. } }

    { rewrite h5 in *; ginv.
      unfold M_byz_output_ls_on_this_one_event in h5.
      unfold M_byz_run_ls_on_one_event in h5.
      revert dependent o.
      unfold data_is_in_out, event2out in *.
      remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; ginv; tcsp; introv a run b.

      unfold M_run_ls_on_trusted, M_run_ls_on_input in *; simpl in *.
      autorewrite with microbft in *.
      destruct i, o; simpl in *; repndors; ginv; tcsp. }
  Qed.
  Hint Resolve ASSUMPTION_disseminate_unique_true : microbft.

End MicroBFTass_uniq.


Hint Resolve ASSUMPTION_disseminate_unique_true : microbft.
