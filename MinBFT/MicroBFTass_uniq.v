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

    pose proof (ex_M_byz_run_ls_before_event_MicroBFTlocalSys e (loc e)) as run.
    repndors; exrepnd; rewrite run0 in h5, h6; simpl in *.

    { remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; ginv; tcsp;[].
      unfold state_of_trusted in *; simpl in *.
      unfold USIG_update in *; destruct i; simpl in *;
        repeat (simpl in *; autorewrite with microbft in *; smash_microbft2);
        try (complete (inversion Heqx; clear Heqx; subst; simpl in *; repndors;
                       tcsp; subst; simpl in *; tcsp)). }

    remember (trigger e) as trig; symmetry in Heqtrig.
    destruct trig; simpl in *; ginv; tcsp;[|].

    { autorewrite with microbft in *.
      Time microbft_dest_msg Case;
        repeat (simpl in *; autorewrite with microbft in *; smash_microbft2);
        try (complete (repndors; ginv; tcsp)). }

    { unfold state_of_trusted in *; simpl in *.
      unfold USIG_update in *; destruct i; simpl in *;
        repeat (simpl in *; autorewrite with microbft in *; smash_microbft2);
        try (complete (inversion Heqx; clear Heqx; subst; simpl in *; repndors;
                       tcsp; subst; simpl in *; tcsp)). }
  Qed.
  Hint Resolve ASSUMPTION_disseminate_unique_true : microbft.

End MicroBFTass_uniq.


Hint Resolve ASSUMPTION_disseminate_unique_true : microbft.
