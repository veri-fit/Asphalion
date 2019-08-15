Require Export ComponentSM7.
Require Export MinBFTgen.


Section MinBFTcount_gen3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma M_run_ls_before_event_minbft_preserves_in_subs :
    forall cn {eo : EventOrdering} (e : Event) R s subs subs',
      M_run_ls_before_event (MinBFTlocalSysP R subs) e
      = Some (MinBFTlocalSys_newP R s subs')
      -> in_subs cn subs = true
      -> in_subs cn subs' = true.
  Proof.
    intros cn eo.
    induction e as [e ind] using predHappenedBeforeInd;introv eqls ins.
    rewrite M_run_ls_before_event_unroll in eqls.
    destruct (dec_isFirst e) as [d|d]; ginv.

    { inversion eqls as [xx]; subst; auto. }

    apply map_option_Some in eqls; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbftP in eqls1; exrepnd; subst.
    apply ind in eqls1; auto; eauto 3 with eo.

    clear dependent subs.
    apply map_option_Some in eqls0; exrepnd; simpl in *; rev_Some.
    autorewrite with minbft comp in *.
    Time minbft_dest_msg Case;
      repeat (autorewrite with minbft comp in *; simpl in *; smash_minbft2);
      try (complete (inversion eqls2; subst; auto));
      repeat (gdest; smash_minbft1_at_ eqls2; repeat hide_break; repnd; simpl in *; repndors; ginv; tcsp; eauto 2 with minbft);
      try (complete (inversion eqls2; subst; simpl in *; in_subs_tac)).
  Qed.
  Hint Resolve M_run_ls_before_event_minbft_preserves_in_subs : minbft.

End MinBFTcount_gen3.


Hint Resolve M_run_ls_before_event_minbft_preserves_in_subs : minbft.
