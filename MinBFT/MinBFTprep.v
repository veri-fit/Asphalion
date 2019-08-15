Require Export MinBFTprops0.


Section MinBFTprep.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma invalid_prepare_false_implies :
    forall slf km v p s,
      invalid_prepare slf km v p s = false
      -> valid_prepare slf km v p s = true.
  Proof.
    introv h.
    unfold invalid_prepare in *; smash_minbft.
  Qed.
  Hint Resolve invalid_prepare_false_implies : minbft.

  Lemma valid_prepare_implies_executed_prior :
    forall slf km v p s,
      valid_prepare slf km v p s = true
      -> executed_prior_counter (prepare2ui p) s = true.
  Proof.
    introv h.
    unfold valid_prepare in h; smash_minbft.
  Qed.
  Hint Resolve valid_prepare_implies_executed_prior : minbft.

End MinBFTprep.
