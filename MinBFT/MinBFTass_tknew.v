Require Export MinBFTass_knew.


Section MinBFTass_tknew.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Lemma ASSUMPTION_trusted_knew_or_learns_or_gen_true :
    forall (eo : EventOrdering) t, assume_eo eo (ASSUMPTION_trusted_knew_or_learns_or_gen t).
  Proof.
    introv kn.
    apply ASSUMPTION_all_knew_or_learns_or_gen_true; auto.
  Qed.
  Hint Resolve ASSUMPTION_trusted_knew_or_learns_or_gen_true : minbft.

End MinBFTass_tknew.


Hint Resolve ASSUMPTION_trusted_knew_or_learns_or_gen_true : minbft.
