Require Export MinBFTass_knew.
Require Export MinBFTass_genfor.
(*Require Export MinBFTass_lig.*)
(*Require Export MinBFTass_diss.*)


Section MinBFTass_ktrust.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma ASSUMPTION_know_data_implies_know_trust_true :
    forall eo, assume_eo eo ASSUMPTION_know_data_implies_know_trust.
  Proof.
    introv; introv.
    rewrite <- sequent_true_iff_interpret.
    apply DERIVED_RULE_implies_know_trust_true; simseqs j;
      apply sequent_true_iff_interpret; eauto 2 with minbft.
    { apply ASSUMPTION_all_knew_or_learns_or_gen_true. }


  Abort.

End MinBFTass_ktrust.

