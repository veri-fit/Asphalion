Require Export CalculusSM_derived4.
Require Export MinBFTprops2.
Require Export MinBFTtacts2.


Section MinBFTass_tknows.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma ASSUMPTION_in_knows_implies_trusted_knows_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_in_knows_implies_trusted_knows.
  Proof.
    introv kn h; simpl in *; exrepnd; repndors; subst; tcsp.
    unfold knows_after in *; exrepnd; simpl in *.
    exists mem; dands; auto.
    unfold MinBFT_data_knows in *; simpl in *.
    destruct c; simpl in *; tcsp.
    unfold request_data_in_log in *; smash_minbft2.
  Qed.

End MinBFTass_tknows.

Hint Resolve ASSUMPTION_in_knows_implies_trusted_knows_true : minbft.
