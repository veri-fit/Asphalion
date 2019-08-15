Require Export CalculusSM_derived2.
Require Export MinBFTprops2.
Require Export MinBFTtacts2.


Section MinBFTass_genfor.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Lemma ASSUMPTION_gen_for_implies_tknows_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_gen_for_implies_tknows.
  Proof.
    introv kn gf; simpl in *.
    unfold knows_after in *; exrepnd; exists mem; dands; auto.
    unfold generated_for in *; simpl in *; exrepnd; subst; simpl in *.
    unfold MinBFT_data_knows in *; simpl in *.
    destruct c; simpl in *; tcsp.
    unfold request_data_in_log in *; smash_minbft2.
  Qed.

End MinBFTass_genfor.

Hint Resolve ASSUMPTION_gen_for_implies_tknows_true : minbft.
