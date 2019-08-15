Require Export MinBFTg.


Section MinBFTrep.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Definition is_replica {eo : EventOrdering} (e : Event) :=
    exists r, loc e = MinBFT_replica r.

  Lemma local_pred_preserves_is_replica :
    forall {eo : EventOrdering} (e1 e2 : Event),
      e1 ⊂ e2
      -> is_replica e2
      -> is_replica e1.
  Proof.
    introv lte isrep.
    unfold is_replica in *; exrepnd; exists r; rewrite <- isrep0; eauto 3 with eo.
  Qed.
  Hint Resolve local_pred_preserves_is_replica : minbft.

End MinBFTrep.


Hint Resolve local_pred_preserves_is_replica : minbft.
