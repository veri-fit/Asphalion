Require Export TrIncprops3.
Require Export TrIncagreement.


Section TrIncagreement_iff.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Lemma agreement_iff :
    forall (eo : EventOrdering) (e1 e2 : Event) r1 r2 i1 i2 l1 l2,
      AXIOM_authenticated_messages_were_sent_or_byz eo MinBFTsys
      -> (send_accept (accept r1 i1) l1) ∈ MinBFTsys ⇝ e1
      -> (send_accept (accept r2 i2) l2) ∈ MinBFTsys ⇝ e2
      -> (i1 = i2 <-> r1 = r2).
  Proof.
    introv sendbyz send1 send2.
    applydup in_output_implies_is_replica in send1 as isrep1.
    applydup in_output_implies_is_replica in send2 as isrep2.
    split; intro h; subst.
    { eapply agreement; eauto. }
    { eapply unique_counter; try exact send1; try exact send2; auto. }
  Qed.

End TrIncagreement_iff.
