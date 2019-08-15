Require Export MinBFTass_tknows.
Require Export MinBFTass_knew.
Require Export MinBFTass_diss.
Require Export ComponentAxiom.


Section MinBFTass_tlearn.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma ASSUMPTION_trusted_learns_if_gen_true :
    forall (eo : EventOrdering),
      AXIOM_authenticated_messages_were_sent_or_byz eo MinBFTsys
      -> assume_eo eo (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen).
  Proof.
    introv sendbyz; introv.
    rewrite <- sequent_true_iff_interpret.
    apply DERIVED_RULE_implies_all_trusted_learns_if_gen2_true; simseqs j;
      apply sequent_true_iff_interpret; eauto 3 with minbft;
      try (apply ASSUMPTION_in_knows_implies_trusted_knows_true);
      try (apply ASSUMPTION_diss_correct_implies_knows_true);
      try (apply ASSUMPTION_all_knew_or_learns_or_gen_true).

    { apply ASSUMPTION_authenticated_messages_were_sent_or_byz_true; simpl; auto; tcsp;
        try (complete (introv h q; destruct a as [a x], a; simpl in *; ginv; simpl in *; tcsp; eauto));
        try (complete (introv h q; destruct m; simpl in *; tcsp; repndors; subst; tcsp;
                       try (destruct p as [p a], p, a);
                       try (destruct c as [c a], c, a);
                       simpl in *; repndors; subst; simpl in *; tcsp)). }
  Qed.

End MinBFTass_tlearn.


Hint Resolve ASSUMPTION_trusted_learns_if_gen_true : minbft.
