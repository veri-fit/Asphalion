Require Export ComponentSM3.
Require Export TrIncprops2.


Section TrIncsm_mon.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma les_update_counter :
    forall l a b, les l (update_counter a b l).
  Proof.
    induction l; introv; simpl; tcsp.
    destruct a0; simpl; tcsp.
    dands; try apply max_prop2; apply les_reflexive.
  Qed.
  Hint Resolve les_update_counter : minbft.

  Lemma getCounter_nil :
    forall cid, getCounter cid [] = 0.
  Proof.
    introv; unfold getCounter; simpl; destruct cid; auto.
  Qed.
  Hint Rewrite getCounter_nil : minbft.

  Lemma getCounter_0_cons :
    forall a l, getCounter 0 (a :: l) = a.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite getCounter_0_cons : minbft.

  Lemma pos_implies_not_all_zeros_nil :
    forall cid new,
      0 < new
      -> ~ all_zeros (update_counter cid new []).
  Proof.
    induction cid; introv h q; simpl in *; tcsp.
    { destruct new; simpl in *; tcsp. }
    { apply IHcid in q; tcsp. }
  Qed.
  Hint Resolve pos_implies_not_all_zeros_nil : minbft.

  Lemma implies_lts_update_counter :
    forall cid new l,
      getCounter cid l < new
      -> lts l (update_counter cid new l).
  Proof.
    induction cid; introv h; simpl in *; tcsp.

    { destruct l; simpl in *; tcsp; autorewrite with minbft in *.

      { destruct new; simpl; tcsp. }

      { left; dands; eauto 3 with minbft; try apply les_reflexive.
        apply Nat.max_lt_iff; tcsp. } }

    { destruct l; simpl in *; tcsp; autorewrite with minbft in *; eauto 3 with minbft. }
  Qed.
  Hint Resolve implies_lts_update_counter : minbft.

  Lemma USIG_sm_mon :
    forall n l s1 s2,
      trusted_run_sm_on_inputs s1 (USIG_comp n) l = s2
      -> trinc_counters s1 = trinc_counters s2
         \/
         lts (trinc_counters s1) (trinc_counters s2).
  Proof.
    unfold trusted_run_sm_on_inputs.
    induction l; introv run; simpl in *; subst; tcsp.
    destruct a; repnd; simpl in *; tcsp;[].
    unfold update_state in *; simpl in *.
    autorewrite with comp in *.

    unfold try_update_TRINC in *; simpl in *; dest_cases w;[].

    match goal with
    | [ |- _ \/ lts (trinc_counters ?a) (trinc_counters ?b) ] =>
      pose proof (IHl (update_TRINC msg0 msg s1) b) as IHl
    end; repeat (autodimp IHl hyp); simpl in *; repndors; tcsp; try omega; smash_minbft2.

    { right; rewrite <- IHl; eauto 3 with minbft. }

    { right; eapply lts_transitive;[|eauto]; eauto 3 with minbft. }
  Qed.

End TrIncsm_mon.


Hint Resolve les_update_counter : minbft.
Hint Resolve pos_implies_not_all_zeros_nil : minbft.
Hint Resolve implies_lts_update_counter : minbft.

Hint Rewrite getCounter_nil : minbft.
Hint Rewrite getCounter_0_cons : minbft.
