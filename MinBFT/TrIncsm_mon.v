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
    forall {eo : EventOrdering} (e : Event) n l s1 s2,
      loc e = MinBFT_replica n
      -> trinc_id s1 = n
      -> run_sm_on_inputs_trusted (USIG_sm_new s1) l = s2
      -> trinc_counters s1 = trinc_counters s2
         \/
         lts (trinc_counters s1) (trinc_counters s2).
  Proof.
    induction l; introv eqloc eqid run; simpl in *; tcsp.

    { autorewrite with minbft in *; simpl in *; subst; tcsp. }

    pose proof (run_sm_on_inputs_trusted_cons
                  _ _ _ (USIG_sm_new s1) a l) as w.
    simpl in *; rewrite w in run; auto; clear w;[].

    unfold USIG_update in run; destruct a; repnd; simpl in *;
      [|apply IHl in run; auto];[].

    unfold try_update_TRINC in run; simpl in *; dest_cases w.
    apply IHl in run; simpl; auto; clear IHl;[].
    simpl in *.
    repndors; exrepnd; try omega; smash_minbft2.

    { right; rewrite <- run; clear run; eauto 3 with minbft. }

    { right; eapply lts_transitive;[|eauto]; eauto 3 with minbft. }
  Qed.

End TrIncsm_mon.


Hint Resolve les_update_counter : minbft.
Hint Resolve pos_implies_not_all_zeros_nil : minbft.
Hint Resolve implies_lts_update_counter : minbft.

Hint Rewrite getCounter_nil : minbft.
Hint Rewrite getCounter_0_cons : minbft.
