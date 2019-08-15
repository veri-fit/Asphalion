Require Export MinBFTprops0.
Require Export MinBFTrep.
Require Export MinBFTstate.
Require Export MinBFTsubs.
Require Export MinBFTtacts2.


Section MinBFTmon.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma le_usig_counter_increment_USIG :
    forall u, usig_counter u <= usig_counter (increment_USIG u).
  Proof.
    tcsp.
  Qed.
  Hint Resolve le_usig_counter_increment_USIG : minbft.

  Lemma monotonicity_local :
    forall {eo : EventOrdering}
           (e : Event)
           (s1 s2 : USIG_state),
      is_replica e
      -> M_state_sys_before_event MinBFTsys e USIGname = Some s1
      -> M_state_sys_on_event MinBFTsys e USIGname = Some s2
      -> usig_counter s1 <= usig_counter s2.
  Proof.
    introv isr eqst1 eqst2.

    apply map_option_Some in eqst1.
    apply map_option_Some in eqst2.

    unfold is_replica in isr.
    destruct isr as [r isr].
    rewrite isr in *; simpl in *.
    exrepnd; rev_Some.

    applydup M_run_ls_on_event_ls_is_minbft in eqst2; exrepnd; subst; simpl in *.
    rewrite M_run_ls_on_event_unroll2 in eqst2.
    rewrite eqst1 in eqst2; simpl in *.
    applydup M_run_ls_before_event_ls_is_minbft in eqst1; exrepnd; subst; simpl in *.
    unfold state_of_subcomponents in *; simpl in *; ginv.
    clear eqst1.

    apply map_option_Some in eqst2; exrepnd; rev_Some; simpl in *.
    autorewrite with comp minbft in *.

    Time minbft_dest_msg Case;
      repeat (simpl in *; autorewrite with comp minbft in *; smash_minbft2).
  Qed.

  Lemma monotonicity_local2 :
    forall {eo : EventOrdering}
           (e1 e2 : Event)
           (s1 s2 : USIG_state),
      is_replica e2
      -> e1 ⊂ e2
      -> M_state_sys_on_event MinBFTsys e1 USIGname = Some s1
      -> M_state_sys_on_event MinBFTsys e2 USIGname = Some s2
      -> usig_counter s1 <= usig_counter s2.
  Proof.
    introv isr lte eqst1 eqst2.
    applydup pred_implies_local_pred in lte.
    subst.
    rewrite <- M_state_sys_before_event_as_M_state_sys_on_event_pred in eqst1; eauto 3 with eo.
    eapply monotonicity_local; eauto.
  Qed.

  Lemma monotonicity :
    forall {eo : EventOrdering}
           (e1 e2 : Event)
           (s1 s2 : USIG_state),
      is_replica e2
      -> M_state_sys_on_event MinBFTsys e1 USIGname = Some s1
      -> M_state_sys_on_event MinBFTsys e2 USIGname = Some s2
      -> e1 ⊑ e2
      -> usig_counter s1 <= usig_counter s2.
  Proof.
    intros eo e1 e2; revert e1.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv isrep eqst1 eqst2 lte.

    apply localHappenedBeforeLe_implies_or2 in lte; repndors; subst; tcsp;[|].

    { rewrite eqst1 in eqst2; ginv. }

    apply local_implies_pred_or_local in lte; repndors; exrepnd.

    {
      eapply (@M_state_sys_before_event_if_on_event_direct_pred _ _ _ _ _ _ _ _ USIGname) in lte;[|eauto].
      eapply monotonicity_local; eauto.
    }

    pose proof (M_state_sys_on_event_some_between e e2 MinBFTsys USIGname s2) as q.
    repeat (autodimp q hyp); eauto 3 with eo minbft comp;[].
    exrepnd.

    pose proof (ind e lte1 e1 s1 s') as ind; repeat (autodimp ind hyp); eauto 3 with eo minbft comp.
    pose proof (monotonicity_local2 e e2 s' s2) as q; repeat (autodimp q hyp); try omega.
  Qed.


End MinBFTmon.


Hint Resolve le_usig_counter_increment_USIG : minbft.
