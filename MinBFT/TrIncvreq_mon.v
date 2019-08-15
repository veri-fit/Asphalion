Require Export TrInccount.
Require Export TrInckn.


Section TrIncvreq_mon.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma vreq_monotonic_step :
    forall {eo : EventOrdering} (e : Event) r s u l s' c t (ls : MLocalSystem 1 0),
      M_run_ls_on_this_one_event (MinBFTlocalSys_new r s u l) e = Some ls
      -> state_of_component MAINname ls = Some s'
      -> find_latest_executed_request c (vreq s) = Some t
      -> exists t',
          find_latest_executed_request c (vreq s') = Some t'
          /\ t <= t'.
  Proof.
    introv run eqst find.
    apply map_option_Some in run; exrepnd; simpl in *; rev_Some.
    autorewrite with minbft in *.

    Time minbft_dest_msg Case;
      repeat (simpl in *; autorewrite with minbft in * );
      repeat smash_minbft2; eauto.
  Qed.

  Lemma vreq_monotonic :
    forall {eo : EventOrdering} (e1 e2 : Event) s1 s2 c t,
      is_replica e1
      -> e1 ⊏ e2
      -> M_state_sys_on_event MinBFTsys e1 MAINname = Some s1
      -> M_state_sys_before_event MinBFTsys e2 MAINname = Some s2
      -> find_latest_executed_request c (vreq s1) = Some t
      -> exists t',
          find_latest_executed_request c (vreq s2) = Some t'
          /\ t <= t'.
  Proof.
    introv isrep lte eqsta eqstb find.
    unfold M_state_sys_on_event, M_state_sys_before_event in *.
    unfold is_replica in *; exrepnd.
    applydup local_implies_loc in lte as eqloc.
    rewrite <- eqloc in *.
    rewrite isrep0 in *; simpl in *.

    unfold M_state_ls_on_event, M_state_ls_before_event in *.
    apply map_option_Some in eqsta; exrepnd; rev_Some.
    apply map_option_Some in eqstb; exrepnd; rev_Some.

    clear eqloc isrep0.

    revert dependent a0.
    revert dependent s2.
    revert dependent e2.

    induction e2 as [e ind] using predHappenedBeforeInd;[]; introv lte eqst2 comp2.

    apply local_implies_pred_or_local in lte; repndors.

    { rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred in eqst2; eauto 3 with eo;[].
      unfold local_pred in eqst2; rewrite lte in eqst2.
      rewrite eqsta1 in eqst2; ginv.
      rewrite comp2 in eqsta0; ginv.
      eexists; dands; eauto. }

    exrepnd.
    pose proof (ind e0) as ind; repeat (autodimp ind hyp);[].
    rewrite M_run_ls_before_event_unroll in eqst2.
    assert (~ isFirst e) as nif by eauto 3 with eo.
    destruct (dec_isFirst e) as [d|d]; tcsp;[].
    apply map_option_Some in eqst2; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbft in eqst1; exrepnd; subst; simpl in *.
    unfold local_pred in eqst0; rewrite lte1 in eqst0.
    unfold local_pred in eqst1; rewrite lte1 in eqst1.

    pose proof (ind s (MinBFTlocalSys_new r s s0 s3)) as ind.
    repeat (autodimp ind hyp);[].
    exrepnd.
    eapply vreq_monotonic_step in eqst0; try exact ind1;[|eauto].
    exrepnd.
    eexists; dands; eauto; try omega.
  Qed.

End TrIncvreq_mon.
