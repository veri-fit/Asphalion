Require Export TrInccount.
Require Export TrInckn.


Section TrIncacc_exec.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma accepted_implies_latest_executed_step :
    forall {eo     : EventOrdering}
           (e      : Event)
           (r      : Rep)
           (req    : Request)
           (i      : nat)
           (l      : list name)
           (s  s'  : MAIN_state)
           (s1 s1' : TRINC_state)
           (s2 s2' : LOG_state),
      In (send_accept (accept req i) l) (M_output_ls_on_this_one_event (MinBFTlocalSys_new r s s1 s2) e)
      -> M_run_ls_on_this_one_event (MinBFTlocalSys_new r s s1 s2) e = Some (MinBFTlocalSys_new r s' s1' s2')
      ->
      exists t,
        find_latest_executed_request (request2sender req) (vreq s') = Some t /\
        request2timestamp req <= t.
  Proof.
    introv out eqst.
    unfold M_output_ls_on_this_one_event in *.
    apply map_option_Some in eqst; exrepnd; rev_Some; simpl in *.
    rewrite eqst1 in out; simpl in *.
    autorewrite with minbft in *.

    Time minbft_dest_msg Case;
      repeat (simpl in *; autorewrite with minbft in * );
      repeat smash_minbft2;
      repndors; ginv; simpl in *; smash_minbft2;
        try (complete (apply MinBFTlocalSys_new_inj in eqst0; repnd; subst; smash_minbft2)).
  Qed.

  Lemma accepted_implies_latest_executed :
    forall {eo  : EventOrdering}
           (e   : Event)
           (req : Request)
           (i   : nat)
           (l   : list name)
           (s   : MAIN_state),
      is_replica e
      -> In (send_accept (accept req i) l) (M_output_sys_on_event MinBFTsys e)
      -> M_state_sys_on_event MinBFTsys e MAINname = Some s
      ->
      exists t,
        find_latest_executed_request (request2sender req) (vreq s) = Some t
        /\ request2timestamp req <= t.
  Proof.
    introv isrep out eqst.
    unfold is_replica in *; exrepnd.
    unfold M_output_sys_on_event in *; simpl in *.
    unfold M_state_sys_on_event in *; simpl in *.
    rewrite isrep0 in out, eqst; simpl in *.
    unfold M_state_ls_on_event in eqst.
    apply map_option_Some in eqst; exrepnd; rev_Some.
    applydup M_run_ls_on_event_ls_is_minbft in eqst1; exrepnd; subst; simpl in *; ginv.
    rewrite M_output_ls_on_event_as_run_before in out.
    rewrite M_run_ls_on_event_unroll in eqst1.
    rewrite M_run_ls_before_event_unroll_on in out.
    rewrite M_run_ls_before_event_unroll_on in eqst1.

    destruct (dec_isFirst e) as [d|d].

    { rewrite MinBFTlocalSys_as_new in out, eqst1.
      eapply accepted_implies_latest_executed_step in out; eauto. }

    apply map_option_Some in eqst1; exrepnd; rev_Some.
    rewrite eqst1 in out.
    applydup M_run_ls_on_event_ls_is_minbft in eqst1; exrepnd; subst.
    eapply accepted_implies_latest_executed_step in out; eauto.
  Qed.

End TrIncacc_exec.
