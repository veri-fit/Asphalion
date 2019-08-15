Require Export TrInccount.
Require Export TrInckn.
Require Export MinBFTacc_sp.


Section TrIncacc_new.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma accepted_implies_new_request_step :
    forall {eo  : EventOrdering}
           (e   : Event)
           (r   : Rep)
           (req : Request)
           (i   : nat)
           (l   : list name)
           (s   : MAIN_state)
           (s1  : TRINC_state)
           (s2  : LOG_state),
      In (send_accept (accept req i) l) (M_output_ls_on_this_one_event (MinBFTlocalSys_new r s s1 s2) e)
      -> new_bare_request (request_b req) (vreq s) = true.
  Proof.
    introv out.
    unfold M_output_ls_on_this_one_event in *.
    remember (trigger_op e) as trig.
    destruct trig; rev_Some; simpl in *; tcsp.
    autorewrite with minbft in *.

    Time minbft_dest_msg Case;
      repeat (simpl in *; autorewrite with minbft in * );
      repeat smash_minbft2;
      repndors; ginv; simpl in *; smash_minbft2;
        try (complete (unfold invalid_commit, valid_commit, invalid_commit2, valid_commit2 in *; smash_minbft;
                         rewrite <- new_bare_request_as_new_request; auto));
        try (complete (unfold invalid_prepare, valid_prepare in *; smash_minbft;
                         rewrite <- new_bare_request_prep_as_new_request_prep; auto)).
  Qed.

  Lemma accepted_implies_new_request :
    forall {eo  : EventOrdering}
           (e   : Event)
           (req : Request)
           (i   : nat)
           (l   : list name)
           (s   : MAIN_state),
      is_replica e
      -> In (send_accept (accept req i) l) (M_output_sys_on_event MinBFTsys e)
      -> M_state_sys_before_event MinBFTsys e MAINname = Some s
      -> new_bare_request (request_b req) (vreq s) = true.
  Proof.
    introv isrep out eqst.
    unfold is_replica in *; exrepnd.
    unfold M_output_sys_on_event in *; simpl in *.
    unfold M_state_sys_before_event in *; simpl in *.
    rewrite isrep0 in out, eqst; simpl in *.
    unfold M_state_ls_before_event in eqst.
    apply map_option_Some in eqst; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbft in eqst1; exrepnd; subst; simpl in *; ginv.
    rewrite M_output_ls_on_event_as_run_before in out.
    rewrite eqst1 in out.
    apply accepted_implies_new_request_step in out; auto.
  Qed.

End TrIncacc_new.

