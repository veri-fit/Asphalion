Require Export MinBFTass_knew0.


Section MinBFTass_knew2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma on_request_implies_generates_trusted :
    forall {eo : EventOrdering} (e : Event) r v m s1 u1 l1 s2 u2 l2 msg,
      loc e = MinBFT_replica r
      -> usig_counter u2 = S (usig_counter u1)
      -> r = usig_id u1
      -> v = current_view s1
      -> trigger_op e = Some msg
      -> msg2request msg = Some m
      -> M_run_ls_before_event (MinBFTlocalSys r) e = Some (MinBFTlocalSys_new r s1 u1 l1)
      -> M_run_ls_on_event (MinBFTlocalSys r) e = Some (MinBFTlocalSys_new r s2 u2 l2)
      -> disseminate_data
           e
           (minbft_data_ui
              (Build_UI
                 (MkPreUI (usig_id u1) (S (usig_counter u1)))
                 (create_hash_usig
                    (Build_HashData
                       v
                       m
                       (MkPreUI (usig_id u1) (S (usig_counter u1))))
                    (usig_local_keys u1)))).
  Proof.
    introv eqloc eqc eqr eqv eqtrig eqm runBef runOn.
    unfold disseminate_data; simpl.
    applydup @M_run_ls_on_event_M_byz_run_ls_on_event in runOn as byzRunOn.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    unfold M_byz_output_sys_on_event; simpl.
    rewrite M_byz_output_ls_on_event_as_run; simpl.
    unfold M_byz_output_ls_on_this_one_event.
    apply (trigger_op_Some_implies_trigger_message e msg) in eqtrig.
    allrw; simpl.

    rewrite <- eqr.
    rewrite byzRunBef; simpl.

    clear byzRunOn byzRunBef.

    rewrite M_run_ls_on_event_unroll2 in runOn.
    rewrite runBef in runOn; simpl in *.
    apply map_option_Some in runOn; exrepnd; rev_Some.
    unfold trigger_op in *.
    rewrite eqtrig in *; simpl in *; ginv.

    clear runBef.

    autorewrite with minbft in *.

    Time minbft_dest_msg Case;
      repeat (simpl in *; autorewrite with minbft in *; smash_minbft2; try omega);
      try (complete (dands; tcsp; right; left; unfold invalid_prepare, valid_prepare in *; smash_minbft2));
      try (complete (dands; tcsp; right; left; unfold invalid_commit, valid_commit in *; smash_minbft2));
      try (complete (apply MinBFTlocalSys_new_inj in runOn0; repnd; subst; try omega)).
  Qed.
  Hint Resolve on_request_implies_generates_trusted : minbft.

End MinBFTass_knew2.


Hint Resolve on_request_implies_generates_trusted : minbft.
