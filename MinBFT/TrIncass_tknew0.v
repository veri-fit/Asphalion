Require Export TrIncprops2.


Section TrIncass_tknew0.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  (* MOVE *)
  Hint Rewrite ui_in_log_log_new_prepare : minbft.
  Hint Rewrite ui_in_log_log_new_commit : minbft.

  Lemma invalid_prepare_false_implies_equal_views :
    forall i keys v p s,
      invalid_prepare i keys v p s = false
      -> prepare2view p = v.
  Proof.
    introv h; unfold invalid_prepare, valid_prepare in *; smash_minbft.
  Qed.
  Hint Resolve invalid_prepare_false_implies_equal_views : minbft.

  Lemma invalid_commit_false_implies_equal_views :
    forall i keys v c pil s,
      invalid_commit i keys v c pil s = false
      -> commit2view c = v.
  Proof.
    introv h; unfold invalid_commit, valid_commit in *; smash_minbft.
  Qed.
  Hint Resolve invalid_commit_false_implies_equal_views : minbft.

  Definition msg2request (m : MinBFT_msg) : option Request :=
    match m with
    | MinBFT_request r => Some r
    | MinBFT_reply r   => Some (bare_reply_r (reply_b r))
    | MinBFT_prepare p => Some (prepare2request p)
    | MinBFT_commit  c => Some (commit2request c)
    | MinBFT_accept  _ => None
    | MinBFT_debug   _ => None
    end.

  Lemma current_counter_from_usig :
    forall {eo : EventOrdering} (e : Event) i m u l,
      M_run_ls_before_event (MinBFTlocalSys i) e
      = Some (MinBFTlocalSys_new i m u l)
      -> getCounter cid0 (trinc_counters u) = current_counter m.
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv run.
    rewrite M_run_ls_before_event_unroll in run.
    destruct (dec_isFirst e) as [d|d]; ginv; minbft_simp; tcsp;[].

    apply map_option_Some in run; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbft in run1; exrepnd; subst.

    dup run1 as run.
    rename run1 into run_backup.
    eapply ind in run; eauto 3 with eo;[].
    hide_hyp run_backup.

    apply map_option_Some in run0; exrepnd; simpl in *; rev_Some; minbft_simp.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input in *; simpl in *.
    autorewrite with minbft comp in *; simpl in *.
    Time minbft_dest_msg Case;
      repeat (autorewrite with minbft comp in *; simpl in *; smash_minbft2);
      try (complete (unfold try_create_trinc_ui, try_update_TRINC in *; simpl in *; smash_minbft2;
                       remember (trinc_counters s1) as K; destruct K; simpl in *; tcsp;
                         destruct n; simpl in *; tcsp;
                           unfold getCounter in *; simpl in *; rewrite Max.max_l; auto; try omega)).
  Qed.

  Lemma on_request_implies_generates_trusted :
    forall {eo : EventOrdering} (e : Event) r v m s1 u1 l1 s2 u2 l2 msg,
      loc e = MinBFT_replica r
      -> current_counter s2 = S (current_counter s1)
      -> r = trinc_id u1
      -> v = current_view s1
      -> trigger_op e = Some msg
      -> msg2request msg = Some m
      -> M_run_ls_before_event (MinBFTlocalSys r) e = Some (MinBFTlocalSys_new r s1 u1 l1)
      -> M_run_ls_on_event (MinBFTlocalSys r) e = Some (MinBFTlocalSys_new r s2 u2 l2)
      -> disseminate_data
           e
           (minbft_data_ui
              (Build_UI
                 (Build_preUI (trinc_id u1) cid0 (S (current_counter s1)))
                 (create_hash_usig
                    (Build_HashData
                       v
                       m
                       (Build_preUI (trinc_id u1) cid0 (S (current_counter s1))))
                    (trinc_local_keys u1)))).
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
    apply map_option_Some in runOn; exrepnd; rev_Some; minbft_simp.
    unfold trigger_op in *.
    rewrite eqtrig in *; simpl in *; ginv.

    clear runBef.

    unfold M_byz_run_ls_on_one_event; simpl.
    unfold data_is_in_out, event2out; simpl; allrw; simpl.
    unfold M_run_ls_on_input_ls in *.
    remember (M_run_ls_on_input (MinBFTlocalSys_new (trinc_id u1) s1 u1 l1) (msg_comp_name 0) a) as run.
    symmetry in Heqrun; repnd; simpl in *; subst.
    unfold M_run_ls_on_input in *; simpl in *.
    autorewrite with minbft in *; simpl in *.

    Time minbft_dest_msg Case;
      repeat (simpl in *; autorewrite with minbft in *; smash_minbft2; try omega);
      unfold try_create_trinc_ui in *; simpl in *; smash_minbft2;
        try (complete (dands; tcsp; left; unfold invalid_prepare, valid_prepare in *; smash_minbft2));
        try (complete (dands; tcsp; left; unfold invalid_commit, valid_commit in *; smash_minbft2));
        unfold lower_out_break in *; simpl in *; minbft_simp; eexists; dands; eauto;
          simpl in *; tcsp; try omega;
            try (complete (dands; tcsp; left; unfold invalid_prepare, valid_prepare in *; smash_minbft2));
            try (complete (dands; tcsp; left; unfold invalid_commit, valid_commit in *; smash_minbft2)).
  Qed.
  Hint Resolve on_request_implies_generates_trusted : minbft.

(*  Lemma on_request_implies_generates_trusted :
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
                 (Build_preUI (usig_id u1) (S (usig_counters u1)))
                 (create_hash_usig
                    (Build_HashData
                       v
                       m
                       (Build_preUI (usig_id u1) (S (usig_counters u1))))
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
      try (complete (dands; tcsp; left; unfold invalid_prepare, valid_prepare in *; smash_minbft2));
      try (complete (dands; tcsp; left; unfold invalid_commit, valid_commit in *; smash_minbft2)).
  Qed.
  Hint Resolve on_request_implies_generates_trusted : minbft.*)

End TrIncass_tknew0.


Hint Resolve invalid_prepare_false_implies_equal_views : minbft.
Hint Resolve invalid_commit_false_implies_equal_views : minbft.
Hint Resolve on_request_implies_generates_trusted : minbft.

Hint Rewrite @ui_in_log_log_new_prepare : minbft.
Hint Rewrite @ui_in_log_log_new_commit : minbft.
