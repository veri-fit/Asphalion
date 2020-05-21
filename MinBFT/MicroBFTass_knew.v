Require Export MicroBFTprops2.
Require Export CalculusSM_derived.


Section MicroBFTass_knew.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  (* MOVE *)
  Hint Rewrite ui_in_log_log_new_request : microbft.

  Definition msg2request (m : MicroBFT_msg) : option nat :=
    match m with
    | MicroBFT_request n => Some n
    | MicroBFT_commit  r => Some (commit_n r)
    | MicroBFT_accept  _  => None
    end.


  Lemma on_request_implies_generates_trusted :
    forall {eo : EventOrdering} (e : Event) r m s1 u1 l1 s2 u2 l2 msg,
      loc e = r
      -> usig_counter u2 = S (usig_counter u1)
      -> r = usig_id u1
      -> trigger_op e = Some msg
      -> msg2request msg = Some m
      -> M_run_ls_before_event (MicroBFTlocalSys r) e = Some (MicroBFTlocalSys_new r s1 u1 l1)
      -> M_run_ls_on_event (MicroBFTlocalSys r) e = Some (MicroBFTlocalSys_new r s2 u2 l2)
      -> disseminate_data
           e
           (microbft_data_ui
              (Build_UI
                 (Build_preUI (usig_id u1) (S (usig_counter u1)))
                 (create_hash_usig
                    (Build_HashData
                       (MicroBFT.sm_state s1 + m)
                       (Build_preUI (usig_id u1) (S (usig_counter u1))))
                    (usig_local_keys u1)))).
  Proof.
    introv eqloc eqc eqr eqtrig eqm runBef runOn.
    unfold disseminate_data; simpl.
    applydup @M_run_ls_on_event_M_byz_run_ls_on_event in runOn as byzRunOn.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    unfold M_byz_output_sys_on_event; simpl.
    rewrite M_byz_output_ls_on_event_as_run; simpl.
    unfold M_byz_output_ls_on_this_one_event.
    unfold M_byz_run_ls_on_one_event.
    apply (trigger_op_Some_implies_trigger_message e msg) in eqtrig.
    allrw; simpl.

    rewrite <- eqr.
    unfold MicroBFTsys; subst; simpl in *.
    rewrite byzRunBef; simpl.

    clear byzRunOn byzRunBef.

    rewrite M_run_ls_on_event_unroll2 in runOn.
    rewrite runBef in runOn; simpl in *.
    apply map_option_Some in runOn; exrepnd; rev_Some; microbft_simp.
    unfold trigger_op in *.
    unfold data_is_in_out, event2out; simpl.
    rewrite eqtrig in *; simpl in *; ginv.

    clear runBef.

    unfold M_run_ls_on_input_ls in *.
    remember (M_run_ls_on_input (MicroBFTlocalSys_new (loc e) s1 u1 l1) (msg_comp_name 0) a) as z;
      symmetry in Heqz; repnd; simpl in *; subst; simpl in *.
    unfold M_run_ls_on_input in *.
    autorewrite with microbft in *.

    Time microbft_dest_msg Case;
      unfold lower_out_break in *; simpl in *; microbft_simp; try omega;
        repeat (simpl in *; autorewrite with microbft in *; smash_microbft2; try omega);
        rewrite eqr; tcsp; eexists; dands; try reflexivity; simpl; tcsp.
  Qed.
  Hint Resolve on_request_implies_generates_trusted : microbft.

  (* MOVE to props0 *)
  Lemma microbft_data_rdata_in_MicroBFT_auth2data :
    forall r,
      In (microbft_data_rdata r) (MicroBFT_auth2data (commit2auth_data r)).
  Proof.
    destruct r as [b ui], ui as [pui d]; simpl; tcsp.
  Qed.
  Hint Resolve microbft_data_rdata_in_MicroBFT_auth2data : microbft.

  Lemma implies_learns_microbft_data_rdata :
    forall {eo : EventOrdering} (e : Event) (r : Commit) n s u l,
      loc e = MicroBFTheader.node2name n
      -> trigger_op e = Some (MicroBFT_commit r)
      -> M_run_ls_before_event (MicroBFTlocalSys n) e = Some (MicroBFTlocalSys_new n s u l)
      -> verify_UI (commit_n r) (commit_ui r) u = true
      -> learns_data e (microbft_data_rdata r).
  Proof.
    introv eqloc eqtrig runBef verif.
    exists n (commit2auth_data r).
    simpl; allrw; simpl; dands; eauto 3 with microbft;[].
    unfold MicroBFT_ca_verify.
    rewrite request2auth_data_eq.
    unfold M_byz_state_sys_before_event; simpl.
    allrw; simpl.
    unfold M_byz_state_ls_before_event.
    unfold MicroBFTsys, MicroBFTheader.node2name; simpl.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    allrw; simpl.
    autorewrite with microbft; smash_microbft.
  Qed.
  Hint Resolve implies_learns_microbft_data_rdata : microbft.

  Lemma on_request_implies_generates :
    forall {eo : EventOrdering} (e : Event) r m s1 u1 l1 s2 u2 l2 msg,
      loc e = r
      -> usig_counter u2 = S (usig_counter u1)
      -> r = usig_id u1
      -> trigger_op e = Some msg
      -> msg2request msg = Some m
      -> M_run_ls_before_event (MicroBFTlocalSys r) e = Some (MicroBFTlocalSys_new r s1 u1 l1)
      -> M_run_ls_on_event (MicroBFTlocalSys r) e = Some (MicroBFTlocalSys_new r s2 u2 l2)
      -> disseminate_data
           e
           (microbft_data_rdata
              (commit
                 (MicroBFT.sm_state s1 + m)
                 (Build_UI
                    (Build_preUI (usig_id u1) (S (usig_counter u1)))
                    (create_hash_usig
                       (Build_HashData
                          (MicroBFT.sm_state s1 + m)
                          (Build_preUI (usig_id u1) (S (usig_counter u1))))
                       (usig_local_keys u1))))).
  Proof.
    introv eqloc eqc eqr eqtrig eqm runBef runOn.
    unfold disseminate_data; simpl.
    applydup @M_run_ls_on_event_M_byz_run_ls_on_event in runOn as byzRunOn.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    unfold M_byz_output_sys_on_event; simpl.
    rewrite M_byz_output_ls_on_event_as_run; simpl.
    unfold M_byz_output_ls_on_this_one_event.
    unfold M_byz_run_ls_on_one_event.
    apply (trigger_op_Some_implies_trigger_message e msg) in eqtrig.
    allrw; simpl.

    rewrite <- eqr.
    unfold MicroBFTsys; subst; simpl in *.
    rewrite byzRunBef; simpl.

    hide_hyp byzRunOn.
    hide_hyp byzRunBef.

    rewrite M_run_ls_on_event_unroll2 in runOn.
    rewrite runBef in runOn; simpl in *.
    apply map_option_Some in runOn; exrepnd; rev_Some; microbft_simp.
    unfold trigger_op in *.
    unfold data_is_in_out, event2out; simpl.
    rewrite eqtrig in *; simpl in *; ginv.

    hide_hyp runBef.

    unfold M_run_ls_on_input_ls in *.
    remember (M_run_ls_on_input (MicroBFTlocalSys_new (loc e) s1 u1 l1) (msg_comp_name 0) a) as z;
      symmetry in Heqz; repnd; simpl in *; subst; simpl in *.
    unfold M_run_ls_on_input in *.
    autorewrite with microbft in *.

    Time microbft_dest_msg Case;
      unfold lower_out_break in *; simpl in *; microbft_simp; try omega;
        repeat (simpl in *; autorewrite with microbft in *; smash_microbft2; try omega);
        rewrite eqr; tcsp; eexists; dands; try reflexivity; simpl; tcsp.
  Qed.
  Hint Resolve on_request_implies_generates : microbft.

  Lemma verify_UI_implies_MicroBFT_ca_verify :
    forall {eo : EventOrdering} (e : Event) s u l m n,
      loc e = n
      -> M_run_ls_before_event (MicroBFTsys n) e = Some (MicroBFTlocalSys_new n s u l)
      -> verify_UI (commit_n m) (commit_ui m) u = true
      -> MicroBFT_ca_verify eo e (commit2auth_data m) = true.
  Proof.
    introv eqloc run verif.
    unfold MicroBFT_ca_verify; simpl.
    destruct m as [k ui]; simpl.
    unfold M_byz_state_sys_before_event.
    subst.
    unfold M_byz_state_ls_before_event.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in run.
    simpl in *; allrw; simpl.
    unfold state_of_trusted; simpl; auto.
  Qed.
  Hint Resolve verify_UI_implies_MicroBFT_ca_verify : microbft.

  Lemma ASSUMPTION_knew_or_learns_or_gen_true :
    forall (eo : EventOrdering), assume_eo eo (KE_ALL_DATA ASSUMPTION_knew_or_learns_or_gen).
  Proof.
    introv kn.
    Opaque KE_KNEW.
    simpl in *; repnd.
    rewrite interp_KE_KNEW.

    unfold knows_after in kn; exrepnd; simpl in *.
    unfold MicroBFT_data_knows in *; simpl in *.
    unfold state_after in *; exrepnd; simpl in *.
    unfold M_state_sys_on_event in *; simpl in *.
    rewrite kn1 in *; simpl in *.
    apply map_option_Some in kn2; exrepnd; rev_Some.
    applydup M_run_ls_on_event_ls_is_microbft in kn2; exrepnd; subst; simpl in *.
    apply option_map_Some in kn3; exrepnd; subst; simpl in *; microbft_simp.
    dup kn2 as runOn; hide_hyp runOn.
    dup kn2 as eqid.

    apply (preserves_usig_id2 _ _ _ s1) in eqid; simpl; tcsp;[].
    rewrite M_run_ls_on_event_unroll2 in kn2.
    apply map_option_Some in kn2; exrepnd; rev_Some.

    applydup M_run_ls_before_event_ls_is_microbft in kn2; exrepnd; subst; simpl in *.
    apply map_option_Some in kn3; exrepnd; subst; simpl in *; rev_Some; microbft_simp.
    rename kn2 into runBef.
    rename kn1 into eqloc.

    unfold M_run_ls_on_input_ls, M_run_ls_on_input in *.
    autorewrite with microbft in *.

    Time (destruct c; simpl in *; microbft_dest_msg Case);
      repeat (simpl in *; try autorewrite with minbft in *; smash_microbft2; repndors);
      try (complete (left; eexists; simpl; unfold state_before; simpl;
                       rewrite M_state_sys_before_event_unfold;
                       rewrite eqloc; simpl; rewrite runBef; simpl; dands;[eexists;dands|];
                         try reflexivity; simpl; auto));
      try (complete (right; right; left;
                       unfold data_is_owned_by; simpl; unfold commit2sender; simpl;
                         dands; eauto;
                           eapply on_request_implies_generates; eauto; tcsp));
      try (complete (try (unfold ui_in_log_entry in *; smash_microbft2);
                       right; right; left;
                         unfold data_is_owned_by; simpl; unfold commit2sender; simpl;
                           dands; eauto;
                             eapply on_request_implies_generates_trusted; eauto; tcsp));
      try (complete (try (unfold ui_in_log_entry in *; smash_microbft2);
                       right; left;
                       eexists; allrw; simpl; eexists; dands; eauto;
                         eauto 3 with microbft)).
  Qed.
  Hint Resolve ASSUMPTION_knew_or_learns_or_gen_true : microbft.

End MicroBFTass_knew.


Hint Rewrite @ui_in_log_log_new_request : microbft.

Hint Resolve on_request_implies_generates_trusted : microbft.
Hint Resolve microbft_data_rdata_in_MicroBFT_auth2data : microbft.
Hint Resolve implies_learns_microbft_data_rdata : microbft.
Hint Resolve on_request_implies_generates : microbft.
Hint Resolve verify_UI_implies_MicroBFT_ca_verify : microbft.
Hint Resolve ASSUMPTION_knew_or_learns_or_gen_true : microbft.
