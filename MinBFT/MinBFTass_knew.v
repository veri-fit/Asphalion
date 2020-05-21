Require Export MinBFTass_knew1.
Require Export MinBFTass_knew2.
Require Export MinBFTass_knew0.


Section MinBFTass_knew.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma in_minbft_data_rdata_prepare2request_data_MinBFT_auth2data_prepare2auth_data :
    forall p,
      In (minbft_data_rdata (prepare2request_data p))
         (MinBFT_auth2data (prepare2auth_data p)).
  Proof.
    introv.
    destruct p as [p ui], p as [v r], ui; simpl in *; tcsp.
  Qed.
  Hint Resolve in_minbft_data_rdata_prepare2request_data_MinBFT_auth2data_prepare2auth_data : minbft.

  Lemma in_minbft_data_rdata_commit2request_data_i_MinBFT_auth2data_commit2auth_data :
    forall c,
      In (minbft_data_rdata (commit2request_data_i c))
         (MinBFT_auth2data (commit2auth_data c)).
  Proof.
    introv.
    destruct c as [b uj], b as [v m ui], ui; simpl in *; tcsp.
  Qed.
  Hint Resolve in_minbft_data_rdata_commit2request_data_i_MinBFT_auth2data_commit2auth_data : minbft.

(*  Lemma in_minbft_data_rdata_commit2request_data_j_MinBFT_auth2data_commit2auth_data :
    forall c,
      In (minbft_data_rdata (commit2request_data_j c))
         (MinBFT_auth2data (commit2auth_data c)).
  Proof.
    introv.
    destruct c as [b uj], b as [v m ui], uj; simpl in *; tcsp.
  Qed.
  Hint Resolve in_minbft_data_rdata_commit2request_data_j_MinBFT_auth2data_commit2auth_data : minbft.*)

  Lemma implies_learns_prepare2rdata :
    forall {eo : EventOrdering} (e : Event) p n s u l,
      loc e = MinBFT_replica n
      -> trigger_op e = Some (MinBFT_prepare p)
      -> M_run_ls_before_event (MinBFTlocalSys n) e = Some (MinBFTlocalSys_new n s u l)
      -> verify_UI (prepare2view p) (prepare2request p) (prepare2ui p) u = true
      -> learns_data e (minbft_data_rdata (prepare2request_data p)).
  Proof.
    introv eqloc eqtrig runBef verif.
    exists n (prepare2auth_data p).
    simpl; allrw; simpl; dands; eauto 3 with minbft;[].
    unfold MinBFT_ca_verify.
    rewrite prepare2auth_data_eq.
    unfold M_byz_state_sys_before_event; simpl.
    allrw; simpl.
    unfold M_byz_state_ls_before_event.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    allrw; simpl.
    unfold state_of_trusted; simpl.
    autorewrite with minbft; smash_minbft.
  Qed.
  Hint Resolve implies_learns_prepare2rdata : minbft.

  Lemma implies_learns_commit2rdata_i :
    forall {eo : EventOrdering} (e : Event) c n s u l,
      loc e = MinBFT_replica n
      -> trigger_op e = Some (MinBFT_commit c)
      -> M_run_ls_before_event (MinBFTlocalSys n) e = Some (MinBFTlocalSys_new n s u l)
      -> verify_UI (commit2view c) (commit2request c) (commit2ui_j c) u = true
      -> verify_UI (commit2view c) (commit2request c) (commit2ui_i c) u = true
      -> learns_data e (minbft_data_rdata (commit2request_data_i c)).
  Proof.
    introv eqloc eqtrig runBef verifj verifi.
    exists n (commit2auth_data c).
    simpl; allrw; simpl; dands; eauto 3 with minbft;[].
    unfold MinBFT_ca_verify.
    rewrite commit2auth_data_eq.
    unfold M_byz_state_sys_before_event; simpl.
    allrw; simpl.
    unfold M_byz_state_ls_before_event.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    allrw; simpl.
    unfold state_of_trusted; simpl.
    autorewrite with minbft; smash_minbft.
  Qed.
  Hint Resolve implies_learns_commit2rdata_i : minbft.

(*  Lemma implies_learns_commit2rdata_j :
    forall {eo : EventOrdering} (e : Event) c n s u l,
      loc e = MinBFT_replica n
      -> trigger_op e = Some (MinBFT_commit c)
      -> M_run_ls_before_event (MinBFTlocalSys n) e = Some (MinBFTlocalSys_new n s u l)
      -> verify_UI (commit2view c) (commit2request c) (commit2ui_j c) u = true
      -> verify_UI (commit2view c) (commit2request c) (commit2ui_i c) u = true
      -> learns_data e (minbft_data_rdata (commit2request_data_j c)).
  Proof.
    introv eqloc eqtrig runBef verifj verifi.
    exists n (commit2auth_data c).
    simpl; allrw; simpl; dands; eauto 3 with minbft;[].
    unfold MinBFT_ca_verify.
    rewrite commit2auth_data_eq.
    unfold M_byz_state_sys_before_event_of_trusted; simpl.
    allrw; simpl.
    unfold M_byz_state_ls_before_event_of_trusted.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    allrw; simpl.
    unfold state_of_trusted; simpl.
    autorewrite with minbft; smash_minbft.
  Qed.
  Hint Resolve implies_learns_commit2rdata_j : minbft.*)

  Lemma ASSUMPTION_all_knew_or_learns_or_gen_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_all_knew_or_learns_or_gen.
  Proof.
    introv kn.
    Opaque KE_TKNEW.
    Opaque KE_KNEW.
    Opaque KE_FALSE.
    simpl in *; repnd.
    rewrite interp_KE_KNEW.
    rewrite interp_KE_FALSE.

    unfold knows_after in kn; exrepnd; simpl in *.
    unfold MinBFT_data_knows in *; simpl in *.
    unfold state_after in *; exrepnd; simpl in *.
    unfold M_state_sys_on_event in *; simpl in *.
    rewrite kn1 in *; simpl in *.
    apply map_option_Some in kn2; exrepnd; rev_Some.
    applydup M_run_ls_on_event_ls_is_minbft in kn2; exrepnd; subst; simpl in *.
    unfold state_of_component in *; simpl in *; ginv.
    dup kn2 as runOn; hide_hyp runOn.
    dup kn2 as eqid.
    apply (preserves_usig_id2 _ _ _ s1) in eqid; simpl; tcsp;[].
    rewrite M_run_ls_on_event_unroll2 in kn2.
    apply map_option_Some in kn2; exrepnd; rev_Some.

    applydup M_run_ls_before_event_ls_is_minbft in kn2; exrepnd; subst; simpl in *.
    apply map_option_Some in kn3; exrepnd; subst; simpl in *; rev_Some; minbft_simp.
    rename kn2 into runBef.
    rename kn1 into eqloc.

    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as runByzBef.

    unfold M_run_ls_on_input_ls, M_run_ls_on_input in *; simpl in *.
    autorewrite with minbft in *; simpl in *.

    Time minbft_dest_msg Case;
      repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
      try (destruct c; simpl in * );
      repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
             try (complete (left; eexists; simpl; unfold state_before; simpl;
                            rewrite M_state_sys_before_event_unfold;
                              rewrite eqloc; simpl; rewrite runBef; simpl; dands;[eexists;dands|];
                                try reflexivity; simpl; auto));
             try (complete (right; right; left;
                              unfold data_is_owned_by; simpl; unfold ui2rep; simpl; dands; eauto;
                                eapply on_request_implies_generates_trusted; eauto; simpl; tcsp;
                                  eauto 3 with comp minbft));
             try (complete (right; right; left;
                              unfold data_is_owned_by; simpl; unfold ui2rep; simpl; dands; eauto;
                                eapply on_request_implies_generates; eauto; simpl; tcsp;
                                  eauto 3 with comp minbft));
             try (complete (right; left; eauto 3 with minbft;
                              try (applydup invalid_prepare_false_implies_eq_prepare2view in Heqx as eqv; try rewrite <- eqv);
                              try (applydup invalid_commit_false_implies_eq_commit2view in Heqx as eqv; try rewrite <- eqv);
                              autorewrite with minbft; eauto 3 with minbft)).
  Qed.
  Hint Resolve ASSUMPTION_all_knew_or_learns_or_gen_true : minbft.

End MinBFTass_knew.


Hint Resolve ASSUMPTION_all_knew_or_learns_or_gen_true : minbft.
