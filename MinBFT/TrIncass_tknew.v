Require Export TrIncass_tknew0.


Section TrIncass_tknew.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma ASSUMPTION_trusted_knew_or_learns_or_gen_true :
    forall (eo : EventOrdering) t, assume_eo eo (ASSUMPTION_trusted_knew_or_learns_or_gen t).
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

    unfold M_run_ls_on_input_ls, M_run_ls_on_input in *; simpl in *.
    autorewrite with minbft in *; simpl in *.

    Time minbft_dest_msg Case;
      repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
      unfold try_create_trinc_ui, try_update_TRINC in *; simpl in *; smash_minbft2;
      try (complete (left; eexists; simpl; unfold state_before; simpl;
                       rewrite M_state_sys_before_event_unfold;
                       rewrite eqloc; simpl; rewrite runBef; simpl; dands;[eexists;dands|];
                         try reflexivity; simpl; auto));
      try (complete (right; right; left;
                       unfold data_is_owned_by; simpl; unfold ui2rep; simpl; dands; eauto;
                         eapply on_request_implies_generates_trusted; eauto; simpl; tcsp;
                           eauto 3 with comp minbft));
      try (complete (right; left; eauto 3 with minbft)).
  Qed.
  Hint Resolve ASSUMPTION_trusted_knew_or_learns_or_gen_true : minbft.

End TrIncass_tknew.


Hint Resolve ASSUMPTION_trusted_knew_or_learns_or_gen_true : minbft.
