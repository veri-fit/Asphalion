(* GENERIC *)

Require Export MinBFTcount_gen_cond.


Section MinBFTcount_gen4_reply.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma M_run_ls_on_this_one_event_minbft_preserves_cond_LOGname_reply :
    forall r {eo : EventOrdering} (e : Event) R s s' subs subs',
      ~ In MAINname (get_names subs)
      -> lower_head 1 subs = true
      -> wf_procs subs
      -> are_procs_n_procs subs
      -> trigger e = trigger_info_data (MinBFT_reply r)
      -> M_run_ls_on_this_one_event (MinBFTlocalSys_newP R s subs) e
         = Some (MinBFTlocalSys_newP R s' subs')
      -> in_subs LOGname subs = true
      -> in_subs USIGname subs = true
      -> cond_LOGname_ex_entry subs
      -> cond_LOGname_ex_entry subs'.
  Proof.
    introv ni low wf aps trig eqls insL insU cond.
    apply map_option_Some in eqls; exrepnd; rev_Some; minbft_simp.
    unfold trigger_op in eqls1; rewrite trig in *; simpl in *; ginv; simpl in *.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input in *.
    autorewrite with minbft comp in *.

    Time post_minbft_dest_msg;
      repeat (autorewrite with minbft comp in *; simpl in *; smash_minbft2);
      try (complete (inversion eqls0; subst; auto));
      repeat (try gdest; smash_minbft1_at_ eqls0; repeat hide_break; repnd; simpl in *;
              repeat rm_is_M_break_mon; repeat is_M_break_out_some;
              simpl in *; repndors; ginv; tcsp; eauto 2 with minbft;
              minbft_simp; repeat simplify_find_name_replace);
      try (complete (minbft_simp; tcsp; autorewrite with minbft comp in *;
                     repeat rw_find_name_replace_name; repeat rm_is_M_break_mon;
                     try (rewrite replace_name_in_replace_subs_MinBFTlocalSys_newP in eqls0; auto;[|pwf]);
                     minbft_simp; tcsp;
                     repeat (first [apply implies_cond_LOGname_ex_entry_replace_name_eq; try prove_in_subs
                                   |apply implies_cond_LOGname_ex_entry_replace_name_diff; try prove_in_subs]);
                     autorewrite with comp; eauto 10 with minbft comp)).
  Qed.

End MinBFTcount_gen4_reply.
