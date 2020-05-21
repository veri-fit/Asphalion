Require Export MinBFTcount_gen5_aux.


Section MinBFTcount_gen5_prepare.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.



  Lemma accepted_counter_if_received_UI_primary_prepare :
    forall R s x subs s' subs' out r i l,
      ~ In MAINname (get_names subs)
      -> lower_head 1 subs = true
      -> wf_procs subs
      -> are_procs_n_procs subs
      -> in_subs USIGname subs = true
      -> in_subs LOGname subs = true
      -> cond_LOGname_ex_entry subs
      -> M_run_ls_on_input (MinBFTlocalSys_newP R s subs) (msg_comp_name 0) (MinBFT_prepare x)
         = (MinBFTlocalSys_newP R s' subs', Some out)
      -> In (send_accept (accept r i) l) out
      -> exists log rd ui,
          state_of_component LOGname subs' = Some log
          /\ ex_entry rd log
          /\ request_data2ui rd = ui
          /\ request_data2request rd = r
          /\ request_data2view rd = current_view s'
          /\ ui2counter ui = i
          /\ ui2cid ui = cid0
          /\ ui2rep ui = MinBFTprimary (current_view s').
  Proof.
    introv ni low wf aps iU iL cond run inout.

    unfold M_run_ls_on_input in *; simpl in *.
    autorewrite with comp minbft in *.

    Time post_minbft_dest_msg;
      repeat (autorewrite with minbft comp in *; simpl in *; smash_minbft2);
      repeat (try gdest; repeat sp_sm_or_at;
              repeat smash_minbft1_at_ run;
              repeat hide_break; repnd; simpl in *;
              repeat rm_is_M_break_mon; repeat is_M_break_out_some;
              repndors; ginv; tcsp; eauto 2 with minbft;
              repeat simplify_find_name_replace);
      try (complete (unfold lower_out_break in *; simpl in *;
                     minbft_simp; tcsp; autorewrite with minbft comp in *;
                     repndors; tcsp; ginv;
                     repeat rw_find_name_replace_name; repeat rm_is_M_break_mon;
                     try (rewrite replace_name_in_replace_subs_MinBFTlocalSys_newP in run0; auto;[|pwf]);
                     minbft_simp; tcsp;
                     rewrite state_of_component_replace_name;
                     try (complete (apply has_comp_implies_in_subs; repeat (apply implies_has_comp_replace_name); eauto 3 with comp));
                     eexists;
                     first [exists (commit2request_data_i c)
                           |exists (commit2request_data_i (mk_auth_commit (current_view s) (prepare2request x) (prepare2ui x) x0))];
                     eexists;
                     dands; try reflexivity; simpl; autorewrite with minbft in *; auto; eauto 2 with minbft;
                     try (apply (implies_ex_entry_request_data x0));
                     repeat simplify_find_name_replace;
                     eauto 7 with minbft)).
  Qed.

End MinBFTcount_gen5_prepare.
