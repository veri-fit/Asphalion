(* GENERIC *)

Require Export ComponentSM7.
Require Export MinBFTcount_gen_tacs.
Require Export MinBFTcount_gen1.
Require Export MinBFTrep.
Require Export MinBFTprep.


Section MinBFTcount_gen2_commit.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma cexec_increases_commit :
    forall c
           {eo     : EventOrdering}
           (e      : Event)
           (s      : Rep)
           (s1     : _)
           (s2     : _)
           (subs1  : n_procs _)
           (subs2  : n_procs _),
      ~ In MAINname (get_names subs1)
      -> wf_procs subs1
      -> are_procs_n_procs subs1
      -> trigger e = trigger_info_data (MinBFT_commit c)
      -> M_run_ls_on_this_one_event (MinBFTlocalSys_newP s s1 subs1) e
         = Some (MinBFTlocalSys_newP s s2 subs2)
      -> cexec s1 = cexec s2
         \/
         exists r l,
           cexec s2 = S (cexec s1)
           /\ In (send_accept (accept r (cexec s2)) l)
                 (M_output_ls_on_this_one_event (MinBFTlocalSys_newP s s1 subs1) e).
  Proof.
    introv ni wf aps trig h.
    apply map_option_Some in h; exrepnd; rev_Some; minbft_simp.
    unfold M_output_ls_on_this_one_event, M_run_ls_on_input_out.
    unfold trigger_op in *; rewrite trig in *; simpl in *; ginv; simpl in *.
    unfold M_run_ls_on_input_ls in h0.
    remember (M_run_ls_on_input (MinBFTlocalSys_newP s s1 subs1) (msg_comp_name 0) (MinBFT_commit c)) as run.
    symmetry in Heqrun; repnd; simpl in *; subst.

    unfold M_run_ls_on_input in Heqrun; simpl in *.
    autorewrite with comp minbft in *.

    Time post_minbft_dest_msg;
      repeat (autorewrite with minbft comp in *; simpl in *; smash_minbft2);
      repeat (try gdest;
              repeat smash_minbft1_at_ Heqrun;
              repeat hide_break; repnd; simpl in *;
              repeat rm_is_M_break_mon; repeat is_M_break_out_some;
              repndors; ginv; tcsp; eauto 2 with minbft;
              repeat simplify_find_name_replace;
              try (complete (unfold lower_out_break in *; simpl in *;
                             minbft_simp; tcsp; autorewrite with minbft comp in *;
                             repeat rw_find_name_replace_name; repeat rm_is_M_break_mon;
                             try (rewrite replace_name_in_replace_subs_MinBFTlocalSys_newP in Heqrun0; auto;[|pwf]);
                             minbft_simp; tcsp;
                             right;
                             try (invalid_prep_imp_count xx; rewrite xx);
                             eexists; eexists; dands; tcsp; eauto))).
  Qed.

End MinBFTcount_gen2_commit.
