Require Export TrInccount.
Require Export TrInckn.
Require Export TrIncacc_exec.
Require Export TrIncacc_new.
Require Export TrIncvreq_mon.

Section TrIncprops1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.



  Lemma accepted_counter_if_know_UI_primary :
    forall {eo    : EventOrdering}
           (e     : Event)
           (R     : Rep)
           (r     : Request)
           (i     : nat)
           (l     : list name),
      In (send_accept (accept r i) l) (M_output_ls_on_event (MinBFTlocalSys R) e)
      ->
      exists (s  : MAIN_state)
             (s1 : TRINC_state)
             (s2 : LOG_state)
             (ui : UI),
        M_run_ls_on_event (MinBFTlocalSys R) e = Some (MinBFTlocalSys_new R s s1 s2)
        /\ kc_knows (minbft_data_rdata (request_data (current_view s) r ui)) s2
        /\ kc_Tknows ui s2
        /\ kc_trust2owner ui = MinBFTprimary (current_view s)
        /\ ui2cid ui = 0
        /\ ui2counter ui = i.
  Proof.
    introv h.
    apply accepted_counter_if_received_UI_primary in h.
    exrepnd.
    exists s s1 s2 ui.
    simpl.
    dands; auto; unfold MinBFT_data_knows; simpl; subst; eauto 3 with minbft;[].
    unfold request_data_in_log; simpl.
    allrw <-; autorewrite with minbft; allrw; auto.
  Qed.

  Lemma kc_Tknows_implies :
    forall  (ui : UI) (l : LOG_state),
      kc_Tknows ui l
      -> exists en,
        In en l                     (* FIX: Do we need this one instead? find_entry rd l = Some e *)
        /\ ui_in_log ui l = true    (* FIX: do we need this one? *)
        /\
        (
          (exists rd, request_data2ui rd = ui )
          \/
          (In ui (log_entry_commits en))
        ).
  Proof.
    introv H.
    unfold kc_Tknows in *.
    unfold kc_knows in *. simpl in *.
    unfold MinBFT_data_knows in *.
    unfold MinBFT_data_in_log in *.

    unfold ui_in_log in *.
    eapply existsb_exists in H.
    exrepnd.
    rename x into en.

    unfold ui_in_log_entry in *.
    dest_cases w;[|].
    {
      exists en; dands; eauto.
      eapply existsb_exists.
      exists en. dands; eauto.
      dest_cases x.
    }
    {
      dest_cases x;[].
      exists en; dands; eauto.
      eapply existsb_exists.
      exists en; dands; eauto.
      dest_cases x;[].
      dest_cases y.
    }
  Qed.

(*  Lemma uis_where_verified :
    forall {eo : EventOrdering} (e : Event) (l : LOG_state) (u : USIG_state) (ui : UI),
      is_replica e
      -> M_state_sys_on_event MinBFTsys e LOGname = Some l
      -> M_state_sys_on_event MinBFTsys e USIGname = Some u
      -> kc_Tknows ui l
      ->
      exists hd,
        kc_knows (minbft_data_hdata hd) l
        /\ verify_hash_usig hd (ui2digest ui) (usig_local_keys u) = true.
  Proof.
    introv isr eqst1 eqst2 unl.

    unfold kc_Tknows in unl; simpl in unl.
    unfold MinBFT_data_knows in unl; simpl in unl.

    rewrite M_state_sys_on_event_unfold in eqst1.
    rewrite M_state_sys_on_event_unfold in eqst2.

    apply map_option_Some in eqst1.
    apply map_option_Some in eqst2.
    exrepnd; try rev_Some.

    rewrite eqst1 in eqst2; ginv.

    unfold is_replica in *; exrepnd.

    revert dependent u.
    revert dependent l.
    revert dependent a.
    rewrite isr0; simpl.

    (* WARNING *)
    clear isr0.

    induction e as [e ind] using predHappenedBeforeInd;[]; introv run stl inlog stu.

    rewrite M_run_ls_on_event_unroll in run.
    rewrite M_run_ls_before_event_unroll_on in run.

    destruct (dec_isFirst e) as [d|d].

    {
      clear ind.

      unfold M_run_ls_on_this_one_event in run; simpl in *.
      apply map_option_Some in run; exrepnd; rev_Some.
      unfold M_break in run0; simpl in *; smash_minbft; repnd; simpl in *.
      apply option_map_Some in run0; exrepnd; subst; simpl in *.

      minbft_dest_msg Case a0; simpl in *;
        try (complete (inversion Heqx; subst; simpl in *;
                       unfold state_of_subcomponents in *;
                       simpl in *; ginv));
        [| |].

      { Case "Request".

        unfold call_create_ui, bind in *; simpl in *.
        inversion Heqx; subst; simpl in *; clear Heqx;
          unfold state_of_subcomponents in *; simpl in *; ginv.
        unfold ui_in_log in *; simpl in *.
        unfold ui_in_log_entry in *; simpl in *.
        smash_minbft; simpl in *.
        unfold MinBFT_data_knows; simpl.
        unfold hash_data_in_log_entry, RequestData2HashData; simpl.
        exists (Build_HashData initial_view (request_b m) (Build_preUI r 1)).
        simpl; smash_minbft; GC; dands; auto. }

      { Case "Prepare".

        unfold call_verify_ui, bind in *; simpl in *; smash_minbft;
          try (complete (unfold state_of_subcomponents in *; simpl in *;
                         ginv; eapply ind in run1; eauto; eauto 3 with eo)).

        { unfold state_of_subcomponents in *; simpl in *; ginv.
          unfold ui2rep, ui_in_log in *; simpl in *; autorewrite with bool in *; subst.
          unfold ui_in_log_entry in *; simpl in *; autorewrite with minbft in *; smash_minbft.
          unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
          exists (prepare2hash_data p); dands; auto.
          unfold MinBFT_data_knows; simpl.
          unfold hash_data_in_log_entry; simpl; smash_minbft. }

        { unfold state_of_subcomponents in *; simpl in *; ginv.
          unfold ui2rep, ui_in_log in *; simpl in *; autorewrite with bool in *; subst.
          unfold ui_in_log_entry in *; simpl in *; autorewrite with minbft in *; smash_minbft.

          { unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
            exists (prepare2hash_data p); dands; auto.
            unfold MinBFT_data_knows; simpl.
            unfold hash_data_in_log_entry; simpl; smash_minbft. }

          { exists (Build_HashData
                      (prepare2view p)
                      (request_b (prepare2request p))
                      (Build_preUI r 1)); simpl.
            autorewrite with minbft; dands; auto.
            unfold MinBFT_data_knows; simpl.
            unfold hash_data_in_log_entry; simpl; smash_minbft. } }

        { unfold state_of_subcomponents in *; simpl in *; ginv.
          unfold ui2rep, ui_in_log in *; simpl in *; autorewrite with bool in *; subst.
          unfold ui_in_log_entry in *; simpl in *; autorewrite with minbft in *; smash_minbft.

          { unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
            exists (prepare2hash_data p); dands; auto.
            unfold MinBFT_data_knows; simpl.
            unfold hash_data_in_log_entry; simpl; smash_minbft. }

          { unfold invalid_prepare in *; smash_minbft.
            apply valid_prepare_implies_view in Heqx0; rewrite Heqx0 in *.
            autorewrite with minbft in *; tcsp. } }
      }

      { Case "Commit".
        unfold call_verify_ui, bind in *; simpl in *; smash_minbft;
          try (complete (unfold state_of_subcomponents in *; simpl in *; ginv));[].

        unfold call_prepare_already_in_log, bind_pair, bind in *; simpl in *; smash_minbft;[].
        unfold call_log_commit, bind in *; simpl in *; smash_minbft;[|].

        { unfold invalid_commit, valid_commit in *; smash_minbft. }

        { unfold call_is_committed, bind in *; simpl in *; smash_minbft;[|].

          { unfold state_of_subcomponents in *; simpl in *; ginv; simpl in *.
            smash_minbft; repndors; ginv.
            unfold ui_in_log_entry in *; simpl in *; autorewrite with minbft in *; smash_minbft;[|].

            { exists (commit2hash_data_i c).
              unfold verify_UI in *; autorewrite with minbft in *; dands; auto.
              unfold MinBFT_data_knows; simpl.
              unfold hash_data_in_log_entry; simpl; smash_minbft. }

            { unfold add_commit2commits, ui2rep in *; simpl in *; smash_minbft;
                repndors; subst; tcsp;[| |].
              { exists (Build_HashData
                          (commit2view c)
                          (request_b (commit2request c))
                          (Build_preUI (commit2sender_j c) 1)); simpl.
                autorewrite with minbft; dands; auto.
                unfold MinBFT_data_knows; simpl.
                unfold hash_data_in_log_entry; simpl; smash_minbft; tcsp. }
              { exists (commit2hash_data_j c).
                unfold verify_UI in *; autorewrite with minbft in *; dands; auto.
                unfold MinBFT_data_knows; simpl.
                unfold hash_data_in_log_entry; simpl; smash_minbft. }
              { unfold ui2digest; simpl.
                exists (Build_HashData
                          (commit2view c)
                          (request_b (commit2request c))
                          (Build_preUI r 1)); simpl.
                autorewrite with minbft; dands; auto;[].
                unfold MinBFT_data_knows; simpl.
                unfold hash_data_in_log_entry; simpl; smash_minbft; tcsp. }
            }
          }

          { unfold state_of_subcomponents in *; simpl in *; ginv.
            unfold ui_in_log in *; simpl in *; autorewrite with bool in *.
            unfold ui_in_log_entry in *; simpl in *; smash_minbft;[|].

            { exists (commit2hash_data_i c).
              unfold verify_UI in *; autorewrite with minbft in *; dands; auto.
              unfold MinBFT_data_knows; simpl.
              unfold hash_data_in_log_entry; simpl; smash_minbft. }

            { unfold add_commit2commits, ui2rep in *; simpl in *; smash_minbft;
                repndors; subst; tcsp;[| |].
              { exists (Build_HashData
                          (commit2view c)
                          (request_b (commit2request c))
                          (Build_preUI (commit2sender_j c) 1)); simpl.
                autorewrite with minbft; dands; auto.
                unfold MinBFT_data_knows; simpl.
                unfold hash_data_in_log_entry; simpl; smash_minbft; tcsp. }
              { exists (commit2hash_data_j c).
                unfold verify_UI in *; autorewrite with minbft in *; dands; auto.
                unfold MinBFT_data_knows; simpl.
                unfold hash_data_in_log_entry; simpl; smash_minbft. }
              { unfold ui2digest; simpl.
                exists (Build_HashData
                          (commit2view c)
                          (request_b (commit2request c))
                          (Build_preUI r 1)); simpl.
                autorewrite with minbft; dands; auto;[].
                unfold MinBFT_data_knows; simpl.
                unfold hash_data_in_log_entry; simpl; smash_minbft; tcsp. }
            }
          }
        }
      }
    }

    {
      apply map_option_Some in run; exrepnd; rev_Some.
      applydup M_run_ls_on_event_ls_is_minbft in run1; exrepnd; subst.

      unfold M_run_ls_on_this_one_event in run0; simpl in *.
      apply map_option_Some in run0; exrepnd; rev_Some.
      unfold M_break in run2; simpl in *; smash_minbft; repnd; simpl in *.
      apply option_map_Some in run2; exrepnd; subst; simpl in *.

      minbft_dest_msg Case a0; simpl in *;
        try (complete (inversion Heqx; subst; simpl in *;
                       unfold state_of_subcomponents in *;
                       simpl in *; ginv;
                       eapply ind in run1; eauto; eauto 3 with eo));
        [| |].

      { Case "Request".

        unfold call_create_ui, bind in *; simpl in *.
        inversion Heqx; subst; simpl in *; clear Heqx;
          unfold state_of_subcomponents in *; simpl in *; ginv.

        rewrite ui_in_log_log_new_prepare in inlog; simpl in *.
        smash_minbft; simpl in *.

        { unfold MinBFT_data_knows; simpl.
          exists (Build_HashData
                    (current_view s)
                    (request_b m)
                    (Build_preUI (usig_id s1) (S (usig_counter s1)))).
          rewrite hash_data_in_log_log_new_prepare.
          Opaque HashData_Deq.
          simpl.
          unfold RequestData2HashData; simpl.
          smash_minbft. }

        eapply ind in run1; try exact inlog; try reflexivity; eauto 3 with eo;[].
        exrepnd.
        exists hd.

        unfold MinBFT_data_knows; simpl.
        rewrite hash_data_in_log_log_new_prepare; simpl in *.
        unfold RequestData2HashData; simpl; allrw.
        smash_minbft. }

      { Case "Prepare".

        unfold call_verify_ui, bind in Heqx; simpl in *; smash_minbft;
          try (complete (unfold state_of_subcomponents in *; simpl in *;
                         ginv; eapply ind in run1; eauto; eauto 3 with eo));[].
        unfold call_prepare_already_in_log, bind in Heqx2; simpl in *; smash_minbft;
          try (complete (unfold state_of_subcomponents in *; simpl in *;
                         ginv; eapply ind in run1; eauto; eauto 3 with eo));[].
        unfold state_of_subcomponents in *; simpl in *; ginv.
        unfold invalid_prepare in *; smash_minbft.
        rewrite ui_in_log_log_new_commit in inlog ;simpl in *.
        unfold commit2ui_i in inlog; simpl in *.
        unfold commit_ui_j_rep_not_in_log in inlog; simpl in *.
        unfold commit2sender_j in inlog; simpl in *.
        unfold MinBFT_data_knows; simpl.
        applydup valid_prepare_implies_view in Heqx0 as eqv.
        rewrite eqv in inlog; autorewrite with minbft in *.
        rewrite prepare_not_already_in_log_implies_find_entry in inlog; auto;[].
        simpl in *; autorewrite with minbft in *.

        smash_minbft;[| |].

        { exists (prepare2hash_data p); simpl.
          unfold verify_UI in *; autorewrite with minbft in *.
          dands; auto;[].
          rewrite hash_data_in_log_log_new_commit_eq.
          unfold commit2hash_data_i; simpl.
          unfold commit_ui_j_rep_not_in_log; simpl.
          unfold commit2sender_j in *; simpl in *.
          unfold commit2hash_data_j; simpl.
          unfold RequestData2HashData; simpl in *.
          rewrite eqv; autorewrite with minbft.
          smash_minbft. }

        { rewrite ui_in_log_log_new_prepare in Heqx2; smash_minbft;[]; GC.
          eapply ind in run1; try exact Heqx2; try reflexivity; eauto 3 with eo.
          exrepnd.
          exists hd; dands; auto.
          unfold MinBFT_data_knows; simpl.
          rewrite hash_data_in_log_log_new_commit_eq; simpl.
          unfold commit2hash_data_i; simpl.
          unfold commit_ui_j_rep_not_in_log; simpl.
          unfold commit2sender_j in *; simpl in *.
          unfold commit2hash_data_j; simpl.
          unfold RequestData2HashData; simpl in *.
          rewrite eqv; autorewrite with minbft.
          rewrite prepare_not_already_in_log_implies_find_entry; auto;[].
          simpl in *; autorewrite with minbft.
          unfold MinBFT_data_knows in run1;simpl in run1.
          smash_minbft; allrw MinBFTprops0.not_over_or; repnd; tcsp; GC;
            try rewrite @hash_data_in_log_log_new_prepare in *; smash_minbft. }

        { exists (Build_HashData
                    (prepare2view p)
                    (request_b (prepare2request p))
                    (Build_preUI (usig_id s1) (S (usig_counter s1)))); simpl.
          autorewrite with minbft; dands; auto;[].
          allrw not_over_or; repnd; GC.
          Opaque UI_dec.
          rewrite @ui_in_log_log_new_prepare in *; simpl in *.
          smash_minbft;[]; GC.
          rewrite hash_data_in_log_log_new_commit_eq; simpl.
          unfold commit2hash_data_i; simpl.
          unfold commit_ui_j_rep_not_in_log; simpl.
          unfold commit2sender_j in *; simpl in *.
          unfold commit2hash_data_j; simpl.
          unfold RequestData2HashData; simpl in *.
          rewrite eqv; autorewrite with minbft.
          rewrite prepare_not_already_in_log_implies_find_entry; auto;[].
          simpl in *; autorewrite with minbft.
          smash_minbft. }
      }

      { Case "Commit".

        unfold call_verify_ui, bind in Heqx; simpl in *; smash_minbft;
          try (complete (unfold state_of_subcomponents in *; simpl in *;
                         ginv; eapply ind in run1; eauto; eauto 3 with eo));[].
        unfold call_prepare_already_in_log, bind_pair, bind in *; simpl in *; smash_minbft;
          try (complete (unfold state_of_subcomponents in *; simpl in *;
                         ginv; eapply ind in run1; eauto; eauto 3 with eo));[|].

        {
          unfold call_log_commit, bind in Heqx4; simpl in *; smash_minbft;
            try (complete (unfold state_of_subcomponents in *; simpl in *;
                           ginv; eapply ind in run1; eauto; eauto 3 with eo));[].
          unfold call_is_committed, bind in Heqx; simpl in *; smash_minbft;
            try (complete (unfold state_of_subcomponents in *; simpl in *;
                           ginv; eapply ind in run1; eauto; eauto 3 with eo));[|].

          { unfold state_of_subcomponents in *; simpl in *; ginv.
            rewrite ui_in_log_log_new_commit in inlog; smash_minbft;
              try (complete (eapply ind in run1; eauto; eauto 3 with eo));
              [| |].

            { exists (commit2hash_data_i c); simpl.
              unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
              dands; auto;[].
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }

            { eapply ind in run1; try exact Heqx; simpl in *;
                unfold state_of_subcomponents in *; simpl in *; try reflexivity;
                  eauto 3 with eo; exrepnd; exists hd; dands; auto.
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }

            { exists (commit2hash_data_j c).
              unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
              dands; auto;[].
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }
          }

          { unfold state_of_subcomponents in *; simpl in *; ginv.
            rewrite ui_in_log_log_new_commit in inlog; smash_minbft;
              try (complete (eapply ind in run1; eauto; eauto 3 with eo));
              [| |].

            { exists (commit2hash_data_i c); simpl.
              unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
              dands; auto;[].
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }

            { eapply ind in run1; try exact Heqx; simpl in *;
                unfold state_of_subcomponents in *; simpl in *; try reflexivity;
                  eauto 3 with eo; exrepnd; exists hd; dands; auto.
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }

            { exists (commit2hash_data_j c).
              unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
              dands; auto;[].
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }
          }
        }

        {
          unfold call_log_commit, bind in Heqx4; simpl in *; smash_minbft;
            try (complete (unfold state_of_subcomponents in *; simpl in *;
                           ginv; eapply ind in run1; eauto; eauto 3 with eo));[].
          unfold call_is_committed, bind in Heqx; simpl in *; smash_minbft;
            try (complete (unfold state_of_subcomponents in *; simpl in *;
                           ginv; eapply ind in run1; eauto; eauto 3 with eo));[|].

          { unfold state_of_subcomponents in *; simpl in *; ginv.
            rewrite ui_in_log_log_new_commit in inlog; smash_minbft;
              try (complete (eapply ind in run1; eauto; eauto 3 with eo));
              [| |].

            { exists (commit2hash_data_i c); simpl.
              unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
              dands; auto;[].
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }

            { rewrite ui_in_log_log_new_commit in Heqx; smash_minbft;
                try (complete (eapply ind in run1; eauto; eauto 3 with eo));
                [| |].

              { exists (commit2hash_data_i c); simpl.
                unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
                dands; auto;[].
                unfold MinBFT_data_knows in *; simpl in *.
                rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }

              { eapply ind in run1; try exact Heqx; simpl in *;
                  unfold state_of_subcomponents in *; simpl in *; try reflexivity;
                    eauto 3 with eo; exrepnd; exists hd; dands; auto.
                unfold MinBFT_data_knows in *; simpl in *.
                unfold commit2ui_i in *; simpl in *.
                autorewrite with minbft in *.
                rewrite hash_data_in_log_log_new_commit_eq; smash_minbft.
                { rewrite hash_data_in_log_log_new_commit_eq in Heqx; simpl in *.
                  unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft. }
                { rewrite hash_data_in_log_log_new_commit_eq in Heqx; simpl in *.
                  unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft. }
              }

              { exists (Build_HashData
                          (commit2view c)
                          (request_b (commit2request c))
                          (Build_preUI (usig_id s1) (S (usig_counter s1)))); simpl.
                unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
                dands; auto;[].
                unfold MinBFT_data_knows in *; simpl in *.
                rewrite hash_data_in_log_log_new_commit_eq; smash_minbft.
                { rewrite hash_data_in_log_log_new_commit_eq in Heqx; simpl in *.
                  unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft. }
                { rewrite hash_data_in_log_log_new_commit_eq in Heqx; simpl in *.
                  unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft. }
              }
            }

            { exists (commit2hash_data_j c).
              unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
              dands; auto;[].
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }
          }

          { unfold state_of_subcomponents in *; simpl in *; ginv.
            rewrite ui_in_log_log_new_commit in inlog; smash_minbft;
              try (complete (eapply ind in run1; eauto; eauto 3 with eo));
              [| |].

            { exists (commit2hash_data_i c); simpl.
              unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
              dands; auto;[].
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }

            { rewrite ui_in_log_log_new_commit in Heqx; smash_minbft;
                try (complete (eapply ind in run1; eauto; eauto 3 with eo));
                [| |].

              { exists (commit2hash_data_i c); simpl.
                unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
                dands; auto;[].
                unfold MinBFT_data_knows in *; simpl in *.
                rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }

              { eapply ind in run1; try exact Heqx; simpl in *;
                  unfold state_of_subcomponents in *; simpl in *; try reflexivity;
                    eauto 3 with eo; exrepnd; exists hd; dands; auto.
                unfold MinBFT_data_knows in *; simpl in *.
                unfold commit2ui_i in *; simpl in *.
                autorewrite with minbft in *.
                rewrite hash_data_in_log_log_new_commit_eq; smash_minbft.
                { rewrite hash_data_in_log_log_new_commit_eq in Heqx; simpl in *.
                  unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft. }
                { rewrite hash_data_in_log_log_new_commit_eq in Heqx; simpl in *.
                  unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft. }
              }

              { exists (Build_HashData
                          (commit2view c)
                          (request_b (commit2request c))
                          (Build_preUI (usig_id s1) (S (usig_counter s1)))); simpl.
                unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
                dands; auto;[].
                unfold MinBFT_data_knows in *; simpl in *.
                rewrite hash_data_in_log_log_new_commit_eq; smash_minbft.
                { rewrite hash_data_in_log_log_new_commit_eq in Heqx; simpl in *.
                  unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft. }
                { rewrite hash_data_in_log_log_new_commit_eq in Heqx; simpl in *.
                  unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft. }
              }
            }

            { exists (commit2hash_data_j c).
              unfold verify_UI in *; simpl in *; autorewrite with minbft in *.
              dands; auto;[].
              unfold MinBFT_data_knows in *; simpl in *.
              rewrite hash_data_in_log_log_new_commit_eq; smash_minbft. }
          }
        }
      }
    }
  Qed.*)

  Lemma request_data_was_verified :
    forall {eo : EventOrdering} (e : Event) (l : LOG_state) (u : TRINC_state) v r ui,
      is_replica e
      -> M_state_sys_on_event MinBFTsys e LOGname = Some l
      -> M_state_sys_on_event MinBFTsys e USIGname = Some u
      -> kc_knows (minbft_data_rdata (request_data v r ui)) l
      -> verify_hash_usig (Build_HashData v r (ui_pre ui)) (ui2digest ui) (trinc_local_keys u) = true.
  Proof.
    introv isr eqst1 eqst2 unl.

    unfold kc_Tknows in unl; simpl in unl.
    unfold MinBFT_data_knows in unl; simpl in unl.

    rewrite M_state_sys_on_event_unfold in eqst1.
    rewrite M_state_sys_on_event_unfold in eqst2.

    apply map_option_Some in eqst1.
    apply map_option_Some in eqst2.
    exrepnd; try rev_Some.

    rewrite eqst1 in eqst2; ginv.

    unfold is_replica in *; exrepnd.

    revert dependent u.
    revert dependent l.
    revert dependent a.
    rewrite isr0; simpl.

    (* WARNING *)
    clear isr0.

    induction e as [e ind] using predHappenedBeforeInd;[]; introv run stl inlog stu.

    rewrite M_run_ls_on_event_unroll2 in run.

    (*rewrite M_run_ls_before_event_unroll_on in run.

    destruct (dec_isFirst e) as [d|d].

    {
      clear ind.

      unfold M_run_ls_on_this_one_event in run; simpl in *.
      apply map_option_Some in run; exrepnd; rev_Some.
      autorewrite with minbft in *.

      Time minbft_dest_msg Case;
        repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
        ginv; simpl in *; autorewrite with minbft in *; auto;
          unfold verify_UI in *; simpl in *; autorewrite with minbft in *;
            first [destruct p as [b pui], b
                  |destruct c as [b pui], b]; simpl in *; ginv;
              unfold prepare2hash_data, RequestData2HashData, prepare2request in *; simpl in *; auto;
                unfold invalid_prepare, valid_prepare in *; simpl in *; smash_minbft;
                  unfold prepare2view in *; simpl in *; subst; tcsp;
                    try (complete (unfold state_of_subcomponents in *; simpl in *; ginv)).
    }*)

    {
      apply map_option_Some in run; exrepnd; rev_Some.
      applydup M_run_ls_before_event_ls_is_minbft in run1; exrepnd; subst.

      unfold M_run_ls_on_this_one_event in run0; simpl in *.
      apply map_option_Some in run0; exrepnd; rev_Some.
      autorewrite with minbft in *.

      Time minbft_dest_msg Case;
        repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
        try (simpl in *; unfold state_of_subcomponents in *; simpl in *; ginv);
        try (complete (ginv; unfold try_create_trinc_ui, try_update_TRINC in *; simpl in *; smash_minbft2;
                         rewrite M_run_ls_before_event_unroll_on in run1;
                         destruct (dec_isFirst e); smash_minbft2;
                           eapply ind in run1; eauto; eauto 3 with eo));
        try (complete (ginv; unfold try_create_trinc_ui, try_update_TRINC in *; simpl in *; smash_minbft2;
                         unfold verify_UI in *; simpl in *; autorewrite with minbft in *;
                           first [destruct p as [b pui], b
                                 |destruct c as [b pui], b]; simpl in *; ginv;
                             unfold prepare2hash_data, RequestData2HashData, prepare2request in *; simpl in *; auto;
                               unfold invalid_prepare, valid_prepare in *; simpl in *; smash_minbft;
                                 unfold prepare2view in *; simpl in *; subst; tcsp; ginv; auto;
                                   try (complete (rewrite M_run_ls_before_event_unroll_on in run1;
                                                    destruct (dec_isFirst e); smash_minbft2;
                                                      eapply ind in run1; eauto; eauto 3 with eo)))).
    }
  Qed.

  Lemma M_run_ls_on_event_MinBFT_to_components :
    forall i {eo : EventOrdering} (e : Event) j s l u,
      loc e = MinBFT_replica i
      -> M_run_ls_on_event (MinBFTlocalSys i) e = Some (MinBFTlocalSys_new j s u l)
      -> M_state_sys_on_event MinBFTsys e MAINname = Some s
         /\ M_state_sys_on_event MinBFTsys e USIGname = Some u
         /\ M_state_sys_on_event MinBFTsys e LOGname = Some l.
  Proof.
    introv eqrep h.
    unfold M_state_sys_on_event; allrw; simpl.
    unfold M_state_ls_on_event.
    allrw; simpl.
    unfold state_of_subcomponents; simpl; tcsp.
  Qed.

End TrIncprops1.
