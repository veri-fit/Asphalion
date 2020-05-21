Require Export MinBFTdeq.
Require Export TrIncprops2.
Require Export TrIncsm_mon.
Require Export TrIncrun.
Require Export ComponentAxiom.


Section TrIncass_tlearn.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Opaque KE_TOWNS.
  Opaque KE_TGENS.


  Lemma ASSUMPTION_trusted_learns_if_gen_true :
    forall (eo : EventOrdering),
      AXIOM_authenticated_messages_were_sent_or_byz eo MinBFTsys
      -> forall t, assume_eo eo (ASSUMPTION_trusted_learns_if_gen t).
  Proof.
    introv sendbyz; repeat introv.
    destruct e as [e exe].

    induction e as [e ind] using HappenedBeforeInd;[]; introv lrn.
    hide_hyp ind.
    simpl in *; exrepnd; GC.
    unfold learns_data in *; exrepnd; GC.

    pose proof (sendbyz e a (const_opTrust lrn3)) as sendbyz.
    simpl in *.
    repeat (autodimp sendbyz hyp).
    exrepnd; repndors; exrepnd; ginv;[|].

    {
      autodimp sendbyz5 hyp; eauto 3 with minbft.

      assert (exists k, loc e' = MinBFT_replica k) as eqloc'.
      { destruct a as [a tok], a, m; simpl in *; tcsp; ginv;
          try (complete (inversion sendbyz4; eauto)). }
      exrepnd.

      unfold M_output_sys_on_event in sendbyz5; simpl in *.
      rewrite eqloc'0 in *; simpl in *.
      apply M_output_ls_on_event_as_run in sendbyz5; exrepnd.
      applydup M_run_ls_before_event_ls_is_minbft in sendbyz5; exrepnd; subst; simpl in *.

      unfold M_output_ls_on_this_one_event in sendbyz6.
      remember (trigger_op e') as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; tcsp;[].

      unfold M_run_ls_on_input_out, M_run_ls_on_input in *; simpl in *.
      autorewrite with minbft in *.

      (* XXXXXXXXXXX *)
      Time minbft_dest_msg Case;
        repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
        try (complete (inversion sendbyz6; subst; simpl in *; tcsp));
        [| | | | | | |].

      { Case "Request".

        inversion sendbyz6; subst; simpl in *; clear sendbyz6.
        repeat (repndors; subst; tcsp; simpl in *; ginv);[].

        assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).
        repeat (dest_cases w; rev_Some).
        apply eq_cons in sendbyz2; repnd; GC.

        exists (MkEventN e' exe'); dands;
          allrw interp_owns; simpl; eauto 3 with minbft;
            try (complete (unfold data_is_owned_by; simpl; unfold ui2rep; simpl; eauto));[].
        unfold disseminate_data; simpl.
        unfold M_byz_output_sys_on_event; simpl.
        allrw; simpl.
        rewrite M_byz_output_ls_on_event_as_run.
        applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
        applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
        repeat (allrw; simpl).

        unfold M_byz_output_ls_on_this_one_event; simpl.
        unfold M_byz_run_ls_on_one_event; simpl.
        unfold data_is_in_out, event2out; simpl; allrw; simpl.

        unfold M_run_ls_on_input; simpl; autorewrite with comp minbft.

        repeat unfold_handler_concl; smash_minbft;
          try (complete (unfold try_create_trinc_ui in *; simpl; smash_minbft)).
        allrw; simpl.
        eexists; dands; eauto; simpl; tcsp.
        destruct x, w0; simpl in *; subst; tcsp.
      }

      { Case "Prepare".

        repndors; tcsp;
          inversion sendbyz6; subst; simpl in *; clear sendbyz6;
            repeat (repndors; subst; tcsp; ginv; simpl in * );[|].

        { pose proof (ind e') as ind.
          repeat (autodimp ind hyp); try (complete (eexists; allrw; simpl; reflexivity)).

          { exists (trinc_id s1) (prepare2auth_data p).
            allrw; simpl.
            unfold try_create_trinc_ui in *; simpl in *; smash_minbft2.
            dands; tcsp; eauto 3 with minbft;[].

            unfold MinBFT_ca_verify; simpl.
            rewrite prepare2auth_data_eq.
            unfold M_byz_state_sys_before_event; simpl.
            allrw; simpl.
            unfold M_byz_state_ls_before_event; simpl.
            applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
            applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
            allrw; simpl.
            unfold state_of_trusted; simpl; autorewrite with minbft in *; auto. }

          exrepnd.
          exists e'0; dands; eauto 3 with eo; exists c; dands; auto.
        }

        { assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).
          exists (MkEventN e' exe'); simpl; allrw interp_towns; dands; eauto 3 with minbft;
            try (complete (unfold data_is_owned_by; simpl; unfold ui2rep; simpl; eauto));[].

          repeat (dest_cases w; rev_Some);[].
          apply eq_cons in sendbyz2; repnd; GC.

          unfold disseminate_data; simpl.
          unfold M_byz_output_sys_on_event; simpl.
          allrw; simpl.
          rewrite M_byz_output_ls_on_event_as_run.
          applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
          applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
          repeat (allrw; simpl).

          unfold M_byz_output_ls_on_this_one_event; simpl.
          unfold M_byz_run_ls_on_one_event; simpl.
          unfold data_is_in_out, event2out; simpl; allrw; simpl.

          unfold M_run_ls_on_input; simpl; autorewrite with comp minbft.

          repeat unfold_handler_concl; smash_minbft;[].
          repnd; simpl in *.
          unfold call_verify_ui, bind in *; simpl in *; smash_minbft;[].
          unfold call_prepare_already_in_log, bind_pair, bind in *; simpl in *; smash_minbft.
          unfold try_create_trinc_ui in *; simpl in *; repeat smash_minbft2.
          eexists; dands; eauto; simpl in *; allrw; tcsp.
        }
      }

      { Case "Prepare".

        repndors; tcsp;
          inversion sendbyz6; subst; simpl in *; clear sendbyz6;
            repeat (repndors; subst; tcsp; ginv; simpl in * );[|].

        { pose proof (ind e') as ind.
          repeat (autodimp ind hyp); try (complete (eexists; allrw; simpl; reflexivity)).

          { exists (trinc_id s1) (prepare2auth_data p).
            allrw; simpl.
            unfold try_create_trinc_ui in *; simpl in *; smash_minbft2.
            dands; tcsp; eauto 3 with minbft;[].

            unfold MinBFT_ca_verify; simpl.
            rewrite prepare2auth_data_eq.
            unfold M_byz_state_sys_before_event; simpl.
            allrw; simpl.
            unfold M_byz_state_ls_before_event; simpl.
            applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
            applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
            allrw; simpl.
            unfold state_of_trusted; simpl; autorewrite with minbft in *; auto. }

          exrepnd.
          exists e'0; dands; eauto 3 with eo; exists c; dands; auto.
        }

        { assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).
          exists (MkEventN e' exe'); simpl; allrw interp_towns; dands; eauto 3 with minbft;
            try (complete (unfold data_is_owned_by; simpl; unfold ui2rep; simpl; eauto));[].

          unfold disseminate_data; simpl.
          unfold M_byz_output_sys_on_event; simpl.
          allrw; simpl.
          rewrite M_byz_output_ls_on_event_as_run.
          applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
          applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
          repeat (allrw; simpl).

          unfold M_byz_output_ls_on_this_one_event; simpl.
          unfold M_byz_run_ls_on_one_event; simpl.
          unfold data_is_in_out, event2out; simpl; allrw; simpl.

          unfold M_run_ls_on_input; simpl; autorewrite with comp minbft.

          repeat unfold_handler_concl; smash_minbft;[].
          repnd; simpl in *.
          unfold call_verify_ui, bind in *; simpl in *; smash_minbft;[].
          unfold call_prepare_already_in_log, bind_pair, bind in *; simpl in *; smash_minbft.
          unfold try_create_trinc_ui in *; simpl in *; repeat smash_minbft2.
          eexists; dands; eauto; simpl in *; allrw; tcsp. }
      }

      { Case "Commit".

        repeat (repndors; subst; tcsp; ginv; simpl in * );
          inversion sendbyz6; subst; simpl in *; clear sendbyz6; tcsp;[].
        repeat (repndors; subst; tcsp; simpl in *; ginv );[|].

        { pose proof (ind e') as ind.
          repeat (autodimp ind hyp); try (complete (eexists; allrw; simpl; reflexivity)).

          { exists (trinc_id s1) (commit2auth_data c).
            allrw; simpl.
            unfold try_create_trinc_ui in *; simpl in *; smash_minbft2;[].
            dands; tcsp; eauto 3 with minbft;[].

            unfold MinBFT_ca_verify; simpl.
            rewrite commit2auth_data_eq.
            unfold M_byz_state_sys_before_event; simpl.
            allrw; simpl.
            unfold M_byz_state_ls_before_event; simpl.
            applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
            applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
            allrw; simpl.
            unfold state_of_trusted; simpl; autorewrite with minbft in *; smash_minbft. }

          exrepnd.
          exists e'0; dands; eauto 3 with eo; eexists; dands; eauto.
        }

        { assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).
          exists (MkEventN e' exe'); simpl; allrw interp_towns; dands; eauto 3 with minbft;
            try (complete (unfold data_is_owned_by; simpl; unfold ui2rep; simpl; eauto));[].

          repeat (dest_cases w; rev_Some);[].
          apply eq_cons in sendbyz2; repnd; GC.

          unfold disseminate_data; simpl.
          unfold M_byz_output_sys_on_event; simpl.
          allrw; simpl.
          rewrite M_byz_output_ls_on_event_as_run.
          applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
          applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
          repeat (allrw; simpl).

          unfold M_byz_output_ls_on_this_one_event; simpl.
          unfold M_byz_run_ls_on_one_event; simpl.
          unfold data_is_in_out, event2out; simpl; allrw; simpl.

          unfold M_run_ls_on_input; simpl; autorewrite with comp minbft.

          repeat unfold_handler_concl; smash_minbft;[].
          repnd; simpl in *.
          unfold call_prepare_already_in_log_bool, bind in *; simpl in *; smash_minbft;[].
          unfold call_verify_ui, bind in *; simpl in *; smash_minbft;[].
          unfold call_prepare_already_in_log, bind_pair, bind in *; simpl in *; smash_minbft;[].
          unfold call_log_commit, bind in *; simpl in *; smash_minbft;[].
          unfold call_is_committed, bind in *; simpl in *; smash_minbft.
          unfold try_create_trinc_ui in *; simpl in *; smash_minbft2.
          eexists; dands; eauto; simpl in *; allrw; tcsp. }
      }

      { Case "Commit".

        repndors; subst; tcsp; inversion sendbyz6; subst; simpl in *; clear sendbyz6; tcsp; ginv;[].
        repeat (repndors; subst; tcsp; simpl in *; ginv);[|].

        { pose proof (ind e') as ind.
          repeat (autodimp ind hyp); try (complete (eexists; allrw; simpl; reflexivity)).

          { exists (trinc_id s1) (commit2auth_data c).
            allrw; simpl.

            unfold try_create_trinc_ui in *; simpl in *; smash_minbft2;[].
            dands; tcsp; eauto 3 with minbft;[].

            unfold MinBFT_ca_verify; simpl.
            rewrite commit2auth_data_eq.
            unfold M_byz_state_sys_before_event; simpl.
            allrw; simpl.
            unfold M_byz_state_ls_before_event; simpl.
            applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
            applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
            allrw; simpl.
            unfold state_of_trusted; simpl; autorewrite with minbft in *; smash_minbft. }

          exrepnd.
          exists e'0; dands; eauto 3 with eo; eexists; dands; eauto.
        }

        { assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).
          exists (MkEventN e' exe'); simpl; allrw interp_towns; dands; eauto 3 with minbft;
            try (complete (unfold data_is_owned_by; simpl; unfold ui2rep; simpl; eauto));[].

          repeat (dest_cases w; rev_Some);[].
          apply eq_cons in sendbyz2; repnd; GC.

          unfold disseminate_data; simpl.
          unfold M_byz_output_sys_on_event; simpl.
          allrw; simpl.
          rewrite M_byz_output_ls_on_event_as_run.
          applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
          applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
          repeat (allrw; simpl).

          unfold M_byz_output_ls_on_this_one_event; simpl.
          unfold M_byz_run_ls_on_one_event; simpl.
          unfold data_is_in_out, event2out; simpl; allrw; simpl.

          unfold M_run_ls_on_input; simpl; autorewrite with comp minbft.

          repeat unfold_handler_concl; smash_minbft;[].
          repnd; simpl in *.
          unfold call_prepare_already_in_log_bool, bind in *; simpl in *; smash_minbft;[].
          unfold call_verify_ui, bind in *; simpl in *; smash_minbft;[].
          unfold call_prepare_already_in_log, bind_pair, bind in *; simpl in *; smash_minbft;[].
          unfold call_log_commit, bind in *; simpl in *; smash_minbft;[].
          unfold call_is_committed, bind in *; simpl in *; smash_minbft.
          unfold try_create_trinc_ui in *; simpl in *; smash_minbft2.
          eexists; dands; eauto; simpl in *; allrw; tcsp. }
      }

      { Case "Commit".

        repndors; subst; tcsp; inversion sendbyz6; subst; simpl in *; clear sendbyz6; tcsp; ginv. }

      { Case "Commit".

        repndors; subst; tcsp; inversion sendbyz6; subst; simpl in *; clear sendbyz6; tcsp; ginv. }

      { Case "Accept".

        inversion sendbyz6; subst; simpl in *; clear sendbyz6.
        repeat (repndors; subst; tcsp; simpl in *; ginv).
      }
    }

    {
      ginv.
      assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).
      exists (MkEventN e' exe'); simpl; allrw interp_towns; dands; eauto 3 with minbft;
        try (complete (unfold data_is_owned_by; simpl; unfold ui2rep; simpl; eauto));[].

      revert dependent o.
      rewrite sendbyz7 in *; introv run tout.

      unfold M_byz_output_sys_on_event in *.
      rewrite sendbyz7 in *; simpl in *.
      unfold M_byz_output_ls_on_event in run; simpl in *.

      remember (M_byz_run_ls_before_event (MinBFTlocalSys (ui2rep t0)) e') as z; symmetry in Heqz.

      unfold disseminate_data; simpl.
      unfold M_byz_output_sys_on_event; simpl.
      unfold M_byz_output_ls_on_event; simpl.
      repeat (allrw; simpl).
      exists o; dands; auto.

      unfold M_byz_run_ls_on_one_event in *; simpl in *.
      unfold M_byz_run_ls_on_input in *; simpl in *.

      unfold is_trusted_event, data_is_in_out, trusted_is_in_out, event2out in *.
      remember (trigger e') as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; tcsp; ginv;[].

      apply M_byz_run_ls_before_event_ls_is_minbft in Heqz.
      assert (i0 = i) as xx by (inversion p; auto); subst.
      pose proof (UIPReflDeq ti_deq (trigger_info_trusted i) p) as xx; subst; simpl in *.

      repndors; exrepnd; subst; simpl in *.

      { pose proof (snd_M_run_ls_on_trusted_incr_n_procs_eq (USIGlocalSys u) i) as z.
        unfold LocalSystem in *; simpl in *; rewrite z in run; clear z.
        rewrite rw_M_run_ls_on_trusted_USIGlocalSys in run.
        destruct i as [cn i]; simpl in *; dest_cases w;[].
        subst; simpl in *.
        destruct i; repnd; repeat (simpl in *; repndors; ginv; tcsp).
        unfold try_create_trinc_ui in *; simpl in *; smash_minbft2. }

      { pose proof (snd_M_run_ls_on_trusted_incr_n_procs_eq (USIGlocalSys u) i) as z.
        unfold LocalSystem in *; simpl in *; rewrite z in run; clear z.
        rewrite rw_M_run_ls_on_trusted_USIGlocalSys in run.
        destruct i as [cn i]; simpl in *; dest_cases w;[].
        subst; simpl in *.
        destruct i; repnd; repeat (simpl in *; repndors; ginv; tcsp).
        unfold try_create_trinc_ui in *; simpl in *; smash_minbft2. }
    }
  Qed.
  Hint Resolve ASSUMPTION_trusted_learns_if_gen_true : minbft.

End TrIncass_tlearn.


Hint Resolve ASSUMPTION_trusted_learns_if_gen_true : minbft.
