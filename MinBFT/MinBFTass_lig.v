Require Export CalculusSM_derived2.
Require Export MinBFTprops2.
Require Export MinBFTsame.
Require Export MinBFTtacts2.


Section MinBFTass_lig.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma state_byz_usig_same_keys :
    forall {eo : EventOrdering} (e : Event) s,
      M_byz_state_sys_before_event_of_trusted MinBFTsys e = Some s
      -> usig_local_keys s = usig_initial_keys (loc e).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    apply map_option_Some in h; simpl in *; exrepnd; rev_Some.
    remember (loc e) as x; destruct x; simpl in *; tcsp;
      [|eapply M_byz_run_ls_before_event_unit_ls in h1; subst; simpl in *; inversion h0];[].

    rewrite M_byz_run_ls_before_event_unroll_on in h1.
    destruct (dec_isFirst e) as  [d|d]; smash_minbft1; simpl in *.

    { unfold state_of_trusted_in_ls in h0; simpl in *; ginv. }

    applydup @on_M_trusted_implies_or in h0; repndors; exrepnd; subst; simpl in *; rev_Some; GC.

    { apply M_byz_run_ls_on_event_M_run_ls_on_event in h1.
      applydup M_run_ls_on_event_ls_is_minbft in h1; exrepnd; subst.
      applydup usig_same_id_on in h1; subst.
      apply usig_same_keys_on in h1; simpl in *.
      unfold state_of_trusted_in_ls in h0; simpl in *; ginv. }

    ginv.

    pose proof (MinBFT_M_byz_run_ls_on_event_unroll_sp (local_pred e) n) as q.
    repndors; exrepnd.

    { pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo.
      pose proof (ind u) as ind; autodimp ind hyp.

      { unfold M_byz_state_sys_before_event_of_trusted; simpl; autorewrite with eo.
        unfold M_byz_state_ls_before_event_of_trusted; simpl.
        rewrite <- Heqx; simpl.
        allrw; simpl; tcsp. }

      autorewrite with eo.
      rewrite q1 in h1.
      clear q1 q0.

      unfold M_byz_run_ls_on_this_one_event in *.
      unfold if_trigger_info_data in *.
      remember (trigger (local_pred e)) as trig.
      destruct trig; simpl in *; simpl in *;
        repeat(simpl in *; autorewrite with minbft in *; smash_minbft2); ginv.

      { Time minbft_dest_msg Case;
          repeat(simpl in *; autorewrite with minbft in *; smash_minbft2;
                   try (complete (inversion h1))). }

      { unfold state_of_trusted in *; simpl in *; destruct i; simpl in *; repnd; simpl in *;
          unfold USIG_update in *; smash_minbft2; ginv;
            inversion Heqx0; subst; simpl in *; try congruence. } }

    { rewrite q1 in h1; clear q1; ginv; simpl in *.
      pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo.
      pose proof (ind u) as ind; autodimp ind hyp.

      { unfold M_byz_state_sys_before_event_of_trusted; simpl; autorewrite with eo.
        unfold M_byz_state_ls_before_event_of_trusted; simpl.
        rewrite <- Heqx; simpl.
        allrw; simpl; tcsp. }

      clear q0.
      remember (trigger (local_pred e)) as trig.
      destruct trig; simpl in *; simpl in *;
        repeat(simpl in *; autorewrite with minbft in *; smash_minbft2); ginv.
      unfold state_of_trusted in *; simpl in *.
      destruct i; simpl in *; repnd; simpl in *;
        unfold USIG_update in *; smash_minbft2; ginv;
          inversion Heqx0; subst; simpl in *; try congruence. }
  Qed.

  Lemma ui_in_one_data_of_msg :
    forall L c a m dst delay,
      In c (MinBFT_auth2data a)
      -> In a (MinBFT_get_contained_auth_data m)
      -> In (MkDMsg m dst delay) L
      -> In (minbft_data_ui (MinBFT_data2ui c)) (flat_map (fun dm => MinBFTmsg2data (dmMsg dm)) L).
  Proof.
    induction L; introv h q z; simpl in *; tcsp.
    repndors; subst; simpl; apply in_app_iff;[|right; eapply IHL; eauto];[].
    left.
    destruct m; simpl in *; repndors; subst; tcsp.
    { destruct p as [p ui], p as [v r], ui; simpl in *; repndors; subst; simpl in *; tcsp. }
    { destruct c0 as [c0 ui], c0 as [v r ui'], ui; simpl in *; repndors; subst; simpl in *; tcsp. }
  Qed.
  Hint Resolve ui_in_one_data_of_msg : minbft.

  Lemma ASSUMPTION_all_learns_if_trusted_gen_for_true :
    forall (eo : EventOrdering),
      AXIOM_authenticated_messages_were_sent_or_byz eo MinBFTsys
      -> assume_eo eo ASSUMPTION_all_learns_if_trusted_gen_for.
  Proof.
    introv sendbyz h; simpl in *.
    destruct e as [e exe].

    unfold learns_data in *; simpl in *; exrepnd.

    assert (In (minbft_data_ui (MinBFT_data2ui c)) (MinBFT_auth2data a)) as i.
    { destruct c as [rd|ui]; simpl in *; tcsp.
      destruct rd as [v r ui]; simpl in *; tcsp.
      destruct a as [a b], a, b; simpl in *; tcsp;
        destruct b; simpl in *; tcsp;
          try (complete (destruct p; simpl in *; repndors; ginv; tcsp));
          try (complete (destruct c; simpl in *; repndors; ginv; tcsp)). }

    exists (MinBFT_data2ui c).
    dands; eauto 3 with minbft.

    { pose proof (sendbyz e a (const_opTrust i)) as sendbyz.
      repeat (autodimp sendbyz hyp);[].
      exrepnd; repndors; exrepnd; ginv;[|].

      { autodimp sendbyz5 hyp; eauto 3 with minbft;[].

        assert (exists k, loc e' = MinBFT_replica k) as eqloc'.
        { destruct a as [a tok], a, m; simpl in *; tcsp; ginv;
            try (complete (inversion sendbyz4; eauto)). }
        exrepnd.
        assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).

        exists (MkEventN e' exe'); simpl; dands; auto.

        { unfold disseminate_data; simpl.
          unfold M_output_sys_on_event in *; simpl in *.
          pose proof (in_M_output_ls_on_event_implies_byz_eq e' (MinBFTsys (loc e')) (MkDMsg m dst delay)) as w.
          autodimp w hyp.
          unfold M_byz_output_sys_on_event; simpl in *.
          rewrite w; simpl; clear w; eauto 3 with minbft. }

        { exists k; dands; auto.
          unfold data_is_owned_by; simpl.

          (* In case [c] is the primary's UI in a commit [a], we have to get back to the primary *)

Set Nested Proofs Allowed.

SearchAbout M_byz_output_ls_on_event.
SearchAbout M_output_sys_on_event.
        }

      }
    }

    { unfold generated_for; dands; auto.
      introv h; exists n.
      destruct a as [a b], a, b; simpl in *; tcsp;
        destruct b; simpl in *; tcsp;
          first [destruct p as [v r] |destruct c0 as [v r uij] ];
          simpl in *; repndors; smash_minbft2;
            unfold verify_UI in *; simpl in *;
              unfold RequestData2HashData; simpl;
                apply state_byz_usig_same_keys in Heqx; try congruence. }
  Qed.

End MinBFTass_lig.

Hint Resolve ASSUMPTION_all_learns_if_trusted_gen_for_true : minbft.
