Require Export MicroBFTprops2.
Require Export ComponentAxiom.


Section MicroBFTass_tlearn.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Opaque KE_TOWNS.
  Opaque KE_TGENS.


  Lemma ASSUMPTION_trusted_learns_if_gen_true :
    forall (eo : EventOrdering),
      AXIOM_authenticated_messages_were_sent_or_byz eo MicroBFTsys
      -> assume_eo eo (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen).
  Proof.
    introv sendbyz; introv lrn.
    destruct e as [e exe].

    simpl in *; exrepnd; GC.
    unfold learns_data in *; exrepnd; GC.

    pose proof (sendbyz e a (const_opTrust lrn3)) as sendbyz.
    simpl in *.
    repeat (autodimp sendbyz hyp).
    exrepnd; repndors; exrepnd; ginv;[|].

    {
      autodimp sendbyz5 hyp; eauto 3 with microbft.


      assert (exists k, loc e' = MicroBFTheader.node2name k) as eqloc'.
      { destruct a as [a tok], a, m; simpl in *; tcsp; ginv;
          try (complete (inversion sendbyz4; eauto)). }
      exrepnd.

      (* this was original proof
      assert (exists k, loc e' = MicroBFT_replica k) as eqloc'.
      { destruct a as [a tok], a, m; simpl in *; tcsp; ginv;
          try (complete (inversion sendbyz4; eauto)). }
      exrepnd. *)

      unfold M_output_sys_on_event in sendbyz5; simpl in *.
      rewrite eqloc'0 in *; simpl in *.
      apply M_output_ls_on_event_as_run in sendbyz5; exrepnd.
      applydup M_run_ls_before_event_ls_is_microbft in sendbyz5; exrepnd; subst; simpl in *.

      unfold M_output_ls_on_this_one_event in sendbyz6.
      remember (trigger_op e') as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; tcsp;[].

      (* XXXXXXXXXXX *)
      autorewrite with microbft in *.
      Time microbft_dest_msg Case; [|].

      { Case "Request".

        inversion sendbyz6; subst; simpl in *; clear sendbyz6.
        repeat (repndors; subst; tcsp; simpl in *; ginv);[].

        assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).

        exists (MkEventN e' exe'); dands;
          allrw interp_owns; simpl; eauto 3 with minbft;
            try (complete (unfold data_is_owned_by; simpl; unfold ui2rep; simpl; eauto));[ | unfold data_is_owned_by; smash_microbft].

        unfold disseminate_data; simpl.
        unfold M_byz_output_sys_on_event; simpl.
        allrw; simpl.
        rewrite M_byz_output_ls_on_event_as_run.
        applydup @M_run_ls_before_event_M_byz_run_ls_before_event in sendbyz5 as byz.
        applydup trigger_op_Some_implies_trigger_message in Heqtrig as trig'.
        repeat (allrw; simpl).

        autorewrite with microbft.
        repeat unfold_handler_concl. smash_microbft.
      }
      {
        Case "Commit".

        repeat (simpl in *; autorewrite with minbft in *; smash_microbft2);
          try (complete (inversion sendbyz6; subst; simpl in *; tcsp)).
      }
    }

    {
      ginv.
      assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).
      exists (MkEventN e' exe'); simpl; allrw interp_towns; dands; eauto 3 with minbft;
        try (complete (unfold data_is_owned_by; simpl; unfold ui2rep; simpl; eauto));[].

      unfold M_byz_output_sys_on_event_to_byz in *; simpl in *.
      unfold M_byz_output_sys_on_event in *.
      rewrite sendbyz6 in *; simpl in *.
      rewrite M_byz_output_ls_on_event_as_run in sendbyz5.

      assert (MicroBFTsys (MicroBFTheader.node2name (ui2rep t)) = MicroBFTlocalSys (ui2rep t)) as temp by auto.
      rewrite temp in *.

      pose proof (ex_M_byz_run_ls_before_event_MicroBFTlocalSys e' (ui2rep t)) as w.
      repndors; exrepnd;[|].

      {
        rewrite w0 in *; simpl in *.
        remember (trigger e') as trig; symmetry in Heqtrig.
        destruct trig; simpl in *; ginv;[].
        destruct i; simpl in *; repnd; simpl in *; ginv; simpl in *;[].

        unfold ui2rep in *; simpl in *.
        unfold state_of_trusted in *; simpl in *.

        unfold disseminate_data; simpl.
        unfold M_byz_output_sys_on_event; simpl.
        allrw; simpl.
        rewrite M_byz_output_ls_on_event_as_run.
        repeat (allrw; simpl); tcsp.
      }

      {
        rewrite w0 in *; simpl in *.
        remember (trigger e') as trig; symmetry in Heqtrig.
        destruct trig; simpl in *; ginv;[|].

        { Time microbft_dest_msg Case;
            unfold M_break, call_verify_ui, bind in *; simpl in *; smash_microbft. }

        destruct i; simpl in *; repnd; simpl in *; ginv; simpl in *;[].

        unfold kc_trust_is_owned; simpl.
        unfold ui2rep in *; simpl in *.
        unfold state_of_trusted in *; simpl in *.
        unfold ui2counter in *; simpl in *.

        unfold disseminate_data; simpl.
        unfold M_byz_output_sys_on_event; simpl.
        allrw; simpl.
        rewrite M_byz_output_ls_on_event_as_run.
        repeat (allrw; simpl); tcsp.
      }
    }


  Qed.
  Hint Resolve ASSUMPTION_trusted_learns_if_gen_true : microbft.

End MicroBFTass_tlearn.


Hint Resolve ASSUMPTION_trusted_learns_if_gen_true : microbft.
