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

      unfold M_output_sys_on_event in sendbyz5; simpl in *.
      rewrite eqloc'0 in *; simpl in *.
      apply M_output_ls_on_event_as_run in sendbyz5; exrepnd.
      applydup M_run_ls_before_event_ls_is_microbft in sendbyz5; exrepnd; subst; simpl in *.

      unfold M_output_ls_on_this_one_event in sendbyz6.
      remember (trigger_op e') as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; tcsp;[].

      (* XXXXXXXXXXX *)
      unfold M_run_ls_on_input_out in *.
      unfold M_run_ls_on_input in *.
      autorewrite with comp microbft in *.
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
        unfold M_byz_output_ls_on_this_one_event; simpl.
        unfold M_byz_run_ls_on_one_event; simpl.
        repeat (allrw; simpl).
        unfold data_is_in_out, event2out; rewrite trig'; simpl.
        unfold M_run_ls_on_input; simpl.
        autorewrite with comp microbft.
        repeat unfold_handler_concl.
        smash_microbft.
        eexists; dands; try reflexivity; dands; tcsp.
      }

      {
        Case "Commit".

        repeat (simpl in *; try autorewrite with comp minbft in *; smash_microbft2);
          try (complete (inversion sendbyz6; subst; simpl in *; tcsp)).
      }
    }

    {
      ginv.
      assert (ex_node_e e') as exe' by (eexists; allrw; simpl; eauto).
      exists (MkEventN e' exe'); simpl; allrw interp_towns; dands; eauto 3 with minbft;
        try (complete (unfold data_is_owned_by; simpl; unfold ui2rep; simpl; eauto));[].

      unfold M_byz_output_sys_on_event in *; simpl in *.
      rewrite sendbyz7 in *; simpl in *.

      assert (MicroBFTsys (MicroBFTheader.node2name (ui2rep t)) = MicroBFTlocalSys (ui2rep t)) as temp by auto.
      rewrite temp in *.

      unfold disseminate_data.
      unfold M_byz_output_sys_on_event; simpl.
      allrw.
      exists o; dands; auto.
      clear sendbyz4.

      revert dependent o.
      unfold is_trusted_event in *.
      unfold data_is_in_out, trusted_is_in_out, event2out; simpl in *; rewrite p; simpl in *.
      introv xx; subst; simpl in *.
      allrw; simpl; tcsp.
    }
  Qed.
  Hint Resolve ASSUMPTION_trusted_learns_if_gen_true : microbft.

End MicroBFTass_tlearn.


Hint Resolve ASSUMPTION_trusted_learns_if_gen_true : microbft.
