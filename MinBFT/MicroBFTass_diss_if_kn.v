Require Export MicroBFTprops2.


Section MicroBFTass_diss_if_kn.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Lemma ASSUMPTION_disseminate_if_knows_true :
    forall (eo : EventOrdering) d, assume_eo eo (ASSUMPTION_disseminate_if_knows d).
  Proof.
    introv diss.
    simpl in *.
    exrepnd.

    unfold disseminate_data in *.
    unfold knows_after. simpl in *.
(*    unfold MicroBFT_data_knows.
    unfold MicroBFT_data_in_log. *)
    unfold state_after. simpl.

    (* exists c. *)


    unfold M_byz_output_sys_on_event in *; simpl.
    rewrite M_byz_output_ls_on_event_as_run in diss0; simpl.
    unfold M_byz_output_ls_on_this_one_event in *.
    allrw; simpl.

    unfold MicroBFTheader.node2name in *. simpl in *; subst.
    unfold MicroBFTsys in *. simpl in *.

    SearchAbout M_byz_run_ls_before_event.

    pose proof (ex_M_byz_run_ls_before_event_MicroBFTlocalSys e (loc e)) as run.
    repndors.
    {
      exrepnd.
      rewrite run0 in *. clear run0. simpl in *.

      remember (trigger e) as trig. symmetry in Heqtrig.
      destruct trig; simpl in *; ginv; tcsp;[].
      unfold state_of_trusted in *. simpl in *.
      unfold USIG_update in *. destruct i; simpl in *; ginv; subst; tcsp;[|].
      {
        destruct diss0; simpl in *; ginv; tcsp.

        eexists; dands; eauto;[|].
        {
          eexists; dands; eauto.
          erewrite M_state_sys_on_event_unfold.
          erewrite map_option_Some.
          

