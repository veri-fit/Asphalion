(* GENERIC *)

Require Export MinBFTcount_gen5_request.
Require Export MinBFTcount_gen5_reply.
Require Export MinBFTcount_gen5_prepare.
Require Export MinBFTcount_gen5_commit.
Require Export MinBFTcount_gen5_accept.
Require Export MinBFTcount_gen5_debug.


Section MinBFTcount_gen5.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  (* This uses compositional reasoning, but using [LOG_comp]'s spec defined in
     [M_output_ls_on_input_is_committed_implies] *)
  Lemma accepted_counter_if_received_UI_primary :
    forall {eo   : EventOrdering}
           (e    : Event)
           (R    : Rep)
           (subs : n_procs _)
           (r    : Request)
           (i    : nat)
           (l    : list name),
      ~ In MAINname (get_names subs)
      -> lower_head 1 subs = true
      -> wf_procs subs
      -> are_procs_n_procs subs
      -> in_subs LOGname subs = true
      -> in_subs USIGname subs = true
      -> cond_LOGname_ex_entry subs
      -> In (send_accept (accept r i) l) (M_output_ls_on_event (MinBFTlocalSysP R subs) e)
      ->
      exists (s     : MAIN_state)
             (subs' : n_procs _)
             (log   : LOG_state)
             (rd    : RequestData)
             (ui    : UI),
        M_run_ls_on_event (MinBFTlocalSysP R subs) e = Some (MinBFTlocalSys_newP R s subs')
        /\ state_of_component LOGname subs' = Some log
        /\ ex_entry rd log
        /\ request_data2ui rd = ui
        /\ request_data2request rd = r
        /\ request_data2view rd = current_view s
        /\ ui2counter ui = i
        /\ ui2cid ui = cid0
        /\ ui2rep ui = MinBFTprimary (current_view s).
  Proof.
    introv ni low wf aps logIN usigIN condL h.
    apply M_output_ls_on_event_as_run in h; exrepnd.
    rename ls' into ls.
    rewrite M_run_ls_on_event_unroll2; allrw; simpl.

    applydup M_run_ls_before_event_ls_is_minbftP in h1; exrepnd; subst; auto;[].
    unfold M_output_ls_on_this_one_event in h0; simpl in *.
    unfold M_run_ls_on_this_one_event; simpl; allrw; simpl.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input_out, trigger_op in *; simpl in *.
    remember (trigger e) as trig; symmetry in Heqtrig.
    destruct trig; simpl in *; tcsp;[].

    remember (M_run_ls_on_input (MinBFTlocalSys_newP R s subs') (msg_comp_name 0) d) as run.
    symmetry in Heqrun; repnd; simpl in *.

    apply (M_run_ls_before_event_minbft_preserves_in_subs LOGname) in h1 as insL'; auto;[].
    apply (M_run_ls_before_event_minbft_preserves_in_subs USIGname) in h1 as insU'; auto;[].
    applydup M_run_ls_before_event_preserves_subs in h1; eauto 3 with minbft; repnd;[].
    applydup M_run_ls_before_event_minbft_preserves_cond_LOGname in h1; auto;[].
    applydup @similar_subs_preserves_get_names in h2 as eqn.
    applydup wf_procs_MinBFTlocalSys_newP_implies_wf_procs_subs in h4; auto;
      try (complete (rewrite <-eqn; auto));[].
    apply wf_procs_MinBFTlocalSys_newP_implies_lower_head_subs in h4; auto;
      try (complete (rewrite <-eqn; auto));[].
    apply are_procs_n_procs_MinBFTlocalSys_newP_implies_are_procs_n_procs_subs in h5.
    rewrite eqn in ni.

    clear dependent subs.

    apply in_olist2list in h0; exrepnd; subst; simpl in *.
    pose proof (M_run_ls_on_input_ls_is_minbft_newP
                  (msg_comp_name 0) d (Some l0) s R run0 subs') as q.
    repeat (autodimp q hyp); exrepnd.
    subst; simpl in *.
    exists s' subs'0.

    destruct d.
    { eapply accepted_counter_if_received_UI_primary_request in Heqrun; eauto; exrepnd; eexists; eexists; eexists; dands; eauto. }
    { eapply accepted_counter_if_received_UI_primary_reply in Heqrun; eauto; exrepnd; eexists; eexists; eexists; dands; eauto. }
    { eapply accepted_counter_if_received_UI_primary_prepare in Heqrun; eauto; exrepnd; eexists; eexists; eexists; dands; eauto. }
    { eapply accepted_counter_if_received_UI_primary_commit in Heqrun; eauto; exrepnd; eexists; eexists; eexists; dands; eauto. }
    { eapply accepted_counter_if_received_UI_primary_accept in Heqrun; eauto; exrepnd; eexists; eexists; eexists; dands; eauto. }
    { eapply accepted_counter_if_received_UI_primary_debug in Heqrun; eauto; exrepnd; eexists; eexists; eexists; dands; eauto. }
  Qed.


End MinBFTcount_gen5.


Hint Resolve invalid_commit_implies_ui2cui_0 : minbft.
Hint Resolve invalid_prepare_implies_ui2cui_0 : minbft.
