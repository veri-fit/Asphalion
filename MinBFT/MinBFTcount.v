(* USIG instance *)

Require Export MinBFTcount_gen1.
Require Export MinBFTcount_gen2.
Require Export MinBFTcount_gen5.

Require Export MinBFTprops0.
Require Export MinBFTrep.
Require Export MinBFTstate.
Require Export MinBFTsubs.
Require Export MinBFTbreak0.
Require Export ComponentSM6.
Require Export MinBFTtacts2.


Section MinBFTcount.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma main_not_in_subs :
    forall s, ~ In MAINname (get_names (MinBFTsubs s)).
  Proof.
    introv; simpl; intro xx; repndors; tcsp; inversion xx.
  Qed.
  Hint Resolve main_not_in_subs : minbft.

  Lemma wf_minbft_subs :
    forall s, wf_procs (MinBFTsubs s).
  Proof.
    tcsp.
  Qed.
  Hint Resolve wf_minbft_subs : minbft.

  Lemma is_proc_n_proc_USIG_comp :
    forall s, is_proc_n_proc (USIG_comp s).
  Proof.
    introv; unfold is_proc_n_proc; simpl; eexists; introv; try reflexivity.
  Qed.
  Hint Resolve is_proc_n_proc_USIG_comp : minbft.

  Lemma is_proc_n_proc_LOG_comp :
    is_proc_n_proc LOG_comp.
  Proof.
    introv; unfold is_proc_n_proc; simpl; eexists; introv; try reflexivity.
  Qed.
  Hint Resolve is_proc_n_proc_LOG_comp : minbft.

  Lemma are_procs_n_procs_minbft_subs :
    forall s, are_procs_n_procs (MinBFTsubs s).
  Proof.
    introv i; simpl in *; repndors; subst; tcsp;
      unfold is_proc_n_nproc; simpl; eauto 3 with minbft.
  Qed.
  Hint Resolve are_procs_n_procs_minbft_subs : minbft.


  Lemma lower_headF_minbft_subs : lower_headF 1 MinBFTsubs.
  Proof.
    introv; simpl; auto.
  Qed.
  Hint Resolve lower_headF_minbft_subs : minbft.

  Lemma main_not_in_namesF_minbft_subs : not_in_namesF MAINname MinBFTsubs.
  Proof.
    introv xx; simpl in *; repndors; tcsp; inversion xx.
  Qed.
  Hint Resolve main_not_in_namesF_minbft_subs : minbft.

  Lemma wf_procsF_minbft_subs : wf_procsF MinBFTsubs.
  Proof.
    introv; simpl; tcsp.
  Qed.
  Hint Resolve wf_procsF_minbft_subs : minbft.

  Lemma are_procs_n_procsF_minbft_subs : are_procs_n_procsF MinBFTsubs.
  Proof.
    introv i; simpl in *; repndors; subst; tcsp;
      unfold is_proc_n_nproc; eauto 3 with minbft.
  Qed.
  Hint Resolve are_procs_n_procsF_minbft_subs : minbft.


  Lemma accepted_if_executed_previous_step :
    forall {eo  : EventOrdering}
           (e   : Event)
           (req : Request)
           (i   : nat)
           (l   : list name)
           (r   : Rep)
           (s   : MAIN_state)
           (s1  : USIG_state)
           (s2  : LOG_state),
      In (send_accept (accept req i) l)
         (M_output_ls_on_this_one_event (MinBFTlocalSys_new r s s1 s2) e)
      -> i = S (cexec s).
  Proof.
    introv h.
    eapply accepted_if_executed_previous_step; eauto.
  Qed.

  Lemma operation_inc_counter_ls_step :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i     : nat)
           (l     : list name)
           (s     : Rep)
           (ls    : MinBFTls),
      M_run_ls_before_event (MinBFTlocalSys s) e = Some ls
      -> In (send_accept (accept r (S i)) l) (M_output_ls_on_this_one_event ls e)
      -> i = 0
         \/
         exists r' l' e' ls',
           e' ⊏ e
           /\ M_run_ls_before_event (MinBFTlocalSys s) e' = Some ls'
           /\ In (send_accept (accept r' i) l') (M_output_ls_on_this_one_event ls' e').
  Proof.
    introv eqls out.
    eapply operation_inc_counter_ls_step; eauto 3 with minbft.
  Qed.

  Lemma operation_inc_counter_ls :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i1 i2 : nat)
           (l     : list name)
           (s     : Rep)
           (ls    : MinBFTls),
      M_run_ls_before_event (MinBFTlocalSys s) e = Some ls
      -> In (send_accept (accept r i2) l) (M_output_ls_on_this_one_event ls e)
      -> i1 < i2
      -> 0 < i1
      -> exists r' l' e' ls',
          e' ⊏ e
          /\ M_run_ls_before_event (MinBFTlocalSys s) e' = Some ls'
          /\ In (send_accept (accept r' i1) l') (M_output_ls_on_this_one_event ls' e').
  Proof.
    introv run i lt1 lt2.
    eapply operation_inc_counter_ls; eauto 3 with minbft.
  Qed.

  Lemma operation_inc_counter :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i1 i2 : nat)
           (l     : list name),
      is_replica e
      -> In (send_accept (accept r i2) l) (M_output_sys_on_event MinBFTsys e)
      -> i1 < i2
      -> 0 < i1
      -> exists r' l' e',
          e' ⊏ e
          /\ In (send_accept (accept r' i1) l') (M_output_sys_on_event MinBFTsys e').
  Proof.
    introv isr h lti lti0.
    eapply operation_inc_counter; eauto 3 with minbft.
  Qed.

  Lemma accepted_counter_positive :
    forall {eo    : EventOrdering}
           (e     : Event)
           (r     : Request)
           (i     : nat)
           (l     : list name),
      is_replica e
      -> In (send_accept (accept r i) l) (M_output_sys_on_event MinBFTsys e)
      -> 0 < i.
  Proof.
    introv isrep out.
    eapply accepted_counter_positive; eauto 3 with minbft.
  Qed.
  Hint Resolve accepted_counter_positive : minbft.

  Lemma M_output_ls_on_input_is_committed_implies :
    forall u c ls,
      M_run_ls_on_input (LOGlocalSys u) LOGname (is_committed_in c) = (ls, Some (log_out true))
      -> is_committed c u = true
         /\ ls = LOGlocalSys u.
  Proof.
    introv out.
    eapply M_output_ls_on_input_is_committed_implies; eauto.
  Qed.

  Lemma is_committed_implies_ex_entry :
    forall c l,
      is_committed c l = true
      -> ex_entry (commit2request_data_i c) l.
  Proof.
    induction l; introv h; simpl in *.
    { unfold is_committed in h; simpl in h; ginv. }
    unfold is_committed in *; simpl in *; dest_cases w.
    { exists a; simpl; repeat dest_cases w. }
    autodimp IHl hyp.
    unfold ex_entry in *; exrepnd; simpl; repeat dest_cases w; ginv; eauto.
  Qed.
  Hint Resolve is_committed_implies_ex_entry : minbft.

  Lemma ex_entry_log_new_commit :
    forall c l,
      ex_entry (commit2request_data_i c) (log_new_commit c l).
  Proof.
    induction l; unfold ex_entry in *; simpl in *; tcsp; repeat (dest_cases w); eauto;
      simpl in *; repeat dest_cases w; eauto;
        autorewrite with minbft in *; tcsp.
  Qed.
  Hint Resolve ex_entry_log_new_commit : minbft.

  Lemma prepare_already_in_log_implies_ex_entry :
    forall c l,
      prepare_already_in_log (commit2prepare c) l = true
      -> ex_entry (commit2request_data_i c) l.
  Proof.
    induction l; introv h; simpl in *; ginv.
    dest_cases w; autorewrite with minbft in *;
      unfold ex_entry; simpl; dest_cases w; eauto.
  Qed.
  Hint Resolve prepare_already_in_log_implies_ex_entry : minbft.

  Lemma ex_entry_log_new_commit_mk_my_commit :
    forall c ui l,
      ex_entry (commit2request_data_i c) (log_new_commit (mk_my_commit c ui) l).
  Proof.
    induction l; unfold ex_entry in *;
      repeat (simpl in *; repeat dest_cases w; autorewrite with minbft in *; eauto; tcsp).
  Qed.
  Hint Resolve ex_entry_log_new_commit_mk_my_commit : minbft.

  Lemma cond_LOGname_ex_entry_MinBFTsubs :
    forall R,
      cond_LOGname_ex_entry (MinBFTsubs R).
  Proof.
    introv h; introv.
    simpl in h; inversion h; subst; clear h.

    remember LOG_initial as l; clear Heql.

    revert l.
    induction k; simpl; introv w; simpl in *; repndors; tcsp.

    { unfold is_M_break_out, M_break_out, M_break in w; simpl in w; ginv.
      inversion w; subst; simpl in *; eauto 3 with minbft. }

    { exrepnd.
      unfold is_M_break_out, M_break_out, M_break in w0; simpl in w0; ginv.
      simpl; eauto 3 with minbft. }

    { unfold is_M_break_out, M_break_out, M_break in w; simpl in w; ginv.
      inversion w; subst; simpl in *; eauto 3 with minbft. }

    { exrepnd.
      unfold is_M_break_out, M_break_out, M_break in w1; simpl in w1; ginv.
      simpl; eauto 3 with minbft. }

    { unfold is_M_break_out, M_break_out, M_break in w.
      destruct i; simpl in *; smash_minbft_2;
        try (complete (unfold at2sm in w0; inversion w0; subst; eauto)). }
  Qed.
  Hint Resolve cond_LOGname_ex_entry_MinBFTsubs : minbft.

  Lemma MinBFTlocalSysP_MinBFTsubs_eq :
    forall R, MinBFTlocalSysP R (MinBFTsubs R) = MinBFTlocalSys R.
  Proof.
    tcsp.
  Qed.
  Hint Resolve MinBFTlocalSysP_MinBFTsubs_eq : minbft.

  Lemma MinBFTlocalSys_newP_new_inj :
    forall R s subs s1 s2 s3,
      MinBFTlocalSys_newP R s subs = MinBFTlocalSys_new R s1 s2 s3
      -> s = s1 /\ subs = MinBFTsubs_new s2 s3.
  Proof.
    introv h.
    apply eq_MinBFTlocalSys_newP_implies in h; tcsp.
  Qed.

  (* This uses compositional reasoning, but using [LOG_comp]'s spec defined in
     [M_output_ls_on_input_is_committed_implies] *)
  Lemma accepted_counter_if_received_UI_primary :
    forall {eo    : EventOrdering}
           (e     : Event)
           (R     : Rep)
           (r     : Request)
           (i     : nat)
           (l     : list name),
      In (send_accept (accept r i) l) (M_output_ls_on_event (MinBFTlocalSys R) e)
      ->
      exists (s  : MAIN_state)
             (s1 : USIG_state)
             (s2 : LOG_state)
             (rd : RequestData)
             (x  : LOG_state_entry)
             (ui : UI),
        M_run_ls_on_event (MinBFTlocalSys R) e = Some (MinBFTlocalSys_new R s s1 s2)
        /\ find_entry rd s2 = Some x
        (*/\ rd = log_entry_request_data x*)
        /\ request_data2ui rd = ui
        /\ request_data2request rd = r
        /\ request_data2view rd = current_view s
        /\ ui2counter ui = i
        /\ ui2rep ui = MinBFTprimary (current_view s).
  Proof.
    introv h.

    pose proof (accepted_counter_if_received_UI_primary e R (MinBFTsubs R) r i l) as q.
    repeat (autodimp q hyp); eauto 2 with minbft;[].
    simpl in *.
    rewrite MinBFTlocalSysP_MinBFTsubs_eq in q.
    exrepnd.
    applydup M_run_ls_on_event_ls_is_minbft in q1; exrepnd.
    apply MinBFTlocalSys_newP_new_inj in q10; repnd; subst.
    unfold ex_entry in *; exrepnd.
    autorewrite with minbft in *; ginv.

    exists s0 s1 log rd e0 (request_data2ui rd).
    dands; tcsp.
  Qed.

End MinBFTcount.


Hint Resolve main_not_in_subs : minbft.
Hint Resolve wf_minbft_subs : minbft.
Hint Resolve is_proc_n_proc_USIG_comp : minbft.
Hint Resolve is_proc_n_proc_LOG_comp : minbft.
Hint Resolve are_procs_n_procs_minbft_subs : minbft.
Hint Resolve lower_headF_minbft_subs : minbft.
Hint Resolve main_not_in_namesF_minbft_subs : minbft.
Hint Resolve wf_procsF_minbft_subs : minbft.

Hint Resolve accepted_counter_positive : minbft.
