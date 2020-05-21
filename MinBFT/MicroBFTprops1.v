Require Export MicroBFTcount.


Section MicroBFTprops1.


  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.



  Lemma accepted_counter_if_know_UI_primary :
    forall {eo : EventOrdering}
           (e  : Event)
           (R  : MicroBFT_node)
           (r  : nat)
           (i  : nat)
           (l  : list name),
      In (send_accept (accept r i) l) (M_output_ls_on_event (MicroBFTlocalSys R) e)
      ->
      exists (s  : MAIN_state)
             (s1 : USIG_state)
             (s2 : LOG_state)
             (ui : UI)
             (rq : Commit),
        M_run_ls_on_event (MicroBFTlocalSys R) e = Some (MicroBFTlocalSys_new R s s1 s2)
        /\ kc_knows (microbft_data_rdata rq) s2
        /\ kc_Tknows ui s2
        /\ kc_trust2owner ui = Some MicroBFT_primary
        /\ kc_trust_has_id ui i
        /\ commit_ui rq = ui
        /\ commit_n rq = r
        /\ not_primary R = true.
  Proof.
    introv h.
    apply accepted_counter_if_received_UI_primary in h.
    exrepnd.
    exists s s1 s2 ui rq.
    simpl.
    dands; auto; unfold MicroBFT_data_knows; simpl; subst; eauto 3 with microbft; try congruence;[].
    unfold request_in_log; simpl; smash_microbft.
  Qed.

  (*
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
    unfold MicroBFT_data_knows in *.
    unfold MicroBFT_data_in_log in *.

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

*)

  Lemma node_backup1_backup2_or_primary :
    forall i,
      MicroBFTheader.node2name i =  MicroBFT_backup1
      \/ MicroBFTheader.node2name i =  MicroBFT_backup2
      \/ MicroBFTheader.node2name i =  MicroBFT_primary.
  Proof.
    destruct i; dands; eauto.
  Qed.

  (*
  (* Trying to generalize the lemmas below *)
  (* I believe that this one is false in case when loc e = MicroBFT_primary (see blow) *)
  Lemma request_was_verified :
    forall  i {eo : EventOrdering} (e : Event) (l : LOG_state) (u : USIG_state) r,
      loc e = MicroBFTheader.node2name i
      -> M_state_sys_on_event MicroBFTsys e LOGname = Some l
      -> M_state_sys_on_event MicroBFTsys e USIGname = Some u
      -> kc_knows (microbft_data_rdata r) l
      -> verify_hash_usig (Build_HashData (request_n r) (ui_pre (request_ui r))) (ui2digest (request_ui r)) (usig_local_keys u) = true.
  Proof.
    introv isr eqst1 eqst2 unl.

    unfold kc_Tknows in unl; simpl in unl.
    unfold MicroBFT_data_knows in unl; simpl in unl.

    rewrite M_state_sys_on_event_unfold in eqst1.
    rewrite M_state_sys_on_event_unfold in eqst2.

    apply map_option_Some in eqst1.
    apply map_option_Some in eqst2.
    exrepnd; try rev_Some.

    rewrite eqst1 in eqst2; ginv.

    revert dependent u.
    revert dependent l.
    revert dependent a.
    rewrite isr; simpl.

    (* WARNING *)
    clear isr.

    induction e as [e ind] using predHappenedBeforeInd;[]; introv run stl inlog stu.

    rewrite M_run_ls_on_event_unroll2 in run.

    {
      apply map_option_Some in run; exrepnd; rev_Some.
      applydup M_run_ls_before_event_ls_is_microbft in run1; exrepnd; subst.

      unfold M_run_ls_on_this_one_event in run0; simpl in *.
      apply map_option_Some in run0; exrepnd; rev_Some.
      autorewrite with microbft in *.

      Time microbft_dest_msg Case; repeat(simpl in *; autorewrite with microbft in *; smash_microbft);
        try (complete (rewrite M_run_ls_before_event_unroll_on in run1;
                         destruct (dec_isFirst e); [| eapply ind in run1; eauto; eauto 3 with eo]; smash_microbft)); [].

      {
        pose proof (node_backup1_backup2_or_primary i)as xx.
        repndors; try (rewrite xx in *; ginv);[].
  Abort.
*)

  Lemma request_was_verified :
    forall {eo : EventOrdering} (e : Event) (l : LOG_state) (u : USIG_state) r,
      (loc e = MicroBFT_backup1 \/ loc e = MicroBFT_backup2)
      -> M_state_sys_on_event MicroBFTsys e LOGname = Some l
      -> M_state_sys_on_event MicroBFTsys e USIGname = Some u
      -> kc_knows (microbft_data_rdata r) l
      -> verify_hash_usig (Build_HashData (commit_n r) (ui_pre (commit_ui r))) (ui2digest (commit_ui r)) (usig_local_keys u) = true.
  Proof.
    introv isr eqst1 eqst2 unl.

    unfold kc_Tknows in unl; simpl in unl.
    unfold MicroBFT_data_knows in unl; simpl in unl.

    rewrite M_state_sys_on_event_unfold in eqst1.
    rewrite M_state_sys_on_event_unfold in eqst2.

    apply map_option_Some in eqst1.
    apply map_option_Some in eqst2.
    exrepnd; try rev_Some.

    rewrite eqst1 in eqst2; ginv.

    revert dependent u.
    revert dependent l.
    revert dependent a.
    destruct isr as [isr1|isr2].

    { (* backup1*)
      rewrite isr1; simpl.

      (* WARNING *)
      clear isr1.

      induction e as [e ind] using predHappenedBeforeInd;[]; introv run stl inlog stu.

      rewrite M_run_ls_on_event_unroll2 in run.

      {
        apply map_option_Some in run; exrepnd; rev_Some.
        applydup M_run_ls_before_event_ls_is_microbft in run1; exrepnd; subst.

        unfold M_run_ls_on_this_one_event in run0; simpl in *.
        apply map_option_Some in run0; exrepnd; rev_Some; microbft_simp.

        unfold M_run_ls_on_input_ls, M_run_ls_on_input in *.
        autorewrite with microbft in *.
        unfold state_of_component in *; simpl in *.

        Time microbft_dest_msg Case; repeat(simpl in *; autorewrite with microbft in *; smash_microbft);
          try (complete (rewrite M_run_ls_before_event_unroll_on in run1;
                           destruct (dec_isFirst e); [| eapply ind in run1; eauto; eauto 3 with eo]; smash_microbft)).
      }
    }

    { (* backup2 *)
      rewrite isr2; simpl.

      (* WARNING *)
      clear isr2.

      induction e as [e ind] using predHappenedBeforeInd;[]; introv run stl inlog stu.

      rewrite M_run_ls_on_event_unroll2 in run.

      {
        apply map_option_Some in run; exrepnd; rev_Some.
        applydup M_run_ls_before_event_ls_is_microbft in run1; exrepnd; subst.

        unfold M_run_ls_on_this_one_event in run0; simpl in *.
        apply map_option_Some in run0; exrepnd; rev_Some.

        unfold M_run_ls_on_input_ls, M_run_ls_on_input in *.
        autorewrite with microbft in *.
        unfold state_of_component in *; simpl in *.

        Time microbft_dest_msg Case; repeat(simpl in *; autorewrite with microbft in *; smash_microbft);
          try (complete (rewrite M_run_ls_before_event_unroll_on in run1;
                           destruct (dec_isFirst e); [| eapply ind in run1; eauto; eauto 3 with eo]; smash_microbft)).
      }
    }
  Qed.

  (*
  Lemma request_was_verified_backup1 :
    forall {eo : EventOrdering} (e : Event) (l : LOG_state) (u : USIG_state) r,
      loc e = MicroBFT_backup1
      -> M_state_sys_on_event MicroBFTsys e LOGname = Some l
      -> M_state_sys_on_event MicroBFTsys e USIGname = Some u
      -> kc_knows (microbft_data_rdata r) l
      -> verify_hash_usig (Build_HashData (request_n r) (ui_pre (request_ui r))) (ui2digest (request_ui r)) (usig_local_keys u) = true.
  Proof.
    introv isr eqst1 eqst2 unl.

    unfold kc_Tknows in unl; simpl in unl.
    unfold MicroBFT_data_knows in unl; simpl in unl.

    rewrite M_state_sys_on_event_unfold in eqst1.
    rewrite M_state_sys_on_event_unfold in eqst2.

    apply map_option_Some in eqst1.
    apply map_option_Some in eqst2.
    exrepnd; try rev_Some.

    rewrite eqst1 in eqst2; ginv.

    revert dependent u.
    revert dependent l.
    revert dependent a.
    rewrite isr; simpl.

    (* WARNING *)
    clear isr.

    induction e as [e ind] using predHappenedBeforeInd;[]; introv run stl inlog stu.

    rewrite M_run_ls_on_event_unroll2 in run.

    {
      apply map_option_Some in run; exrepnd; rev_Some.
      applydup M_run_ls_before_event_ls_is_microbft in run1; exrepnd; subst.

      unfold M_run_ls_on_this_one_event in run0; simpl in *.
      apply map_option_Some in run0; exrepnd; rev_Some.
      autorewrite with microbft in *.

      Time microbft_dest_msg Case; repeat(simpl in *; autorewrite with microbft in *; smash_microbft);
        try (complete (rewrite M_run_ls_before_event_unroll_on in run1;
                         destruct (dec_isFirst e); [| eapply ind in run1; eauto; eauto 3 with eo]; smash_microbft)); [].

      unfold verify_UI, request_deq, invalid_request, valid_request in *.
      smash_microbft.
      destruct m. simpl in *; ginv; subst; tcsp.
    }

  Qed.


  Lemma request_was_verified_backup2 :
    forall {eo : EventOrdering} (e : Event) (l : LOG_state) (u : USIG_state) r,
      loc e = MicroBFT_backup2
      -> M_state_sys_on_event MicroBFTsys e LOGname = Some l
      -> M_state_sys_on_event MicroBFTsys e USIGname = Some u
      -> kc_knows (microbft_data_rdata r) l
      -> verify_hash_usig (Build_HashData (request_n r) (ui_pre (request_ui r))) (ui2digest (request_ui r)) (usig_local_keys u) = true.
  Proof.
    introv isr eqst1 eqst2 unl.

    unfold kc_Tknows in unl; simpl in unl.
    unfold MicroBFT_data_knows in unl; simpl in unl.

    rewrite M_state_sys_on_event_unfold in eqst1.
    rewrite M_state_sys_on_event_unfold in eqst2.

    apply map_option_Some in eqst1.
    apply map_option_Some in eqst2.
    exrepnd; try rev_Some.

    rewrite eqst1 in eqst2; ginv.

    revert dependent u.
    revert dependent l.
    revert dependent a.
    rewrite isr; simpl.

    (* WARNING *)
    clear isr.

    induction e as [e ind] using predHappenedBeforeInd;[]; introv run stl inlog stu.

    rewrite M_run_ls_on_event_unroll2 in run.

    {
      apply map_option_Some in run; exrepnd; rev_Some.
      applydup M_run_ls_before_event_ls_is_microbft in run1; exrepnd; subst.

      unfold M_run_ls_on_this_one_event in run0; simpl in *.
      apply map_option_Some in run0; exrepnd; rev_Some.
      autorewrite with microbft in *.

      Time microbft_dest_msg Case; repeat(simpl in *; autorewrite with microbft in *; smash_microbft);
        try (complete (rewrite M_run_ls_before_event_unroll_on in run1;
                         destruct (dec_isFirst e); [| eapply ind in run1; eauto; eauto 3 with eo]; smash_microbft)); [].

      unfold verify_UI, request_deq, invalid_request, valid_request in *.
      smash_microbft.
      destruct m. simpl in *; ginv; subst; tcsp.
    }
  Qed.
   *)

  Lemma M_run_ls_on_event_MicroBFT_to_compoments :
    forall i {eo : EventOrdering} (e : Event) j s l u,
      loc e = MicroBFTheader.node2name i
      -> M_run_ls_on_event (MicroBFTlocalSys i) e = Some (MicroBFTlocalSys_new j s u l)
      -> M_state_sys_on_event MicroBFTsys e MAINname = Some s
         /\ M_state_sys_on_event MicroBFTsys e USIGname = Some u
         /\ M_state_sys_on_event MicroBFTsys e LOGname = Some l.
  Proof.
    introv eqrep h.
    unfold M_state_sys_on_event.
    allrw.
    unfold M_state_ls_on_event.
    unfold state_of_component. simpl in *.
    pose proof (node_backup1_backup2_or_primary i) as xx.
    destruct xx as [xx| [xx| xx]];
      rewrite xx in eqrep; clear xx;
      dands; eauto; apply map_option_Some; eexists; dands; eauto.
  Qed.


  (*
  Lemma M_run_ls_on_event_MicroBFT_backup1_to_compoments :
    forall {eo : EventOrdering} (e : Event) j s l u,
      loc e = MicroBFT_backup1
      -> M_run_ls_on_event (MicroBFTlocalSys MicroBFT_backup1) e = Some (MicroBFTlocalSys_new j s u l)
      -> M_state_sys_on_event MicroBFTsys e MAINname = Some s
         /\ M_state_sys_on_event MicroBFTsys e USIGname = Some u
         /\ M_state_sys_on_event MicroBFTsys e LOGname = Some l.
  Proof.
    introv eqrep h.
    unfold M_state_sys_on_event.
    allrw.
    unfold M_state_ls_on_event.
    unfold state_of_component. simpl in *.
    dands; eauto; apply map_option_Some;  eexists; dands; eauto.
  Qed.


  Lemma M_run_ls_on_event_MicroBFT_backup2_to_compoments :
    forall {eo : EventOrdering} (e : Event) j s l u,
      loc e = MicroBFT_backup2
      -> M_run_ls_on_event (MicroBFTlocalSys MicroBFT_backup2) e = Some (MicroBFTlocalSys_new j s u l)
      -> M_state_sys_on_event MicroBFTsys e MAINname = Some s
         /\ M_state_sys_on_event MicroBFTsys e USIGname = Some u
         /\ M_state_sys_on_event MicroBFTsys e LOGname = Some l.
  Proof.
    introv eqrep h.
    unfold M_state_sys_on_event.
    allrw.
    unfold M_state_ls_on_event.
    unfold state_of_component. simpl in *.
    dands; eauto; apply map_option_Some;  eexists; dands; eauto.
  Qed.


  Lemma M_run_ls_on_event_MicroBFT_primary_to_compoments :
    forall {eo : EventOrdering} (e : Event) j s l u,
      loc e = MicroBFT_primary
      -> M_run_ls_on_event (MicroBFTlocalSys MicroBFT_primary) e = Some (MicroBFTlocalSys_new j s u l)
      -> M_state_sys_on_event MicroBFTsys e MAINname = Some s
         /\ M_state_sys_on_event MicroBFTsys e USIGname = Some u
         /\ M_state_sys_on_event MicroBFTsys e LOGname = Some l.
  Proof.
    introv eqrep h.
    unfold M_state_sys_on_event.
    allrw.
    unfold M_state_ls_on_event.
    unfold state_of_component. simpl in *.
    dands; eauto; apply map_option_Some;  eexists; dands; eauto.
  Qed.

*)

  (*
  Lemma accepted_implies_latest_executed_step :
    forall {eo     : EventOrdering}
           (e      : Event)
           (r      : Rep)
           (req    : Request)
           (i      : nat)
           (l      : list name)
           (s  s'  : MAIN_state)
           (s1 s1' : USIG_state)
           (s2 s2' : LOG_state),
      In (send_accept (accept req i) l) (M_output_ls_on_this_one_event (MicroBFTlocalSys_new r s s1 s2) e)
      -> M_run_ls_on_this_one_event (MicroBFTlocalSys_new r s s1 s2) e = Some (MicroBFTlocalSys_new r s' s1' s2')
      ->
      exists t,
        find_latest_executed_request (request2sender req) (vreq s') = Some t /\
        request2timestamp req <= t.
  Proof.
    introv out eqst.
    unfold M_output_ls_on_this_one_event in *.
    apply map_option_Some in eqst; exrepnd; rev_Some; simpl in *.
    rewrite eqst1 in out; simpl in *.
    autorewrite with microbft in *.

    Time microbft_dest_msg Case;
      repeat (simpl in *; autorewrite with microbft in * );
      repeat smash_microbft2;
      repndors; ginv; simpl in *; smash_microbft2.
  Qed.

  Lemma accepted_implies_latest_executed :
    forall {eo  : EventOrdering}
           (e   : Event)
           (req : Request)
           (i   : nat)
           (l   : list name)
           (s   : MAIN_state),
      is_replica e
      -> In (send_accept (accept req i) l) (M_output_sys_on_event MicroBFTsys e)
      -> M_state_sys_on_event MicroBFTsys e MAINname = Some s
      ->
      exists t,
        find_latest_executed_request (request2sender req) (vreq s) = Some t
        /\ request2timestamp req <= t.
  Proof.
    introv isrep out eqst.
    unfold is_replica in *; exrepnd.
    unfold M_output_sys_on_event in *; simpl in *.
    unfold M_state_sys_on_event in *; simpl in *.
    rewrite isrep0 in out, eqst; simpl in *.
    unfold M_state_ls_on_event in eqst.
    apply map_option_Some in eqst; exrepnd; rev_Some.
    applydup M_run_ls_on_event_ls_is_microbft in eqst1; exrepnd; subst; simpl in *; ginv.
    rewrite M_output_ls_on_event_as_run_before in out.
    rewrite M_run_ls_on_event_unroll in eqst1.
    rewrite M_run_ls_before_event_unroll_on in out.
    rewrite M_run_ls_before_event_unroll_on in eqst1.

    destruct (dec_isFirst e) as [d|d].

    { rewrite MicroBFTlocalSys_as_new in out, eqst1.
      eapply accepted_implies_latest_executed_step in out; eauto. }

    apply map_option_Some in eqst1; exrepnd; rev_Some.
    rewrite eqst1 in out.
    applydup M_run_ls_on_event_ls_is_microbft in eqst1; exrepnd; subst.
    eapply accepted_implies_latest_executed_step in out; eauto.
  Qed.

  Lemma accepted_implies_new_request_step :
    forall {eo  : EventOrdering}
           (e   : Event)
           (r   : Rep)
           (req : Request)
           (i   : nat)
           (l   : list name)
           (s   : MAIN_state)
           (s1  : USIG_state)
           (s2  : LOG_state),
      In (send_accept (accept req i) l) (M_output_ls_on_this_one_event (MicroBFTlocalSys_new r s s1 s2) e)
      -> new_bare_request (request_b req) (vreq s) = true.
  Proof.
    introv out.
    unfold M_output_ls_on_this_one_event in *.
    remember (trigger_op e) as trig.
    destruct trig; rev_Some; simpl in *; tcsp.
    autorewrite with microbft in *.

    Time microbft_dest_msg Case;
      repeat (simpl in *; autorewrite with microbft in * );
      repeat smash_microbft2;
      repndors; ginv; simpl in *; smash_microbft2;
        try (complete (unfold invalid_commit, valid_commit in *; smash_microbft;
                         rewrite <- new_bare_request_as_new_request; auto)).
  Qed.

  Lemma accepted_implies_new_request :
    forall {eo  : EventOrdering}
           (e   : Event)
           (req : Request)
           (i   : nat)
           (l   : list name)
           (s   : MAIN_state),
      is_replica e
      -> In (send_accept (accept req i) l) (M_output_sys_on_event MicroBFTsys e)
      -> M_state_sys_before_event MicroBFTsys e MAINname = Some s
      -> new_bare_request (request_b req) (vreq s) = true.
  Proof.
    introv isrep out eqst.
    unfold is_replica in *; exrepnd.
    unfold M_output_sys_on_event in *; simpl in *.
    unfold M_state_sys_before_event in *; simpl in *.
    rewrite isrep0 in out, eqst; simpl in *.
    unfold M_state_ls_before_event in eqst.
    apply map_option_Some in eqst; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_microbft in eqst1; exrepnd; subst; simpl in *; ginv.
    rewrite M_output_ls_on_event_as_run_before in out.
    rewrite eqst1 in out.
    apply accepted_implies_new_request_step in out; auto.
  Qed.

  Lemma vreq_monotonic_step :
    forall {eo : EventOrdering} (e : Event) r s u l s' c t (ls : MLocalSystem 1 0),
      M_run_ls_on_this_one_event (MicroBFTlocalSys_new r s u l) e = Some ls
      -> state_of_component MAINname ls = Some s'
      -> find_latest_executed_request c (vreq s) = Some t
      -> exists t',
          find_latest_executed_request c (vreq s') = Some t'
          /\ t <= t'.
  Proof.
    introv run eqst find.
    apply map_option_Some in run; exrepnd; simpl in *; rev_Some.
    autorewrite with microbft in *.

    Time microbft_dest_msg Case;
      repeat (simpl in *; autorewrite with microbft in * );
      repeat smash_microbft2; eauto.
  Qed.

  Lemma vreq_monotonic :
    forall {eo : EventOrdering} (e1 e2 : Event) s1 s2 c t,
      is_replica e1
      -> e1 ⊏ e2
      -> M_state_sys_on_event MicroBFTsys e1 MAINname = Some s1
      -> M_state_sys_before_event MicroBFTsys e2 MAINname = Some s2
      -> find_latest_executed_request c (vreq s1) = Some t
      -> exists t',
          find_latest_executed_request c (vreq s2) = Some t'
          /\ t <= t'.
  Proof.
    introv isrep lte eqsta eqstb find.
    unfold M_state_sys_on_event, M_state_sys_before_event in *.
    unfold is_replica in *; exrepnd.
    applydup local_implies_loc in lte as eqloc.
    rewrite <- eqloc in *.
    rewrite isrep0 in *; simpl in *.

    unfold M_state_ls_on_event, M_state_ls_before_event in *.
    apply map_option_Some in eqsta; exrepnd; rev_Some.
    apply map_option_Some in eqstb; exrepnd; rev_Some.

    clear eqloc isrep0.

    revert dependent a0.
    revert dependent s2.
    revert dependent e2.

    induction e2 as [e ind] using predHappenedBeforeInd;[]; introv lte eqst2 comp2.

    apply local_implies_pred_or_local in lte; repndors.

    { rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred in eqst2; eauto 3 with eo;[].
      unfold local_pred in eqst2; rewrite lte in eqst2.
      rewrite eqsta1 in eqst2; ginv.
      rewrite comp2 in eqsta0; ginv.
      eexists; dands; eauto. }

    exrepnd.
    pose proof (ind e0) as ind; repeat (autodimp ind hyp);[].
    rewrite M_run_ls_before_event_unroll in eqst2.
    assert (~ isFirst e) as nif by eauto 3 with eo.
    destruct (dec_isFirst e) as [d|d]; tcsp;[].
    apply map_option_Some in eqst2; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_microbft in eqst1; exrepnd; subst; simpl in *.
    unfold local_pred in eqst0; rewrite lte1 in eqst0.
    unfold local_pred in eqst1; rewrite lte1 in eqst1.

    pose proof (ind s (MicroBFTlocalSys_new r s s0 s3)) as ind.
    repeat (autodimp ind hyp);[].
    exrepnd.
    eapply vreq_monotonic_step in eqst0; try exact ind1;[|eauto].
    exrepnd.
    eexists; dands; eauto; try omega.
  Qed.
*)
End MicroBFTprops1.
