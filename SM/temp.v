(* searched for state_sm_on_event (PBFTreplicaSM good...) *)


  Definition event_triggered_by_message (e : Event) (m : msg) : Prop :=
    trigger e = Some m.


  Lemma commit_received_from_good_replica_was_in_log :
    forall (eo : EventOrdering) (e : Event) good c i,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> commit2sender c = good
      -> verify_commit i (keys e) c = true
      -> event_triggered_by_message e (PBFTcommit c)
      ->
      exists e' st,
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st
        /\ commit_in_log c (log st) = true.

    (* used in PBFT_A_1_7 *)
    (* Invariant 1.7 pg 149 *)
    Lemma PBFT_A_1_7 :
      forall (eo : EventOrdering)
           (e  : Event)
           (i  : Rep)
           (rd : RequestData)
           (st : PBFTstate),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> exists_at_most_f_faulty [e] F
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> committed_log rd (log st) = true
      ->
      exists (R : list Rep),
        no_repeats R
        /\ F < length R
        /\ forall (k : Rep),
            In k R
            ->
            exists (e' : Event) (st' : PBFTstate),
              isCorrect e'
              /\ e' ≼ e
              /\ loc e' = PBFTreplica k
              /\ state_sm_on_event (PBFTreplicaSM k) e' = Some st'
              /\ prepared_log rd (log st') = true.


    (****************************************)

    (************************************************************************************)

      (* this one is never used*)
    Lemma pbft_knows_prepare_like_propagates1 :
    forall (eo : EventOrdering) (e : Event) good pl i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> prepare_like2sender pl = good
      -> prepare_like_in_log pl (log st)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      ->
      exists e' st,
        e' ≼ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st'
        /\ prepare_like_in_log pl (log st').


      (****************************************************************)

      Lemma pbft_knows_prepare_like_propagates :
    forall (eo : EventOrdering) (e : Event) pl,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> node_has_correct_trace_before e (prepare_like2sender pl)
      -> knows e pl
      ->
      exists e',
        e' ≼ e
        /\ loc e' = PBFTreplica (prepare_like2sender pl)
        /\ knows e' pl.
  Proof.
    introv auth ckeys ctrace kn.
    apply knows_propagates in kn; eauto 3 with pbft.
  Qed.


  (*************************************)

  Definition pbft_cp_vc_nv_data := Checkpoint.

  Definition pbft_cp_vc_nv_info := StateInfo.

  Definition pbft_cp_vc_nv_knows (d : pbft_cp_vc_nv_data) (s : PBFTstate) : Prop :=
    exists nv vc,
      new_view_in_log nv (view_change_state s)
      /\ In vc (new_view2cert nv)
      /\ In d (view_change2cert vc).

  Definition checkpoint2main_auth_data (cp : Checkpoint) : AuthenticatedData :=
    match cp with
    | checkpoint cp a => MkAuthData (PBFTmsg_bare_checkpoint cp) a
    end.

  Definition pbft_cp_vc_nv_data2main_auth_data (d : pbft_cp_vc_nv_data) : AuthenticatedData :=
    checkpoint2main_auth_data d.

  Definition pbft_cp_vc_nv_verify (eo : EventOrdering) (e : Event) (d : pbft_cp_vc_nv_data) : bool :=
    verify_one_auth_data (loc e) (keys e) (checkpoint2auth_data d).

  Definition pbft_cp_vc_nv_data2loc (d : pbft_cp_vc_nv_data) : Rep :=
    checkpoint2sender d.

  Lemma pbft_cp_vc_nv_no_initial_memory :
    forall n d, ~ pbft_cp_vc_nv_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h.
    unfold pbft_cp_vc_nv_knows in h; exrepnd; simpl in *; auto.
  Qed.

  Instance PBFT_I_LearnAndKnow_cp_vc_nv : LearnAndKnow 4.
  Proof.
    exact (MkLearnAndKnow
             4
             pbft_cp_vc_nv_data
             pbft_cp_vc_nv_info
             checkpoint2state_info
             PBFTstate
             pbft_cp_vc_nv_knows
             pbft_cp_vc_nv_data2loc
             pbft_cp_vc_nv_data2main_auth_data
             pbft_cp_vc_nv_verify
             _ _ pbft_cp_vc_nv_no_initial_memory).
  Defined.


      (* this one is used below *)
  Lemma knows4_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) good cp i,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> checkpoint2sender cp = good
      -> knows4 e cp
      ->
      exists e' good' st2,
        e' ≺ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
        /\ checkpoint2digest cp = create_hash_state_last_reply (PBFT.sm_state st2) (last_reply_state st2).


    (* but this one is used newer *)
      Lemma view_change_of_new_view_received_from_good_replica_was_logged_xxx :
    forall (eo : EventOrdering) (e : Event) vc nv i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> In vc (new_view2cert nv)
      ->
      exists e' good' st2,
        e' ≺ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        /\ next_to_execute st2 = next_seq (view_change2seq vc)
        /\ view_change2digest vc = create_hash_state_last_reply (sm_state st2) (last_reply_state st2).
      Proof.

        (********************************************************************************************)

   Record StateInfo :=
    MkStateInfo
      {
        si_digest : PBFTdigest;
        si_seq    : SeqNum;
      }.

  Definition view_change2state_info (vc : ViewChange) : StateInfo :=
    MkStateInfo (view_change2digest vc) (view_change2seq vc).

  Definition checkpoint2state_info (cp : Checkpoint) : StateInfo :=
    MkStateInfo (checkpoint2digest cp) (checkpoint2seq cp).


  Definition pbft_vc_nv_data := ViewChange.

  Definition pbft_vc_nv_info := StateInfo.

  Definition pbft_vc_nv_knows (vc : pbft_vc_nv_data) (s : PBFTstate) : Prop :=
    exists nv,
      new_view_in_log nv (view_change_state s)
      /\ In vc (new_view2cert nv).

  Definition view_change2main_auth_data (vc : ViewChange) : AuthenticatedData :=
    match vc with
    | view_change vc a => MkAuthData (PBFTmsg_bare_view_change vc) a
    end.

  Definition pbft_vc_nv_data2main_auth_data (d : pbft_vc_nv_data) : AuthenticatedData :=
    view_change2main_auth_data d.

  Definition pbft_vc_nv_verify (eo : EventOrdering) (e : Event) (d : pbft_vc_nv_data) : bool :=
    verify_list_auth_data (loc e) (keys e) (view_change2auth_data d).

  Definition pbft_vc_nv_data2loc (d : pbft_vc_nv_data) : Rep :=
    view_change2sender d.

  Lemma pbft_vc_nv_no_initial_memory :
    forall n d, ~ pbft_vc_nv_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h.
    unfold pbft_vc_nv_knows in h; exrepnd; simpl in *; auto.
  Qed.

  Instance PBFT_I_LearnAndKnow_vc_nv : LearnAndKnow 3.
  Proof.
    exact (MkLearnAndKnow
             3
             pbft_vc_nv_data
             pbft_vc_nv_info
             view_change2state_info
             PBFTstate
             pbft_vc_nv_knows
             pbft_vc_nv_data2loc
             pbft_vc_nv_data2main_auth_data
             pbft_vc_nv_verify
             _ _ pbft_vc_nv_no_initial_memory).
  Defined.


      Lemma view_change_of_new_view_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) vc i,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> knows3 e vc
      ->
      exists e' good' st2,
        e' ≺ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        /\ next_to_execute st2 = next_seq (view_change2seq vc)
        /\ view_change2digest vc = create_hash_state_last_reply (sm_state st2) (last_reply_state st2).
  Proof.

    (* this one is used in *)
      Lemma same_states_if_same_next_to_execute :
    forall (eo : EventOrdering) (ei ej : Event) i j sti stj,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [ei,ej] F
      -> loc ei = PBFTreplica i
      -> loc ej = PBFTreplica j
      -> state_sm_on_event (PBFTreplicaSM i) ei = Some sti
      -> state_sm_on_event (PBFTreplicaSM j) ej = Some stj
      -> next_to_execute sti = next_to_execute stj
      -> PBFT.sm_state sti = PBFT.sm_state stj /\ last_reply_state sti = last_reply_state stj.


    (*************************************************************************)

      Lemma prepare_like_received_from_correct_replica_was_in_log :
    forall (eo : EventOrdering) (e : Event) good pl i,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> prepare_like2sender pl = good
      -> verify_main_prepare_like i (keys e) pl = true
      -> auth_data_in_trigger (prepare_like2main_auth_data pl) e
      ->
      exists e' st,
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st
        /\ prepare_like_in_log pl (log st).

        (*************************************************************************)
        (* knows0 *)

 Inductive Prepare_like :=
  | prepare_like_pre_prepare (pp : Pre_prepare)
  | prepare_like_prepare (p : Prepare).


  Definition pbft_pl_data := Prepare_like.

  Definition pbft_pl_info := RequestData.

  Definition pbft_pl_knows (d : pbft_pl_data) (s : PBFTstate) : Prop :=
    prepare_like_in_log d (log s).

  Definition pbft_pl_data2main_auth_data (d : pbft_pl_data) : AuthenticatedData :=
    prepare_like2main_auth_data d.

  Definition pbft_pl_data2loc (d : pbft_pl_data) : Rep :=
    prepare_like2sender d.

  Lemma pbft_pl_no_initial_memory :
    forall n d, ~ pbft_pl_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h; simpl in h; auto.
  Qed.

  Definition pbft_pl_verify (eo : EventOrdering) (e : Event) (d : pbft_pl_data) : bool :=
    verify_authenticated_data (loc e) (pbft_pl_data2main_auth_data d) (keys e).

  Global Instance PBFT_I_LearnAndKnow_pl : LearnAndKnow 0.
  Proof.
    exact (MkLearnAndKnow
             0
             pbft_pl_data
             pbft_pl_info
             prepare_like2request_data
             PBFTstate
             pbft_pl_knows
             pbft_pl_data2loc
             pbft_pl_data2main_auth_data
             pbft_pl_verify
             _ _ pbft_pl_no_initial_memory).
  Defined.


  (* knows1 *)
  Definition pbft_pl_nv_knows (d : pbft_pl_data) (s : PBFTstate) : Prop :=
    exists nv pi,
      new_view_in_log nv (view_change_state s)
      /\ In pi (mergeP (new_view2cert nv))
      /\ prepare_like_in_prepared_info d pi.

  Lemma pbft_pl_nv_no_initial_memory :
    forall n d, ~ pbft_pl_nv_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h; simpl in h.
    unfold pbft_pl_nv_knows in h; exrepnd; simpl in *; auto.
  Qed.

  Instance PBFT_I_LearnAndKnow_pl_nv : LearnAndKnow 1.
  Proof.
  Defined.


  (* this one is used in one below *)
  Lemma prepares_like_of_new_views_are_received0 :
    forall (eo : EventOrdering) (e : Event) pl good,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> replica_has_correct_trace_before eo e good
      -> PBFTcorrect_keys eo
      -> knows1 e pl
      -> prepare_like2sender pl = good
      ->
      exists e',
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ knows0 e' pl.



    Lemma prepares_like_of_new_views_are_received :
    forall (eo : EventOrdering) (e : Event) nv i st pi pl good,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> replica_has_correct_trace_before eo e good
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> In pi (mergeP (new_view2cert nv))
      -> prepare_like_in_prepared_info pl pi
      -> prepare_like2sender pl = good
      ->
      exists e' st',
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st'
        /\ prepare_like_in_log pl (log st').


      (******************CHECKPOINTS****************************************)

    Definition similar_checkpoint_in_new_view (cp : Checkpoint) (nv : NewView) :=
    exists cp' vc,
      In vc (new_view2cert nv)
      /\ checkpoint2digest cp' = checkpoint2digest cp
      /\ checkpoint2seq cp' = checkpoint2seq cp
      /\ In cp' (view_change2cert vc).

    (* used in checkpoint_somewhere_in_log_received_from_good_replica_was_logged *) (*???*)
      Lemma similar_checkpoint_in_new_view_implies :
    forall (eo : EventOrdering) (e : Event) nv cp,
      exists_at_most_f_faulty [e] F
      -> correct_new_view nv = true
      -> similar_checkpoint_in_new_view cp nv
      ->
      exists cp' vc,
        In vc (new_view2cert nv)
        /\ checkpoint2digest cp' = checkpoint2digest cp
        /\ checkpoint2seq cp' = checkpoint2seq cp
        /\ In cp' (view_change2cert vc)
        /\ node_has_correct_trace_before e (checkpoint2sender cp').
  Proof.
    introv atmost cor sim.
    unfold similar_checkpoint_in_new_view in sim; exrepnd.

    dup sim0 as corvc.
    apply correct_new_view_implies_correct_view_change in corvc; auto;[].
    applydup correct_view_change_implies_length in corvc.
    applydup correct_view_change_implies_no_repeats in corvc.
    pose proof (there_is_one_good_guy_before eo (map checkpoint2sender (view_change2cert vc)) [e]) as q.
    repeat (autodimp q hyp); exrepnd.
    allrw in_map_iff; exrepnd; subst.
    rewrite <- sim2, <- sim3.
    exists x vc; dands; auto; eauto 3 with pbft;[].
    introv w z; apply (q0 e); simpl; tcsp.
  Qed.


  (* used in  checkpoint_somewhere_in_log_received_from_good_replica_was_logged *)(*???*)
    Lemma similar_checkpoint_in_stable_implies :
    forall (eo : EventOrdering) (e : Event) cp s,
      exists_at_most_f_faulty [e] F
      -> wf_checkpoint_state (cp_state s) = true
      -> similar_checkpoint_in_stable cp s
      ->
      exists cp',
        In cp' (checkpoint_certificate_of_last_stable_checkpoint s)
        /\ checkpoint2digest cp' = checkpoint2digest cp
        /\ checkpoint2seq cp' = checkpoint2seq cp
        /\ node_has_correct_trace_before e (checkpoint2sender cp').
  Proof.
    introv atmost wf sim.
    unfold similar_checkpoint_in_stable in sim; exrepnd.

    unfold wf_checkpoint_state in *; smash_pbft.
    unfold wf_stable_checkpoint in *; smash_pbft.
    unfold wf_stable_checkpoint_entry in *; smash_pbft.
    unfold wf_stable_checkpoint_entry_no_repeats in *.
    unfold wf_stable_checkpoint_entry_same_seq_and_digest in *.

    allrw forallb_forall.
    allrw @norepeatsb_as_no_repeats.

    fold (checkpoint_certificate_of_last_stable_checkpoint s) in *.

    repndors;
      [destruct (checkpoint_certificate_of_last_stable_checkpoint s);
       simpl in *; tcsp|];[].

    pose proof (there_is_one_good_guy_before eo (map checkpoint2sender (checkpoint_certificate_of_last_stable_checkpoint s)) [e]) as q.
    repeat (autodimp q hyp); autorewrite with list; auto;[].
    exrepnd.
    allrw in_map_iff; exrepnd; subst.

    applydup wf in q2; smash_pbft.
    applydup wf in sim0; smash_pbft.
    unfold same_seq_nums, same_digests in *; smash_pbft.

    exists x; dands; auto; try congruence.
  Qed.

  (* used in checkpoint_somewhere_in_log_received_from_good_replica_was_logged *)(*???!!!*) (* I need this one *)
  Lemma sent_checkpoint_contains_state :
    forall (eo : EventOrdering) (e : Event) cp dst i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> (forall e' i good vc nv cp st,
             e' ≼ e
             -> loc e' = PBFTreplica i
             -> node_has_correct_trace_before e good
             -> checkpoint2sender cp = good
             -> state_sm_on_event (PBFTreplicaSM i) e' = Some st
             -> new_view_in_log nv (view_change_state st)
             -> In vc (new_view2cert nv)
             -> In cp (view_change2cert vc)
             ->
             exists e'' good' st2,
               e'' ≼ e'
               /\ loc e'' = PBFTreplica good'
               /\ state_sm_on_event (PBFTreplicaSM good') e'' = Some st2
               /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
               /\ checkpoint2digest cp = state2hash st2)
      -> loc e = PBFTreplica i
      -> In (send_checkpoint cp dst) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> exists e' good st2,
          e' ≼ e
          /\ loc e' = PBFTreplica good
          /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st2
          /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
          /\ checkpoint2digest cp = create_hash_state_last_reply (PBFT.sm_state st2) (last_reply_state st2).
  Proof.


    (* used in checkpoint_of_new_view_received_from_good_replica_was_logged *)
      Lemma checkpoint_somewhere_in_log_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) good cp i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> checkpoint2sender cp = good
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> checkpoint_somewhere_in_log cp st
      ->
      exists e' good' st2,
        e' ≼ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        (* cp is created when sequence number of the executed requests is divisible by some predefined constant k *)
        (* checkpoint contains digest of the state at event e' *)
        /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
        /\ checkpoint2digest cp = create_hash_state_last_reply (PBFT.sm_state st2) (last_reply_state st2).


          Lemma checkpoint_of_new_view_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) good vc nv cp i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> checkpoint2sender cp = good
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> In vc (new_view2cert nv)
      -> In cp (view_change2cert vc)
      ->
      exists e' good' st2,
        e' ≺ e
        /\ loc e' = PBFTreplica good'
        /\ state_sm_on_event (PBFTreplicaSM good') e' = Some st2
        /\ next_to_execute st2 = next_seq (checkpoint2seq cp)
        /\ checkpoint2digest cp = create_hash_state_last_reply (PBFT.sm_state st2) (last_reply_state st2).
  Proof.


    (***********************************************************************************)
      Lemma view_change_of_new_view_received_from_good_replica_was_logged :
    forall (eo : EventOrdering) (e : Event) good vc nv i st,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> loc e = PBFTreplica i
      -> node_has_correct_trace_before e good
      -> view_change2sender vc = good
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> new_view_in_log nv (view_change_state st)
      -> In vc (new_view2cert nv)
      ->
      exists e' st1 st2 v,
        e' ≼ e
        /\ loc e' = PBFTreplica good
        /\ state_sm_before_event (PBFTreplicaSM good) e' = Some st1
        /\ state_sm_on_event (PBFTreplicaSM good) e' = Some st2
        /\ own_view_change_in_log vc (view_change_state st2)
        /\ vc = mk_current_view_change good v st1
        /\ current_view st1 <= v <= current_view st2.
  Proof.



    (***********************************************************************************)
        (* knows0 *)

 Inductive Prepare_like :=
  | prepare_like_pre_prepare (pp : Pre_prepare)
  | prepare_like_prepare (p : Prepare).


  Definition pbft_pl_data := Prepare_like.

  Definition pbft_pl_info := RequestData.

  Definition pbft_pl_knows (d : pbft_pl_data) (s : PBFTstate) : Prop :=
    prepare_like_in_log d (log s).

  Definition pbft_pl_data2main_auth_data (d : pbft_pl_data) : AuthenticatedData :=
    prepare_like2main_auth_data d.

  Definition pbft_pl_data2loc (d : pbft_pl_data) : Rep :=
    prepare_like2sender d.

  Lemma pbft_pl_no_initial_memory :
    forall n d, ~ pbft_pl_knows d (Process.sm_state (PBFTreplicaSM n)).
  Proof.
    introv h; simpl in h; auto.
  Qed.

  Definition pbft_pl_verify (eo : EventOrdering) (e : Event) (d : pbft_pl_data) : bool :=
    verify_authenticated_data (loc e) (pbft_pl_data2main_auth_data d) (keys e).

  Global Instance PBFT_I_LearnAndKnow_pl : LearnAndKnow 0.
  Proof.
    exact (MkLearnAndKnow
             0
             pbft_pl_data
             pbft_pl_info
             prepare_like2request_data
             PBFTstate
             pbft_pl_knows
             pbft_pl_data2loc
             pbft_pl_data2main_auth_data
             pbft_pl_verify
             _ _ pbft_pl_no_initial_memory).
  Defined.


    Lemma prepares_like_of_new_views_are_received0 :
    forall (eo : EventOrdering) (e : Event) pl good,
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> node_has_correct_trace_before e good
      -> PBFTcorrect_keys eo
      -> knows1 e pl
      -> prepare_like2sender pl = good
      ->
      exists e',
        e' ≺ e
        /\ loc e' = PBFTreplica good
        /\ knows0 e' pl.
    Proof.

      (* used in PBFT_A_1_5 *)

    Lemma PBFT_A_1_5 :
    forall (eo : EventOrdering) (e : Event),
      authenticated_messages_were_sent_or_byz_usys eo PBFTsys
      -> PBFTcorrect_keys eo
      -> exists_at_most_f_faulty [e] F
      ->
      forall (nv      : NewView)
             (p_info1 : PreparedInfo)
             (p_info2 : PreparedInfo)
             (slf     : Rep)
             (state   : PBFTstate),
        loc e = PBFTreplica slf
        -> state_sm_on_event (PBFTreplicaSM slf) e = Some state
        -> new_view_in_log nv (view_change_state state)
        -> In p_info1 (mergeP (new_view2cert nv))
        -> In p_info2 (mergeP (new_view2cert nv))
        -> info_is_prepared p_info1 = true
        -> info_is_prepared p_info2 = true
        -> prepared_info2view p_info1 = prepared_info2view p_info2
        -> prepared_info2seq p_info1 = prepared_info2seq p_info2
        -> prepared_info2digest p_info1 = prepared_info2digest p_info2.



