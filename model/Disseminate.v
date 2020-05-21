(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxebourg University
  Copyright 2018 Luxembourg University
  Copyright 2019 Luxembourg University

  This file is part of Velisarios.

  Velisarios is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Velisarios is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Velisarios.  If not, see <http://www.gnu.org/licenses/>.


  Authors: Vincent Rahli
           Ivana Vukotic

*)


Require Export LearnAndKnows.
Require Export Synch.


Section Disseminate.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pm  : @Msg }.
  Context { qc  : @Quorum_context pn}.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pda : @DataAuth pd pn }.
  Context { cad : @ContainedAuthData pd pat pm }.
  Context { gms : @MsgStatus pm }.
  Context { dtc : @DTimeContext }.
  Context { iot : @IOTrustedFun }.
  Context { tc  : @TimeConstraint dtc }.


  Local Open Scope eo.
  Local Open Scope proc.


  (* ========== WE ONLY CONSIDER SYSTEMS THAT OUTPUT MESSAGES ========= *)

  Instance DisSysOutput : SysOutput.
  Proof.
    exact (MkSysOutput DirectedMsg).
  Defined.

  Context { p : nat }.
  Context { lak : LearnAndKnow p }.


  (* ========== USEFUL TACTICS ========= *)

  Ltac op_st_some m h :=
    match goal with
    | [ H : op_state _ _ _ _ = Some _ |- _ ] =>
      apply op_state_some_iff in H;
      destruct H as [m [h H]]

    | [ H : op_output _ _ _ _ = Some _ |- _ ] =>
      apply op_output_some_iff in H;
      destruct H as [m [h H]]
    end.


  (* ========== COMMUNICATION & EPOCHS ========= *)

  (* generalized [all_containers_satisfy_constraint] *)
  (* FIX: can we abstract this even more? Can we remove the [is_protocol_message] part? Do we really have to?*)
  Definition AXIOM_all_containers_satisfy_constraint
             (eo : EventOrdering) :=
    forall (d : lak_data) (m : msg),
      In (lak_data2auth d) (get_contained_authenticated_data m)
      -> is_protocol_message m = true.

  Definition nat2duration (n : nat) : dt_T := (nat2pdt n * epoch_duration)%dtime.

  (* This should be probable for instances of LearnAndKnow and AuthFun classes *)
  Definition AXIOM_verify_implies_lak_verify (eo : EventOrdering) :=
    forall (e e' : Event) (rk : receiving_key) (tok : Token) (d : lak_data),
      In rk (lookup_receiving_keys (keys e') (loc e))
      -> In tok (authenticate (lak_data2auth d) (keys e))
      -> verify (lak_data2auth d) (loc e) rk tok = true
      -> lak_verify e' d = true.

  (* In thesis this axiom is called: AXIOM_verify_implies_verify_authent_data *)
  Definition AXIOM_lak_verify_implies_verify_authenticated_data
             (eo  : EventOrdering) :=
    forall (e : Event)
           (d : lak_data),
      lak_verify e d = true
      -> verify_authenticated_data (loc e) (lak_data2auth d) (keys e) = true.

  Definition AXIOM_verify_authenticated_data_lak_verify_implies
             (eo  : EventOrdering) :=
    forall (e : Event)
           (d : lak_data),
      verify_authenticated_data (loc e) (lak_data2auth d) (keys e) = true
      -> lak_verify e d = true.

  Definition last_owns {eo : EventOrdering} (e : Event) (d : lak_data) (n : name) :=
    data_auth (loc e) (lak_data2auth d) = Some n.

  Definition has_correct_trace_bounded_lt_deadline
             (eo : EventOrdering) (n : name) (deadline : dt_T) :=
    exists e,
      loc e = n
      /\ has_correct_trace_bounded_lt e
      /\ (deadline < time e)%dtime.

  Definition AXIOM_preserves_knows (eo : EventOrdering) : Prop :=
    forall (e1 e2 : Event) (d : lak_data),
      has_correct_trace_bounded e2
      -> e1 ⊑ e2
      -> knows e1 d
      -> knows e2 d.

  Lemma knows_implies_knew :
    forall (eo : EventOrdering) (e1 e2 : Event) d,
      AXIOM_preserves_knows eo
      -> has_correct_trace_bounded_lt e2
      -> e1 ⊏ e2
      -> knows e1 d
      -> knew e2 d.
  Proof.
    introv pres cor lte kn.
    applydup localHappenedBefore_implies_le_local_pred in lte.
    eapply pres in lte0; autorewrite with eo;auto;[|eauto 3 with eo];
      autodimp lte0 hyp;[eauto|];[].
    unfold knows in lte0; unfold knew; exrepnd.
    autorewrite with eo in *.
    exists mem n; dands; auto.
    rewrite state_sm_before_event_as_state_sm_on_event_pred; auto; eauto 3 with eo.
  Qed.

  (* MOVE *)
  Lemma has_correct_trace_bounded_if_lt :
    forall {eo : EventOrdering} (e1 e2 : Event),
      e1 ⊏ e2
      -> has_correct_trace_bounded_lt e2
      -> has_correct_trace_bounded e1.
  Proof.
    introv lte cor lee.
    apply cor; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_bounded_if_lt : eo.

  (* MOVE *)
  Lemma subset_sing_left_as_in :
    forall {A} (a : A) l,
      subset [a] l <-> In a l.
  Proof.
    introv; split; intro h.
    { apply h; simpl; auto. }
    { introv i; simpl in *; repndors; subst; tcsp. }
  Qed.
  Hint Rewrite @subset_sing_left_as_in : list.

  Definition AXIOM_lak_data2auth_subset_lak_data2auth_list : Prop :=
    forall d,
      subset [lak_data2auth d] (lak_data2auth_list d).

  Definition AXIOM_lak_verify_implies_lak_data2auth_list_not_nil (eo  : EventOrdering) : Prop :=
    forall (e   :  Event)
           (d   :  lak_data),
      lak_data2auth_list d <> [].

  Lemma events_in_same_epoch_implies_has_correct_trace_before :
    forall {eo : EventOrdering} (e e' : Event),
      is_correct_in_near_future (loc e') e
      -> events_in_same_epoch e e'
      -> has_correct_trace_before e' (loc e').
  Proof.
    introv cor same le1 eqloc le2.

    unfold events_in_same_epoch in same.
    unfold is_correct_in_near_future in cor; exrepnd.

    pose proof (cor0 e') as cor0.

    assert (time e' <= time e'2)%dtime as letime.
    { eapply dt_le_rel_Transitive; eauto. }
    assert (e' ⊑ e'2) as lt3.
    { apply le_time_implies_happened_before; auto. }

    repeat (autodimp cor0 hyp); eauto 3 with eo;[].

    apply cor0; eauto 3 with eo.
  Qed.

  (* MOVE to DTime.v *)
  Lemma dt_add_0_r :
    forall t, (t + dt_nat_inj 0 == t)%dtime.
  Proof.
    introv; simpl.
    rewrite (Radd_comm dt_ring).
    apply dt_add_0_l.
  Qed.

  Lemma events_in_same_epoch_delay_implies :
    forall {eo : EventOrdering} (e e' : Event),
      events_in_same_epoch_delay e e' ('0)
      -> events_in_same_epoch e e'.
  Proof.
    introv h.
    unfold events_in_same_epoch.
    unfold events_in_same_epoch_delay in h.
    destruct h as [h1 h2].
    split.

    { eapply dt_le_trans;[|eauto].
      unfold min_received.
      repeat rewrite (Rsub_def dt_ring).
      apply dt_add_le_compat; try reflexivity.
      apply dt_add_le_compat; try reflexivity.
      simpl.
      rewrite dt_add_0_r; try reflexivity. }

    { eapply dt_le_trans;[eauto|].
      unfold max_received.
      apply dt_add_le_compat; try reflexivity.
      simpl.
      rewrite dt_add_0_r; try reflexivity. }
  Qed.
  Hint Resolve events_in_same_epoch_delay_implies : diss.

  Lemma snoc_implies_empty :
    forall  {T} a (l : list T),
      snoc l a = [] -> False.
  Proof.
    destruct l; introv h; simpl in *; tcsp.
  Qed.

  (*  generalization [all_verify_signed_msg_sign] *)
  Definition AXIOM_all_verify_lak_data_sign (eo : EventOrdering) : Prop :=
    forall (e1 e2 : Event) (d : lak_data) (g1 g2 : node_type),
      AXIOM_all_correct_can_verify eo
      -> loc e1 = node2name g1
      -> loc e2 = node2name g2
      -> has_correct_trace_before e1 (loc e1)
      -> has_correct_trace_before e2 (loc e2)
      -> lak_verify e1 d = true
      -> lak_verify e2 d = true.

  Definition AXIOM_output_immediately (eo : EventOrdering) :=
    forall (e : Event) m dst delay,
      In (MkDMsg m dst delay) (output_system_on_event_ldata lak_system e) -> delay = '0.

  Definition all_verified_in_trigger
             {eo : EventOrdering}
             (e  : Event) :=
    forall d,
      In (lak_data2auth d) (bind_op_list get_contained_authenticated_data (trigger_op e))
      -> lak_verify e d = true.

  Definition on_time {eo : EventOrdering} (e : Event) d (E : lak_data -> nat) B :=
    (time e <= nat2pdt (E d) * epoch_duration)%dtime
    /\ E d <= B.

  Definition events_in_later_epoch
             {eo    : EventOrdering}
             (e e'  : Event) :=
    (max_received (time e) < time e')%dtime.

  Lemma implies_events_in_later_epoch :
    forall {eo : EventOrdering} (e1 e2 : Event) E B,
      (nat2pdt B * epoch_duration < time e2)%dtime
      -> E < B
      -> (time e1 <= nat2pdt E * epoch_duration)%dtime
      -> events_in_later_epoch e1 e2.
  Proof.
    introv conda condb condc.
    unfold events_in_later_epoch.
    unfold max_received.
    eapply dt_le_lt_trans;[|eauto].
    eapply dt_le_trans;[apply dt_add_le_compat;[eauto|apply dt_le_refl] |].
    simpl; rewrite <- S_dt_T_mul.
    apply dt_mul_le_r; unfold epoch_duration; eauto 3 with dtime.
    apply dt_nat_nat_inj_le; auto.
  Qed.
  Hint Resolve implies_events_in_later_epoch : diss.

  Lemma events_in_later_of_same_implies :
    forall {eo : EventOrdering} (e e1 e2 : Event),
      events_in_same_epoch e e1
      -> events_in_later_epoch e e2
      -> (time e1 < time e2)%dtime.
  Proof.
    introv same later.
    unfold events_in_same_epoch, events_in_later_epoch in *; repnd.
    eapply dt_le_lt_trans;[eauto|]; auto.
  Qed.


  (* ========== DISSEMINATING ========= *)

  (* sending message, i.e. disseminating some data *)
  (* it could be defined as [disseminate_to_list e d []] *)
  Definition disseminate
             {eo : EventOrdering}
             (e  : Event)
             (d  : lak_data) :=
    exists (m : DirectedMsg),
      In m (output_system_on_event_ldata lak_system e)
      /\ In (lak_data2auth d) (get_contained_authenticated_data (dmMsg m)).

  (* NOTE: for now this is just for messages with delay 0 *)
  Definition disseminate_to_list
             {eo : EventOrdering}
             (e  : Event)
             (d  : lak_data)
             (L  : list node_type) :=
    exists (m : DirectedMsg),
      In m (output_system_on_event_ldata lak_system e)
      /\ In (lak_data2auth d) (get_contained_authenticated_data (dmMsg m))
      /\ subset (map node2name L) (dmDst m)
      /\ dmDelay m = '0.

  Definition disseminate_to
             {eo  : EventOrdering}
             (e   : Event)
             (d   : lak_data)
             (dst : node_type) :=
    disseminate_to_list e d [dst].

  (* generalization [gens_not_in_list] *)
  Definition nodes_not_in_list (l : list node_type) : list node_type :=
    diff node_deq l nodes.

  Definition disseminate_to_except
             {eo : EventOrdering}
             (e  : Event)
             (d  : lak_data)
             (L  : list node_type) :=
    disseminate_to_list e d (nodes_not_in_list L).

  Definition disseminate_i {eo : EventOrdering} (e : Event) (i : lak_info):=
    exists d, disseminate e d /\ i = lak_data2info d.

  (* One often disseminate knowledge that it holds *)
  Definition AXIOM_knows_if_disseminate (eo : EventOrdering) : Prop :=
    forall (e : Event) (d : lak_data) (n : node_type),
      loc e = node2name n
      -> disseminate e d
      -> knows e d.

  Definition AXIOM_knows_if_disseminate_i (eo : EventOrdering) : Prop :=
    forall (e : Event) (i : lak_info),
      disseminate_i e i -> knows_i e i.

  (* generalize [all_messages_are_sent_before_deadline] *)
  (* In thesis this axiom is called: AXIOM_messages_are_disseminated_before_deadline*)
  Definition AXIOM_all_messages_are_disseminated_before_deadline
             (eo  : EventOrdering)
             (N   : name -> Prop)
             (deadline : dt_T) :=
    forall (e : Event) (d : lak_data),
      has_correct_trace_before e (loc e)
      -> N (loc e)
      -> disseminate e d
      -> (time e <= deadline)%dtime.

  (* generalization of the [message_is_sent_before_deadline] *)
  Lemma dis_message_is_disseminated_before_deadline2 :
    forall {eo       : EventOrdering}
           (e        : Event)
           (N        : name -> Prop)
           (d        : lak_data)
           (n        : name)
           (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> has_correct_trace_before e n
      -> AXIOM_all_messages_are_disseminated_before_deadline eo N deadline
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> learns e d
      -> last_owns e d n
      -> N(n)
      -> exists e',
          e' ≺ e
          /\ loc e' = n
          /\ (time e' <= deadline)%dtime
          /\ disseminate e' d.
  Proof.
    introv sendbyz cor before cont verif lrn eqn nn.

    unfold learns in *; exrepnd; subst.

    apply implies_authenticated_messages_were_sent_non_byz_usys in sendbyz.
    pose proof (sendbyz e (lak_data2auth d) n) as w.
    repeat (autodimp w hyp); eauto 2 with eo;[].
    simpl in w.

    exrepnd; subst.
    pose proof (cont d m) as xx. clear cont.
    repeat (autodimp xx hyp). exrepnd.

    autodimp w4 hyp.

    pose proof (before e' d) as yy. clear before.
    repeat(autodimp yy hyp); allrw; eauto; [eauto 3 with eo | |].
    { exists (MkDMsg m dst delay); simpl; dands; auto. }
    { exists e'; dands; auto.
      exists (MkDMsg m dst delay); simpl; dands; auto. }
  Qed.

  Lemma dis_message_is_disseminated_before_deadline3 :
    forall {eo       : EventOrdering}
           (e        : Event)
           (N        : name -> Prop)
           (d        : lak_data)
           (n        : node_type)
           (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> has_correct_trace_before e (node2name n)
      -> AXIOM_all_messages_are_disseminated_before_deadline eo N deadline
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_knows_if_disseminate eo
      -> learns e d
      -> last_owns e d (node2name n)
      -> N(node2name n)
      -> exists e',
          e' ≺ e
          /\ loc e' = node2name n
          /\ (time e' <= deadline)%dtime
          /\ disseminate e' d
          /\ knows e' d.
  Proof.
    introv sendbyz cor before cont verif kid lrn eqn nn.
    apply (dis_message_is_disseminated_before_deadline2 e N d (node2name n) deadline) in lrn; auto.
    exrepnd.
    exists e'.
    dands; auto.
    eapply kid in lrn0; eauto.
  Qed.

  Lemma dis_message_is_disseminated_before_deadline4 :
    forall {eo       : EventOrdering}
           (e1 e2    : Event)
           (N        : name -> Prop)
           (d        : lak_data)
           (n        : node_type)
           (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> AXIOM_all_messages_are_disseminated_before_deadline eo N deadline
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_knows_if_disseminate eo
      -> AXIOM_preserves_knows eo
      -> has_correct_trace_before e1 (loc e2)
      -> has_correct_trace_bounded_lt e2
      -> learns e1 d
      -> last_owns e1 d (loc e2)
      -> N(loc e2)
      -> (deadline < time e2)%dtime
      -> loc e2 = node2name n
      -> knew e2 d.
  Proof.
    introv sendbyz before cont verif kid pres;
      introv cor1 cor2 lrn eqn nn ltdt eqloc.
    rewrite eqloc in *.
    apply (dis_message_is_disseminated_before_deadline3 e1 N d n deadline) in lrn; auto.
    exrepnd.
    assert (time e' < time e2)%dtime as ltt by (eapply dt_le_lt_trans;eauto).
    apply lt_time_implies_happened_before in ltt; auto.
    eapply knows_implies_knew; eauto.
    allrw. eauto.
  Qed.

  Lemma dis_message_is_disseminated_before_deadline2_learns_list :
    forall {eo       : EventOrdering}
           (e        : Event)
           (N        : name -> Prop)
           (d        : lak_data)
           (n        : name)
           (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> has_correct_trace_before e n
      -> AXIOM_all_messages_are_disseminated_before_deadline eo N deadline
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_lak_data2auth_subset_lak_data2auth_list
      -> AXIOM_lak_verify_implies_lak_data2auth_list_not_nil eo
      -> learns_list e d
      -> last_owns e d n
      -> N(n)
      -> exists e',
          e' ≺ e
          /\ loc e' = n
          /\ (time e' <= deadline)%dtime
          /\ disseminate e' d.
  Proof.
    introv sendbyz cor before cont verif aldildal aldnn lrn eqn nn.

    unfold learns_list in *; exrepnd; subst.

    apply implies_authenticated_messages_were_sent_non_byz_usys in sendbyz.


    pose proof (sendbyz e (lak_data2auth d) n) as w.
    repeat (autodimp w hyp); eauto 2 with eo;[|].
    {
      unfold auth_data_in_trigger in *.
      remember (trigger_op) as tt.
      destruct tt; ginv; simpl in *; subst; tcsp; [|].
      {

        assert (subset [lak_data2auth d] (lak_data2auth_list d)) as ff by apply aldildal.

        pose proof (subset_trans [lak_data2auth d] (lak_data2auth_list d)  (get_contained_authenticated_data m)) as ll.
        repeat (autodimp ll hyp);[].
        apply subset_sing_left_as_in. tcsp.
      }
      {
        rewrite subset_nil_r in lrn2.
        pose proof (aldnn e d) as tt. tcsp.
      }
    }

    simpl in w.

    exrepnd; subst.
    pose proof (cont d m) as xx. clear cont.
    repeat (autodimp xx hyp). exrepnd.

    autodimp w4 hyp.

    pose proof (before e' d) as yy. clear before.
    repeat(autodimp yy hyp); allrw; eauto; [eauto 3 with eo | |].
    { exists (MkDMsg m dst delay); simpl; dands; auto. }
    { exists e'; dands; auto.
      exists (MkDMsg m dst delay); simpl; dands; auto. }
  Qed.

  Lemma dis_message_is_disseminated_before_deadline3_learns_list :
    forall {eo       : EventOrdering}
           (e        : Event)
           (N        : name -> Prop)
           (d        : lak_data)
           (n        : node_type)
           (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> has_correct_trace_before e (node2name n)
      -> AXIOM_all_messages_are_disseminated_before_deadline eo N deadline
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_knows_if_disseminate eo
      -> AXIOM_lak_data2auth_subset_lak_data2auth_list
      -> AXIOM_lak_verify_implies_lak_data2auth_list_not_nil eo
      -> learns_list e d
      -> last_owns e d (node2name n)
      -> N(node2name n)
      -> exists e',
          e' ≺ e
          /\ loc e' = node2name n
          /\ (time e' <= deadline)%dtime
          /\ disseminate e' d
          /\ knows e' d.
  Proof.
    introv sendbyz cor before cont verif kid;
      introv aldaslda alvild lrn eqn nn.
    apply (dis_message_is_disseminated_before_deadline2_learns_list e N d (node2name n) deadline) in lrn; auto; [].
    exrepnd.
    exists e'.
    dands; auto.
    eapply kid in lrn0; eauto.
  Qed.

  (* we learn at [e'] in the same epoch as [e] *)
  Definition learns_in_same_epoch
             {eo   : EventOrdering}
             (e e' : Event)
             (d    : lak_data) :=
    learns e' d
    /\ events_in_same_epoch e e'.

  Definition correct_messages_get_delivered
             (eo : EventOrdering) :=
    forall (e : Event)
           (d : lak_data)
           (dst : node_type),
      disseminate_to e d dst
      -> has_correct_trace_before e (loc e)
      -> is_correct_in_near_future (node2name dst) e
      ->
      exists e',
        loc e' = node2name dst
        /\ learns_in_same_epoch e e' d.

  Lemma implies_correct_messages_get_delivered :
    forall {eo : EventOrdering},
      AXIOM_verify_implies_lak_verify eo
      -> AXIOM_verified_authenticated eo
      -> AXIOM_messages_get_delivered eo lak_system
      -> correct_messages_get_delivered eo.
  Proof.
    introv verif auth del.
    introv diss corr nf.
    unfold disseminate_to, disseminate_to_list in *; exrepnd; simpl in *.
    autorewrite with list in *.

    pose proof (del e m (node2name dst)) as del.
    repeat (autodimp del hyp).
    exrepnd.
    exists e'.
    dands; auto.
    rewrite diss0 in *.

    split; auto; eauto 3 with diss;[].

    unfold learns.
    exists dst; dands; auto; try (complete (allrw; simpl; auto));[].

    pose proof (events_in_same_epoch_implies_has_correct_trace_before e e') as q.
    repeat (autodimp q hyp); try (complete (allrw; auto)); eauto 3 with diss;[].

    pose proof (auth e e' (lak_data2auth d)) as auth.
    repeat (autodimp auth hyp).
    exrepnd.
    eapply verif; eauto.
  Qed.


  (* ========== DISSEMINATING + CLASS ========= *)

  Class Disseminate :=
    MkDisseminate {
        dis_data2msg  : lak_data -> msg; (* sm_msg_signed *)
      }.

  Context { dis : Disseminate }.


  Definition disseminate_top_to_list
             {eo : EventOrdering}
             (e  : Event)
             (d  : lak_data)
             (L  : list node_type) :=
    exists dst,
      In (MkDMsg (dis_data2msg d) dst ('0)) (output_system_on_event_ldata lak_system e)
      /\ subset (map node2name L) dst.

  Definition disseminate_top_to
             {eo  : EventOrdering}
             (e   : Event)
             (d   : lak_data)
             (dst : node_type) :=
    disseminate_top_to_list e d [dst].

  Definition disseminate_top_to_except
             {eo : EventOrdering}
             (e  : Event)
             (d  : lak_data)
             (L  : list node_type) :=
    disseminate_top_to_list e d (nodes_not_in_list L).

  Definition learns_on_time {eo : EventOrdering}
             (e : Event)
             (d : lak_data)
             (E : lak_data -> nat) (* epoch *)
             (B : nat) (* bound *) :=
    exists n,
      loc e = node2name n
      /\ trigger_op e = Some (dis_data2msg d)
      /\ lak_verify e d = true
      /\ on_time e d E B.

  Lemma learns_on_time_implies_cond :
    forall {eo : EventOrdering} (e : Event) d E B,
      learns_on_time e d E B -> on_time e d E B.
  Proof.
    introv lrn; unfold learns_on_time in *; exrepnd; tcsp.
  Qed.
  Hint Resolve learns_on_time_implies_cond : diss.

  Definition AXIOM_in_get_contained_authenticated_data_dis_data2msg :=
    forall d,
      In (lak_data2auth d) (get_contained_authenticated_data (dis_data2msg d)).

  Lemma learns_on_time_implies_learns :
    forall {eo : EventOrdering} (e : Event) d E B,
      AXIOM_in_get_contained_authenticated_data_dis_data2msg
      -> learns_on_time e d E B
      -> learns e d.
  Proof.
    introv ax lrn.
    unfold learns_on_time, learns in *; exrepnd.
    allrw; simpl; eexists; dands; eauto.
  Qed.
  Hint Resolve learns_on_time_implies_learns : diss.

  Definition AXIOM_in_get_contained_authenticated_data_preserves_lak_verify (eo : EventOrdering) :=
    forall (e : Event) a b,
      In (lak_data2auth a) (get_contained_authenticated_data (dis_data2msg b))
      -> lak_verify e b = true
      -> lak_verify e a = true.

  Lemma verify_trig_implies_all_verified :
    forall {eo : EventOrdering} (e : Event) m,
      AXIOM_in_get_contained_authenticated_data_preserves_lak_verify eo
      -> trigger_op e = Some (dis_data2msg m)
      -> lak_verify e m = true
      -> all_verified_in_trigger e.
  Proof.
    introv ax trig verif i; subst.
    rewrite trig in i; simpl in i.
    eapply ax; eauto.
  Qed.

  Lemma AXIOM_messages_get_delivered_implies :
    forall {eo : EventOrdering} (e : Event) m L d,
      AXIOM_messages_get_delivered eo lak_system
      -> disseminate_top_to_list e m L
      -> has_correct_trace_before e (loc e)
      -> In d L
      -> is_correct_in_near_future (node2name d) e
      ->
      exists e',
        loc e' = node2name d
        /\ trigger_op e' = Some (dis_data2msg m)
        /\ events_in_same_epoch e e'.
  Proof.
    introv deliv diss cor i near.
    unfold disseminate_top_to_list in diss; exrepnd.
    apply (deliv _ _ (node2name d)) in diss1; simpl; auto.
    { exrepnd; exists e'; dands; auto; eauto 3 with diss. }
    apply diss0; apply in_map_iff; eexists; dands; eauto; simpl; auto.
  Qed.

  Definition AXIOM_learns_on_time_implies_knows (eo : EventOrdering) N D E B :=
    forall (e : Event) n d,
      has_correct_trace_before e (node2name n)
      -> loc e = node2name n
      -> N n
      -> D d
      -> learns_on_time e d E B
      -> knows e d.


  (* ========== Memory ========= *)

  Class Memory :=
    MkMemory {
        mem_mem2list_info  : lak_memory -> list lak_info; (* this is (V s)  for SM *)
      }.

  Context { mm : Memory }.

  Definition AXIOM_values_increase_step (eo : EventOrdering) : Prop :=
    forall (e : Event) g s1 s2,
      state_sm_before_event (lak_system g) e = Some s1
      -> state_sm_on_event (lak_system g) e = Some s2
      -> subset (mem_mem2list_info s1) (mem_mem2list_info s2).

  (* generalization [values_increase_before] *)
  Lemma dis_values_increase_before :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      e1 ⊑ e2
      -> AXIOM_values_increase_step eo
      -> state_sm_before_event (lak_system g) e1 = Some s1
      -> state_sm_before_event (lak_system g) e2 = Some s2
      -> subset (mem_mem2list_info s1) (mem_mem2list_info s2).
  Proof.
    introv.
    revert s2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 ais h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
      pose proof (ais e1 g s1 s2) as xx.
      repeat (autodimp xx hyp).
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_before_event_some_between e e2 (lak_system g) s2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q; repeat (autodimp h hyp); eauto 4 with eo.

    eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
    pose proof (ais e g s' s2) as xx.
    repeat (autodimp xx hyp).
    eapply subset_trans; eauto.
  Qed.

  (* generalization [values_increase_on] *)
  Lemma dis_values_increase_on :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      e1 ⊑ e2
      -> AXIOM_values_increase_step eo
      -> state_sm_on_event (lak_system g) e1 = Some s1
      -> state_sm_on_event (lak_system g) e2 = Some s2
      -> subset (mem_mem2list_info s1) (mem_mem2list_info s2).
  Proof.
    introv.
    revert s2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 ais h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_before_event_if_on_event_direct_pred in h2; eauto.
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_on_event_some_between e e2 (lak_system g) s2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q; repeat (autodimp h hyp); eauto 4 with eo.

    eapply state_sm_before_event_if_on_event_direct_pred in h1;[|eauto].
    pose proof (ais e2 g s' s2) as xx.
    repeat (autodimp xx hyp).
    eapply subset_trans; eauto.
  Qed.

  (* generalization [values_increase_on_before] *)
  Lemma dis_values_increase_on_before :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      e1 ⊏ e2
      -> AXIOM_values_increase_step eo
      -> state_sm_on_event (lak_system g) e1 = Some s1
      -> state_sm_before_event (lak_system g) e2 = Some s2
      -> subset (mem_mem2list_info s1) (mem_mem2list_info s2).
  Proof.
    introv lte ais aseqst1 eqst2.
    applydup localHappenedBefore_implies_le_local_pred in lte.
    rewrite state_sm_before_event_as_state_sm_on_event_pred in eqst2; eauto 3 with eo;[].
    eapply dis_values_increase_on in lte0; eauto.
  Qed.

  Definition AXIOM_knows_implies_in : Prop :=
    forall d mem,
      lak_knows d mem
      -> In (lak_data2info d) (mem_mem2list_info mem).



  (* Q : can we define this one even more abstract (as knew predicate)? Memory is the one that makes issues. I did not use it inside IC1 *)
  (* generalization [IC1_safety_loc_before] part 1 *)
  Lemma diss_IC1_safety_loc_before_part1 :
    forall {eo : EventOrdering} (e1 e2 : Event) d g s1 s2,
      (e1) ⊏ (e2)
      -> AXIOM_values_increase_step eo
      -> loc e1 = node2name g
      -> loc e2 = node2name g
      -> state_sm_before_event (lak_system g) e1 = Some s1
      -> state_sm_before_event (lak_system g) e2 = Some s2
      -> In d (mem_mem2list_info s1)
      -> ~ In d (mem_mem2list_info s2)
      -> False.
  Proof.
    introv tri avi eqloc1 eqloc2 eqst1 eqst2 kni1 kn2.

    pose proof (dis_values_increase_before e1 e2 g s1 s2) as w.
    repeat (autodimp w hyp); eauto 3 with eo.
  Qed.


  (* ========== Authenticated Knowledge ========= *)

  Inductive lak_data_or_info :=
  | lak_is_data (d : lak_data)
  | lak_is_info (i : lak_info).

    (* FIX: do we need all parameters, like in Disseminate_old.v? *)
  (* Note: Here lak_data is usually [sm_signed_msg] or [DirectedMsg] *)
  (* In SM, we'll assume that lak_data is either a signed message or a value *)
  Class AuthKnowledge :=
    MkAuthKnowledge {

        (* ---- Destructors ---- *)
        dis_data2sign : lak_data -> Sign; (* this is [sm_signed_msg2sign] in SM *)

        (* ---- Constructors ---- *)
        dis_extend_info : lak_info -> Sign -> lak_data;
        dis_extend_data : lak_data -> Sign -> lak_data;
        (* -- Axioms regarding these constructors *)
        dis_extend_data_inj :
          forall d1 d2 s1 s2, dis_extend_data d1 s1 = dis_extend_data d2 s2 -> d1 = d2 /\ s1 = s2;
        dis_extend_info_inj :
          forall i1 i2 s1 s2, dis_extend_info i1 s1 = dis_extend_info i2 s2 -> i1 = i2 /\ s1 = s2;

        (* ---- Canonical form ---- *)
        dis_data2can  : lak_data -> list (lak_data_or_info * Sign);
        (* Q: Do we really need this one? So far we never used it.
        dis_can2data  : list (lak_data * Sign) -> lak_data;
        (* -- Axioms regarding canonical forms -- *)
        dis_can_prop_inv1      : forall c, dis_data2can (dis_can2data c) = c;
        dis_can_prop_inv2      : forall d, dis_can2data (dis_data2can d) = d; *)
        dis_can_prop_sign      :
          forall (d : lak_data) (s : Sign),
            dis_data2sign d = s <-> exists l d', dis_data2can d = snoc l (d',s);
        dis_can_prop_empty     :
          forall d,
            dis_data2can d <> [];
        dis_can_prop_snoc      :
          forall d l ds s,
            dis_data2can d = snoc l (ds,s)
            ->
            (exists i,
                d = dis_extend_info i s
                /\ l = []
            (*/\ ds = lak_is_info i*))
            \/ (exists d',
                   d = dis_extend_data d' s
                   /\ l = dis_data2can d'
               (*/\ ds = lak_is_data d'*));
        dis_can_prop_diff      :
          forall i d s s',
            dis_extend_info i s <> dis_extend_data d s';

(*        dis_ind :
          forall (P : lak_data -> Prop),
            (forall i s, P (dis_extend_info i s))
            -> (forall d s, P d -> P (dis_extend_data d s))
            -> forall (d : lak_data), P d;

        dis_rect :
          forall (P : lak_data -> Type),
            (forall i s, P (dis_extend_info i s))
            -> (forall d s, P d -> P (dis_extend_data d s))
            -> forall (d : lak_data), P d;*)

        (* ---- ---- *)
        (*dis_epoch_duration : PosDTime;*)
        dis_max_sign            : nat; (* for SM this is F+1 *)
        dis_max_sign_strict_pos : 1 <= dis_max_sign;

        (* abstracting away sm_signed_msg and extended msg *)
        (* Here sm_signed_msg is lak_data
                sm_value is lak_info *)

        (*dis_data2tokens   : lak_data -> Token; (* this is [sm_signed_msg2auth] in case of SM *)*)

        (* FIX: should we also add local_key_map to the extend_data? *)

        (* the system *)
        (*dis_msg2data      : DirectedMsg -> list lak_data;*)
        (*dis_msg2senders   : DirectedMsg -> list name;*)
        (*dis_msgs2senders  : DirectedMsgs -> list name;*)
        (*dis_sys           : MUSystem (fun _ => lak_memory);*)


        dis_data2data : lak_data -> node_type -> data; (* sm_msg_signed *)

      }.
  Context { ak : AuthKnowledge }.

  Lemma dis_ind :
    forall (P : lak_data -> Prop),
      (forall i s, P (dis_extend_info i s))
      -> (forall d s, P d -> P (dis_extend_data d s))
      -> forall (d : lak_data), P d.
  Proof.
    introv base ind; introv.
    remember (dis_data2can d) as l; symmetry in Heql.
    revert dependent d.
    induction l using list_ind_snoc; introv Heql; repnd.
    { apply dis_can_prop_empty in Heql; exrepnd; subst; tcsp. }
    { apply dis_can_prop_snoc in Heql; repndors; exrepnd; subst; tcsp. }
  Qed.

  (* this is [sm_signed_msg2signs] in case of SM *)
  Definition dis_data2signs (d : lak_data) : list Sign :=
    map snd (dis_data2can d).

  (* this is [sm_signed_msg2senders] in SM *)
  Definition dis_data2senders (d : lak_data) : list node_type :=
    map sign_name (dis_data2signs d).

  (* this is [sm_signed_msg2sender] in SM *)
  Definition dis_data2sender (d : lak_data) : node_type :=
    sign_name (dis_data2sign d).


  Definition AXIOM_all_messages_are_disseminated_on_time
             (eo : EventOrdering)
             (N  : name -> Prop) :=
    forall (e : Event) (d : lak_data),
      has_correct_trace_before e (loc e)
      -> N (loc e)
      -> disseminate e d
      -> exists (k : nat),
          k < dis_max_sign
          /\ length (dis_data2signs d) <= k
          /\ (time e <= nat2duration k)%dtime.



  (* generalize [extend_signed_msg_list] *)
  Fixpoint dis_extend_lak_data_list
           (d : lak_data)
           (l : list Sign) : lak_data :=
    match l with
    | [] => d
    | s :: l => dis_extend_lak_data_list (dis_extend_data d s) l
    end.

  Definition owns {eo : EventOrdering} (e : Event) (d : lak_data) (n : name) :=
      exists d' l,
        d = dis_extend_lak_data_list d' l
        /\ last_owns e d' n.


  (* generalization [send_value] *)
  (* Note: Our predicate [disseminate] actually does not state to whom we send the message *)
  (* Q : How can we use something like this? *)
  Definition AXIOM_learns_and_knows_but_not_knew_implies_disseminates  (eo : EventOrdering) : Prop :=
    forall (e : Event) (d : lak_data) a,
      learns e d
      -> knows e d
      -> ~ knew e d
(*      -> length (dis_data2signs d) < dis_max_sign *) (* FIX : IS this important? *)
      -> disseminate e (dis_extend_data d a).

  (* generalization [message_is_on_time] *)
  (* msg has no more than F+1 signatures and happened before alarm *)
  Definition dis_message_is_on_time (d : lak_data) (t : PosDTime) : bool :=
    let signs := dis_data2signs d in
    if dt_le_lt_dec t (nat2pdt (length signs) * epoch_duration)%dtime then
      if le_dec (length signs) dis_max_sign then true else false
    else false.


  (* generalization [message_is_on_time_implies_sm_signed_msg2signs] *)
  Lemma dis_message_is_on_time_implies_dis_data2signs :
    forall (d : lak_data) (t : PosDTime),
      dis_message_is_on_time d t = true
      -> length (dis_data2signs d) <= dis_max_sign.
  Proof.
    introv h; unfold dis_message_is_on_time in h.
    destruct (dt_le_lt_dec t); simpl in *; ginv; subst; tcsp;[].
    destruct (le_dec (length (dis_data2signs d)) dis_max_sign); simpl in *; ginv; subst; tcsp.
  Qed.
  Hint Resolve dis_message_is_on_time_implies_dis_data2signs : diss.

  (* generalization [message_is_on_time_implies_qle] *)
  Lemma dis_message_is_on_time_implies_qle :
    forall d t,
      dis_message_is_on_time d t = true
      -> (t <= nat2pdt (length (dis_data2signs d)) * epoch_duration)%dtime.
  Proof.
    introv h.
    unfold dis_message_is_on_time in h.
    destruct (dt_le_lt_dec t); simpl in *; ginv; subst; tcsp.
  Qed.
  Hint Resolve dis_message_is_on_time_implies_qle : diss.


  Lemma dis_extend_data_list_snoc :
    forall l d s,
      dis_extend_lak_data_list d (snoc l s)
      = dis_extend_data (dis_extend_lak_data_list d l) s.
  Proof.
    induction l; introv; simpl; auto.
  Qed.

  (* This axiom should be probable for whatever instances of [LearnAndKnow]
     and [AuthData] and [Disseminate], we're using *)
  Definition AXIOM_verify_dis_extend_data g ks d :=
    forall d' l,
      verify_authenticated_data g (lak_data2auth d) ks = true
      -> d = dis_extend_lak_data_list d' l
      -> verify_authenticated_data g (lak_data2auth d') ks = true.

  (* original *)
  Definition AXIOM_in_auth_data_trigger_extend (eo : EventOrdering) :=
    forall (e : Event) d a,
      auth_data_in_trigger (lak_data2auth (dis_extend_data d a)) e
      -> auth_data_in_trigger (lak_data2auth d) e.

  Definition AXIOM_knows_extend :=
    forall d a m,
      lak_knows d m
      -> lak_knows (dis_extend_data d a) m.

  (* generalization [verify_extend_signed_msg_list_implies] *)
  Lemma dis_verify_extend_lak_data_list_implies :
    forall (g   : name)
           (ks  : local_key_map)
           (l   : list Sign)
           (d   : lak_data),
      AXIOM_verify_dis_extend_data g ks (dis_extend_lak_data_list d l)
      -> verify_authenticated_data g (lak_data2auth (dis_extend_lak_data_list d l)) ks = true
      -> verify_authenticated_data g (lak_data2auth d) ks = true.
  Proof.
    introv verif h.
    apply (verif d l) in h; auto.
  Qed.

  Definition AXIOM_verify_extend_implies (eo : EventOrdering) :=
    forall (e : Event)
           (d : lak_data)
           (s : Sign),
      lak_verify e (dis_extend_data d s) = true
      -> lak_verify e d = true.

  Lemma lak_verify_extend_data_list_implies :
    forall {eo : EventOrdering}
           (e  : Event)
           (l  : list Sign)
           (d  : lak_data),
      AXIOM_verify_extend_implies eo
      -> lak_verify e (dis_extend_lak_data_list d l) = true
      -> lak_verify e d = true.
  Proof.
    induction l; introv ax verif; simpl in *; auto.
    apply IHl in verif; auto.
    apply ax in verif; auto.
  Qed.

  Lemma in_auth_data_trigger_extend_data_list (eo : EventOrdering) :
    forall (e : Event) l d,
      AXIOM_in_auth_data_trigger_extend eo
      -> auth_data_in_trigger (lak_data2auth (dis_extend_lak_data_list d l)) e
      -> auth_data_in_trigger (lak_data2auth d) e.
  Proof.
    induction l; introv ax h; simpl in *; auto.
    apply IHl in h; auto.
    apply ax in h; auto.
  Qed.


  Definition AXIOM_in_auth_data_trigger_extend_learns_list : Prop :=
    forall d l m,
      subset (lak_data2auth_list (dis_extend_lak_data_list d l)) (get_contained_authenticated_data m)
      -> subset (lak_data2auth_list d) (get_contained_authenticated_data m).


  Definition AXIOM_lak_data2auth_list_dis_extend_lak_data_list_not_nil : Prop :=
    forall l d,
      lak_data2auth_list (dis_extend_lak_data_list d l) <> [].


  Lemma learns_list_extend_data_list :
    forall {eo : EventOrdering} (e : Event) d l,
      AXIOM_in_auth_data_trigger_extend_learns_list
      -> AXIOM_verify_extend_implies eo
      -> AXIOM_lak_data2auth_list_dis_extend_lak_data_list_not_nil
      -> learns_list e (dis_extend_lak_data_list d l)
      -> learns_list e d.
  Proof.
    introv atrig verifex aldal lrn.
    unfold learns_list in *; exrepnd.
    exists n.
    apply lak_verify_extend_data_list_implies in lrn0; auto.
    dands; auto.

    unfold bind_op_list in *. simpl in *.
    unfold bind_op in *.
    remember (trigger_op e) as xx.
    destruct xx; ginv; simpl in *; subst; tcsp; [|].

    {
      eapply atrig; eauto.
    }

    {
      rewrite subset_nil_r in lrn2.
      rewrite subset_nil_r.
      eapply aldal in lrn2. tcsp.
    }
  Qed.


  (* this one is not going to be true fro SM2. Because of this statement I defined learns_list *)
  Lemma learns_extend_data_list :
    forall {eo : EventOrdering} (e : Event) d l,
      AXIOM_in_auth_data_trigger_extend eo
      -> AXIOM_verify_extend_implies eo
      -> learns e (dis_extend_lak_data_list d l)
      -> learns e d.
  Proof.
    introv atrig verifex lrn.
    unfold learns in *; exrepnd.
    exists n.
    apply lak_verify_extend_data_list_implies in lrn0; auto.
    dands; auto.
    rewrite in_bind_op_list_as_auth_data_in_trigger in *.
    apply in_auth_data_trigger_extend_data_list in lrn2; auto.
  Qed.

  Lemma knows_extend_data_list :
    forall l d m,
      AXIOM_knows_extend
      -> lak_knows d m
      -> lak_knows (dis_extend_lak_data_list d l) m.
  Proof.
    induction l; introv ax kn; simpl in *; auto.
  Qed.

  Lemma implies_knows_extend_data_list :
    forall {eo : EventOrdering} (e : Event) d l,
      AXIOM_knows_extend
      -> knows e d
      -> knows e (dis_extend_lak_data_list d l).
  Proof.
    introv ax kn.
    unfold knows in *; exrepnd.
    exists mem n; dands; auto.
    apply knows_extend_data_list; auto.
  Qed.

  (* part of generalization of [gen_sm_received_msg_was_sent] *)
  Lemma dis_message_is_disseminated_before_deadline5_new :
    forall {eo : EventOrdering}
           (e  : Event)
           (N  : name -> Prop)
           (d  : lak_data)
           (n  : node_type)
           (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> AXIOM_all_messages_are_disseminated_on_time eo N
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_knows_if_disseminate eo
      -> AXIOM_preserves_knows eo
      -> AXIOM_in_auth_data_trigger_extend eo
      -> AXIOM_verify_authenticated_data_lak_verify_implies eo
      -> AXIOM_verify_dis_extend_data (loc e) (keys e) d
      -> AXIOM_knows_extend
      -> has_correct_trace_before e (node2name n)
      -> has_correct_trace_bounded_lt_deadline eo (node2name n) deadline
      -> learns e d
      -> owns e d (node2name n)
      -> N(node2name n)
      -> exists (k : nat),
          k < dis_max_sign
          /\ forall (e' : Event),
            loc e' = node2name n
            -> has_correct_trace_bounded_lt e'
            -> (nat2duration k <= time e')%dtime
            -> (time e' <= deadline)%dtime
            -> knows e' d.
  Proof.
    introv sendbyz aamadbd aacsn alvivad akid apk aiadte avadlvi avded ake.
    introv corr corrlt lrn eqn nn.

    unfold learns in *; exrepnd; subst.
    unfold owns in eqn; exrepnd; subst.

    dup sendbyz as sendbyz'.

    apply implies_authenticated_messages_were_sent_non_byz_usys in sendbyz.
    pose proof (sendbyz e (lak_data2auth d') (node2name n)) as w.
    repeat (autodimp w hyp); eauto 2 with eo;[ | | ].
    { eapply in_auth_data_trigger_extend_data_list; eauto;[].
      unfold auth_data_in_trigger.
      destruct (trigger_op e); simpl in *; ginv; subst; eauto. }
    { eapply alvivad in lrn0;[].
      eapply avded; eauto. }
    simpl in w.
    exrepnd; subst.
    pose proof (aacsn d' m) as xx.
    repeat (autodimp xx hyp). exrepnd.
    autodimp w4 hyp.

    pose proof (aamadbd e' d') as rr.
    repeat (autodimp rr hyp); eauto 3 with eo; try congruence;[| |].
    { rewrite w1; auto; eauto 3 with eo. }
    { eexists; dands; eauto. }
    exrepnd.

    exists k; dands; auto.
    introv eqloc cortr tm1 tm2.

    pose proof (akid e' d' n) as w.
    repeat (autodimp w hyp).
    { eexists; dands; eauto. }

    assert (e' ⊑ e'0) as lee.
    { apply le_time_implies_happened_before; try congruence.
      eapply dt_le_trans;[eauto|]; auto. }

    eapply apk in w;[| |eauto]; eauto 3 with eo;[|].
    { apply implies_knows_extend_data_list; auto. }

    unfold has_correct_trace_bounded_lt_deadline in corrlt; exrepnd.

    assert (e'0 ⊏ e0) as lee'; eauto 3 with eo;[].
    { apply lt_time_implies_happened_before; try congruence.
      eapply dt_le_lt_trans;[eauto|]; auto. }
  Qed.

  Definition deadline_preserves_extend (deadline : lak_data -> dt_T) :=
    forall d a,
      (deadline d <= deadline (dis_extend_data d a))%dtime.

  Lemma deadline_preserves_extend_data_list :
    forall deadline l d,
      deadline_preserves_extend deadline
      -> (deadline d <= deadline (dis_extend_lak_data_list d l))%dtime.
  Proof.
    induction l; introv h; auto; simpl; eauto 3 with dtime; try reflexivity.
    eapply dt_le_trans;[|apply IHl]; auto.
  Qed.

  (* part of generalization of [gen_sm_received_msg_was_sent] *)
  (* In thesis this lemma is called: disseminated_before_deadline *)
  Lemma dis_message_is_disseminated_before_deadline5 :
    forall {eo       : EventOrdering}
           (e1 e2    : Event)
           (N        : name -> Prop)
           (d        : lak_data)
           (n        : node_type)
           (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> AXIOM_all_messages_are_disseminated_before_deadline eo N deadline
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_knows_if_disseminate eo
      -> AXIOM_preserves_knows eo
      -> AXIOM_in_auth_data_trigger_extend eo
      -> AXIOM_verify_extend_implies eo
      -> AXIOM_knows_extend
      -> has_correct_trace_before e1 (loc e2)
      -> has_correct_trace_bounded_lt e2
      -> learns e1 d
      -> loc e2 = node2name n
      -> owns e1 d (loc e2)
      -> N(loc e2)
      -> (deadline < time e2)%dtime
      -> knew e2 d.
  Proof.
    introv sendbyz before cont verif kid pres atrig verifex knex;
      introv cor1 cor2 lrn eqn own nn ltdt.
    rewrite eqn in *.
    unfold owns in *; exrepnd; subst.
    apply learns_extend_data_list in lrn; auto.

    apply (dis_message_is_disseminated_before_deadline3 e1 N d' n deadline) in lrn; auto.
    exrepnd.

    assert (time e' < time e2)%dtime as ltt by (eapply dt_le_lt_trans;eauto).

    apply lt_time_implies_happened_before in ltt; auto; try congruence;[].
    eapply knows_implies_knew; eauto.
    apply implies_knows_extend_data_list; auto.
  Qed.

  (* part of generalization of [gen_sm_received_msg_was_sent] *)
  Lemma dis_message_is_disseminated_before_deadline5_learns_list :
    forall {eo       : EventOrdering}
           (e1 e2    : Event)
           (N        : name -> Prop)
           (d        : lak_data)
           (n        : node_type)
           (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> AXIOM_all_messages_are_disseminated_before_deadline eo N deadline
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_knows_if_disseminate eo
      -> AXIOM_preserves_knows eo
      -> AXIOM_verify_extend_implies eo
      -> AXIOM_knows_extend
      -> AXIOM_in_auth_data_trigger_extend_learns_list
      -> AXIOM_lak_data2auth_list_dis_extend_lak_data_list_not_nil
      -> AXIOM_lak_data2auth_subset_lak_data2auth_list
      -> AXIOM_lak_verify_implies_lak_data2auth_list_not_nil eo
      -> has_correct_trace_before e1 (loc e2)
      -> has_correct_trace_bounded_lt e2
      -> learns_list e1 d
      -> loc e2 = node2name n
      -> owns e1 d (loc e2)
      -> N(loc e2)
      -> (deadline < time e2)%dtime
      -> knew e2 d.
  Proof.
    introv sendbyz before cont verif kid pres verifex knex atrig aldal;
      introv aldasldal alvildau cor1 cor2 lrn eqn own nn ltdt.
    rewrite eqn in *.
    unfold owns in *. exrepnd; subst.
    apply learns_list_extend_data_list in lrn; auto; [].

    apply (dis_message_is_disseminated_before_deadline3_learns_list e1 N d' n deadline) in lrn; auto; [].

    exrepnd.

    assert (time e' < time e2)%dtime as ltt by (eapply dt_le_lt_trans;eauto).

    apply lt_time_implies_happened_before in ltt; auto; try congruence;[].

    eapply knows_implies_knew; eauto.
    apply implies_knows_extend_data_list; auto.
  Qed.


  Definition lak_data2lak_datas (d : lak_data) : list lak_data :=
    mapOption
      (fun p =>
         match fst p with
         | lak_is_data d => Some d
         | lak_is_info _ => None
           end)
      (dis_data2can d).

  Definition AXIOM_verify_authenticated_datas_iff_lak_verify
             (eo  : EventOrdering) :=
    forall (e : Event)
           (d : lak_data),
      (forall d',
          In d' (lak_data2lak_datas d)
          -> verify_authenticated_data (loc e) (lak_data2auth d') (keys e) = true)
      <-> lak_verify e d = true.


  Lemma dis_data2can_dis_extend_info :
    forall i s,
    exists d,
      dis_data2can (dis_extend_info i s)
      = [(d, s)].
  Proof.
    introv.
    pose proof (snoc_cases (dis_data2can (dis_extend_info i s))) as h; repndors; exrepnd; auto.

    { apply dis_can_prop_empty in h; tcsp. }

    rewrite h1.
    apply dis_can_prop_snoc in h1; repndors; exrepnd; subst; tcsp.
    { apply dis_extend_info_inj in h1; repnd; subst; tcsp; simpl; eauto. }
    apply dis_can_prop_diff in h1; tcsp.
  Qed.

  Lemma dis_data2sender_dis_extend_info :
    forall i s, dis_data2sender (dis_extend_info i s) = sign_name s.
  Proof.
    introv.
    unfold dis_data2sender.
    remember (dis_data2sign (dis_extend_info i s)) as h; symmetry in Heqh.
    apply dis_can_prop_sign in Heqh; exrepnd.
    pose proof (dis_data2can_dis_extend_info i s) as q; exrepnd.
    rewrite q0 in Heqh1; simpl in *.
    destruct l; simpl in *; repnd; ginv.
    inversion Heqh1; subst.
    match goal with [ H : [] = snoc _ _ |- _ ] => rename H into bad end.
    symmetry in bad; apply snoc_implies_empty in bad; tcsp.
  Qed.
  Hint Rewrite dis_data2sender_dis_extend_info : diss.

  Lemma dis_data2senders_dis_extend_info :
    forall i s, dis_data2senders (dis_extend_info i s) = [sign_name s].
  Proof.
    introv.
    unfold dis_data2senders, dis_data2signs.
    pose proof (dis_data2can_dis_extend_info i s) as q; exrepnd.
    rewrite q0; simpl; auto.
  Qed.
  Hint Rewrite dis_data2senders_dis_extend_info : diss.

  Lemma dis_data2can_dis_data2can :
    forall d s,
    exists d',
      dis_data2can (dis_extend_data d s)
      = snoc (dis_data2can d) (d', s).
  Proof.
    introv.
    pose proof (snoc_cases (dis_data2can (dis_extend_data d s))) as h; repndors; exrepnd; auto.

    { apply dis_can_prop_empty in h; exrepnd; tcsp. }

    rewrite h1.
    apply dis_can_prop_snoc in h1; repndors; exrepnd; subst.

    { symmetry in h1.
      apply dis_can_prop_diff in h1; tcsp. }

    apply dis_extend_data_inj in h1; repnd; subst.
    eexists; eauto.
  Qed.

  Lemma dis_data2senders_dis_extend_data :
    forall d s,
      dis_data2senders (dis_extend_data d s)
      = snoc (dis_data2senders d) (sign_name s).
  Proof.
    introv.
    unfold dis_data2senders, dis_data2signs.
    pose proof (dis_data2can_dis_data2can d s) as h; exrepnd.
    rewrite h0.
    repeat (rewrite map_snoc); simpl; auto.
  Qed.
  Hint Rewrite dis_data2senders_dis_extend_data : diss.

  Lemma dis_data2sender_dis_extend_data :
    forall d s,
      dis_data2sender (dis_extend_data d s) = sign_name s.
  Proof.
    introv.
    unfold dis_data2sender.
    pose proof (snoc_cases (dis_data2can (dis_extend_data d s))) as h; repndors; exrepnd; auto.

    { apply dis_can_prop_empty in h; exrepnd; tcsp. }

    applydup dis_can_prop_snoc in h1; repndors; exrepnd; subst.

    { symmetry in h0.
      apply dis_can_prop_diff in h0; tcsp. }

    apply dis_extend_data_inj in h0; repnd; subst.
    assert (dis_data2sign (dis_extend_data d' a) = a) as q.
    { apply dis_can_prop_sign; eexists; eexists; eauto. }
    rewrite q; simpl; auto.
  Qed.
  Hint Rewrite dis_data2sender_dis_extend_data : diss.

  (* generalization of [in_sm_signed_msg2senders_implies] *)
  Lemma dis_in_lak_data2senders_implies :
    forall (g   : node_type)
           (d   : lak_data),
      In g (dis_data2senders d)
      ->
      exists d' l,
        dis_data2sender d' =  g
        /\ d = dis_extend_lak_data_list d' l.
  Proof.
    introv i.
    induction d using dis_ind; simpl in *; autorewrite with diss in *; simpl in *;
      repndors; subst; tcsp.

    {
      exists (dis_extend_info i0 s) ([] : list Sign); simpl; dands;
        autorewrite with diss; auto.
    }

    apply in_snoc in i.
    repndors; subst; tcsp.

    { autodimp IHd hyp; exrepnd; subst.
      exists d' (snoc l s); dands; auto.
      rewrite dis_extend_data_list_snoc; auto. }

    exists (dis_extend_data d s) ([] : list Sign); simpl; dands; auto.
    autorewrite with diss; auto.
  Qed.

  (* generalization [length_sm_signed_msg2signs_eq_length_sm_signed_msg2senders] *)
  Lemma dis_length_lak_data2signs_eq_length_lak_data2senders :
    forall d,
      length (dis_data2signs d)
      = length (dis_data2senders d).
  Proof.
    introv.
    unfold dis_data2signs.
    unfold dis_data2senders.
    unfold dis_data2signs. simpl in *.
    induction (dis_data2can); simpl; tcsp; autorewrite with list; allrw; auto.
  Qed.
  Hint Resolve dis_length_lak_data2signs_eq_length_lak_data2senders : dtime.


  Definition AXIOM_data_auth_eq : Prop :=
    forall (d  : lak_data)  (g  : node_type),
      data_auth (node2name g) (lak_data2auth d) = Some (node2name (dis_data2sender d)).

  (* first part of the case when:
      [m] is signed by strictly less than [F+1] generals *)
  Lemma exists_one_correct_implies :
    forall {eo : EventOrdering}
           (C  : list Event)
           (e  : Event)
           (d  : lak_data)
           (n  : node_type)
           (k  : nat),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> AXIOM_exists_at_most_f_faulty C k (* need *)
      -> AXIOM_verify_extend_implies eo
      -> AXIOM_in_auth_data_trigger_extend eo
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_data_auth_eq
      -> AXIOM_all_containers_satisfy_constraint eo
      -> loc e = node2name n
      -> in_event_cut e C
      -> learns e d
      -> k < length (dis_data2senders d)
      -> no_repeats (dis_data2senders d)
      -> exists e' d' l,
          In (dis_data2sender d') (dis_data2senders d)
          /\ cut_has_correct_trace_before C (node2name (dis_data2sender d'))
          /\ loc e' = node2name (dis_data2sender d')
          /\ d = dis_extend_lak_data_list d' l
          /\ e' ≺ e
          /\ disseminate e' d'.
  Proof.
    introv sendbyz atmost verif intrig vauth dauth cont;
      introv eqloc incut lrn len norep.

    unfold learns in *; exrepnd.

    pose proof (there_is_one_correct_before eo (dis_data2senders d) C k) as cor.
    repeat (autodimp cor hyp); try omega.

    exrepnd; simpl in *.

    applydup dis_in_lak_data2senders_implies in cor1 as z. exrepnd; subst.
    rename_hyp_with lak_verify verf.
    dup verf as verf'.

    assert (lak_verify e d' = true) as temp.
    { eapply lak_verify_extend_data_list_implies; eauto. }

    apply implies_authenticated_messages_were_sent_non_byz_usys in sendbyz.
    pose proof (sendbyz e (lak_data2auth d') (node2name (dis_data2sender d'))) as w.
    repeat (autodimp w hyp); eauto 3 with eo;
      try (complete (eapply in_auth_data_trigger_extend_data_list; eauto;
                     unfold auth_data_in_trigger; destruct (trigger_op e); simpl in *; ginv; subst; eauto ));
      try (complete (pose proof (alvivad e' d') as ttt; autodimp ttt hyp));
      try (complete (rewrite eqloc in *;  pose proof (dauth d' n) as ff; eauto));[].
    exrepnd.

    pose proof (cont d' m) as cont.
    autodimp cont hyp; repnd.
    autodimp w4 hyp.

    exists e' d' l; dands; auto.
    eexists; dands; eauto.
  Qed.

  Lemma correct_in_list_implies :
    forall {eo : EventOrdering}
           (e  : Event)
           (d  : lak_data)
           (n  : node_type)
           (correct : node_type),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> AXIOM_verify_extend_implies eo
      -> AXIOM_in_auth_data_trigger_extend_learns_list
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_data_auth_eq
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_data2auth_list_dis_extend_lak_data_list_not_nil
      -> AXIOM_lak_data2auth_subset_lak_data2auth_list
      -> loc e = node2name n
      -> has_correct_trace_before e (node2name correct)
      -> learns_list e d
      -> no_repeats (dis_data2senders d)
      -> In correct (dis_data2senders d)
      -> exists e' d' l,
          In correct (dis_data2senders d)
          /\ dis_data2sender d' = correct
          /\ loc e' = node2name correct
          /\ d = dis_extend_lak_data_list d' l
          /\ e' ≺ e
          /\ disseminate e' d'.
  Proof.
    introv sendbyz verif intrig vauth dauth cont;
      introv aldnn aldasldal eqloc incut lrn norep cor1.

    unfold learns_list in *; exrepnd.

    applydup dis_in_lak_data2senders_implies in cor1 as z. exrepnd; subst.

    rename_hyp_with lak_verify verf.
    dup verf as verf'.

    assert (lak_verify e d' = true) as temp.
    { eapply lak_verify_extend_data_list_implies; eauto. }

    apply implies_authenticated_messages_were_sent_non_byz_usys in sendbyz.
    pose proof (sendbyz e (lak_data2auth d') (node2name (dis_data2sender d'))) as w.
    repeat (autodimp w hyp); eauto 3 with eo;
      try (complete (rewrite eqloc in *;  pose proof (dauth d' n) as ff; eauto));[|].

    {
      unfold auth_data_in_trigger in *.
      remember (trigger_op) as tt.
      destruct tt; ginv; simpl in *; subst; tcsp;
        try (complete (rewrite subset_nil_r in lrn2; pose proof (aldnn l d') as tt; tcsp));[].

      apply subset_sing_left_as_in.

      pose proof (intrig d' l m) as ll.
      autodimp ll hyp; [].

      pose proof (aldasldal d') as kk.


      pose proof (subset_trans [lak_data2auth d']
                                 (lak_data2auth_list d')
                                 (get_contained_authenticated_data m)) as ss.
      apply ss; eauto.
    }

    {
      exrepnd.

      pose proof (cont d' m) as cont.
      autodimp cont hyp; repnd.
      autodimp w4 hyp.

      exists e' d' l; dands; auto.
      eexists; dands; eauto.
    }
  Qed.


  (* first part of the case when:
      [m] is signed by strictly less than [F+1] generals *)
  Lemma exists_one_correct_implies_learns_list :
    forall {eo : EventOrdering}
           (C  : list Event)
           (e  : Event)
           (d  : lak_data)
           (n  : node_type)
           (k  : nat),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo lak_system
      -> AXIOM_exists_at_most_f_faulty C k (* need *)
      -> AXIOM_verify_extend_implies eo
      -> AXIOM_in_auth_data_trigger_extend_learns_list
      -> AXIOM_lak_verify_implies_verify_authenticated_data eo
      -> AXIOM_data_auth_eq
      -> AXIOM_all_containers_satisfy_constraint eo
      -> AXIOM_lak_data2auth_list_dis_extend_lak_data_list_not_nil
      -> AXIOM_lak_data2auth_subset_lak_data2auth_list
      -> loc e = node2name n
      -> in_event_cut e C
      -> learns_list e d
      -> k < length (dis_data2senders d)
      -> no_repeats (dis_data2senders d)
      -> exists e' d' l,
          In (dis_data2sender d') (dis_data2senders d)
          /\ cut_has_correct_trace_before C (node2name (dis_data2sender d'))
          /\ loc e' = node2name (dis_data2sender d')
          /\ d = dis_extend_lak_data_list d' l
          /\ e' ≺ e
          /\ disseminate e' d'.
  Proof.
    introv sendbyz atmost verif intrig vauth dauth cont;
      introv aldnn aldasldal eqloc incut lrn len norep.

    pose proof (there_is_one_correct_before eo (dis_data2senders d) C k) as cor.
    repeat (autodimp cor hyp); try omega;[].

    exrepnd; simpl in *.

    eapply correct_in_list_implies in cor1; eauto; eauto 3 with eo.

    exrepnd; subst.

    eexists; eexists; eexists; dands; eauto.
  Qed.


  (* generalization [extend_signed_msg_list_snoc] *)
  Lemma dis_extend_lak_data_list_snoc :
    forall l m a,
      dis_extend_lak_data_list m (snoc l a)
      = dis_extend_data (dis_extend_lak_data_list m l) a.
  Proof.
    induction l; introv; simpl; auto.
  Qed.

  (* generalization [sm_signed_msg2senders_extend_signed_msg_list] *)
  Lemma dis_data2senders_extend_lak_data_list :
    forall l m,
      dis_data2senders (dis_extend_lak_data_list m l)
      = dis_data2senders m ++ (map sign_name l).
  Proof.
    induction l using snoc_list_ind; introv; simpl in *; tcsp;
      autorewrite with list; auto.
    rewrite dis_extend_lak_data_list_snoc; simpl.
    rewrite map_snoc.
    rewrite app_snoc.
    rewrite dis_data2senders_dis_extend_data.
    rewrite IHl; autorewrite with list; auto.
  Qed.

  (* generalization of the [sm_signed_msg2sender_in_senders] *)
  Definition AXIOM_dis_data2sender_in_senders :  Prop :=
    forall d, In (dis_data2sender d) (dis_data2senders d).


  (* generalization [extend_signed_msg_list_eq_extend_signed_msg_implies_if_no_repeats] *)
  Lemma dis_extend_lak_data_list_eq_extend_lak_data_implies_if_no_repeats :
    forall l (d v : lak_data) a,
      AXIOM_dis_data2sender_in_senders
      -> ~ In (dis_data2sender d) (dis_data2senders v)
      -> dis_extend_lak_data_list d l = dis_extend_data v (MkSign (dis_data2sender d) a)
      -> l = [].
  Proof.
    introv addis verif eqm.

    match type of eqm with
    | ?a = ?b =>
      assert (dis_data2senders a = dis_data2senders b) as xx;
        try congruence;[]
    end.
    simpl in *.

    hide_hyp eqm.

    pose proof (snoc_cases l) as cs; repndors; tcsp;[].
    assert False; tcsp.
    exrepnd; subst; simpl in *.
    rewrite dis_extend_lak_data_list_snoc in *.
    rewrite dis_data2senders_dis_extend_data in xx.
    rewrite dis_data2senders_dis_extend_data in xx.
    apply snoc_inj in xx.
    repnd. simpl in *.

    rewrite <- xx0 in verif.

    rewrite dis_data2senders_extend_lak_data_list in verif.
    destruct verif; apply in_app_iff; left.
    apply addis.
  Qed.


  Definition sign_data m n ks :=
    dis_extend_data m (MkSign n (authenticate (dis_data2data m n) ks)).

  (* In thesis this lemma is called: AXIOM_same_epoch_implies_verify_extend *)
  Definition AXIOM_events_in_same_epoch_implies_verify_extend (eo : EventOrdering) :=
    forall (e e' : Event) (n n' : node_type) (m : lak_data),
      loc e <> loc e'
      -> loc e = node2name n
      -> loc e' = node2name n'
      -> has_correct_trace_before e (loc e)
      -> has_correct_trace_before e' (loc e')
      -> ~ In n (dis_data2senders m)
      -> ~ In n' (dis_data2senders m)
      -> events_in_same_epoch e e'
      -> lak_verify e m = true
      -> lak_verify e' (sign_data m n (keys e)) = true.

  Definition AXIOM_extend_data_raises_epoch E :=
    forall d s, E (dis_extend_data d s) = S (E d).

  Lemma implies_on_time_extend_signed_msg :
    forall {eo : EventOrdering} (e e' : Event) m n ks E B,
      AXIOM_extend_data_raises_epoch E
      -> events_in_same_epoch e e'
      -> E m < B
      -> on_time e m E B
      -> on_time e' (sign_data m n ks) E B.
  Proof.
    introv condE same letb ontime.
    unfold events_in_same_epoch in *.
    unfold on_time in *; repnd.
    unfold sign_data; simpl.
    unfold AXIOM_extend_data_raises_epoch in *.
    unfold dis_extend_data in *; simpl in *.
    rewrite condE.
    dands; try omega;[].
    unfold max_received in same.
    eapply dt_le_trans;[eauto|].
    eapply dt_le_trans;[apply dt_add_le_compat;[eauto|apply dt_le_refl] |].
    rewrite <- S_dt_T_mul; eauto 3 with dtime.
    apply dt_le_refl.
  Qed.

  Lemma messages_get_delivered_implies_learns_on_time :
    forall {eo : EventOrdering} (e : Event) n L d m E B,
      AXIOM_messages_get_delivered eo lak_system
      -> AXIOM_events_in_same_epoch_implies_verify_extend eo
      -> AXIOM_extend_data_raises_epoch E
      -> loc e = node2name n
      -> n <> d
      -> ~ In n (dis_data2senders m)
      -> ~ In d (dis_data2senders m)
      -> lak_verify e m = true
      -> disseminate_top_to_except e (sign_data m n (keys e)) L
      -> In d (nodes_not_in_list L)
      -> has_correct_trace_before e (loc e)
      -> is_correct_in_near_future (node2name d) e
      -> on_time e m E B
      -> E m < B
      -> exists e',
          loc e' = node2name d
          /\ events_in_same_epoch e e'
          /\ learns_on_time e' (sign_data m n (keys e)) E B.
  Proof.
    introv deliv sameve condE eqloc dn ni1 ni2 verif diss i; introv cor near ontime ltb.
    unfold disseminate_top_to_except, disseminate_top_to_list in diss; exrepnd.
    pose proof (deliv e (MkDMsg (dis_data2msg (sign_data m n (keys e))) dst ('0)) (node2name d)) as deliv; simpl in *.
    repeat (autodimp deliv hyp).
    { apply diss0; apply in_map_iff; eexists; dands; eauto. }
    exrepnd.
    exists e'; dands; auto; eauto 3 with diss.
    unfold learns_on_time.
    exists d; dands; auto.

    {
      simpl.
      eapply sameve; eauto 3 with diss.

      { allrw; intro xx; apply node2name_inj in xx; subst; tcsp. }

      { eapply events_in_same_epoch_implies_has_correct_trace_before;[|eauto 3 with diss].
        allrw; auto. }
    }

    { eapply implies_on_time_extend_signed_msg; eauto with diss. }
  Qed.

  Definition just_learned_on_time {eo : EventOrdering} e m E B :=
    learns_on_time e m E B
    /\ knows e m
    /\ didnt_know e m
    /\ E m < B.

  Lemma just_learned_on_time_implies_learns_on_time :
    forall {eo : EventOrdering} e m E B,
      just_learned_on_time e m E B
      -> learns_on_time e m E B.
  Proof.
    introv h; destruct h; tcsp.
  Qed.
  Hint Resolve just_learned_on_time_implies_learns_on_time : diss.

  Lemma just_learned_on_time_implies_knows :
    forall {eo : EventOrdering} e m E B,
      just_learned_on_time e m E B
      -> knows e m.
  Proof.
    introv h; destruct h; tcsp.
  Qed.
  Hint Resolve just_learned_on_time_implies_knows : diss.

  Lemma just_learned_on_time_implies_didnt_know :
    forall {eo : EventOrdering} e m E B,
      just_learned_on_time e m E B
      -> didnt_know e m.
  Proof.
    introv h; destruct h; tcsp.
  Qed.
  Hint Resolve just_learned_on_time_implies_didnt_know : diss.

  Lemma just_learned_on_time_implies_bound :
    forall {eo : EventOrdering} e m E B,
      just_learned_on_time e m E B
      -> E m < B.
  Proof.
    introv h; destruct h; tcsp.
  Qed.
  Hint Resolve just_learned_on_time_implies_bound : diss.

  (* In thesis this axiom is called: AXIOM_just_learned_on_time_implies_disseminate *)
  Definition AXIOM_learns_new_on_time_implies_disseminate (eo : EventOrdering) N E B :=
    forall (e : Event) g m,
      N g
      -> loc e = node2name g
      -> just_learned_on_time e m E B
      -> disseminate_top_to_except
           e
           (sign_data m g (keys e))
           (g :: dis_data2senders m).

  Lemma messages_get_delivered_implies_knows :
    forall {eo : EventOrdering} (e : Event) n L d m N D E B,
      AXIOM_messages_get_delivered eo lak_system
      -> AXIOM_events_in_same_epoch_implies_verify_extend eo
      -> AXIOM_learns_on_time_implies_knows eo N D E B
      -> AXIOM_extend_data_raises_epoch E
      -> loc e = node2name n
      -> n <> d
      -> ~ In n (dis_data2senders m)
      -> ~ In d (dis_data2senders m)
      -> lak_verify e m = true
      -> disseminate_top_to_except e (sign_data m n (keys e)) L
      -> In d (nodes_not_in_list L)
      -> has_correct_trace_before e (loc e)
      -> is_correct_in_near_future (node2name d) e
      -> on_time e m E B
      -> E m < B
      -> N d
      -> D (sign_data m n (keys e))
      -> exists e',
          loc e' = node2name d
          /\ events_in_same_epoch e e'
          /\ knows e' (sign_data m n (keys e)).
  Proof.
    introv deliv sameve lik condE eqloc dn ni1 ni2 verif diss;
      introv i cor near ontime ltb nn dd.
    eapply messages_get_delivered_implies_learns_on_time in ontime; eauto;[].
    exrepnd.
    eapply lik in ontime0; eauto.
    rewrite <- ontime1.
    eapply events_in_same_epoch_implies_has_correct_trace_before; eauto.
    allrw; auto.
  Qed.

  Lemma messages_get_delivered_implies_knew :
    forall {eo : EventOrdering} (e e' : Event) n L d m N D E B,
      AXIOM_preserves_knows eo
      -> AXIOM_messages_get_delivered eo lak_system
      -> AXIOM_events_in_same_epoch_implies_verify_extend eo
      -> AXIOM_learns_on_time_implies_knows eo N D E B
      -> AXIOM_extend_data_raises_epoch E
      -> loc e = node2name n
      -> loc e' = node2name d
      -> n <> d
      -> ~ In n (dis_data2senders m)
      -> ~ In d (dis_data2senders m)
      -> lak_verify e m = true
      -> disseminate_top_to_except e (sign_data m n (keys e)) L
      -> In d (nodes_not_in_list L)
      -> has_correct_trace_before e (loc e)
      -> is_correct_in_near_future (node2name d) e
      -> has_correct_trace_bounded_lt e'
      -> on_time e m E B
      -> E m < B
      -> N d
      -> D (sign_data m n (keys e))
      -> events_in_later_epoch e e'
      -> knew e' (sign_data m n (keys e)).
  Proof.
    introv pres deliv sameve lik condE eqloc eqloc' dn ni1 ni2;
      introv verif diss i cor near cor' ontime ltb nn dd;
      introv later.
    apply (messages_get_delivered_implies_knows e n L d m N D E B) in ontime; auto;[].
    exrepnd.

    eapply events_in_later_of_same_implies in later; eauto.

    pose proof (lt_time_implies_happened_before e'0 e') as lee.
    repeat (autodimp lee hyp); try congruence;[].

    apply (knows_implies_knew _ e'0 e') in ontime0; auto; eauto 3 with eo.
  Qed.

  (*
     - [N]: a node constraint
     - [D]: a data constraint
     - [E]: an epoch constraint
     - [B]: an epoch bound
   *)
  (* In thesis this lemma is called: learns_on_time_imp_other_knew *)
  Lemma learns_on_time_implies_other_knew :
    forall {eo : EventOrdering} (e e' : Event) n d m N D E B,
      AXIOM_preserves_knows eo
      -> AXIOM_messages_get_delivered eo lak_system
      -> AXIOM_events_in_same_epoch_implies_verify_extend eo
      -> AXIOM_learns_on_time_implies_knows eo N D E B
      -> AXIOM_learns_new_on_time_implies_disseminate eo N E B
      -> AXIOM_extend_data_raises_epoch E
      -> loc e = node2name n
      -> loc e' = node2name d
      -> n <> d
      -> ~ In n (dis_data2senders m)
      -> ~ In d (dis_data2senders m)
      -> lak_verify e m = true
      -> just_learned_on_time e m E B
      -> has_correct_trace_before e (loc e)
      -> is_correct_in_near_future (node2name d) e
      -> has_correct_trace_bounded_lt e'
      -> N n
      -> N d
      -> D (sign_data m n (keys e))
      -> events_in_later_epoch e e'
      -> knew e' (sign_data m n (keys e)).
  Proof.
    introv pres deliv sameve lik lrnn condE eqloc eqloc' dn;
      introv ni1 ni2 verif lrn cor near;
      introv ltb nn nd dd later.

    applydup (lrnn e n m) in lrn; auto.
    apply (messages_get_delivered_implies_knew e e' n (n :: dis_data2senders m) d m N D E B) in lrn0;
      auto; eauto 3 with diss.
    unfold nodes_not_in_list.
    apply in_diff; simpl; dands; auto.
    { apply nodes_prop. }
    intro xx; repndors; subst; tcsp.
  Qed.

End Disseminate.


Hint Resolve events_in_same_epoch_delay_implies : diss.
Hint Resolve dis_message_is_on_time_implies_dis_data2signs : diss.
Hint Resolve dis_message_is_on_time_implies_qle : diss.
Hint Resolve dis_length_lak_data2signs_eq_length_lak_data2senders : dtime.
Hint Resolve learns_on_time_implies_cond : diss.
Hint Resolve learns_on_time_implies_learns : diss.
Hint Resolve implies_events_in_later_epoch : diss.
Hint Resolve just_learned_on_time_implies_learns_on_time : diss.
Hint Resolve just_learned_on_time_implies_knows : diss.
Hint Resolve just_learned_on_time_implies_didnt_know : diss.
Hint Resolve just_learned_on_time_implies_bound : diss.
