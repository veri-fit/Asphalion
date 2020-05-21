(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2018 Luxembourg University

  This file is part of Velisarios.

  Velisarios is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Velisarios is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICU'LAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Velisarios.  If not, see <http://www.gnu.org/licenses/>.


  Authors: Vincent Rahli
           Ivana Vukotic

*)


Require Export Quorum.
Require Export EventOrderingLemmas.


Section CorrectTrace.

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


  Local Open Scope eo.


  (* All the events at [i] are correct *)
  Definition has_correct_trace (eo : EventOrdering) (i : name) :=
    forall e, loc e = i -> isCorrect e.

  Definition node_has_correct_trace (eo : EventOrdering) (i : node_type) :=
    has_correct_trace eo (node2name i).

  Definition have_correct_traces (eo : EventOrdering) (G : list name) :=
    forall good, In good G -> has_correct_trace eo good.

  Definition nodes_have_correct_traces (eo : EventOrdering) (G : list node_type) :=
    have_correct_traces eo (map node2name G).

  (* all the events at [loc e] before [e] are correct *)
  Definition has_correct_trace_bounded {eo : EventOrdering} (e : Event) :=
    forall e', e' ⊑ e -> isCorrect e'.

  Definition has_correct_trace_bounded_lt {eo : EventOrdering} (e : Event) :=
    forall e', e' ⊏ e -> isCorrect e'.

  Definition have_correct_traces_before
             {eo : EventOrdering}
             (G  : list name)
             (L  : list Event) :=
    forall good e1 e2,
      In good G
      -> In e2 L
      -> e1 ≼ e2
      -> loc e1 = good
      -> has_correct_trace_bounded e1.

  Definition nodes_have_correct_traces_before
             {eo : EventOrdering}
             (G  : list node_type)
             (L  : list Event) :=
    have_correct_traces_before (map node2name G) L.

  Lemma has_correct_trace_bounded_lt_implies_local_pred :
    forall {eo : EventOrdering} (e : Event),
      ~isFirst e
      -> has_correct_trace_bounded_lt e
      -> has_correct_trace_bounded (local_pred e).
  Proof.
    introv nf cor lte.
    apply cor; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_bounded_lt_implies_local_pred : eo.

  Lemma nodes_have_correct_traces_before_causal_le :
    forall (eo : EventOrdering) R (e e' : Event),
      e' ≼ e
      -> nodes_have_correct_traces_before R [e]
      -> nodes_have_correct_traces_before R [e'].
  Proof.
    introv lte ctraces i j w z; simpl in *; repndors; subst; tcsp.
    unfold nodes_have_correct_traces_before, have_correct_traces_before in ctraces.
    pose proof (ctraces (loc e1) e1 e) as q; simpl in q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_causal_le : eo.

  Lemma nodes_have_correct_traces_before_two_left :
    forall (eo : EventOrdering) R (e1 e2 : Event),
      nodes_have_correct_traces_before R [e1, e2]
      -> nodes_have_correct_traces_before R [e1].
  Proof.
    introv ctraces i j w z; simpl in *; repndors; subst; tcsp.
    eapply ctraces; eauto; simpl; tcsp.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_two_left : eo.

  Lemma nodes_have_correct_traces_before_two_right :
    forall (eo : EventOrdering) R (e1 e2 : Event),
      nodes_have_correct_traces_before R [e1, e2]
      -> nodes_have_correct_traces_before R [e2].
  Proof.
    introv ctraces i j w z; simpl in *; repndors; subst; tcsp.
    eapply ctraces; eauto; simpl; tcsp.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_two_right : eo.

  Lemma nodes_have_correct_traces_before_causal :
    forall (eo : EventOrdering) R (e e' : Event),
      e' ≺ e
      -> nodes_have_correct_traces_before R [e]
      -> nodes_have_correct_traces_before R [e'].
  Proof.
    introv lte ctraces i j w z; simpl in *; repndors; subst; tcsp.
    pose proof (ctraces (loc e1) e1 e) as q; simpl in q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_causal : eo.

  Lemma has_correct_trace_bounded_preserves_local_le :
    forall (eo : EventOrdering) e e',
      e' ⊑ e
      -> has_correct_trace_bounded e
      -> has_correct_trace_bounded e'.
  Proof.
    introv lee ctrace i.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_bounded_preserves_local_le : eo.

  Definition all_correct (eo : EventOrdering) := forall (e : Event), isCorrect e.

  Lemma isCorrect_implies_msg :
    forall (eo : EventOrdering)  (e : Event),
      isCorrect e -> exists m, msg_triggered_event m e.
  Proof.
    introv isc.
    unfold isCorrect in isc.
    unfold msg_triggered_event.
    destruct (trigger_op e); tcsp.
    eexists; eauto.
  Qed.

  Lemma has_correct_trace_bounded_implies_message :
    forall {eo : EventOrdering} (e e' : Event),
      has_correct_trace_bounded e
      -> e' ⊑ e
      -> exists m, msg_triggered_event m e'.
  Proof.
    introv cor lee.
    pose proof (cor e' lee) as cor.
    apply isCorrect_implies_msg; auto.
  Qed.

  Definition has_correct_trace_before {eo : EventOrdering} (e : Event) (good : name) :=
    forall e', e' ≼ e -> loc e' = good -> has_correct_trace_bounded e'.

  Definition node_has_correct_trace_before {eo : EventOrdering} (e : Event) (good : node_type) :=
    has_correct_trace_before e (node2name good).

  Definition authenticated_messages_were_sent_non_byz
             (eo : EventOrdering)
             (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs):=
    forall (e : Event) (a : AuthenticatedData) (good : name),
      auth_data_in_trigger a e
      -> has_correct_trace_before e good
      -> verify_authenticated_data (loc e) a (keys e) = true
      -> data_auth (loc e) (am_data a) = Some good
      ->
      exists e' m dst delay,
        e' ≺ e
        /\ am_auth a = authenticate (am_data a) (keys e')
        /\ In a (get_contained_authenticated_data m)
        /\ (is_protocol_message m = true -> In (MkDMsg m dst delay) (F eo e'))
        /\ loc e' = good.

  Lemma implies_authenticated_messages_were_sent_non_byz :
    forall (eo : EventOrdering) F,
      AXIOM_authenticated_messages_were_sent_or_byz F
      -> authenticated_messages_were_sent_non_byz eo F.
  Proof.
    introv auth i ctrace verif sender.
    pose proof (auth e a) as q.
    repeat (autodimp q hyp); exrepnd; eauto 3 with eo;[].
    repndors; exrepnd.

    - exists e' m dst delay; dands; auto.
      rewrite sender in *; ginv.

    - assert False; tcsp.
      rewrite sender in *; ginv.
      pose proof (ctrace e'') as q; repeat (autodimp q hyp); eauto 3 with eo.
(*      pose proof (q e'') as q; autodimp q hyp; eauto 3 with eo.
      apply correct_is_not_byzantine in q; tcsp.*)
  Qed.

  Definition AXIOM_exists_at_most_f_faulty {eo : EventOrdering} (L : list Event) (F : nat) :=
    exists (faulty : list node_type),
      length faulty <= F
      /\
      forall e1 e2 n,
        In e2 L
        -> e1 ≼ e2
        -> loc e1 = node2name n
        -> ~ In n faulty
        -> has_correct_trace_bounded e1.

  Lemma exists_at_most_f_faulty_two_left :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      AXIOM_exists_at_most_f_faulty [e1, e2] F
      -> AXIOM_exists_at_most_f_faulty [e1] F.
  Proof.
    introv atmost; unfold AXIOM_exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto; simpl in *.
    introv xx; repndors; subst; tcsp.
    apply atmost0; auto.
  Qed.
  Hint Resolve exists_at_most_f_faulty_two_left : eo.

  Lemma exists_at_most_f_faulty_two_right :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      AXIOM_exists_at_most_f_faulty [e1, e2] F
      -> AXIOM_exists_at_most_f_faulty [e2] F.
  Proof.
    introv atmost; unfold AXIOM_exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto; simpl in *.
    introv xx; repndors; subst; tcsp.
    apply atmost0; auto.
  Qed.
  Hint Resolve exists_at_most_f_faulty_two_right : eo.

  Lemma implies_atmost_f_faulty_two_causal_le :
    forall (eo : EventOrdering) (e1 e2 e1' e2' : Event) F,
      e1' ≼ e1
      -> e2' ≼ e2
      -> AXIOM_exists_at_most_f_faulty [e1,e2] F
      -> AXIOM_exists_at_most_f_faulty [e1',e2'] F.
  Proof.
    introv lee1 lee2 atmost; unfold AXIOM_exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z eqn u; repndors; tcsp; subst;[|].
    - pose proof (atmost0 e0 e1 n) as q; repeat (autodimp q hyp); eauto 3 with eo.
    - pose proof (atmost0 e0 e2 n) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_two_causal_le : eo.

  Lemma implies_atmost_f_faulty_two_sym :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      AXIOM_exists_at_most_f_faulty [e1,e2] F
      -> AXIOM_exists_at_most_f_faulty [e2,e1] F.
  Proof.
    introv atmost; unfold AXIOM_exists_at_most_f_faulty, AXIOM_exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z eqn u; repndors; tcsp; subst;
      pose proof (atmost0 e0 e3 n) as q; repeat (autodimp q hyp);
        eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_two_sym : eo.

  Lemma exists_at_most_f_faulty_preserves_causal :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      e1 ≺ e2
      -> AXIOM_exists_at_most_f_faulty [e2] F
      -> AXIOM_exists_at_most_f_faulty [e1] F.
  Proof.
    introv lte atmost.
    unfold AXIOM_exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto; simpl in *.
    introv w z u; repndors; subst; tcsp.
    apply (atmost0 e0 e2); auto; eauto 3 with eo.
  Qed.
  Hint Resolve exists_at_most_f_faulty_preserves_causal : eo.

  Lemma exists_at_most_f_faulty_preserves_causal_le :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
      e1 ≼ e2
      -> AXIOM_exists_at_most_f_faulty [e2] F
      -> AXIOM_exists_at_most_f_faulty [e1] F.
  Proof.
    introv lte atmost.
    unfold AXIOM_exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto; simpl in *.
    introv w z u; repndors; subst; tcsp.
    apply (atmost0 e0 e2); auto; eauto 3 with eo.
  Qed.
  Hint Resolve exists_at_most_f_faulty_preserves_causal_le : eo.

  Lemma exists_at_most_f_faulty_twice :
    forall (eo : EventOrdering) (e : Event) F,
      AXIOM_exists_at_most_f_faulty [e] F
      -> AXIOM_exists_at_most_f_faulty [e, e] F.
  Proof.
    introv atmost.
    unfold AXIOM_exists_at_most_f_faulty in *; exrepnd; exists faulty; dands; auto.
    introv w z u; simpl in *; repndors; subst; tcsp; eapply atmost0; eauto.
  Qed.
  Hint Resolve exists_at_most_f_faulty_twice : eo.

  Lemma implies_atmost_f_faulty_local_pred :
    forall (eo : EventOrdering) (e : Event) F,
      AXIOM_exists_at_most_f_faulty [e] F
      -> AXIOM_exists_at_most_f_faulty [local_pred e] F.
  Proof.
    introv atmost; unfold AXIOM_exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z eqn u; repndors; tcsp.
    rewrite <- w in z.
    pose proof (atmost0 e1 e n) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_local_pred : eo.

  Lemma implies_atmost_f_faulty_causal :
    forall (eo : EventOrdering) (e e' : Event) F,
      e' ≺ e
      -> AXIOM_exists_at_most_f_faulty [e] F
      -> AXIOM_exists_at_most_f_faulty [e'] F.
  Proof.
    introv lte atmost; unfold AXIOM_exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z eqn u; repndors; tcsp.
    rewrite <- w in z.
    pose proof (atmost0 e1 e n) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_causal : eo.

  Lemma implies_atmost_f_faulty_causal_le :
    forall (eo : EventOrdering) (e e' : Event) F,
      e' ≼ e
      -> AXIOM_exists_at_most_f_faulty [e] F
      -> AXIOM_exists_at_most_f_faulty [e'] F.
  Proof.
    introv lte atmost; unfold AXIOM_exists_at_most_f_faulty in *; exrepnd.
    exists faulty; dands; auto.
    simpl in *; introv w z eqn u; repndors; tcsp.
    rewrite <- w in z.
    pose proof (atmost0 e1 e n) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve implies_atmost_f_faulty_causal_le : eo.

  Definition in_event_cut {eo : EventOrdering} (e : Event) C :=
    exists e', e ⊏ e' /\ In e' C.

  Lemma in_event_cut_2_left :
    forall {eo : EventOrdering} (e e1 e2 : Event),
      e ⊏ e1
      -> in_event_cut e [e1, e2].
  Proof.
    introv lte.
    exists e1; simpl; tcsp.
  Qed.
  Hint Resolve in_event_cut_2_left : eo.

  Lemma in_event_cut_2_right :
    forall {eo : EventOrdering} (e e1 e2 : Event),
      e ⊏ e2
      -> in_event_cut e [e1, e2].
  Proof.
    introv lte.
    exists e2; simpl; tcsp.
  Qed.
  Hint Resolve in_event_cut_2_right : eo.

  Definition cut_has_correct_trace_before {eo : EventOrdering} (C : list Event) n :=
    forall e, In e C -> has_correct_trace_before e n.

  Lemma in_cut_has_correct_trace_before_implies :
    forall {eo : EventOrdering} (e : Event) C n,
      in_event_cut e C
      -> cut_has_correct_trace_before C n
      -> has_correct_trace_before e n.
  Proof.
    introv incut cor lte eqloc.
    unfold in_event_cut in incut; exrepnd.
    eapply cor; eauto; eauto 4 with eo.
  Qed.
  Hint Resolve in_cut_has_correct_trace_before_implies : eo.

  Lemma in_cut_has_correct_trace_before_implies_correct_node :
    forall {eo : EventOrdering} (e : Event) C n,
      in_event_cut e C
      -> cut_has_correct_trace_before C (node2name n)
      -> node_has_correct_trace_before e n.
  Proof.
    introv incut cor.
    eapply in_cut_has_correct_trace_before_implies; eauto.
  Qed.
  Hint Resolve in_cut_has_correct_trace_before_implies_correct_node : eo.

  Lemma there_is_one_correct_before :
    forall (eo : EventOrdering) (L : list node_type) (E : list Event) (F : nat),
      no_repeats L
      -> F + 1 <= length L
      -> AXIOM_exists_at_most_f_faulty E F
      -> exists (correct : node_type),
          In correct L
          /\ cut_has_correct_trace_before E (node2name correct).
  Proof.
    introv norep cond atmost.
    unfold AXIOM_exists_at_most_f_faulty in atmost.
    exrepnd.

    pose proof (member_of_larger_list2 node_deq L faulty) as q.
    repeat (autodimp q hyp); try omega.
    destruct q as [c q]; repnd.

    exists c; dands; auto.
    introv i j eqn k.
    eapply atmost0 in j; eauto.
  Qed.

  Lemma has_correct_trace_before_preserves_local_le :
    forall (eo : EventOrdering) e e' k,
      e' ⊑ e
      -> has_correct_trace_before e k
      -> has_correct_trace_before e' k.
  Proof.
    introv lee ctrace i j.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_before_preserves_local_le : eo.

  Lemma has_correct_trace_before_preserves_causal_le :
    forall (eo : EventOrdering) e e' k,
      e' ≼ e
      -> has_correct_trace_before e k
      -> has_correct_trace_before e' k.
  Proof.
    introv lee ctrace i j.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_before_preserves_causal_le : eo.

  Lemma some_trigger_implies_isCorrect :
    forall (eo : EventOrdering) (e : Event) x,
      msg_triggered_event x e
      -> isCorrect e.
  Proof.
    introv w; unfold isCorrect; allrw; auto.
  Qed.
  Hint Resolve some_trigger_implies_isCorrect : eo.

  Lemma has_correct_trace_before_local_pred_implies :
    forall (eo : EventOrdering) (e : Event) i,
      loc e = i
      -> isCorrect e
      -> has_correct_trace_before (local_pred e) i
      -> has_correct_trace_before e i.
  Proof.
    introv eqloc1 core cor lee1 eqloc2 lee2.
    assert (e' ⊑ e) as lee3 by (split; allrw; auto).
    assert (e'0 ⊑ e) as lee4 by (eauto 3 with eo).
    apply localHappenedBeforeLe_implies_or in lee4; repndors; subst; auto.
    pose proof (cor e'0) as q; repeat (autodimp q hyp); eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_before_local_pred_implies : eo.

  Lemma has_correct_trace_bounded_local_pred_implies :
    forall (eo : EventOrdering) (e : Event),
      isCorrect e
      -> has_correct_trace_bounded (local_pred e)
      -> has_correct_trace_bounded e.
  Proof.
    introv core cor lee1.
    apply localHappenedBeforeLe_implies_or in lee1; repndors; subst; auto.
  Qed.
  Hint Resolve has_correct_trace_bounded_local_pred_implies : eo.

  Lemma node_has_correct_trace_before_preserves_local_le :
    forall (eo : EventOrdering) e e' k,
      e' ⊑ e
      -> node_has_correct_trace_before e k
      -> node_has_correct_trace_before e' k.
  Proof.
    introv lee ctrace i j.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve node_has_correct_trace_before_preserves_local_le : eo.

  Lemma node_has_correct_trace_before_preserves_causal_le :
    forall (eo : EventOrdering) e e' k,
      e' ≼ e
      -> node_has_correct_trace_before e k
      -> node_has_correct_trace_before e' k.
  Proof.
    introv lee ctrace i j.
    apply ctrace; auto; eauto 3 with eo.
  Qed.
  Hint Resolve node_has_correct_trace_before_preserves_causal_le : eo.

  Lemma node_has_correct_trace_before_preserves_causal :
    forall {eo : EventOrdering} (e1 e2 : Event) i,
      e1 ≺ e2
      -> node_has_correct_trace_before e2 i
      -> node_has_correct_trace_before e1 i.
  Proof.
    introv caus h q w.
    eapply h; eauto 3 with eo.
  Qed.
  Hint Resolve node_has_correct_trace_before_preserves_causal : eo.

  Lemma select_good_guys_before :
    forall (eo : EventOrdering) (L : list node_type) (E : list Event) F,
      no_repeats L
      -> AXIOM_exists_at_most_f_faulty E F
      -> exists (G : list node_type),
          subset G L
          /\ length L - F <= length G
          /\ no_repeats G
          /\ forall e good,
              In e E
              -> In good G
              -> node_has_correct_trace_before e good.
  Proof.
    introv norep byz.
    unfold AXIOM_exists_at_most_f_faulty in byz.
    exrepnd.

    pose proof (members_of_larger_list node_deq L faulty) as q.
    repeat (autodimp q hyp); try omega;[].

    destruct q as [G q]; repnd.
    exists G.
    dands; auto; simpl in *; try omega;[].

    introv i j k eqn w.
    eapply byz0 in k; eauto.
  Qed.

  Lemma nodes_have_correct_traces_before_two_implies_causal_left :
    forall {eo : EventOrdering} (e1 e2 e : Event) a b,
      e ⊏ e1
      -> nodes_have_correct_traces_before [a, b] [e1, e2]
      -> has_correct_trace_before e (node2name b).
  Proof.
    introv h q w z.
    eapply (q (node2name b) e' e1); simpl; tcsp; eauto 4 with eo.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_two_implies_causal_left : eo.

  Lemma nodes_have_correct_traces_before_two_implies_causal_left_1 :
    forall {eo : EventOrdering} (e1 e2 e : Event) a b,
      e ⊏ e1
      -> nodes_have_correct_traces_before [a, b] [e1, e2]
      -> has_correct_trace_before e (node2name a).
  Proof.
    introv h q w z.
    eapply (q (node2name a) e' e1); simpl; tcsp; eauto 4 with eo.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_two_implies_causal_left_1 : eo.

  Lemma nodes_have_correct_traces_before_two_implies_causal_right :
    forall {eo : EventOrdering} (e1 e2 e : Event) a b,
      e ⊏ e2
      -> nodes_have_correct_traces_before [a, b] [e1, e2]
      -> has_correct_trace_before e (node2name b).
  Proof.
    introv h q w z.
    eapply (q (node2name b) e' e2); simpl; tcsp; eauto 4 with eo.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_two_implies_causal_right : eo.

  Lemma nodes_have_correct_traces_before_two_implies_causal_le_right :
    forall {eo : EventOrdering} (e1 e2 e : Event) a b,
      e ⊑ e2
      -> nodes_have_correct_traces_before [a, b] [e1, e2]
      -> has_correct_trace_before e (node2name b).
  Proof.
    introv h q w z.
    eapply (q (node2name b) e' e2); simpl; tcsp; eauto 4 with eo.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_two_implies_causal_le_right : eo.

  Lemma nodes_have_correct_traces_before_two_swap :
    forall {eo : EventOrdering} (e1 e2 : Event) a b,
      nodes_have_correct_traces_before [a, b] [e1, e2]
      -> nodes_have_correct_traces_before [b, a] [e2, e1].
  Proof.
    introv h i j.
    eapply h; simpl in *; tcsp.
  Qed.
  Hint Resolve nodes_have_correct_traces_before_two_swap : eo.

  Lemma has_correct_trace_bounded_implies_before :
    forall {eo : EventOrdering} (e : Event),
      has_correct_trace_bounded e
      -> has_correct_trace_before e (loc e).
  Proof.
    introv cor lte eqloc; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_bounded_implies_before : eo.

  Lemma isFirst_implies_has_correct_trace_bounded_lt :
    forall {eo : EventOrdering} (e : Event),
      isFirst e
      -> has_correct_trace_bounded_lt e.
  Proof.
    introv isf lte.
    apply no_local_predecessor_if_first in lte; tcsp.
  Qed.
  Hint Resolve isFirst_implies_has_correct_trace_bounded_lt : eo.

  Lemma has_correct_trace_bounded_local_pred_implies_lt :
    forall {eo : EventOrdering} (e : Event),
      ~isFirst e
      -> has_correct_trace_bounded (local_pred e)
      -> has_correct_trace_bounded_lt e.
  Proof.
    introv nf cor lte.
    apply cor; eauto 3 with eo.
    apply localHappenedBefore_implies_le_local_pred; auto.
  Qed.
  Hint Resolve has_correct_trace_bounded_local_pred_implies_lt : eo.

  Lemma implies_has_correct_trace_bounded_lt_local_pred :
    forall {eo : EventOrdering} (e : Event),
      has_correct_trace_bounded_lt e
      -> has_correct_trace_bounded_lt (local_pred e).
  Proof.
    introv cor lte.
    apply cor; eauto 3 with eo.
  Qed.
  Hint Resolve implies_has_correct_trace_bounded_lt_local_pred : eo.

  Lemma have_correct_traces_before_left_pair :
    forall {eo : EventOrdering} nodes (e1 e2 : Event),
      have_correct_traces_before nodes [e1, e2]
      -> have_correct_traces_before nodes [e1].
  Proof.
    introv h i j; apply h; simpl in *; tcsp.
  Qed.
  Hint Resolve have_correct_traces_before_left_pair : eo.

  Lemma have_correct_traces_before_right_pair :
    forall {eo : EventOrdering} nodes (e1 e2 : Event),
      have_correct_traces_before nodes [e1, e2]
      -> have_correct_traces_before nodes [e2].
  Proof.
    introv h i j; apply h; simpl in *; tcsp.
  Qed.
  Hint Resolve have_correct_traces_before_right_pair : eo.

  Lemma have_correct_traces_before_le_left_pair :
    forall {eo : EventOrdering} nodes (e e1 e2 : Event),
      e ≼ e1
      -> have_correct_traces_before nodes [e1, e2]
      -> have_correct_traces_before nodes [e].
  Proof.
    introv q h i j u v; simpl in *; repndors; subst; tcsp.
    eapply (h _ _ e1); eauto; simpl; tcsp; eauto 3 with eo.
  Qed.
  Hint Resolve have_correct_traces_before_le_left_pair : eo.

  Lemma have_correct_traces_before_le_right_pair :
    forall {eo : EventOrdering} nodes (e e1 e2 : Event),
      e ≼ e2
      -> have_correct_traces_before nodes [e1, e2]
      -> have_correct_traces_before nodes [e].
  Proof.
    introv q h i j u v; simpl in *; repndors; subst; tcsp.
    eapply (h _ _ e2); eauto; simpl; tcsp; eauto 3 with eo.
  Qed.
  Hint Resolve have_correct_traces_before_le_right_pair : eo.

  Lemma have_correct_traces_before_le_pair_left :
    forall {eo : EventOrdering} nodes (e e1 e2 : Event),
      e ≼ e1
      -> have_correct_traces_before nodes [e1, e2]
      -> have_correct_traces_before nodes [e, e2].
  Proof.
    introv q h i j u v; simpl in *; repndors; subst; tcsp.
    { eapply (h _ _ e1); eauto; simpl; tcsp; eauto 3 with eo. }
    { eapply (h _ _ e3); eauto; simpl; tcsp; eauto 3 with eo. }
  Qed.
  Hint Resolve have_correct_traces_before_le_pair_left : eo.

  Lemma have_correct_traces_before_le_pair_right :
    forall {eo : EventOrdering} nodes (e e1 e2 : Event),
      e ≼ e2
      -> have_correct_traces_before nodes [e1, e2]
      -> have_correct_traces_before nodes [e1, e].
  Proof.
    introv q h i j u v; simpl in *; repndors; subst; tcsp.
    { eapply (h _ _ e3); eauto; simpl; tcsp; eauto 3 with eo. }
    { eapply (h _ _ e2); eauto; simpl; tcsp; eauto 3 with eo. }
  Qed.
  Hint Resolve have_correct_traces_before_le_pair_right : eo.

  Lemma have_correct_traces_before_dup :
    forall {eo : EventOrdering} nodes (e : Event),
      have_correct_traces_before nodes [e]
      -> have_correct_traces_before nodes [e, e].
  Proof.
    introv q h i j; eapply q; eauto; simpl in *; tcsp.
  Qed.
  Hint Resolve have_correct_traces_before_dup : eo.

  Lemma have_correct_traces_before_pair_switch :
    forall {eo : EventOrdering} nodes (e1 e2 : Event),
      have_correct_traces_before nodes [e1, e2]
      -> have_correct_traces_before nodes [e2, e1].
  Proof.
    introv q h i j. eapply q; eauto; simpl in *; tcsp.
  Qed.
  Hint Resolve have_correct_traces_before_pair_switch : eo.

End CorrectTrace.


Hint Resolve exists_at_most_f_faulty_two_left : eo.
Hint Resolve exists_at_most_f_faulty_two_right : eo.
Hint Resolve implies_atmost_f_faulty_two_causal_le : eo.
Hint Resolve implies_atmost_f_faulty_two_sym : eo.
Hint Resolve exists_at_most_f_faulty_preserves_causal : eo.
Hint Resolve exists_at_most_f_faulty_preserves_causal_le : eo.
Hint Resolve exists_at_most_f_faulty_twice : eo.
Hint Resolve implies_atmost_f_faulty_local_pred : eo.
Hint Resolve implies_atmost_f_faulty_causal : eo.
Hint Resolve implies_atmost_f_faulty_causal_le : eo.
Hint Resolve implies_has_correct_trace_bounded_lt_local_pred : eo.

Hint Resolve nodes_have_correct_traces_before_causal_le : eo.
Hint Resolve nodes_have_correct_traces_before_two_left : eo.
Hint Resolve nodes_have_correct_traces_before_two_right : eo.
Hint Resolve nodes_have_correct_traces_before_causal : eo.

Hint Resolve has_correct_trace_before_preserves_local_le : eo.
Hint Resolve has_correct_trace_before_preserves_causal_le : eo.
Hint Resolve has_correct_trace_bounded_preserves_local_le : eo.
Hint Resolve some_trigger_implies_isCorrect : eo.
Hint Resolve has_correct_trace_before_local_pred_implies : eo.
Hint Resolve node_has_correct_trace_before_preserves_local_le : eo.
Hint Resolve node_has_correct_trace_before_preserves_causal_le : eo.
Hint Resolve node_has_correct_trace_before_preserves_causal : eo.

Hint Resolve nodes_have_correct_traces_before_two_implies_causal_left : eo.
Hint Resolve nodes_have_correct_traces_before_two_implies_causal_left_1 : eo.
Hint Resolve nodes_have_correct_traces_before_two_implies_causal_right : eo.
Hint Resolve nodes_have_correct_traces_before_two_implies_causal_le_right : eo.
Hint Resolve nodes_have_correct_traces_before_two_swap : eo.

Hint Resolve has_correct_trace_bounded_lt_implies_local_pred : eo.
Hint Resolve has_correct_trace_bounded_implies_before : eo.
Hint Resolve isFirst_implies_has_correct_trace_bounded_lt : eo.
Hint Resolve has_correct_trace_bounded_local_pred_implies_lt : eo.
Hint Resolve has_correct_trace_bounded_local_pred_implies : eo.
Hint Resolve in_cut_has_correct_trace_before_implies : eo.
Hint Resolve in_event_cut_2_left : eo.
Hint Resolve in_event_cut_2_right : eo.
Hint Resolve in_cut_has_correct_trace_before_implies_correct_node : eo.

Hint Resolve have_correct_traces_before_left_pair : eo.
Hint Resolve have_correct_traces_before_right_pair : eo.
Hint Resolve have_correct_traces_before_le_left_pair : eo.
Hint Resolve have_correct_traces_before_le_right_pair : eo.
Hint Resolve have_correct_traces_before_le_pair_left : eo.
Hint Resolve have_correct_traces_before_le_pair_right : eo.
Hint Resolve have_correct_traces_before_dup : eo.
Hint Resolve have_correct_traces_before_pair_switch : eo.
