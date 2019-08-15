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
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Velisarios.  If not, see <http://www.gnu.org/licenses/>.


  Authors: Vincent Rahli
           Ivana Vukotic

*)


Require Export Quorum.
Require Export CorrectTrace.
Require Export Process.


Section LearnAndKnow.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pm  : @Msg }.
  Context { qc  : @Quorum_context pn}.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pda : @DataAuth pd pn }.
  Context { cad : @ContainedAuthData pd pat pm }.
  Context { dtc : @DTimeContext }.


  Local Open Scope eo.
  Local Open Scope proc.


  Class LearnAndKnow (n : nat) :=
    MkLearnAndKnow {
        (* known raw data *)
        lak_data : Type;

        (* some distinguished information embedded in the data *)
        lak_info : Type;

        (* to compute the info from the data *)
        lak_data2info : lak_data -> lak_info;

        (* where we store data *)
        lak_memory : Type;

        (* explains what it means to know the data *)
        lak_knows : lak_data -> lak_memory -> Prop;

        (* explains what it means to know some info *)
        lak_knows_i : lak_info -> lak_memory -> Prop;

        (* connects the two knowledge operators *)
        lak_knows_i_if : forall d m, lak_knows d m -> lak_knows_i (lak_data2info d) m;

        (* "owner" of the data *)
        lak_data2owner : lak_data -> node_type;

        (* to verify the authenticity of the data *)
        lak_data2auth : lak_data -> AuthenticatedData;
        lak_verify : forall {eo : EventOrdering} (e : Event) (d : lak_data), bool;

        (* the system *)
        lak_output : Type;
        lak_system : node_type -> StateMachine lak_memory msg (list lak_output);
        lak_no_initial_memory_i : forall n i, ~ lak_knows_i i (sm_state (lak_system n));
      }.

  Context { p : nat }.
  Context { lak : LearnAndKnow p }.

  Definition lak_data2node (d : lak_data) : name :=
    node2name (lak_data2owner d).


  (* the default lak_knows_i function *)
  Definition lak_knows_i_trivial (i : lak_info) (m : lak_memory) : Prop :=
    exists (d : lak_data), lak_knows d m /\ i = lak_data2info d.

  Lemma knows_implies_knows_i :
    forall {eo : EventOrdering} (e : Event) (d : lak_data),
      knows e d -> knows_i e (lak_data2info d).
  Proof.
    introv k.
    unfold knows in *; exrepnd; exists mem n; dands; auto.
    apply lak_knows_i_if; auto.
  Qed.

  Lemma lak_no_initial_memory :
    forall n d, ~ lak_knows d (sm_state (lak_system n)).
  Proof.
    introv kn; apply lak_knows_i_if in kn.
    apply lak_no_initial_memory_i in kn; auto.
  Qed.

  Lemma knew_implies_knows :
    forall (eo : EventOrdering) (e : Event) (d : lak_data),
      knew e d
      -> knows (local_pred e) d.
  Proof.
    introv k.
    unfold knew in *; exrepnd.
    rewrite <- ite_first_state_sm_on_event_as_before in k1.
    unfold ite_first in k1; destruct (dec_isFirst e) as [de|de];
      [|exists mem n; autorewrite with eo; dands; auto];[].
    ginv.
    apply lak_no_initial_memory in k2; tcsp.
  Qed.

  Lemma knew_i_implies_knows_i :
    forall (eo : EventOrdering) (e : Event) (i : lak_info),
      knew_i e i
      -> knows_i (local_pred e) i.
  Proof.
    introv k.
    unfold knew_i in *; exrepnd.
    rewrite <- ite_first_state_sm_on_event_as_before in k1.
    unfold ite_first in k1; destruct (dec_isFirst e) as [de|de];
      [|exists mem n; autorewrite with eo; dands; auto];[].
    ginv.
    apply lak_no_initial_memory_i in k2; tcsp.
  Qed.

  Lemma knows_implies :
    forall {eo : EventOrdering} (e : Event) d,
      knows e d
      ->
      exists mem mem' n,
        loc e = node2name n
        /\ op_state (lak_system n) mem (trigger e) (time e) = Some mem'
        /\ lak_knows d mem'
        /\ state_sm_before_event (lak_system n) e = Some mem.
  Proof.
    introv kn.
    unfold knows in kn; exrepnd.
    rewrite state_sm_on_event_unroll2 in kn1.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv]
    end.

    exists l mem n; dands; auto.
  Qed.

  Lemma knows_implies_before_after :
    forall {eo : EventOrdering} (e : Event) d,
      knows e d
      ->
      exists mem mem' n,
        loc e = node2name n
        /\ op_state (lak_system n) mem (trigger e) (time e) = Some mem'
        /\ lak_knows d mem'
        /\ state_sm_before_event (lak_system n) e = Some mem
        /\ state_sm_on_event (lak_system n) e = Some mem'.
  Proof.
    introv kn.
    unfold knows in kn; exrepnd.
    dup kn1 as ston.
    rewrite state_sm_on_event_unroll2 in kn1.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv]
    end.

    exists l mem n; dands; auto.
  Qed.

  Lemma implies_knows :
    forall {eo : EventOrdering} (e : Event) d n mem,
      loc e = node2name n
      -> lak_knows d mem
      -> state_sm_on_event (lak_system n) e = Some mem
      -> knows e d.
  Proof.
    introv eqloc k eqst.
    eexists; eexists; dands; eauto.
  Qed.
  Hint Resolve implies_knows : eo.

  Lemma implies_knows_i :
    forall {eo : EventOrdering} (e : Event) i n mem,
      loc e = node2name n
      -> lak_knows_i i mem
      -> state_sm_on_event (lak_system n) e = Some mem
      -> knows_i e i.
  Proof.
    introv eqloc k eqst.
    eexists; eexists; dands; eauto.
  Qed.
  Hint Resolve implies_knows_i : eo.

  Lemma implies_knew_i :
    forall {eo : EventOrdering} (e : Event) i n mem,
      loc e = node2name n
      -> lak_knows_i i mem
      -> state_sm_before_event (lak_system n) e = Some mem
      -> knew_i e i.
  Proof.
    introv eqloc k eqst.
    eexists; eexists; dands; eauto.
  Qed.
  Hint Resolve implies_knew_i : eo.

  Lemma implies_not_knew_i :
    forall {eo : EventOrdering} (e : Event) i n mem,
      loc e = node2name n
      -> ~lak_knows_i i mem
      -> state_sm_before_event (lak_system n) e = Some mem
      -> ~knew_i e i.
  Proof.
    introv eqloc k eqst kn.
    unfold knew_i in kn; exrepnd.
    rewrite kn0 in *.
    apply node2name_inj in eqloc; subst.
    rewrite eqst in *; ginv.
  Qed.
  Hint Resolve implies_not_knew_i : eo.

  Lemma knows_implies_correct :
    forall {eo : EventOrdering} (e : Event) (d : lak_data),
      knows e d
      -> has_correct_trace_before e (loc e).
  Proof.
    introv kn.
    unfold knows in kn; exrepnd.
    eapply state_sm_on_event_some_implies_has_correct_trace_before;eauto.
  Qed.
  Hint Resolve knows_implies_correct : eo.

  Definition lak_know_dec :=
    forall (d : lak_data) (m : lak_memory),
      lak_knows d m \/ ~lak_knows d m.

  Definition lak_know_i_dec :=
    forall (d : lak_info) (m : lak_memory),
      lak_knows_i d m \/ ~lak_knows_i d m.

  Lemma knowledge_acquired :
    forall {eo : EventOrdering} (e : Event) (d : lak_data),
      lak_know_dec
      -> knows e d
      ->
      exists e',
        e' ⊑ e
        /\ knows e' d
        /\ ~ knew e' d.
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd_type.
    introv dec kn.
    dup kn as kn'.
    unfold knows in kn; exrepnd.
    rewrite state_sm_on_event_unroll2 in kn1.
    remember (state_sm_before_event (lak_system n) e) as s; symmetry in Heqs.
    destruct s; simpl in *; ginv.
    destruct (dec d l) as [dc|dc].

    {
      rewrite <- ite_first_state_sm_on_event_as_before in Heqs.
      remember (state_sm_on_event (lak_system n) (local_pred e)) as s'; symmetry in Heqs'.
      unfold ite_first in *.
      destruct (dec_isFirst e); ginv.

      { apply lak_no_initial_memory in dc; tcsp. }

      subst.
      pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo.
      pose proof (ind d) as ind; repeat (autodimp ind hyp).
      { exists l n; autorewrite with eo; dands; auto. }
      exrepnd.
      exists e'; dands; eauto 3 with eo.
    }

    {
      exists e; dands; eauto with eo.
      introv kn.
      unfold knew in kn; exrepnd.
      rewrite kn0 in *.
      apply node2name_inj in kn3; subst.
      rewrite Heqs in *; ginv.
    }
  Qed.

  Lemma information_acquired :
    forall {eo : EventOrdering} (e : Event) (d : lak_info),
      lak_know_i_dec
      -> knows_i e d
      ->
      exists e',
        e' ⊑ e
        /\ knows_i e' d
        /\ ~ knew_i e' d.
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd_type.
    introv dec kn.
    dup kn as kn'.
    unfold knows_i in kn; exrepnd.
    rewrite state_sm_on_event_unroll2 in kn1.
    remember (state_sm_before_event (lak_system n) e) as s; symmetry in Heqs.
    destruct s; simpl in *; ginv.
    destruct (dec d l) as [dc|dc].

    {
      rewrite <- ite_first_state_sm_on_event_as_before in Heqs.
      remember (state_sm_on_event (lak_system n) (local_pred e)) as s'; symmetry in Heqs'.
      unfold ite_first in *.
      destruct (dec_isFirst e); ginv.

      { apply lak_no_initial_memory_i in dc; tcsp. }

      subst.
      pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo.
      pose proof (ind d) as ind; repeat (autodimp ind hyp).
      { exists l n; autorewrite with eo; dands; auto. }
      exrepnd.
      exists e'; dands; eauto 3 with eo.
    }

    {
      exists e; dands; eauto with eo.
    }
  Qed.

  Lemma information_acquired_between_knew :
    forall {eo : EventOrdering} (e1 e2 : Event) (i : lak_info),
      lak_know_i_dec
      -> e1 ⊏ e2
      -> ~knew_i e1 i
      -> knew_i e2 i
      ->
      exists e,
        e ⊏ e2
        /\ e1 ⊑ e
        /\ knows_i e i
        /\ ~ knew_i e i.
  Proof.
    intros eo e1.
    induction e2 as [e2 ind] using predHappenedBeforeInd_type.
    introv dec lte kn1 kn2.
    dup kn2 as kn'.
    unfold knew_i in kn2; exrepnd.
    rewrite <- ite_first_state_sm_on_event_as_before in kn2.

    unfold ite_first in kn2.
    destruct (dec_isFirst e2) as [isf|isf]; ginv.

    { apply lak_no_initial_memory_i in kn3; tcsp. }

    dup kn2 as kn''.
    rw @state_sm_on_event_unroll2 in kn2.

    remember (state_sm_before_event (lak_system n) (local_pred e2)) as s; symmetry in Heqs.
    destruct s; simpl in *; ginv;[].
    destruct (dec i l) as [dc|dc].

    {
      assert (knew_i (local_pred e2) i) as knp by (eapply implies_knew_i; eauto; autorewrite with eo; auto).

      apply local_implies_pred_or_local in lte.
      repndors; subst;[apply pred_implies_local_pred in lte; subst; tcsp|];[].
      exrepnd.
      apply pred_implies_local_pred in lte1; subst.

      pose proof (ind (local_pred e2)) as ind; autodimp ind hyp; eauto 2 with eo.
      pose proof (ind i) as ind; repeat (autodimp ind hyp); eauto 3 with eo; tcsp;[].
      exrepnd.
      exists e; dands; auto; eauto 3 with eo.
    }

    {
      exists (local_pred e2); dands; eauto 3 with eo.
      { apply local_implies_pred_or_local in lte; repndors; exrepnd; eauto 3 with eo.
        { apply pred_implies_local_pred in lte; subst; eauto 3 with eo. }
        { apply pred_implies_local_pred in lte1; subst; eauto 3 with eo. }
      }
      { eapply implies_knows_i; eauto; autorewrite with eo; auto. }
      { eapply implies_not_knew_i; eauto; autorewrite with eo; auto. }
    }
  Qed.

  (* ========= ========= *)



  (* ========== LEARNING ========= *)


  Lemma learned_local_pred_implies :
    forall (eo : EventOrdering) (e : Event) d,
      learned (local_pred e) d
      -> learned e d.
  Proof.
    introv h.
    unfold learned in *; exrepnd.
    eexists; dands; eauto; eauto 3 with eo.
  Qed.
  Hint Resolve learned_local_pred_implies : eo.

  (* ========= ========= *)




  (* ========== KNOWING/LEARNING CONNECTION ========= *)

  Definition learns_or_knows (eo : EventOrdering) : Prop :=
    forall (d : lak_data) (e : Event),
      knows e d
      -> learned e d \/ lak_data2node d = loc e.

  Definition learns_or_knows_i (eo : EventOrdering) : Prop :=
    forall (i : lak_info) (e : Event),
      knows_i e i
      ->
      exists d,
        i = lak_data2info d
        /\ (learned e d \/ lak_data2node d = loc e).

  Definition learns_if_knows (eo : EventOrdering) :=
    forall (d  : lak_data) (e : Event),
      learns e d
      -> has_correct_trace_before e (lak_data2node d)
      ->
      exists e',
        e' ≺ e
        /\ loc e' = lak_data2node d
        /\ knows e' d.

  Definition learns_or_knows_if_knew (eo : EventOrdering) : Prop :=
    forall (d  : lak_data) (e : Event),
      knew e d
      -> learned e d \/ lak_data2node d = loc e.

  Definition learned_if_knows (eo : EventOrdering) :=
    forall (d  : lak_data) (e : Event),
      learned e d
      -> has_correct_trace_before e (lak_data2node d)
      ->
      exists e',
        e' ≺ e
        /\ loc e' = lak_data2node d
        /\ knows e' d.

  Lemma learns_or_knows_implies_learns_or_knows_if_new :
    forall (eo : EventOrdering),
      learns_or_knows eo
      -> learns_or_knows_if_knew eo.
  Proof.
    introv lok k.
    apply knew_implies_knows in k.
    apply lok in k; autorewrite with eo in *.
    repeat (autodimp k hyp); eauto 3 with eo;[].
    repndors; tcsp; left;[].
    unfold learned in *; exrepnd.
    exists e'; dands; auto; eauto 3 with eo.
  Qed.

  Lemma learned_local_le_implies :
    forall (eo : EventOrdering) (e1 e2 : Event) d,
      e1 ⊑ e2
      -> learned e1 d
      -> learned e2 d.
  Proof.
    introv lee h.
    unfold learned in *; exrepnd.
    eexists; dands;[|eauto]; eauto 3 with eo.
  Qed.
  Hint Resolve learned_local_le_implies : eo.

  Lemma learns_if_knows_implies_learned_if_knows :
    forall (eo : EventOrdering),
      learns_if_knows eo
      -> learned_if_knows eo.
  Proof.
    introv lik l hc.
    unfold learned in l; exrepnd.
    apply lik in l0; autodimp l0 hyp; eauto 3 with eo.
    exrepnd.
    exists e'0; dands; eauto 3 with eo.
  Qed.
  Hint Resolve learns_if_knows_implies_learned_if_knows : eo.

  (* ========= ========= *)



  (* ========== CONSEQUENCES ========= *)

  Lemma knows_propagates :
    forall {eo : EventOrdering} (e : Event) (d : lak_data),
      learns_or_knows eo
      -> learns_if_knows eo
      -> knows e d
      -> has_correct_trace_before e (lak_data2node d)
      ->
      exists e',
        e' ≼ e
        /\ loc e' = lak_data2node d
        /\ knows e' d.
  Proof.
    introv lok lik knows ctrace.
    pose proof (lok d e) as sent.
    repeat (autodimp sent hyp);[].
    repndors; repnd;[|exists e; dands; eauto 2 with eo];[].

    unfold learned in *; exrepnd.

    pose proof (lik d e') as h.
    repeat (autodimp h hyp); eauto 3 with eo;[].
    exrepnd.
    exists e'0; dands; auto; eauto 4 with eo.
  Qed.

  Lemma knows_in_intersection :
    forall {eo : EventOrdering}
           (e1 e2 : Event)
           (n : nat)
           (i1 i2 : lak_info)
           (P : list lak_data -> Prop)
           (E : list Event)
           (F : nat),
      learns_or_knows eo
      -> learns_if_knows eo
      -> n <= num_nodes
      -> num_nodes + F < 2 * n
      -> knows_certificate e1 n i1 P
      -> knows_certificate e2 n i2 P
      -> AXIOM_exists_at_most_f_faulty E F
      -> In e1 E
      -> In e2 E
      ->
      exists e1' e2' d1 d2,
        loc e1' = loc e2'
        /\ e1' ≼ e1
        /\ e2' ≼ e2
        /\ loc e1' = lak_data2node d1
        /\ loc e2' = lak_data2node d2
        /\ knows e1' d1
        /\ knows e2' d2
        /\ i1 = lak_data2info d1
        /\ i2 = lak_data2info d2.
  Proof.
    introv lok lik cond1 cond2 kna knb; introv atmost e1in e2in.
    unfold knows_certificate in *.
    destruct kna as [l1 [lena [norepa [conda impa]]]]; repnd.
    destruct knb as [l2 [lenb [norepb [condb impb]]]]; repnd.

    pose proof (overlapping_quorums_same_size
                  (MkNRlist _ (map lak_data2owner l1) norepa)
                  (MkNRlist _ (map lak_data2owner l2) norepb)
                  n) as q.
    simpl in q; autorewrite with list in *.
    repeat (autodimp q hyp); try omega;[].
    exrepnd.

    pose proof (there_is_one_correct_before eo l E F) as h.
    repeat (autodimp h hyp); try omega;[].
    exrepnd.

    pose proof (h0 e1) as ctrace1; simpl in ctrace1; autodimp ctrace1 hyp.
    pose proof (h0 e2) as ctrace2; simpl in ctrace2; autodimp ctrace2 hyp.

    applydup q3 in h1.
    applydup q0 in h1.
    allrw in_map_iff; exrepnd.

    applydup impa in h5.
    applydup impb in h4.
    repnd.

    pose proof (knows_propagates e1 x0) as w.
    repeat (autodimp w hyp); try (complete (unfold lak_data2node; allrw; auto));[].

    pose proof (knows_propagates e2 x) as z.
    repeat (autodimp z hyp); try (complete (unfold lak_data2node; allrw; auto));[].

    destruct w as [e1' w]; repnd.
    destruct z as [e2' z]; repnd.
    assert (loc e1' = loc e2') as eqloc' by (allrw; unfold lak_data2node; allrw; auto).

    exists e1' e2' x0 x; dands; auto.
  Qed.

  Lemma local_knows_in_intersection :
    forall {eo : EventOrdering}
           (e : Event)
           (n : nat)
           (i1 i2 : lak_info)
           (P : list lak_data -> Prop)
           (E : list Event)
           (F : nat),
      n <= num_nodes
      -> num_nodes + F < 2 * n
      -> knows_certificate e n i1 P
      -> knows_certificate e n i2 P
      -> AXIOM_exists_at_most_f_faulty E F
      -> In e E
      ->
      exists correct d1 d2,
        has_correct_trace_before e (node2name correct)
        /\ lak_data2node d1 = lak_data2node d2
        /\ knows e d1
        /\ knows e d2
        /\ i1 = lak_data2info d1
        /\ i2 = lak_data2info d2
        /\ lak_data2owner d1 = correct
        /\ lak_data2owner d2 = correct.
  Proof.
    introv cond1 cond2 kna knb atmost ein.
    unfold knows_certificate in *.
    destruct kna as [l1 [lena [norepa [conda impa]]]]; repnd.
    destruct knb as [l2 [lenb [norepb [condb impb]]]]; repnd.

    pose proof (overlapping_quorums_same_size
                  (MkNRlist _ (map lak_data2owner l1) norepa)
                  (MkNRlist _ (map lak_data2owner l2) norepb)
                  n) as q.
    simpl in q; autorewrite with list in *.
    repeat (autodimp q hyp); try omega;[].
    exrepnd.

    pose proof (there_is_one_correct_before eo l E F) as h.
    repeat (autodimp h hyp); try omega;[].
    exrepnd.

    exists correct.

    pose proof (h0 e) as ctrace1; simpl in ctrace1; autodimp ctrace1 hyp.

    applydup q3 in h1.
    applydup q0 in h1.
    allrw in_map_iff; exrepnd.

    applydup impa in h5.
    applydup impb in h4.
    repnd.

    exists x0 x; dands; auto;[].
    unfold lak_data2node; allrw; auto.
  Qed.

  Lemma knows_weak_certificate :
    forall {eo : EventOrdering}
           (e : Event)
           (n : nat)
           (i : lak_info)
           (P : list lak_data -> Prop)
           (E : list Event)
           (F : nat),
      F < n
      -> knows_certificate e n i P
      -> AXIOM_exists_at_most_f_faulty E F
      -> In e E
      ->
      exists d,
        has_correct_trace_before e (lak_data2node d)
        /\ knows e d
        /\ i = lak_data2info d.
  Proof.
    introv cond kn atmost ein.
    unfold knows_certificate in *.
    destruct kn as [l [len [norep [condp imp]]]]; repnd.
    pose proof (there_is_one_correct_before eo (map lak_data2owner l) E F) as q.
    repeat (autodimp q hyp); autorewrite with list in *; try omega.
    exrepnd.
    allrw in_map_iff; exrepnd; subst.
    applydup imp in q2; repnd; simpl in *.
    exists x; dands; auto.
  Qed.

  Lemma knows_weak_certificate_propagates :
    forall {eo : EventOrdering}
           (e : Event)
           (n : nat)
           (i : lak_info)
           (P : list lak_data -> Prop)
           (E : list Event)
           (F : nat),
      learns_or_knows eo
      -> learns_if_knows eo
      -> F < n
      -> knows_certificate e n i P
      -> AXIOM_exists_at_most_f_faulty E F
      -> In e E
      ->
      exists e' d,
        e' ≼ e
        /\ loc e' = lak_data2node d
        /\ knows e' d
        /\ i = lak_data2info d.
  Proof.
    introv lok lik cond kn atmost ein.
    eapply knows_weak_certificate in kn; eauto; exrepnd; subst.
    apply knows_propagates in kn2; auto.
    exrepnd.
    exists e' d; dands; auto.
  Qed.

  (* ========= ========= *)

End LearnAndKnow.


Ltac prove_knows :=
  match goal with
  | [ |- knows _ _ ] =>
    eapply implies_knows; simpl;[| |eassumption];auto;
    autorewrite with eo; auto
  end.


Hint Resolve implies_knows : eo.
Hint Resolve learned_local_pred_implies : eo.
Hint Resolve learned_local_le_implies : eo.
Hint Resolve learns_if_knows_implies_learned_if_knows : eo.
Hint Resolve knows_implies_correct : eo.
