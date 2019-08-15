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


(*Require Export IC2.*)
Require Export SMat_most_f_byz.
Require Export SMtactics3.
Require Export SMsame_states.
Require Export SMwell_formed_V.
Require Export SMknows_choice.
Require Export Synch.


Section IC1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc             : @DTimeContext }.
  Context { dtime           : @TimeConstraint dtc }.
  Context { sm_context      : SMcontext }.
  Context { sm_auth         : SMauth }.
  Context { sm_initial_keys : SMinitial_keys }.


  Lemma is_commander_dec :
    forall (g : Gen),
      is_commander g = true
      \/
      is_commander g = false.
  Proof.
    intros; unfold is_commander; dest_cases x; simpl in *; ginv; subst; tcsp.
  Qed.

  Lemma no_order_yet_implies_not_in :
    forall s v,
      no_order_yet (V s) = true
      -> ~ In v (V s).
  Proof.
    introv h i.
    unfold no_order_yet in *.
    allrw @nullb_true_iff; rewrite h in *; simpl in *; tcsp.
  Qed.
  Hint Resolve no_order_yet_implies_not_in : sm.

  Lemma check_new_value_implies_not_in :
    forall s v,
      check_new_value (V s) v = true
      -> ~ In (sm_signed_msg2value v) (V s).
  Proof.
    introv h i.
    unfold check_new_value in h; smash_sm.
  Qed.
  Hint Resolve check_new_value_implies_not_in : sm.

  Lemma value_was_received :
    forall g v {eo : EventOrdering} (e : Event) s,
      state_sm_on_event (SMreplicaSM g) e = Some s
      -> In v (V s)
      -> exists e' s' m,
          e' ⊑ e
          /\ trigger_op e' = Some (sm_msg_signed m)
          /\ v = sm_signed_msg2value m
          /\ state_sm_before_event (SMreplicaSM g) e' = Some s'
          /\ state_sm_on_event (SMreplicaSM g) e' = Some (add_to_V s' (sm_signed_msg2value m))
          /\ ~In v (V s')
          /\ verify_signed_msg g (local_keys s') m = true
          /\ message_is_on_time m (time e') = true.
  Proof.
    intros g v eo e.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv eqst i.

    dup eqst as eqst_At_e; hide_hyp eqst_At_e.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop;
        simpl in *;[|ginv];op_st_some m eqtrig
    end.

    unfold SMupdate in eqst.

    destruct m;
      simpl in *; ginv; subst; tcsp;
        try smash_handlers; try (smash_sm_ind ind);
          try (complete (repndors; subst; try (smash_sm_ind ind);
                         exists e s0 v0; dands; eauto 3 with sm eo)).
  Qed.

  Lemma value_was_received_before :
    forall g v {eo : EventOrdering} (e : Event) s,
      state_sm_before_event (SMreplicaSM g) e = Some s
      -> In v (V s)
      -> exists e' s' m,
          e' ⊏ e
          /\ trigger_op e' = Some (sm_msg_signed m)
          /\ v = sm_signed_msg2value m
          /\ state_sm_before_event (SMreplicaSM g) e' = Some s'
          /\ state_sm_on_event (SMreplicaSM g) e' = Some (add_to_V s' (sm_signed_msg2value m))
          /\ ~In v (V s')
          /\ verify_signed_msg g (local_keys s') m = true
          /\ message_is_on_time m (time e') = true.
  Proof.
    introv eqst i.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in eqst.
    destruct (dec_isFirst e) as [d|d]; [ginv; simpl in *; tcsp|];[].

    eapply value_was_received in eqst;[|eauto]; exrepnd.
    exists e' s' m; dands; eauto 3 with eo.
  Qed.

  Fixpoint extend_signed_msg_list
           (m : sm_signed_msg)
           (l : sm_signs) : sm_signed_msg :=
    match l with
    | [] => m
    | s :: l => extend_signed_msg_list (sm_signed_msg_cons m s) l
    end.

  Lemma extend_signed_msg_list_snoc :
    forall l m a,
      extend_signed_msg_list m (snoc l a)
      = sm_signed_msg_cons (extend_signed_msg_list m l) a.
  Proof.
    induction l; introv; simpl; auto.
  Qed.

  Lemma in_sm_signed_msg2senders_implies :
    forall g m,
      In g (sm_signed_msg2senders m)
      ->
      exists m' l,
        sm_signed_msg2sender m' = g
        /\ m = extend_signed_msg_list m' l.
  Proof.
    induction m; introv i; simpl in *; repndors; subst; tcsp.

    - exists (sm_signed_msg_sing v a) ([] : sm_signs); simpl; tcsp.

    - allrw @in_snoc; repndors; subst; tcsp.

      + apply IHm in i; clear IHm; exrepnd; subst; simpl in *.
        exists m' (snoc l a); simpl; dands; auto.
        rewrite extend_signed_msg_list_snoc; auto.

      + exists (sm_signed_msg_cons m a) ([] : sm_signs); simpl; tcsp.
  Qed.

  Lemma sm_signed_msg2main_auth_data_in_list :
    forall m,
      In (sm_signed_msg2main_auth_data m) (sm_signed_msg2list_auth_data m).
  Proof.
    destruct m; simpl; tcsp.
    rw @in_snoc; tcsp.
  Qed.
  Hint Resolve sm_signed_msg2main_auth_data_in_list : sm.

  Lemma subset_extend_signed_msg_list :
    forall l m,
      subset
        (sm_signed_msg2list_auth_data m)
        (sm_signed_msg2list_auth_data (extend_signed_msg_list m l)).
  Proof.
    induction l using snoc_list_ind; introv; simpl in *; tcsp.
    introv i; apply IHl in i; clear IHl.
    rewrite extend_signed_msg_list_snoc; simpl.
    apply in_snoc; tcsp.
  Qed.

  Lemma sm_signed_msg2main_auth_data_in_extend_signed_msg_list :
    forall m l,
      In (sm_signed_msg2main_auth_data m)
         (sm_signed_msg2list_auth_data (extend_signed_msg_list m l)).
  Proof.
    introv; apply subset_extend_signed_msg_list; eauto 3 with sm.
  Qed.
  Hint Resolve sm_signed_msg2main_auth_data_in_extend_signed_msg_list : sm.

  Lemma sm_signed_msg2sing_extend_signed_msg_list :
    forall m l,
      sm_signed_msg2sing (extend_signed_msg_list m l)
      = sm_signed_msg2sing m.
  Proof.
    induction l using snoc_list_ind; introv; simpl; auto.
    rewrite extend_signed_msg_list_snoc; simpl; auto.
  Qed.
  Hint Rewrite sm_signed_msg2sing_extend_signed_msg_list : sm.

  Lemma verify_extend_signed_msg_list_implies :
    forall g ks l m,
      verify_signed_msg g ks (extend_signed_msg_list m l) = true
      -> verify_signed_msg g ks m = true.
  Proof.
    induction l using snoc_list_ind; simpl; introv h; auto.
    rewrite extend_signed_msg_list_snoc in h; simpl in *.
    unfold verify_signed_msg in h; simpl in *; smash_sm.
    unfold verify_signed_msg_sign in h; simpl in *.
    unfold verify_signed_msg_commander in h0; simpl in *.
    rewrite forallb_snoc in h; smash_sm.
    rewrite @norepeatsb_snoc in *; smash_sm.
    allrw @not_inb_snoc_true_iff; repnd.
    autorewrite with sm in *.
    apply IHl.
    unfold verify_signed_msg; smash_sm; dands; auto.
    (*unfold verify_signed_msg_commander; apply is_commander_true; autorewrite with sm; auto.*)
  Qed.

  Lemma implies_verify_sm_signed_msg2main :
    forall g ks m,
      verify_signed_msg g ks m = true
      -> verify_authenticated_data (general g) (sm_signed_msg2main_auth_data m) ks = true.
  Proof.
    introv verif.
    unfold verify_signed_msg in verif; smash_sm.
    clear verif0.
    unfold verify_signed_msg_sign in verif.
    rewrite forallb_forall in verif.
    apply verif; eauto 3 with sm.
  Qed.
  Hint Resolve implies_verify_sm_signed_msg2main : sm.

  Lemma sm_bare_signed_msg2general_sm_signed_msg2bare_eq :
    forall m,
      sm_bare_signed_msg2general (sm_signed_msg2bare m)
      = general (sm_signed_msg2sender m).
  Proof.
    introv; destruct m; simpl; tcsp;
      unfold sm_signed_msg2sender; simpl;
        destruct a; simpl; tcsp;
          destruct sm_sign_id; simpl; auto.
  Qed.
  Hint Rewrite sm_bare_signed_msg2general_sm_signed_msg2bare_eq : sm.

  Lemma main_in_auth_data_implies_extend_signed_msg_list :
    forall m' m,
      In (sm_signed_msg2main_auth_data m') (SMget_contained_auth_data m)
      -> exists l, m = sm_msg_signed (extend_signed_msg_list m' l).
  Proof.
    introv; destruct m; simpl in *; tcsp.
    induction v; introv i; simpl in *; tcsp; repndors; subst; tcsp.

    - destruct m'; simpl in *; ginv.
      inversion i as []; subst; clear i.
      unfold sm_signed_msg2auth in *; simpl in *; subst.
      destruct a, a0; simpl in *; subst.
      exists ([] : sm_signs); simpl; auto.

    - allrw @in_snoc; repndors; tcsp.

      + apply IHv in i; exrepnd; clear IHv; ginv.
        exists (snoc l a).
        rewrite extend_signed_msg_list_snoc; simpl; auto.

      + clear IHv.
        destruct m'; simpl in *; ginv.
        inversion i as []; subst; clear i.
        unfold sm_signed_msg2auth in *; simpl in *; subst.
        destruct a, a0; simpl in *; subst.
        exists ([] : sm_signs); simpl; auto.
  Qed.

  Lemma is_sm_signed_msg2directly_from_commander_true_implies_length :
    forall v,
      is_sm_signed_msg2directly_from_commander v = true
      -> length (sm_signed_msg2signs v) = 1.
  Proof.
    introv h.
    unfold is_sm_signed_msg2directly_from_commander in *.
    destruct v; ginv.
  Qed.

  Lemma is_sm_signed_msg2directly_from_commander_true_implies_senders :
    forall v,
      is_sm_signed_msg2directly_from_commander v = true
      -> sm_signed_msg2senders v = [SMcommander].
  Proof.
    introv h.
    unfold is_sm_signed_msg2directly_from_commander in *.
    destruct v; ginv.
    unfold is_commander in *; smash_sm.
  Qed.

  Hint Rewrite length_snoc : list.

  Lemma length_sm_signed_msg2signs_eq_length_sm_signed_msg2senders :
    forall v,
      length (sm_signed_msg2signs v)
      = length (sm_signed_msg2senders v).
  Proof.
    induction v; simpl; tcsp; autorewrite with list; allrw; auto.
  Qed.

  Definition send_delayed_sm_msg_lieutenant (m : SMmsg) (n : list name) (d : PosDTime) : DirectedMsg :=
    MkDMsg m n d.

  Lemma lieutenant_output_signed_msg_implies :
    forall {eo : EventOrdering} (e : Event) m l g (d : PosDTime),
      loc e = general g
      -> is_lieutenant g = true
      -> In (send_delayed_sm_msg_lieutenant (sm_msg_signed m) l d) (output_system_on_event_ldata SMsys e)
      -> exists v s1 s2,
          (d = '0)
          /\ l = names_not_in_list (g :: sm_signed_msg2senders v)
          /\ m = extend_signed_msg v (general g) (local_keys s1)
          /\ verify_signed_msg g (local_keys s1) v = true
          /\ trigger_op e = Some (sm_msg_signed v)
          /\ (time e <= (nat2pdt (length (sm_signed_msg2signs v)) * (mu + tau)))%dtime
          /\ length (sm_signed_msg2signs v) <= F
          /\ state_sm_before_event (SMreplicaSM g) e = Some s1
          /\ state_sm_on_event (SMreplicaSM g) e = Some s2
          /\ ~In (sm_signed_msg2value v) (V s1)
          /\ In (sm_signed_msg2value v) (V s2).
  Proof.
    introv eqloc isl i.

    (* unrolling output of e1 *)
    eapply in_output_system_on_event_ldata in i; eauto.
    unfold SMsys in i.
    try rewrite eqloc in i; simpl in *.

    rw @loutput_sm_on_event_unroll2 in i.
    fold (@DirectedMsgs _ _ _) in *.
    simpl in *.
    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q1; symmetry in Heqq1
    end.
    destruct q1; simpl in *; ginv; tcsp;[].

    remember (trigger_op e) as trig1; symmetry in Heqtrig1.
    destruct trig1; simpl in *; tcsp.
    unfold SMupdate in *.
    destruct m0; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends;
        try (complete (repndors; tcsp; ginv));
        try (complete (unfold broadcast2others in *; ginv)).

    { unfold is_lieutenant, is_commander in *; simpl in *; smash_sm. }

    {
      rename_hyp_with is_sm_signed_msg2directly_from_commander dirc.
      applydup is_sm_signed_msg2directly_from_commander_true_implies_length in dirc.
      applydup is_sm_signed_msg2directly_from_commander_true_implies_senders in dirc.
      unfold broadcast2not_in_list in *; simpl in *.
      inversion i; subst; GC; simpl in *.
      unfold message_is_on_time in *; smash_sm.
      rewrite state_sm_on_event_unroll2; allrw; simpl.
      unfold op_state; simpl.
      unfold SMhandler_lieutenant; simpl; smash_sm; try omega.
      { exists v; eexists; eexists; dands; eauto; simpl; tcsp; ginv; try omega; eauto 3 with sm. }
      { unfold message_is_on_time in *; smash_sm.
        eapply dt_le_lt_trans in d0;eauto.
        apply dt_lt_irrefl in d0; tcsp. }
    }

    {
      pose proof (length_sm_signed_msg2signs_eq_length_sm_signed_msg2senders v) as eqlen.
      unfold broadcast2not_in_list in *; simpl in *.
      inversion i; subst; GC; simpl in *.
      unfold message_is_on_time in *; smash_sm.
      rewrite state_sm_on_event_unroll2; allrw; simpl.
      unfold op_state; simpl.
      unfold SMhandler_lieutenant; simpl; smash_sm; try omega.
      { exists v; eexists; eexists; dands; eauto; simpl; tcsp; try omega; eauto 3 with sm. }
      { unfold message_is_on_time in *; smash_sm.
        eapply dt_le_lt_trans in d0;eauto.
        apply dt_lt_irrefl in d0; tcsp. }
    }
  Qed.

  Hint Resolve implies_subset_cons_r_weak : sm list.

  Lemma values_increase_step :
    forall (eo : EventOrdering) (e : Event) g s1 s2,
      state_sm_before_event (SMreplicaSM g) e = Some s1
      -> state_sm_on_event (SMreplicaSM g) e = Some s2
      -> subset (V s1) (V s2).
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_sm_ind3.
  Qed.

  Lemma values_increase_before :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      e1 ⊑ e2
      -> state_sm_before_event (SMreplicaSM g) e1 = Some s1
      -> state_sm_before_event (SMreplicaSM g) e2 = Some s2
      -> subset (V s1) (V s2).
  Proof.
    introv.
    revert s2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
      eapply values_increase_step in h1;[|eauto]; auto.
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_before_event_some_between e e2 (SMreplicaSM g) s2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q; repeat (autodimp h hyp); eauto 4 with eo.

    eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
    eapply values_increase_step in h1;[|eauto]; auto.
    eapply subset_trans; eauto.
  Qed.

  Lemma values_increase_on :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      e1 ⊑ e2
      -> state_sm_on_event (SMreplicaSM g) e1 = Some s1
      -> state_sm_on_event (SMreplicaSM g) e2 = Some s2
      -> subset (V s1) (V s2).
  Proof.
    introv.
    revert s2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_before_event_if_on_event_direct_pred in h2; eauto.
      eapply values_increase_step in h3;[|eauto]; auto.
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_on_event_some_between e e2 (SMreplicaSM g) s2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q; repeat (autodimp h hyp); eauto 4 with eo.

    eapply state_sm_before_event_if_on_event_direct_pred in h1;[|eauto].
    eapply values_increase_step in h1;[|eauto]; auto.
    eapply subset_trans; eauto.
  Qed.

  Lemma values_increase_on_before :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      e1 ⊏ e2
      -> state_sm_on_event (SMreplicaSM g) e1 = Some s1
      -> state_sm_before_event (SMreplicaSM g) e2 = Some s2
      -> subset (V s1) (V s2).
  Proof.
    introv lte eqst1 eqst2.
    applydup localHappenedBefore_implies_le_local_pred in lte.
    rewrite state_sm_before_event_as_state_sm_on_event_pred in eqst2; eauto 3 with eo;[].
    eapply values_increase_on in lte0; eauto.
  Qed.

  Lemma sm_signed_msg2value_extend_signed_msg_list :
    forall l m,
      sm_signed_msg2value (extend_signed_msg_list m l)
      = sm_signed_msg2value m.
  Proof.
    induction l; introv; simpl; auto.
    rewrite IHl; simpl; auto.
  Qed.
  Hint Rewrite sm_signed_msg2value_extend_signed_msg_list : sm.

  Lemma sm_signed_msg2value_extend_signed_msg :
    forall v a ks,
      sm_signed_msg2value (extend_signed_msg v a ks)
      = sm_signed_msg2value v.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite sm_signed_msg2value_extend_signed_msg : sm.

  Lemma message_is_on_time_implies_sm_signed_msg2signs :
    forall m t,
      message_is_on_time m t = true
      -> length (sm_signed_msg2signs m) <= S F.
  Proof.
    introv h; unfold message_is_on_time in h; smash_sm.
  Qed.
  Hint Resolve message_is_on_time_implies_sm_signed_msg2signs : sm.

  Lemma is_sm_signed_msg2directly_from_commander_implies_senders_eq :
    forall m,
      is_sm_signed_msg2directly_from_commander m = true
      -> sm_signed_msg2senders m = [SMcommander].
  Proof.
    introv h.
    unfold is_sm_signed_msg2directly_from_commander in h.
    destruct m; simpl in *; tcsp.
    destruct a; simpl in *.
    unfold is_commander in h; smash_sm.
  Qed.

  Lemma message_is_on_time_implies_qle :
    forall m t,
      message_is_on_time m t = true
      -> (t <= nat2pdt (length (sm_signed_msg2signs m)) * (mu + tau))%dtime.
  Proof.
    introv h.
    unfold message_is_on_time in h; smash_sm.
  Qed.

  Lemma send_value :
    forall {eo : EventOrdering} (e : Event) g m s1 s2,
      is_lieutenant g = true
      -> loc e = general g
      -> trigger_op e = Some (sm_msg_signed m)
      -> length (sm_signed_msg2signs m) < S F
      -> state_sm_before_event (SMreplicaSM g) e = Some s1
      -> state_sm_on_event (SMreplicaSM g) e = Some s2
      -> ~ In (sm_signed_msg2value m) (V s1)
      -> In (sm_signed_msg2value m) (V s2)
      -> verify_signed_msg g (local_keys s1) m = true
      -> In (send_sm_msg_lieutenant
               (sm_msg_signed (extend_signed_msg m (general g) (local_keys s1)))
               (names_not_in_list (g :: sm_signed_msg2senders m)))
            (output_system_on_event_ldata SMsys e).
  Proof.
    introv isl eqloc eqtrig len eqst1 eqst2 niv iv verif.
    eapply in_output_system_on_event_ldata; eauto.

    unfold SMsys.
    try rewrite eqloc; simpl in *.

    rw @loutput_sm_on_event_unroll2.
    rewrite state_sm_on_event_unroll2 in eqst2.

    fold (@DirectedMsgs _ _ _) in *.
    simpl in *.

    pose proof (length_sm_signed_msg2signs_eq_length_sm_signed_msg2senders m) as eqlen.

    rewrite eqst1 in *; simpl in *.
    rewrite eqtrig in *; simpl in *.
    unfold op_state in *; simpl in *.
    unfold SMhandler_lieutenant in *.

    smash_sm; repndors; tcsp; try omega; GC;
      [|rename_hyp_with is_sm_signed_msg2directly_from_commander dirc;
        applydup is_sm_signed_msg2directly_from_commander_true_implies_length in dirc;
        rewrite dirc0 in *; try omega];[].

    GC; left.
    rename_hyp_with is_sm_signed_msg2directly_from_commander fc.
    applydup is_sm_signed_msg2directly_from_commander_implies_senders_eq in fc; allrw; simpl; auto.
  Qed.

  Lemma check_new_value_false_implies_in :
    forall l mv x ks,
      check_new_value l (extend_signed_msg mv x ks) = false
      -> In (sm_signed_msg2value mv) l.
  Proof.
    introv h; unfold check_new_value in h; smash_sm.
  Qed.
  Hint Resolve check_new_value_false_implies_in : sm.

  Lemma verify_signed_msg_commander_extend_signed_msg :
    forall mv g ks,
      verify_signed_msg_commander (extend_signed_msg mv g ks)
      = verify_signed_msg_commander mv.
  Proof.
    introv; tcsp.
  Qed.
  Hint Rewrite verify_signed_msg_commander_extend_signed_msg : sm.

  Lemma verify_signed_msg_sign_extend_signed_msg :
    forall g ks m g' ks',
      verify_signed_msg_sign g ks (extend_signed_msg m g' ks')
      = (verify_signed_msg_sign g ks m)
          &&
          (verify_authenticated_data
             (general g)
             (sm_signed_msg2main_auth_data (sm_signed_msg_cons m (MkSmSign g' (authenticate (sm_bare_msg_signed (sm_bare_signed_msg_cons m g')) ks'))))
             ks).
  Proof.
    introv; unfold verify_signed_msg_sign; simpl.
    allrw @forallb_snoc; tcsp.
  Qed.

  Lemma all_verify_signed_msg_sign :
    forall {eo : EventOrdering} (e1 e2 : Event) m g1 g2,
      AXIOM_all_correct_can_verify eo
      -> loc e1 = general g1
      -> loc e2 = general g2
      -> has_correct_trace_before e1 (loc e1)
      -> has_correct_trace_before e2 (loc e2)
      -> verify_signed_msg_sign g1 (keys e1) m = true
      -> verify_signed_msg_sign g2 (keys e2) m = true.
  Proof.
    introv cverif eqloc1 eqloc2 cor1 cor2 verif.
    induction m; simpl in *; simpl in *; tcsp.

    {
      unfold verify_signed_msg_sign in *; simpl in *; smash_sm; dands; auto.
      rewrite <- eqloc1, <- eqloc2 in *.
      eapply cverif in verif; eauto.
    }

    {
      unfold verify_signed_msg_sign in *; simpl in *.
      allrw @forallb_snoc; smash_sm.
      autodimp IHm hyp;[].
      dands; tcsp;[].
      rewrite <- eqloc1, <- eqloc2 in *.
      eapply cverif in verif0; eauto.
    }
  Qed.

  Lemma sm_msg_signed_trigger_implies_in_V :
    forall {eo : EventOrdering} (e : Event) g s m g' ks,
      AXIOM_SMcorrect_keys eo
      -> node_has_correct_trace_before e g
      -> no_repeats (sm_signed_msg2senders m)
      -> ~ In g (sm_signed_msg2senders m)
      -> ~ In g' (sm_signed_msg2senders m)
      -> g <> g'
      -> loc e = node2name g
      -> verified_authenticated_data (general g') (general g) ks (keys e)
      -> is_lieutenant g = true
      -> length (sm_signed_msg2signs m) <= F
      -> (time e <= nat2pdt (S (length (sm_signed_msg2signs m))) * (mu + tau))%dtime
      -> verify_signed_msg_commander m = true
      -> verify_signed_msg_sign g (keys e) m = true
      -> trigger_op e = Some (sm_msg_signed (extend_signed_msg m (general g') ks))
      -> state_sm_on_event (SMreplicaSM g) e = Some s
      -> In (sm_signed_msg2value m) (V s).
  Proof.
    introv ckeys ctrace norep nigm nig'm dgg' eqn vauth;
      introv isl len lttime;
      introv verifc verifs eqtrig eqst.
    rewrite state_sm_on_event_unroll2 in eqst.
    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv]
    end.
    rewrite eqtrig in *; simpl in *.
    unfold op_state in *; simpl in *.

    pose proof (ckeys e g s0) as ck.
    repeat (autodimp ck hyp).
    rewrite ck in *.

    smash_handlers.

    {
      rename_hyp_with message_is_on_time ontime.
      unfold message_is_on_time in *; smash_sm; autorewrite with list in *; try omega;[].
      assert (time e < time e)%dtime as w by (eapply dt_le_lt_trans; eauto).
      apply dt_lt_irrefl in w; tcsp.
    }

    {
      unfold verify_signed_msg in *; smash_sm.
      autorewrite with sm in *.
      allrw @norepeatsb_snoc.
      allrw @not_inb_snoc_false_iff.
      allrw @andb_false_iff.
      allrw @norepeatsb_false_iff.
      allrw @not_inb_false_iff.
      repndors; tcsp; smash_sm ;[].
      rewrite verify_signed_msg_sign_extend_signed_msg in *; smash_sm.
      repndors; smash_sm.

      match goal with
      | [ H : verify_authenticated_data ?n ?d ?k = false |- _ ] =>
        pose proof (vauth d) as vauth; simpl in vauth;
          autodimp vauth hyp;
          unfold sm_signed_msg2main_auth_data in *; simpl in *;
            unfold sm_signed_msg2auth in *; simpl in *;
              rewrite vauth in H; ginv
      end.
    }
  Qed.

  Lemma verify_signed_msg_implies_no_repeats :
    forall g ks m,
      verify_signed_msg g ks m = true
      -> no_repeats (sm_signed_msg2senders m).
  Proof.
    introv verif.
    unfold verify_signed_msg in *; smash_sm.
    allrw @norepeatsb_as_no_repeats; tcsp.
  Qed.
  Hint Resolve verify_signed_msg_implies_no_repeats : sm.

  Lemma implies_general_in_names_not_in_list :
    forall g l,
      ~In g l
      -> In (general g) (names_not_in_list l).
  Proof.
    introv h.
    apply in_map.
    apply in_diff; dands; eauto 3 with sm.
  Qed.

  Lemma sm_signed_msg2senders_extend_signed_msg_list :
    forall l m,
      sm_signed_msg2senders (extend_signed_msg_list m l)
      = sm_signed_msg2senders m ++ map General2Gen (map sm_sign_id l).
  Proof.
    induction l using snoc_list_ind; introv; simpl in *; tcsp;
      autorewrite with list; auto.
    rewrite extend_signed_msg_list_snoc; simpl.
    rewrite map_snoc.
    rewrite app_snoc.
    rewrite IHl; autorewrite with list; auto.
  Qed.

  Lemma sm_signed_msg2signs_extend_signed_msg_list :
    forall l m,
      sm_signed_msg2signs (extend_signed_msg_list m l)
      = sm_signed_msg2signs m ++ l.
  Proof.
    induction l using snoc_list_ind; introv; simpl in *; tcsp;
      autorewrite with list; auto.
    rewrite extend_signed_msg_list_snoc; simpl.
    rewrite app_snoc.
    rewrite IHl; autorewrite with list; auto.
  Qed.

  Lemma sm_signed_msg2sender_in_senders :
    forall m, In (sm_signed_msg2sender m) (sm_signed_msg2senders m).
  Proof.
    destruct m; simpl; autorewrite with sm; tcsp.
    apply in_snoc; tcsp.
  Qed.
  Hint Resolve sm_signed_msg2sender_in_senders : sm.

  Lemma extend_signed_msg_list_eq_extend_signed_msg_implies_if_no_repeats :
    forall l m v ks1 ks2,
      verify_signed_msg (sm_signed_msg2sender m) ks1 v = true
      -> extend_signed_msg_list m l
         = extend_signed_msg v (general (sm_signed_msg2sender m)) ks2
      -> l = [].
  Proof.
    introv verif eqm.
    unfold verify_signed_msg in *; smash_sm.
    allrw @norepeatsb_as_no_repeats.
    allrw @not_inb_true_iff.

    clear verif verif2.

    match type of eqm with
    | ?a = ?b =>
      assert (sm_signed_msg2senders a = sm_signed_msg2senders b) as xx;
        try congruence;[]
    end.
    simpl in *.

    hide_hyp eqm.

    pose proof (snoc_cases l) as cs; repndors; tcsp;[].
    assert False; tcsp.
    exrepnd; subst; simpl in *.
    rewrite extend_signed_msg_list_snoc in *; simpl in *.
    apply snoc_inj in xx; repnd.
    rewrite <- xx0 in verif0.
    rewrite sm_signed_msg2senders_extend_signed_msg_list in verif0.
    destruct verif0; apply in_app_iff; left; eauto 3 with sm.
  Qed.

  (* CLEAN *)
  Lemma IC1_aux :
    forall {eo : EventOrdering} (e1 e2 e : Event) s2 s g1 g2 m,
      (* === general hypotheses === *)
      AXIOM_SMcorrect_keys eo
      -> AXIOM_all_correct_can_verify eo
      -> AXIOM_verified_authenticated eo
      (* ==== [e] is correct === *)
      -> node_has_correct_trace_before e g1
      (* === locations of events === *)
      -> loc e = general g1
      -> loc e2 = general g2
      -> loc e1 = general g2
      -> g2 <> g1
      -> is_lieutenant g2 = true
      -> ~ In g2 (sm_signed_msg2senders m)
      (* === time === *)
      -> length (sm_signed_msg2signs m) < S F
      -> (nat2pdt (S F) * (mu + tau) < time e2)%dtime
      -> (time e1 <= time e + (mu + tau))%dtime
      -> (time e <= nat2pdt (length (sm_signed_msg2signs m)) * (mu + tau))%dtime
      (* ==== [m] is not in [s2] === *)
      -> ~ In (sm_signed_msg2value m) (V s2)
      (* === ==== *)
      -> trigger_op e1 = Some (sm_msg_signed (extend_signed_msg m (general g1) (local_keys s)))
      (* === ==== *)
      -> verify_signed_msg g1 (local_keys s) m = true
      (* === states ==== *)
      -> state_sm_before_event (SMreplicaSM g1) e = Some s
      -> state_sm_before_event (SMreplicaSM g2) e2 = Some s2
      (* === ==== *)
      -> False.
  Proof.
    introv ckeys cverif vauth ctrace1 eqloc1 eqloc2 eqloc3 dg isl nim;
      introv len1 lttime1 letime1 letime2 ni1;
      introv trig verifd eqst1 eqst2.

    pose proof (lt_time_implies_happened_before e1 e2) as w.
    repeat (autodimp w hyp); try congruence;
      try (complete (eapply dt_le_lt_trans;[eauto|];
                     eapply time_plus_mu_tau_lt; eauto));[].

    pose proof (state_sm_on_event_some_between4 e1 e2 (SMreplicaSM g2) s2) as eqst'0.
    repeat (autodimp eqst'0 hyp).
    destruct eqst'0 as [s'0 eqst'0].

    pose proof (values_increase_on_before e1 e2 g2 s'0 s2) as ss.
    repeat (autodimp ss hyp).

    assert (In (sm_signed_msg2value m) (V s'0)) as ins'0;[|apply ss in ins'0; tcsp];[].

    assert (time e1 <= nat2pdt (S (length (sm_signed_msg2signs m))) * (mu + tau))%dtime as t.
    { eapply dt_le_trans;[eauto|].
      eapply time_plus_tau_le_aux; eauto. }

    rename_hyp_with verify_signed_msg verif.
    unfold verify_signed_msg in *; smash_sm;[].

    pose proof (ckeys e g1 s) as k1.
    repeat (autodimp k1 hyp); eauto 3 with eo;[].
    rewrite <- k1 in verif.

    pose proof (all_verify_signed_msg_sign e e1 m g1 g2) as vm.
    repeat (autodimp vm hyp); eauto 3 with eo; try (complete (allrw; auto));[].

    pose proof (verified_authenticated_implies vauth e e1) as vad.
    repeat (autodimp vad hyp); eauto 3 with eo; try (complete (allrw; auto));[].

    allrw @norepeatsb_as_no_repeats.
    allrw @not_inb_true_iff.

    pose proof (sm_msg_signed_trigger_implies_in_V e1 g2 s'0 m g1 (local_keys s)) as iv.
    repeat (autodimp iv hyp); eauto 3 with eo;
      try (complete (rewrite <- k1, <- eqloc3, <- eqloc1; auto));
      try omega.
  Qed.

  Lemma is_lieutenant_false_implies_is_commander :
    forall g,
      is_lieutenant g = false
      -> is_commander g = true.
  Proof.
    introv h.
    unfold is_commander, is_lieutenant, negb in *; smash_sm.
  Qed.

  Lemma commander_output_signed_msg_implies :
    forall {eo : EventOrdering} (e : Event) m l g d,
      loc e = general g
      -> is_commander g = true
      -> In (send_delayed_sm_msg_lieutenant (sm_msg_signed m) l d) (output_system_on_event_ldata SMsys e)
      -> exists s,
          d = nat2pdt 0
          /\ l = names_not_in_list [SMcommander]
          /\ m = create_new_sm_signed_msg (init s) (local_keys s)
          /\ state_sm_before_event (SMreplicaSM g) e = Some s
          /\ (time e == nat2pdt 0)%dtime
          /\ trigger_op e = Some sm_msg_init.
  Proof.
    introv eqloc isc i.

    (* unrolling output of e1 *)
    eapply in_output_system_on_event_ldata in i; eauto.
    unfold SMsys in i.
    try rewrite eqloc in i; simpl in *.

    rw @loutput_sm_on_event_unroll2 in i.
    fold (@DirectedMsgs _ _ _) in *.
    simpl in *.

    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q1; symmetry in Heqq1
    end.
    destruct q1; simpl in *; ginv; tcsp;[].

    remember (trigger_op e) as trig1; symmetry in Heqtrig1.
    destruct trig1; simpl in *; tcsp.
    unfold SMupdate in *.
    destruct m0; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends;
        try (complete (repndors; tcsp; ginv));
        try (complete (unfold broadcast2others in *; ginv)).

    { unfold broadcast2not_in_list in *; simpl in *.
      inversion i; subst; clear i.
      exists s; dands; auto. }

    { unfold is_lieutenant, is_commander in *; simpl in *; smash_sm. }

    { unfold is_lieutenant, is_commander in *; simpl in *; smash_sm. }
  Qed.

  Lemma sm_signed_msg2sender_create_new_sm_signed_msg :
    forall v ks,
      sm_signed_msg2sender (create_new_sm_signed_msg v ks)
      = SMcommander.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite sm_signed_msg2sender_create_new_sm_signed_msg : sm.

  Lemma no_order_yet_false_implies :
    forall l,
      no_order_yet l = false
      -> exists w, In w l.
  Proof.
    introv h.
    unfold no_order_yet in *; destruct l; simpl in *; ginv.
    eexists; eauto.
  Qed.

  Fixpoint sm_signed_msg2sm_signed_sing (m : sm_signed_msg) : sm_signed_msg :=
    match m with
    | sm_signed_msg_sing v a => m
    | sm_signed_msg_cons v _ => sm_signed_msg2sm_signed_sing v
    end.

  Lemma sm_signed_msg2main_auth_data_sm_signed_msg2sm_signed_sing_in :
    forall m,
      In (sm_signed_msg2main_auth_data (sm_signed_msg2sm_signed_sing m))
         (sm_signed_msg2list_auth_data m).
  Proof.
    induction m; simpl; tcsp.
    apply in_snoc; tcsp.
  Qed.
  Hint Resolve sm_signed_msg2main_auth_data_sm_signed_msg2sm_signed_sing_in : sm.

  Lemma sender_sm_signed_msg2sm_signed_sing_eq :
    forall m,
      sm_signed_msg2sender (sm_signed_msg2sm_signed_sing m)
      = sm_sign_id (snd (sm_signed_msg2sing m)).
  Proof.
    induction m; simpl; tcsp.
  Qed.

  Lemma sender_of_sm_signed_msg2sm_signed_sing :
    forall g ks m,
      verify_signed_msg g ks m = true
      -> sm_signed_msg2sender (sm_signed_msg2sm_signed_sing m) = SMcommander.
  Proof.
    introv verif.
    unfold verify_signed_msg in *; smash_sm.
    unfold verify_signed_msg_commander in *.
    apply is_commander_true in verif2.
    rewrite <- verif2; apply sender_sm_signed_msg2sm_signed_sing_eq.
  Qed.
  Hint Resolve sender_of_sm_signed_msg2sm_signed_sing : sm.

  Lemma sender_bare_sm_signed_msg2sm_signed_sing_eq :
    forall m,
      sm_bare_signed_msg2general (sm_signed_msg2bare (sm_signed_msg2sm_signed_sing m))
      = general (sm_sign_id (snd (sm_signed_msg2sing m))).
  Proof.
    induction m; simpl; tcsp.
    destruct a; simpl; auto.
    destruct sm_sign_id; simpl; tcsp.
  Qed.

  Lemma sender_of_bare_sm_signed_msg2sm_signed_sing :
    forall g ks m,
      verify_signed_msg g ks m = true
      -> sm_bare_signed_msg2general (sm_signed_msg2bare (sm_signed_msg2sm_signed_sing m)) = SMcommander.
  Proof.
    introv verif.
    unfold verify_signed_msg in *; smash_sm.
    unfold verify_signed_msg_commander in *.
    apply is_commander_true in verif2.
    rewrite <- verif2; apply sender_bare_sm_signed_msg2sm_signed_sing_eq.
  Qed.
  Hint Resolve sender_of_bare_sm_signed_msg2sm_signed_sing : sm.

  Lemma implies_verify_main_sm_signed_msg2sm_signed_sing :
    forall g ks m,
      verify_signed_msg g ks m = true
      -> verify_authenticated_data
           (general g)
           (sm_signed_msg2main_auth_data (sm_signed_msg2sm_signed_sing m))
           ks = true.
  Proof.
    introv verif.
    unfold verify_signed_msg in verif; smash_sm.
    unfold verify_signed_msg_sign in verif.
    allrw forallb_forall.
    apply verif; eauto 3 with sm.
  Qed.
  Hint Resolve implies_verify_main_sm_signed_msg2sm_signed_sing : sm.

  Lemma sm_signed_msg2sm_signed_sing_implies_value :
    forall m v ks,
      sm_signed_msg2sm_signed_sing m = create_new_sm_signed_msg v ks
      -> sm_signed_msg2value m = v.
  Proof.
    induction m; introv h; simpl in *.
    { inversion h; subst; tcsp. }
    apply IHm in h; auto.
  Qed.

  Lemma init_doesnt_change_step :
    forall {eo : EventOrdering} (e : Event) s1 s2 g,
      state_sm_before_event (SMreplicaSM g) e = Some s1
      -> state_sm_on_event (SMreplicaSM g) e = Some s2
      -> init s1 = init s2.
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_sm_ind3.
  Qed.

  Lemma init_doesnt_change_le :
    forall {eo : EventOrdering} (e1 e2 : Event) s1 s2 g,
      e1 ⊑ e2
      -> state_sm_before_event (SMreplicaSM g) e1 = Some s1
      -> state_sm_before_event (SMreplicaSM g) e2 = Some s2
      -> init s1 = init s2.
  Proof.
    introv.
    revert s2.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv h1 h2 h3.

    apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; tcsp;[|].

    {
      match goal with
      | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; ginv
      end.
    }

    apply local_implies_pred_or_local in h1; repndors; exrepnd.

    {
      eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
      eapply init_doesnt_change_step in h1;[|eauto]; auto.
    }

    pose proof (ind e) as q; autodimp q hyp; clear ind.

    pose proof (state_sm_before_event_some_between e e2 (SMreplicaSM g) s2) as w.
    repeat (autodimp w hyp); eauto 3 with eo;[].
    exrepnd.

    pose proof (q s') as h; clear q; repeat (autodimp h hyp); eauto 4 with eo.

    eapply state_sm_on_event_if_before_event_direct_pred in h1;[|eauto].
    eapply init_doesnt_change_step in h1;[|eauto]; auto; try congruence.
  Qed.

  Lemma init_doesnt_change :
    forall {eo : EventOrdering} (e1 e2 : Event) s1 s2 g,
      loc e1 = loc e2
      -> state_sm_before_event (SMreplicaSM g) e1 = Some s1
      -> state_sm_before_event (SMreplicaSM g) e2 = Some s2
      -> init s1 = init s2.
  Proof.
    introv eqloc eqst1 eqst2.
    pose proof (tri_if_same_loc e1 e2) as tri; autodimp tri hyp.
    repndors; subst.

    { eapply init_doesnt_change_le; eauto; eauto 3 with eo. }

    { rewrite eqst1 in *; ginv. }

    { symmetry; eapply init_doesnt_change_le; eauto; eauto 3 with eo. }
  Qed.

  (* It doesn't change, so it doesn't matter what event we pick *)
  Definition value_of_commander (eo : EventOrdering) (v : sm_value) :=
    exists e s,
      loc e = SMcommander
      /\ state_sm_before_event (SMreplicaSM SMcommander) e = Some s
      /\ v = init s.

  Lemma sm_msg_signed_commander_trigger_implies_in_V :
    forall {eo : EventOrdering} (e : Event) g s1 s2 v ks,
      authenticated_messages_were_sent_non_byz_usys eo SMsys
      -> AXIOM_SMcorrect_keys eo
      -> loc e = general g
      -> is_lieutenant g = true
      -> value_of_commander eo v
      -> node_has_correct_trace_before e SMcommander
      -> node_has_correct_trace_before e g
      -> (time e <= mu + tau)%dtime
      -> trigger_op e = Some (sm_msg_signed (create_new_sm_signed_msg v ks))
      -> verified_authenticated_data (general SMcommander) (general g) ks (local_keys s1)
      -> state_sm_before_event (SMreplicaSM g) e = Some s1
      -> state_sm_on_event (SMreplicaSM g) e = Some s2
      -> In v (V s2).
  Proof.
    introv sendbyz ckeys eqloc;
      introv isl vcom ctrace1 ctrace2 letime eqtrig verif eqst1 eqst2.
    rewrite state_sm_on_event_unroll2 in eqst2.
    rewrite eqst1 in *; simpl in *.
    rewrite eqtrig in *; simpl in *.
    unfold op_state in *; simpl in *.

    smash_handlers;
      try (complete (unfold is_commander in *; simpl in *; smash_sm)).

    {
      rename_hyp_with no_order_yet nord.
      apply no_order_yet_false_implies in nord; exrepnd.
      pose proof (value_was_received_before g w e s2) as q.
      repeat (autodimp q hyp); exrepnd.
      subst.

      applydup local_implies_loc in q1 as eqn.

      pose proof (ckeys e' g s') as ck1.
      repeat (autodimp ck1 hyp); eauto 3 with eo;
        try (complete (simpl; try rewrite <- eqloc; eauto 3 with eo));[].

      assert (loc e' = general g) as eqloc' by (allrw <-; eauto 3 with eo).

      pose proof (sendbyz
                    e'
                    (sm_signed_msg2main_auth_data (sm_signed_msg2sm_signed_sing m))
                    (sm_signed_msg2sender (sm_signed_msg2sm_signed_sing m))) as w.
      simpl in w.
      erewrite sender_of_sm_signed_msg2sm_signed_sing in w;[|eauto].
      erewrite sender_of_bare_sm_signed_msg2sm_signed_sing in w;[|eauto].
      repeat (autodimp w hyp); eauto 3 with eo sm.
      { unfold auth_data_in_trigger; allrw; simpl; eauto 3 with sm. }
      { rewrite ck1, eqloc'; eauto 3 with sm. }

      exrepnd.
      apply main_in_auth_data_implies_extend_signed_msg_list in w3; exrepnd.
      subst; simpl in *.
      autodimp w4 hyp; eauto 3 with sm;[].
      eapply commander_output_signed_msg_implies in w4;[|eauto|];
        [|apply is_commander_true;tcsp].
      exrepnd; subst.

      pose proof (snoc_cases l) as cs; repndors; exrepnd; subst; tcsp;[|];
        [|rewrite extend_signed_msg_list_snoc in *; inversion w6];[].
      simpl in *; subst; simpl in *; autorewrite with sm in *.

      applydup sm_signed_msg2sm_signed_sing_implies_value in w6 as eqv.
      rewrite eqv in *.

      assert (v = init s) as eqvs;[|subst; tcsp];[].
      unfold value_of_commander in vcom; exrepnd; subst.
      eapply init_doesnt_change;[|eauto|eauto]; try congruence.
    }

    {
      rename_hyp_with message_is_on_time ontime.
      unfold message_is_on_time in *; smash_sm; autorewrite with list in *; try omega;[].
      assert (time e < time e)%dtime as w;[|apply dt_lt_irrefl in w; tcsp].
      eapply dt_le_lt_trans;[|eauto].
      eapply dt_le_trans;[eauto|].
      rewrite dt_mul_1_l at 1; apply dt_le_refl.
    }

    {
      unfold verify_signed_msg in *; smash_sm.
      autorewrite with sm in *.
      repndors; tcsp; smash_sm.

      {
        pose proof (verif (sm_bare_msg_signed (sm_signed_msg2bare (create_new_sm_signed_msg v ks)))) as verif.
        simpl in *; autodimp verif hyp.
        unfold verify_signed_msg_sign in *; simpl in *.
        unfold sm_signed_msg2main_auth_data in *; simpl in *.
        unfold sm_signed_msg2auth in *; simpl in *.
        rewrite verif in *; simpl in *; ginv.
      }

      {
        unfold verify_signed_msg_commander in *; simpl in *.
        allrw is_commander_false; tcsp.
      }

      {
        unfold not_inb in *; simpl in *; smash_sm.
        unfold is_lieutenant, is_commander in *; simpl in *; smash_sm.
      }
    }
  Qed.

  (* MOVE *)
  Definition all_messages_are_sent_before_deadline
             {F}
             (eo  : EventOrdering)
             (sys : MUSystem F)
             (M   : msg -> Prop)
             (N   : name -> Prop)
             (deadline : dt_T) :=
    forall (e : Event) (m : DirectedMsg),
      has_correct_trace_before e (loc e)
      -> M(dmMsg m)
      -> N(loc(e))
      -> In m (output_system_on_event_ldata sys e)
      -> (time e <= deadline)%dtime.

  (* MOVE *)
  Definition all_containers_satisfy_constraint (d : AuthenticatedData) (M : msg -> Prop) :=
    forall m,
      In d (get_contained_authenticated_data m)
      -> M(m) /\ is_protocol_message m = true.

  (* MOVE *)
  Lemma message_is_sent_before_deadline :
    forall {eo : EventOrdering} (e : Event)
           {F} (sys : MUSystem F)
           (M : msg -> Prop) (N : name -> Prop)
           (d : AuthenticatedData) n (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo sys
      -> has_correct_trace_before e n
      -> all_messages_are_sent_before_deadline eo sys M N deadline
      -> all_containers_satisfy_constraint d M
      -> verify_authenticated_data (loc e) d (keys e) = true
      -> In d (bind_op_list get_contained_authenticated_data (trigger_op e))
      -> data_auth (loc e) d = Some n
      -> N(n)
      -> exists e',
          e' ≺ e
          /\ loc e' = n
          /\ (time e' <= deadline)%dtime.
  Proof.
    introv sendbyz cor before cont verif i eqn nn.

    apply implies_authenticated_messages_were_sent_non_byz_usys in sendbyz.
    pose proof (sendbyz e d n) as w.
    repeat (autodimp w hyp); eauto 2 with eo;[].
    simpl in w.

    exrepnd; subst.
    autodimp w4 hyp; try apply cont; auto;[].
    apply before in w4; simpl  in *; auto; eauto 3 with eo; try (apply cont; auto);[].
    exists e'; dands; auto.
  Qed.

  Definition is_signed_msg (m : SMmsg) : bool :=
    match m with
    | sm_msg_init     => false
    | sm_msg_alarm    => false
    | sm_msg_signed v => true
    | sm_msg_result v => false
    end.

  Lemma general_General2Gen :
    forall g, general (General2Gen g) = g.
  Proof.
    introv; destruct g; simpl; auto.
  Qed.
  Hint Rewrite general_General2Gen : sm.

  Lemma all_messages_are_sent_before_deadline_signed_lieutenant :
    forall (eo : EventOrdering),
      all_messages_are_sent_before_deadline
        eo SMsys
        (fun m => is_signed_msg m = true)
        (fun n => is_lieutenant n = true)
        (nat2pdt (S F) * (mu + tau))%dtime.
  Proof.
    introv cor iss isl i.
    destruct m; simpl in *.
    destruct dmMsg; simpl in *; ginv.
    eapply lieutenant_output_signed_msg_implies in i; eauto; autorewrite with sm; auto;[].
    exrepnd.
    eapply dt_le_trans;[eauto|].
    apply dt_mul_le_compat_r; eauto 3 with dtime;[].
    simpl; apply dt_nat_nat_inj_le; try omega.
  Qed.
  Hint Resolve all_messages_are_sent_before_deadline_signed_lieutenant : sm.

  Lemma all_containers_satisfy_constraint_sm_signed_msg2main_auth_data_signed :
    forall m,
      all_containers_satisfy_constraint
        (sm_signed_msg2main_auth_data m)
        (fun m => is_signed_msg m = true).
  Proof.
    introv i.
    destruct m0; simpl in *; tcsp.
  Qed.
  Hint Resolve all_containers_satisfy_constraint_sm_signed_msg2main_auth_data_signed : sm.

  Lemma sm_received_msg_was_sent :
    forall {eo : EventOrdering} (e1 e2 : Event) m g1 g2 s2,
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo SMsys
      -> loc e1 = general g1
      -> loc e2 = general g2
      -> is_lieutenant g2 = true
      -> state_sm_before_event (SMreplicaSM g2) e2 = Some s2
      -> (nat2pdt (S F) * (mu + tau) < time e2)%dtime
      -> ~ In (sm_signed_msg2value m) (V s2)
      -> trigger_op e1 = Some (sm_msg_signed m)
      -> verify_signed_msg g1 (keys e1) m = true
      -> In g2 (sm_signed_msg2senders m)
      -> has_correct_trace_before e1 (node2name g2)
      -> False.
  Proof.
    introv sendbyz eqloc1 eqloc2 isl2 eqst2 lttime2;
      introv vcond2 eqtrig1 verif d cle.

    applydup in_sm_signed_msg2senders_implies in d as z; exrepnd; subst.

    apply verify_extend_signed_msg_list_implies in verif.
    apply implies_verify_sm_signed_msg2main in verif.

    (*
    pose proof (message_is_sent_before_deadline
                  e1 SMsys
                  (fun m => is_signed_msg m = true)
                  (fun n => is_lieutenant n = true)
                  (sm_signed_msg2main_auth_data m')
                  (sm_signed_msg2sender m')
                  (nat2pdt (S F) * (mu + tau))%dtime) as w.
    rewrite eqtrig1 in w; simpl in w.
    repeat (autodimp w hyp); autorewrite with sm; eauto 3 with sm eo.
    exrepnd.

    assert (loc e' = loc e2) as eqloc2' by (allrw; auto).*)

(*
XXXXXX
*)

    apply implies_authenticated_messages_were_sent_non_byz_usys in sendbyz.
    pose proof (sendbyz
                  e1
                  (sm_signed_msg2main_auth_data m')
                  (sm_signed_msg2sender m')) as w.
    rewrite eqloc1 in w; simpl in w.
    repeat (autodimp w hyp); eauto 3 with sm;
      try (complete (unfold auth_data_in_trigger; allrw; simpl; eauto 3 with eo sm));
      try (complete (rewrite sm_bare_signed_msg2general_sm_signed_msg2bare_eq; auto)).

    exrepnd.
    apply main_in_auth_data_implies_extend_signed_msg_list in w3; exrepnd; subst; simpl in *.
    autodimp w4 hyp;[].

    dup w4 as out.
    eapply lieutenant_output_signed_msg_implies in out; eauto; exrepnd; subst.

    (* [S F] could just be [F]*)
    assert (time e' <= nat2pdt (S F) * (mu + tau))%dtime as letime1.
    { eapply dt_le_trans;[eauto|].
      apply dt_mul_le_r; eauto 3 with eo;[].
      apply dt_nat_nat_inj_le; auto. }

    assert (loc e' = loc e2) as eqloc2' by (allrw; auto).

    (*
    *)

    assert (time e' < time e2)%dtime as letime2 by (eapply dt_le_lt_trans;[eauto|]; auto).

    pose proof (lt_time_implies_happened_before e' e2) as hb; repeat (autodimp hb hyp).
    eapply values_increase_on_before in hb; try exact out9; try exact eqst2.
    apply hb in out0.

    match goal with
    | [ H : extend_signed_msg_list ?a ?b = extend_signed_msg ?c ?d ?e |- _ ] =>
      assert (sm_signed_msg2value (extend_signed_msg_list a b)
              = sm_signed_msg2value (extend_signed_msg c d e)) as xx by (allrw; auto)
    end.
    autorewrite with sm in *.
    rewrite xx in *; tcsp.
  Qed.

  Lemma IC1_safety_aux :
    forall {eo : EventOrdering} (e1 e2 : Event) g1 g2 s1 s2 v,
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo SMsys
      -> AXIOM_messages_get_delivered eo SMsys
      -> AXIOM_verified_authenticated eo
      -> AXIOM_all_correct_can_verify eo
      -> AXIOM_SMcorrect_keys eo
      -> AXIOM_exists_at_most_f_faulty [e1, e2] F
      -> nodes_have_correct_traces_before [g1, g2] [e1, e2]
      -> loc e1 = general g1
      -> loc e2 = general g2
      -> is_lieutenant g1 = true
      -> is_lieutenant g2 = true
      -> state_sm_before_event (SMreplicaSM g1) e1 = Some s1
      -> state_sm_before_event (SMreplicaSM g2) e2 = Some s2
      -> (nat2pdt (S F) * (mu + tau) < time e1)%dtime
      -> (nat2pdt (S F) * (mu + tau) < time e2)%dtime
      -> In v (V s1)
      -> ~ In v (V s2)
      -> g1 <> g2
      -> False.
  Proof.
    introv sendbyz deliv vauth cverif ckeys atmost ctraces;
      introv eqloc1 eqloc2 isl1 isl2 eqst1 eqst2 lttime1 lttime2;
      introv vcond1 vcond2 gd.

    pose proof (value_was_received_before g1 v e1 s1) as h.
    repeat (autodimp h hyp); exrepnd; subst.

    assert (loc e' = general g1) as eqloc' by (allrw <-; eauto 3 with eo).
    assert (keys e' = local_keys s') as eqks by (eapply ckeys; eauto 3 with eo).

    destruct (in_dec gen_deq g2 (sm_signed_msg2senders m)) as [d|d].

    {
      (* [g2] is one of the generals who signed the message *)

      pose proof (nodes_have_correct_traces_before_two_implies_causal_left e1 e2 e' g1 g2) as cle.
      repeat (autodimp cle hyp).
      apply (sm_received_msg_was_sent e' e2 m g1 g2 s2); auto; try congruence.
    }

    {
      (* [g2] didn't sign the message *)

      pose proof (nodes_have_correct_traces_before_two_implies_causal_le_right e1 e2 e2 g1 g2) as ce2.
      repeat (autodimp ce2 hyp); eauto 2 with eo.

      rename_hyp_with message_is_on_time ontime.
      applydup message_is_on_time_implies_sm_signed_msg2signs in ontime.
      applydup message_is_on_time_implies_qle in ontime.

      apply le_lt_or_eq in ontime0; repndors.

      {
        (* [m] is signed by strictly less than [F+1] generals *)

        pose proof (send_value e' g1 m s' (add_to_V s' (sm_signed_msg2value m))) as inout.
        repeat (autodimp inout hyp); simpl; tcsp;[].

        assert (In (general g2) (names_not_in_list (g1 :: sm_signed_msg2senders m))) as g2i.
        {
          apply implies_general_in_names_not_in_list; simpl.
          introv xx; repndors; subst; tcsp.
        }

        match goal with
        | [ H : In ?m (output_system_on_event_ldata _ _) |- _ ] =>
          pose proof (deliv e' m (general g2)) as dlv
        end.
        repeat (autodimp dlv hyp); eauto 3 with eo sm.

        {
          exists e2; dands; eauto 3 with eo.
          eapply time_plus_mu_tau_le; eauto.
        }

        simpl in *.
        exrepnd.
        apply (IC1_aux e'0 e2 e' s2 s' g1 g2 m); auto; try omega; eauto 3 with eo sm.
      }

      {
        (* [m] is signed by exactly [F+1] generals.
             There must be 1 correct general among those [F+1] generals. *)

        assert (length (sm_signed_msg2senders m) = S F) as lensenders.
        { rewrite <- length_sm_signed_msg2signs_eq_length_sm_signed_msg2senders; auto. }

        pose proof (there_is_one_correct_before eo (sm_signed_msg2senders m) [e1,e2] F) as cor.
        repeat (autodimp cor hyp); simpl in *; try omega; eauto 3 with sm;[].
        exrepnd.

        pose proof (cor0 e1) as cor2; autodimp cor2 hyp.
        pose proof (cor0 e2) as cor3; autodimp cor3 hyp.
        clear cor0.

        applydup in_sm_signed_msg2senders_implies in cor1 as z; exrepnd; subst.
        rename_hyp_with verify_signed_msg verf.
        applydup verify_extend_signed_msg_list_implies in verf as verif.
        apply implies_authenticated_messages_were_sent_non_byz_usys in sendbyz.
        pose proof (sendbyz
                      e'
                      (sm_signed_msg2main_auth_data m')
                      (sm_signed_msg2sender m')) as w.
        rewrite eqloc', eqks in w; simpl in w.
        repeat (autodimp w hyp); eauto 3 with sm;
          try (complete (unfold auth_data_in_trigger; allrw; simpl; eauto 3 with eo sm));
          try (complete (rewrite sm_bare_signed_msg2general_sm_signed_msg2bare_eq; auto));[].

        exrepnd.
        apply main_in_auth_data_implies_extend_signed_msg_list in w3; exrepnd; subst; simpl in *.
        autodimp w4 hyp;[].

        remember (is_lieutenant (sm_signed_msg2sender m')) as b; symmetry in Heqb; destruct b.

        {
          (* the sender of [m'] is a lieutenant *)

          dup w4 as out.
          eapply lieutenant_output_signed_msg_implies in out; eauto; exrepnd; subst;[].

          pose proof (extend_signed_msg_list_eq_extend_signed_msg_implies_if_no_repeats
                        l0 m' v (local_keys s0) (local_keys s0)) as xx.
          repeat (autodimp xx hyp); subst l0; simpl in *;[].

          assert (time e'0 <= nat2pdt F * (mu + tau))%dtime as letime1.
          { eapply dt_le_trans;[eauto|].
            apply dt_mul_le_r; eauto 3 with eo.
            apply dt_nat_nat_inj_le; auto. }

          assert (In (general g2) (names_not_in_list (sm_signed_msg2sender m' :: sm_signed_msg2senders v))) as gi2.
          {
            apply implies_general_in_names_not_in_list; simpl.
            introv xx; repndors; subst; tcsp;[].
            destruct d.
            rewrite sm_signed_msg2senders_extend_signed_msg_list.
            apply in_app_iff; left.
            rewrite out3; simpl; apply in_snoc; tcsp.
          }

          match goal with
          | [ H : In ?m (output_system_on_event_ldata _ _) |- _ ] =>
            pose proof (deliv e'0 m (general g2)) as dlv
          end.
          repeat (autodimp dlv hyp); simpl; eauto 3 with eo sm.

          {
            exists e2; dands; eauto 3 with eo.
            eapply time_plus_mu_tau_le; eauto.
          }

          simpl in *; exrepnd.
          autorewrite with sm in *.

          assert (sm_signed_msg2value m' = sm_signed_msg2value v) as eqv.
          { rewrite out3; simpl; auto. }

          assert (~ In (sm_signed_msg2value v) (V s2)) as ni1.
          { rewrite <- eqv; tcsp. }

          assert (~ In g2 (sm_signed_msg2senders v)) as ni2.
          { intro xx; destruct d.
            rewrite sm_signed_msg2senders_extend_signed_msg_list.
            apply in_app_iff; left.
            rewrite out3; simpl; apply in_snoc; tcsp. }

          pose proof (IC1_aux e'1 e2 e'0 s2 s0 (sm_signed_msg2sender m') g2 v) as xx.
          repeat (autodimp xx hyp); eauto 3 with eo sm; try omega; try congruence.
        }

        {
          (* the sender of [m'] is the commander *)

          applydup is_lieutenant_false_implies_is_commander in Heqb.
          dup w4 as out.
          eapply commander_output_signed_msg_implies in out; eauto; exrepnd; subst.

          pose proof (snoc_cases l0) as cs; repndors; exrepnd; subst; tcsp;[|];
            [|rewrite extend_signed_msg_list_snoc in *; inversion out3];[].
          simpl in *; subst; simpl in *; autorewrite with sm in *.
          rewrite sm_signed_msg2senders_extend_signed_msg_list in *; simpl in *.
          rewrite sm_signed_msg2signs_extend_signed_msg_list in *; simpl in *.

          clear cor1 Heqb Heqb0.
          apply not_or in d; repnd.

          assert (In (general g2) (names_not_in_list [SMcommander])) as nig2.
          { apply implies_general_in_names_not_in_list; simpl.
            introv xx; repndors; subst; tcsp. }

          match goal with
          | [ H : In ?m (output_system_on_event_ldata _ _) |- _ ] =>
            pose proof (deliv e'0 m (general g2)) as dlv
          end.
          repeat (autodimp dlv hyp); simpl; eauto 3 with eo sm.

          {
            exists e2; dands; eauto 3 with eo.
            rewrite out5; rewrite dt_add_0_l.
            eapply dt_le_trans;[|apply dt_lt_le_weak;eauto];[].
            rewrite <- dt_mul_1_l at 1.
            apply dt_mul_le_compat_r; eauto 3 with eo dtime;[].
            apply dt_nat_nat_inj_le; try omega.
          }

          simpl in *.
          exrepnd.

          rewrite out5 in *.
          rewrite dt_add_0_l in dlv0.

          assert (g2 <> SMcommander) as dgc.
          { introv xx; subst; tcsp. }

          clear nig2.

          assert (time e'1 < time e2)%dtime as lttime'.
          { eapply dt_le_lt_trans;[|eauto].
            eapply dt_le_trans;[eauto|].
            rewrite <- dt_mul_1_l at 1.
            apply dt_mul_le_r; eauto 3 with eo; simpl;[].
            apply dt_nat_nat_inj_le; try omega. }

          pose proof (lt_time_implies_happened_before e'1 e2) as hb2.
          repeat (autodimp hb2 hyp); try congruence;[].

          pose proof (state_sm_on_event_some_between4 e'1 e2 (SMreplicaSM g2) s2) as eqst'.
          repeat (autodimp eqst' hyp);[].
          destruct eqst' as [s'1 eqst'].

          pose proof (state_sm_before_event_some_between3 e'1 e'1 (SMreplicaSM g2) s'1) as eqst''.
          repeat (autodimp eqst'' hyp); eauto 3 with eo;[].
          destruct eqst'' as [s'0 eqst''].

          pose proof (ckeys e'0 SMcommander s) as k1.
          repeat (autodimp k1 hyp); eauto 3 with eo;[].

          pose proof (ckeys e'1 g2 s'0) as k2.
          repeat (autodimp k2 hyp); eauto 3 with eo;[ ].

          pose proof (verified_authenticated_implies vauth e'0 e'1) as vad.
          repeat (autodimp vad hyp); eauto 3 with eo; try (complete (allrw; eauto 3 with eo));[].

          rewrite k1, k2, w1, dlv1 in vad.

          pose proof (values_increase_on_before e'1 e2 g2 s'1 s2) as ss.
          repeat (autodimp ss hyp);[].

          pose proof (sm_msg_signed_commander_trigger_implies_in_V e'1 g2 s'0 s'1 (init s) (local_keys s)) as inv.
          repeat (autodimp inv hyp); eauto 3 with eo;
            try (complete (exists e'0 s; dands; auto)).
        }
      }
    }
  Qed.

  Lemma result_from :
    forall {eo : EventOrdering} (e : Event) g v,
      loc e = general g
      -> In (send_sm_msg_result g (sm_msg_result v)) (output_system_on_event_ldata SMsys e)
      ->
      exists s,
        state_sm_before_event (SMreplicaSM g) e = Some s
        /\ trigger_op e = Some sm_msg_alarm
        /\ is_lieutenant g = true
        /\ (nat2pdt (S F) * (mu + tau) < time e)%dtime
        /\ v = sm_choice (V s).
  Proof.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_sm_ind3.
    inversion h1; subst; eexists; dands; eauto.
  Qed.

  Lemma learned_sm_msg_signed :
    forall {eo : EventOrdering} (e : Event) i,
      knows_i e i
      -> ~ knew_i e i
      ->
      exists m,
        trigger_op e = Some (sm_msg_signed m)
        /\ i = sm_signed_msg2value m
        /\ message_is_on_time m (time e) = true.
  Proof.
    introv kno kne; simpl in *.
    unfold knows_i, knew_i in *; exrepnd.
    rewrite state_sm_on_event_unroll2 in kno1.

    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q1; symmetry in Heqq1
    end.
    destruct q1; simpl in *; ginv; tcsp;[].

    assert (~sm_knows_i i l) as w.
    { intro xx; destruct kne; eexists; eexists; dands; eauto. }
    clear kne.

    remember (trigger_op e) as trig1; symmetry in Heqtrig1.
    destruct trig1; unfold op_state in *; simpl in *; tcsp.
    unfold SMupdate in *.
    destruct m; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends;
        try (complete (repndors; tcsp; ginv));
        try (complete (unfold broadcast2others in *; ginv));
        try (complete (eexists; dands; eauto; unfold add_to_V, sm_knows_i in *; simpl in *; repndors; tcsp)).
  Qed.


  Lemma IC1_safety_loc_before :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      loc e1 = general g
      -> loc e2 = general g
      -> state_sm_before_event (SMreplicaSM g) e1 = Some s1
      -> state_sm_before_event (SMreplicaSM g) e2 = Some s2
      -> (nat2pdt (S F) * (mu + tau) < time e1)%dtime
      -> sm_choice (V s1) <> sm_choice (V s2)
      -> e1 ⊏ e2
      -> False.
  Proof.
    introv eqloc1 eqloc2 eqst1 eqst2 ltt1 dc tri.

    pose proof (values_increase_before e1 e2 g s1 s2) as w; repeat (autodimp w hyp); eauto 3 with eo;[].
    apply sm_choice_diff in dc; destruct dc as [dc vcond].
    repndors; repnd.
    { apply w in vcond0; tcsp. }
    clear w.

    pose proof (information_acquired_between_knew e1 e2 dc) as kno; repeat (autodimp kno hyp);
      try (apply sm_know_i_dec);[| |].
    { pose proof (implies_not_knew_i e1 dc g s1) as w; apply w; auto. }
    { pose proof (implies_knew_i e2 dc g s2) as w; apply w; auto. }
    exrepnd.

    pose proof (learned_sm_msg_signed e dc) as lrn; repeat (autodimp lrn hyp); exrepnd; subst.
    applydup message_is_on_time_implies_qle in lrn0 as tm.
    applydup message_is_on_time_implies_sm_signed_msg2signs in lrn0 as sn.
    apply happened_before_le_implies_le_time in kno2.
    eapply dt_lt_le_trans in ltt1;[|exact kno2].
    eapply dt_lt_le_trans in ltt1;[|exact tm].
    apply dt_mul_lt_r_lt in ltt1; eauto 3 with eo dtime;[].
    apply dt_nat_inj_lt_nat in ltt1; try omega.
  Qed.

  Lemma IC1_safety :
    forall (eo    : EventOrdering)
           (e1 e2 : Event)
           (v1 v2 : sm_value)
           (g1 g2 : Gen),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo SMsys
      -> AXIOM_messages_get_delivered eo SMsys
      -> AXIOM_verified_authenticated eo
      -> AXIOM_all_correct_can_verify eo
      -> AXIOM_SMcorrect_keys eo
      -> AXIOM_exists_at_most_f_faulty [e1,e2] F
      -> nodes_have_correct_traces_before [g1,g2] [e1,e2]
      -> loc e1 = general g1
      -> loc e2 = general g2
      -> In (send_sm_msg_result g1 (sm_msg_result v1)) (output_system_on_event_ldata SMsys e1)
      -> In (send_sm_msg_result g2 (sm_msg_result v2)) (output_system_on_event_ldata SMsys e2)
      -> v1 = v2.
  Proof.
    introv sendbyz deliv vauth cverif ckeys atmost ctraces;
      introv eqloc1 eqloc2 out1 out2.

    destruct (sm_value_deq v1 v2) as [v|v]; auto.
    assert False; tcsp.

    apply result_from in out1; auto.
    apply result_from in out2; auto.
    exrepnd.
    rename s0 into s1.
    rename s  into s2.
    subst.

    destruct (gen_deq g1 g2) as [gd|gd].

    {
      pose proof (tri_if_same_loc e1 e2) as tri; autodimp tri hyp; try (complete (allrw; auto));[].
      repndors; subst; tcsp;
        [eapply IC1_safety_loc_before; try exact tri; eauto
        |rewrite out1 in *; ginv; tcsp
        |eapply IC1_safety_loc_before; try exact tri; eauto].
    }

    apply sm_choice_diff in v; destruct v as [v vcond].

    repndors; repnd.

    { apply (IC1_safety_aux e1 e2 g1 g2 s1 s2 v); auto. }

    { apply (IC1_safety_aux e2 e1 g2 g1 s2 s1 v); auto; eauto 3 with eo. }
  Qed.

End IC1.
