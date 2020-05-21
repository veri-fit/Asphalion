(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
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

  Definition is_initial_value {eo : EventOrdering} (e : Event) (v : sm_value) :=
    exists s g,
      loc e = general g
      /\ state_sm_before_event (SMreplicaSM g) e = Some s
      /\ v = init s.

  Lemma implies_is_initial_value :
    forall {eo : EventOrdering} (e : Event) (v : sm_value) g s,
      loc e = general g
      -> state_sm_before_event (SMreplicaSM g) e = Some s
      -> v = init s
      -> is_initial_value e v.
  Proof.
    introv eqloc eqst eqv; exists s g; dands; auto.
  Qed.
  Hint Resolve implies_is_initial_value : sm.

  Definition sm_signed_msg2size m := length (sm_signed_msg2signs m).

  Lemma message_is_on_time_implies_on_time :
    forall {eo : EventOrdering} (e : Event) d,
      message_is_on_time d (time e) = true
      -> on_time e d sm_signed_msg2size (S F).
  Proof.
    introv ontime.
    unfold message_is_on_time, on_time in *; smash_sm.
  Qed.
  Hint Resolve message_is_on_time_implies_on_time : sm.

  Lemma on_time_implies_message_is_on_time :
    forall {eo : EventOrdering} (e : Event) d,
      on_time e d sm_signed_msg2size (S F)
      -> message_is_on_time d (time e) = true.
  Proof.
    introv ontime.
    unfold message_is_on_time, on_time in *; smash_sm.
    eapply dt_lt_le_trans in d0;[|eauto].
    apply dt_lt_irrefl in d0; tcsp.
  Qed.
  Hint Resolve on_time_implies_message_is_on_time : sm.

  Lemma implies_learns_on_time :
    forall {eo : EventOrdering} (e : Event) v s n,
      AXIOM_SMcorrect_keys eo
      -> loc e = general n
      -> state_sm_before_event (SMreplicaSM n) e = Some s
      -> trigger_op e = Some (sm_msg_signed v)
      -> verify_signed_msg n (local_keys s) v = true
      -> message_is_on_time v (time e) = true
      -> learns_on_time e v sm_signed_msg2size (S F).
  Proof.
    introv ckeys eqloc eqst trig verif ontime.
    unfold learns_on_time.
    allrw; simpl.
    exists n; dands; auto; eauto 3 with sm;[].
    unfold sm_verify.
    rewrite eqloc; simpl.
    pose proof (ckeys e n s) as ckeys.
    repeat (autodimp ckeys hyp); eauto 3 with eo.
    rewrite ckeys; auto.
  Qed.
  Hint Resolve implies_learns_on_time : sm.

  Definition is_commander_e {eo : EventOrdering} (e : Event) :=
    exists g,
      loc e = general g
      /\ is_commander g = true.

  Definition is_lieutenant_e {eo : EventOrdering} (e : Event) :=
    exists g,
      loc e = general g
      /\ is_lieutenant g = true.

  Lemma implies_is_commander_e :
    forall {eo : EventOrdering} (e : Event) g,
      loc e = general g
      -> is_commander g = true
      -> is_commander_e e.
  Proof.
    introv eqloc isc; exists g; dands; auto.
  Qed.
  Hint Resolve implies_is_commander_e : sm.

  Lemma implies_is_lieutenant_e :
    forall {eo : EventOrdering} (e : Event) g,
      loc e = general g
      -> is_lieutenant g = true
      -> is_lieutenant_e e.
  Proof.
    introv eqloc isc; exists g; dands; auto.
  Qed.
  Hint Resolve implies_is_lieutenant_e : sm.

  Lemma is_lieutenant_e_implies_not_is_commander_e :
    forall {eo : EventOrdering} (e : Event),
      is_lieutenant_e e -> ~ is_commander_e e.
  Proof.
    introv h q.
    unfold is_lieutenant_e, is_commander_e in *; exrepnd.
    rewrite h1 in *; ginv.
    unfold is_lieutenant in *.
    rewrite q0 in *; simpl in *; ginv.
  Qed.

  Lemma implies_is_commander_e_com :
    forall {eo : EventOrdering} (e : Event),
      loc e = general SMcommander
      -> is_commander_e e.
  Proof.
    introv eqloc; eapply implies_is_commander_e; eauto.
    unfold is_commander; simpl; dest_cases w.
  Qed.
  Hint Resolve implies_is_commander_e_com : sm.

  Lemma is_commander_e_local_pred :
    forall {eo : EventOrdering} (e : Event),
      is_commander_e (local_pred e)
      <-> is_commander_e e.
  Proof.
    introv; unfold is_commander_e; split; intro h; exrepnd; eexists; dands; eauto;
      autorewrite with eo in *; auto.
  Qed.
  Hint Rewrite @is_commander_e_local_pred : sm.

  Lemma value_was_received :
    forall v {eo : EventOrdering} (e : Event),
      AXIOM_SMcorrect_keys eo
      -> knows_i e v
      -> exists e',
          e' ⊑ e
          /\ knows_i e' v
          /\ didnt_know_i e' v
          /\
          (
            (exists m,
                learns_on_time e' m sm_signed_msg2size (S F)
                /\ v = sm_signed_msg2value m
            )
            \/
            (
              trigger_op e' = Some sm_msg_init
              /\ is_initial_value e' v
              /\ (time e' == nat2pdt 0)%dtime
              /\ is_commander_e e
            )
          ).
  Proof.
    intros v eo e ckeys.
    unfold knows_i, didnt_know_i; simpl.
    unfold sm_knows_i; simpl.
    introv h; exrepnd.
    revert dependent mem.
    induction e as [? ind] using predHappenedBeforeInd_local_pred;[].
    introv i eqst.

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
                         exists e; dands; eauto 3 with sm eo;
                         try (complete (eexists; eexists; dands; eauto; simpl; tcsp));
                         try (complete (eexists; eexists; dands; eauto 3 with sm eo));
                         left; exists v0; dands; eauto 3 with sm;
                         allrw; try (assert (1 = S F) as xx by omega; rewrite xx);
                         eapply implies_learns_on_time; eauto));[].

    { repndors; subst; try (smash_sm_ind ind).
      exists e; dands; eauto 3 with sm eo;
        try (complete (eexists; eexists; dands; eauto; simpl; tcsp));
        try (complete (eexists; eexists; dands; eauto 3 with sm eo)).
      { eexists; eexists; dands; eauto.
        apply time_zero_implies_first in d.
        rewrite state_sm_before_event_as_initial in Heqsop; auto; ginv. }
      right; dands; auto; eauto 3 with eo sm. }
  Qed.

  Lemma value_was_received_before :
    forall v {eo : EventOrdering} (e : Event),
      AXIOM_SMcorrect_keys eo
      -> knew_i e v
      -> exists e',
          e' ⊏ e
          /\ knows_i e' v
          /\ didnt_know_i e' v
          /\
          (
            (exists m,
                learns_on_time e' m sm_signed_msg2size (S F)
                /\ v = sm_signed_msg2value m)
            \/
            (trigger_op e' = Some sm_msg_init
             /\ is_initial_value e' v
             /\ (time e' == nat2pdt 0)%dtime
             /\ is_commander_e e)
          ).
  Proof.
    introv ckeys kn.
    applydup knew_i_implies_not_first in kn.
    apply knew_i_implies_knows_i in kn.
    eapply value_was_received in kn;[|eauto]; exrepnd.
    autorewrite with sm eo in *.
    exists e'; dands; eauto 3 with eo.
  Qed.

  Fixpoint extend_signed_msg_list
           (m : sm_signed_msg)
           (l : sm_signs) : sm_signed_msg :=
    match l with
    | [] => m
    | s :: l => extend_signed_msg_list (sm_signed_msg_cons m s) l
    end.

  Lemma extend_data_list_as_extend_signed_msg_list :
    forall l d,
      dis_extend_lak_data_list d l
      = extend_signed_msg_list d l.
  Proof.
    induction l; simpl; tcsp.
  Qed.

  (* Q : I managed to prove this one based on the one that we have on the knowledge level.
     Should we prove this or the original proof? *)
  Lemma extend_signed_msg_list_snoc :
    forall l m a,
      extend_signed_msg_list m (snoc l a)
      = sm_signed_msg_cons (extend_signed_msg_list m l) a.
  Proof.
    introv.
    rewrite <- extend_data_list_as_extend_signed_msg_list.
    rewrite dis_extend_lak_data_list_snoc; auto.
  Qed.

  Lemma sm_signed_msg2senders_eq_dis_data2senders :
    forall m,
      sm_signed_msg2senders m = dis_data2senders m.
  Proof.
    induction m; simpl in *; ginv; subst; tcsp;[].

    rewrite IHm. clear IHm.
    unfold dis_data2senders. simpl in *.
    unfold dis_data2signs. simpl in *.
    rewrite <- map_snoc.
    f_equal.
    rewrite map_snoc. simpl in *. eauto.
  Qed.

  Lemma sm_signed_msg2sender_eq_dis_data2sender :
    forall m,
      sm_signed_msg2sender m = dis_data2sender m.
  Proof.
    induction m; simpl in *; ginv; subst; tcsp.
  Qed.


  (* Q : I managed to prove this one based on the one that we have on the knowledge level.
     Should we prove this or the original proof? *)
  Lemma in_sm_signed_msg2senders_implies :
    forall g m,
      In g (sm_signed_msg2senders m)
      ->
      exists m' l,
        sm_signed_msg2sender m' = g
        /\ m = extend_signed_msg_list m' l.
  Proof.
    introv H.
    pose proof (dis_in_lak_data2senders_implies g m) as xx.
    rewrite sm_signed_msg2senders_eq_dis_data2senders in H.
    autodimp xx hyp.

    (* original proof
    induction m; introv i; simpl in *; repndors; subst; tcsp.

    - exists (sm_signed_msg_sing v a) ([] : sm_signs); simpl; tcsp.

    - allrw @in_snoc; repndors; subst; tcsp.

      + apply IHm in i; clear IHm; exrepnd; subst; simpl in *.
        exists m' (snoc l a); simpl; dands; auto.
        rewrite extend_signed_msg_list_snoc; auto.

      + exists (sm_signed_msg_cons m a) ([] : sm_signs); simpl; tcsp.
     *)
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


  Lemma sm_signed_msg_eq_dis_data2signs :
    forall m,
      sm_signed_msg2signs m = dis_data2signs m.
  Proof.
    induction m; simpl in *; ginv; subst; tcsp;[].

    rewrite IHm. clear IHm.
    unfold dis_data2signs. simpl in *.
    rewrite map_snoc.
    simpl in *. eauto.
  Qed.



  (* Q : I managed to prove this one based on the one that we have on the knowledge level.
     Should we prove this or the original proof? *)
  Lemma length_sm_signed_msg2signs_eq_length_sm_signed_msg2senders :
    forall m,
      length (sm_signed_msg2signs m)
      = length (sm_signed_msg2senders m).
  Proof.
    introv.
    rewrite sm_signed_msg_eq_dis_data2signs.
    rewrite sm_signed_msg2senders_eq_dis_data2senders.
    erewrite dis_length_lak_data2signs_eq_length_lak_data2senders. eauto.

    (* original proof
    induction v; simpl; tcsp; autorewrite with list; allrw; auto. *)
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

  (* IVANA ...
 Q: Do we need something like this?
  Lemma SM_length_sign_less_then_max_sign :
    forall eo, AXIOM_length_sign_less_then_max_sign eo.
  Proof.
    introv.
    unfold AXIOM_length_sign_less_then_max_sign.
    unfold dis_max_sign. simpl in *.
    unfold sm_max_sign.
    induction d; simpl in *; ginv; subst; tcsp;[|].
    {
      SearchAbout (?a < _ + ?a).
  Abort. *)

  Lemma SM_knows_implies_in : AXIOM_knows_implies_in.
  Proof.
    introv h. tcsp.
  Qed.
  Hint Resolve SM_knows_implies_in : sm.

  Fixpoint sm_signed_msg2sm_signed_sing (m : sm_signed_msg) : sm_signed_msg :=
    match m with
    | sm_signed_msg_sing v a => m
    | sm_signed_msg_cons v _ => sm_signed_msg2sm_signed_sing v
    end.

  Lemma sender_bare_sm_signed_msg2sm_signed_sing_eq :
    forall m,
      sm_bare_signed_msg2general (sm_signed_msg2bare (sm_signed_msg2sm_signed_sing m))
      = general (sign_name (snd (sm_signed_msg2sing m))).
  Proof.
    induction m; simpl; tcsp.
  Qed.


  Lemma sm_bare_signed_msg2general_sm_signed_msg2bare_eq :
    forall m,
      sm_bare_signed_msg2general (sm_signed_msg2bare m)
      = general (sm_signed_msg2sender m).
  Proof.
    introv; destruct m; simpl; tcsp;
      unfold sm_signed_msg2sender; simpl;
        destruct a as [name tok]; simpl; tcsp;
          destruct name; simpl; auto.
  Qed.
  Hint Rewrite sm_bare_signed_msg2general_sm_signed_msg2bare_eq : sm.

  Lemma SM_data_auth_eq : AXIOM_data_auth_eq.
  Proof.
    introv. simpl in *.
    erewrite sm_bare_signed_msg2general_sm_signed_msg2bare_eq.
    simpl in *. tcsp.
  Qed.
  Hint Resolve SM_data_auth_eq : sm.

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

  Lemma SM_values_increase_step :
    forall eo, AXIOM_values_increase_step eo.
  Proof.
    introv.
    unfold AXIOM_values_increase_step.
    prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers4 smash_sm_ind3.
  Qed.
  Hint Rewrite SM_values_increase_step : sm.

  Lemma SM_values_increase_before :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      e1 ⊑ e2
      -> state_sm_before_event (SMreplicaSM g) e1 = Some s1
      -> state_sm_before_event (SMreplicaSM g) e2 = Some s2
      -> subset (V s1) (V s2).
  Proof.
    introv h1 h2 h3.
    pose proof (dis_values_increase_before e1 e2 g s1 s2) as xx.
    repeat (autodimp xx hyp); [].
    eapply SM_values_increase_step.
  Qed.
  Hint Resolve SM_values_increase_before : sm.

  Lemma SM_values_increase_on :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      e1 ⊑ e2
      -> state_sm_on_event (SMreplicaSM g) e1 = Some s1
      -> state_sm_on_event (SMreplicaSM g) e2 = Some s2
      -> subset (V s1) (V s2).
  Proof.
    introv h1 h2 h3.
    pose proof (dis_values_increase_on e1 e2 g s1 s2) as xx.
    repeat (autodimp xx hyp); [].
    eapply SM_values_increase_step.
  Qed.


  Lemma SM_values_increase_on_before :
    forall {eo : EventOrdering} (e1 e2 : Event) g s1 s2,
      e1 ⊏ e2
      -> state_sm_on_event (SMreplicaSM g) e1 = Some s1
      -> state_sm_before_event (SMreplicaSM g) e2 = Some s2
      -> subset (V s1) (V s2).
  Proof.
    introv lte eqst1 eqst2.
    pose proof (dis_values_increase_on_before e1 e2 g s1 s2) as xx.
    repeat (autodimp xx hyp); [].
    eapply SM_values_increase_step.
  Qed.
  Hint Resolve SM_values_increase_on_before : sm.

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


  Lemma length_sm_signed_msg2signs_S_F_length_dis_data2signs_dis_max_sign :
    forall m,
      length (sm_signed_msg2signs m) = S F
      -> length (dis_data2signs m) = dis_max_sign.
  Proof.
    introv H. simpl in *.
    unfold sm_max_sign.
    rewrite Nat.add_1_r.
    erewrite <- sm_signed_msg_eq_dis_data2signs. eauto.
  Qed.
  Hint Resolve length_sm_signed_msg2signs_S_F_length_dis_data2signs_dis_max_sign : sm.

  Lemma dis_max_signs_eq_S_F :
    dis_max_sign = S F.
  Proof.
    unfold dis_max_sign. simpl in *.
    unfold sm_max_sign.
    rewrite Nat.add_1_r. eauto.
  Qed.


  Lemma message_is_on_time_abstract :
    forall m t,
      message_is_on_time m t = true
      -> dis_message_is_on_time m t = true.
  Proof.
    introv H.
    unfold message_is_on_time, dis_message_is_on_time in *.
    rewrite <- sm_signed_msg_eq_dis_data2signs.
    rewrite dis_max_signs_eq_S_F. simpl in *. eauto.
  Qed.



  (* Q : I managed to prove this one based on the one that we have on the knowledge level.
     Should we prove this or the original proof? *)
  Lemma message_is_on_time_implies_sm_signed_msg2signs :
    forall m t,
      message_is_on_time m t = true
      -> length (sm_signed_msg2signs m) <= S F.
  Proof.
    introv h.
    pose proof (dis_message_is_on_time_implies_dis_data2signs m t) as xx.
    autodimp xx hyp; eauto;[apply message_is_on_time_abstract; eauto
                           | rewrite sm_signed_msg_eq_dis_data2signs in *; rewrite dis_max_signs_eq_S_F in xx; eauto].
      (* original proof
         introv h; unfold message_is_on_time in h; smash_sm. *)
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


  (* Q : I managed to prove this one based on the one that we have on the knowledge level.
     Should we prove this or the original proof? *)
  Lemma message_is_on_time_implies_qle :
    forall m t,
      message_is_on_time m t = true
      -> (t <= nat2pdt (length (sm_signed_msg2signs m)) * (mu + tau))%dtime.
  Proof.
    introv h.
    pose proof (dis_message_is_on_time_implies_qle m t) as xx.
    autodimp xx hyp; eauto;[apply message_is_on_time_abstract; eauto
                           |rewrite sm_signed_msg_eq_dis_data2signs in *; eauto ].
  (* original proof
    introv h.
    unfold message_is_on_time in h; smash_sm. *)
  Qed.

  Lemma sm_extend_data_as_extend_signed_msg :
    forall m n ks,
      sm_extend_data m (MkSign n (SMcreate (sm_data2data m n) (map dsk_key (lkm_sending_keys ks))))
      = extend_signed_msg m (node2name n) ks.
  Proof.
    tcsp.
  Qed.

  Lemma sm_signed_msg2size_strictly_pos :
    forall m, 1 <= sm_signed_msg2size m.
  Proof.
    induction m; introv; simpl; auto.
    unfold sm_signed_msg2size; simpl; autorewrite with list; auto.
  Qed.

  (* This is protocol dependent *)
  Lemma SM_learns_new_on_time_implies_disseminate :
    forall {eo : EventOrdering},
      AXIOM_SMcorrect_keys eo
      -> AXIOM_learns_new_on_time_implies_disseminate
           eo
           (fun n => is_lieutenant n = true)
           sm_signed_msg2size (S F).
  Proof.
    introv ckeys isl eqloc jl.
    destruct jl as [lrn [kn [dkn len]]].

    unfold knows, didnt_know in *; exrepnd.
    rewrite eqloc in *; ginv; simpl in *.
    rewrite sm_extend_data_as_extend_signed_msg.
    rewrite <- sm_signed_msg2senders_eq_dis_data2senders.
    unfold disseminate_top_to_except; simpl.
    unfold disseminate_top_to_list; simpl.
    eexists; dands;[|apply subset_refl].

    pose proof (ckeys e n0 mem) as ckeys.
    repeat (autodimp ckeys hyp); eauto 3 with eo;[].

    eapply in_output_system_on_event_ldata; eauto.

    rw @loutput_sm_on_event_unroll2.
    rewrite state_sm_on_event_unroll2 in kn1.

    fold (@DirectedMsgs _ _ _) in *.
    simpl in *.

    pose proof (length_sm_signed_msg2signs_eq_length_sm_signed_msg2senders m) as eqlen.

    unfold sm_sys, SMsys.
    rewrite dkn1 in *; simpl in *.

    unfold learns_on_time in *; exrepnd.
    rewrite eqloc in *; ginv; simpl in *.
    rename_hyp_with sm_data2msg eqtrig.

    pose proof (sm_signed_msg2size_strictly_pos m) as pos.

    rewrite eqtrig in *; simpl in *.
    unfold op_state in *; simpl in *.
    unfold SMhandler_lieutenant in *.

    smash_sm; repndors; tcsp; try omega; GC;
      try (complete (rewrite ckeys; auto));
      try (complete (unfold sm_signed_msg2size in *; try omega));
      try (complete (left;
                     rename_hyp_with is_sm_signed_msg2directly_from_commander fc;
                     applydup is_sm_signed_msg2directly_from_commander_implies_senders_eq in fc; allrw; simpl; auto)).
  Qed.
  Hint Resolve SM_learns_new_on_time_implies_disseminate : sm.

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
             (sm_signed_msg2main_auth_data (sm_signed_msg_cons m (MkSign (General2Gen g') (authenticate (sm_bare_msg_signed (sm_bare_signed_msg_cons m g')) ks'))))
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

  Lemma implies_general_in_names_not_in_list :
    forall g l,
      ~In g l
      -> In (general g) (names_not_in_list l).
  Proof.
    introv h.
    apply in_map.
    apply in_diff; dands; eauto 3 with sm.
  Qed.


  (* Q : I managed to prove this one based on the one that we have on the knowledge level.
     Should we prove this or the original proof? *)
  Lemma sm_signed_msg2senders_extend_signed_msg_list :
    forall l m,
      sm_signed_msg2senders (extend_signed_msg_list m l)
      = sm_signed_msg2senders m ++ (map sign_name l).
  Proof.
    introv.
    pose proof (dis_data2senders_extend_lak_data_list l m) as xx.
    rewrite <- extend_data_list_as_extend_signed_msg_list.
    rewrite sm_signed_msg2senders_eq_dis_data2senders.
    rewrite sm_signed_msg2senders_eq_dis_data2senders.
    eapply xx.

    (* original proof
    induction l using snoc_list_ind; introv; simpl in *; tcsp;
      autorewrite with list; auto.
    rewrite extend_signed_msg_list_snoc; simpl.
    rewrite map_snoc.
    rewrite app_snoc.
    rewrite IHl; autorewrite with list; auto. *)
  Qed.
  Hint Rewrite sm_signed_msg2senders_extend_signed_msg_list : sm.


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


  Lemma SM_dis_data2sender_in_senders :
    AXIOM_dis_data2sender_in_senders.
  Proof.
    introv.
    rewrite <- sm_signed_msg2senders_eq_dis_data2senders.
    rewrite <- sm_signed_msg2sender_eq_dis_data2sender.
    eauto 3 with sm.
  Qed.


  (* Q : I managed to prove this one based on the one that we have on the knowledge level.
     Should we prove this or the original proof? *)
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

    pose proof (dis_extend_lak_data_list_eq_extend_lak_data_implies_if_no_repeats l m v
                                                                                  (SMcreate (sm_bare_msg_signed (sm_bare_signed_msg_cons v (general (sm_signed_msg2sender m)))) (map dsk_key (lkm_sending_keys ks2))) ) as xx.
    eapply xx; [ apply SM_dis_data2sender_in_senders
               | rewrite <- sm_signed_msg2senders_eq_dis_data2senders; rewrite <- sm_signed_msg2sender_eq_dis_data2sender; eauto
               | rewrite extend_data_list_as_extend_signed_msg_list ; rewrite eqm; rewrite <- sm_signed_msg2sender_eq_dis_data2sender; tcsp ].

    (* original proof
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
    destruct verif0; apply in_app_iff; left; eauto 3 with sm. *)
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

    pose proof (SM_values_increase_on_before e1 e2 g2 s'0 s2) as ss.
    repeat (autodimp ss hyp).

    assert (In (sm_signed_msg2value m) (V s'0)) as ins'0;[|apply ss in ins'0; tcsp];[].

    assert (time e1 <= nat2pdt (S (length (sm_signed_msg2signs m))) * (mu + tau))%dtime as t.
    { eapply dt_le_trans;[eauto|].
      eapply time_plus_tau_le_aux; eauto. }

    unfold verify_signed_msg in *; smash_sm;[].

    pose proof (ckeys e g1 s) as k1.
    repeat (autodimp k1 hyp); eauto 3 with eo;[].
    rewrite <- k1 in verifd.

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
      = sign_name (snd (sm_signed_msg2sing m)).
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

  Lemma not_is_lieutenant_and_commander :
    forall g,
      is_lieutenant g = true
      -> is_commander g = true
      -> False.
  Proof.
    introv h q.
    unfold is_lieutenant in h.
    rewrite q in h; simpl in *; auto.
  Qed.

  (* TODO: fix broken abstractions *)
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
      pose proof (value_was_received_before w e) as q.
      repeat (autodimp q hyp); exrepnd;[|].
      { eexists; eexists; simpl; dands; eauto. }

      repndors; exrepnd; subst;
        [|assert (is_lieutenant_e e) as isl by eauto 3 with sm;
          apply is_lieutenant_e_implies_not_is_commander_e in isl; tcsp];[].

      applydup local_implies_loc in q1 as eqn.

      (* TODO: don't do that *)
      unfold didnt_know_i, knows_i in *; simpl in *; exrepnd.
      unfold sm_knows_i in *; simpl in *.
      unfold learns_on_time in *; exrepnd; simpl in *.
      unfold sm_verify in *; simpl in *.
      rename mem0 into s'.
      rename mem into s.
      rename q6 into eqloc'.
      rewrite eqloc, eqloc' in *; ginv; simpl in *.
      (* ==== *)

      pose proof (sendbyz
                    e'
                    (sm_signed_msg2main_auth_data (sm_signed_msg2sm_signed_sing m))
                    (sm_signed_msg2sender (sm_signed_msg2sm_signed_sing m))) as w.
      simpl in w.
      erewrite sender_of_sm_signed_msg2sm_signed_sing in w;[|eauto].
      erewrite sender_of_bare_sm_signed_msg2sm_signed_sing in w;[|eauto].
      repeat (autodimp w hyp); eauto 3 with eo sm.
      { unfold auth_data_in_trigger; allrw; simpl; eauto 3 with sm. }
      { rewrite eqloc'; eauto 3 with sm. }

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

      assert (v = init s0) as eqvs;[|subst; tcsp];[].
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

  (* MOVE *) (* Q: Why I can not replace this one with one that we have at the level of knowledge??? *)
(*  This one is actually never used
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
*)

  (* MOVE *) (* Q: Why I can not replace this one with one that we have at the level of knowledge??? *)
(* This one is actually never used
  Definition all_containers_satisfy_constraint (d : AuthenticatedData) (M : msg -> Prop) :=
    forall m,
      In d (get_contained_authenticated_data m)
      -> M(m) /\ is_protocol_message m = true. *)

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


 Lemma sm_data2main_auth_data_implies_sm_signed_msg2list_auth_data :
    forall m,
      In (sm_data2main_auth_data m) (sm_signed_msg2list_auth_data m).
  Proof.
    introv.
    destruct m; simpl in *; ginv; subst; tcsp.
    unfold sm_data2main_auth_data.
    eapply in_snoc. auto.
  Qed.
  Hint Resolve sm_data2main_auth_data_implies_sm_signed_msg2list_auth_data : sm.

  Lemma names_not_in_list_as_dis_names_not_in_list :
    forall l,
      names_not_in_list l
      = map general (nodes_not_in_list l).
  Proof.
    tcsp.
  Qed.

  (* TODO: turn this into an axiom *)
  Lemma lieutenant_disseminate_signed_msg_implies :
    forall {eo : EventOrdering} (e : Event) m g,
      AXIOM_SMcorrect_keys eo
      -> loc e = general g
      -> is_lieutenant g = true
      -> disseminate e m
      -> exists v l,
          disseminate_top_to_except e (extend_signed_msg v (general g) (keys e)) (g :: sm_signed_msg2senders v)
          /\ extend_signed_msg_list m l = extend_signed_msg v (general g) (keys e)
          /\ learns_on_time e v sm_signed_msg2size (S F)
          /\ length (sm_signed_msg2signs v) <= F
          /\ didnt_know e v
          /\ knows e v.
  Proof.
    introv ckeys eqloc isl i.
    unfold disseminate in i; exrepnd.
    destruct m0 as [msg l d]; simpl in *.
    fold (send_delayed_sm_msg_lieutenant msg l d) in *.
    applydup main_in_auth_data_implies_extend_signed_msg_list in i0; exrepnd.
    subst; simpl in *.
    applydup (lieutenant_output_signed_msg_implies e (extend_signed_msg_list m l0) l g d) in i1; auto.
    exrepnd; subst.

    pose proof (ckeys e g s1) as ckeys.
    repeat (autodimp ckeys hyp); eauto 3 with eo;[].
    rewrite <- ckeys in *.

    exists v l0.
    dands; auto.

    { eexists; dands; eauto; simpl.
      rewrite i5 in i1; auto. }

    { exists g; simpl; unfold sm_verify; rewrite eqloc; simpl; dands; auto.
      unfold on_time; dands; auto. }

    { exists s1 g; dands; auto. }

    { exists s2 g; dands; auto. }
  Qed.

  Lemma in_SMget_contained_auth_data_implies_protocol :
    forall a m,
      In a (SMget_contained_auth_data m)
      -> is_protocol_message m = true.
  Proof.
    introv i; destruct m; simpl in *; tcsp.
  Qed.
  Hint Resolve in_SMget_contained_auth_data_implies_protocol : sm.


  Lemma swap_ex :
    forall A B (P : A -> B -> Prop),
      (exists (a : A) (b : B), P a b)
      -> (exists (b : B) (a : A), P a b).
  Proof.
    introv h; exrepnd; eauto.
  Qed.

  Lemma sm_signed_msg2main_auth_data_eq_implies :
    forall d1 d2,
      sm_signed_msg2main_auth_data d1
      = sm_data2main_auth_data d2
      -> d1 = d2.
  Proof.
    introv h.
    unfold sm_data2main_auth_data in h.
    unfold sm_signed_msg2main_auth_data in h.
    destruct d1, d2; simpl in *; ginv;
      unfold sm_signed_msg2auth in *;
      destruct a, a0; simpl in *;
        inversion h; subst; auto.
  Qed.

  Lemma sm_data2main_auth_data_in_sm_signed_msg2list_auth_data_implies :
    forall d v,
      In (sm_data2main_auth_data d) (sm_signed_msg2list_auth_data v)
      -> sm_signed_msg2value v = sm_signed_msg2value d.
  Proof.
    induction v; introv i; simpl in *; repndors; tcsp.
    { apply sm_signed_msg2main_auth_data_eq_implies in i; subst; simpl; auto. }
    apply in_snoc in i; repndors; tcsp.
    symmetry in i.
    apply sm_signed_msg2main_auth_data_eq_implies in i; subst; simpl in *; auto.
  Qed.
  Hint Resolve sm_data2main_auth_data_in_sm_signed_msg2list_auth_data_implies : sm.

  Lemma SM_knows_if_disseminate :
    forall eo, AXIOM_knows_if_disseminate eo.
  Proof.
    introv eqloc diss.
    unfold disseminate in diss; exrepnd.
    unfold knows; simpl in *.
    unfold sm_knows in *.
    unfold sm_sys in *.

    eapply in_output_system_on_event_ldata in diss1; eauto.
    unfold SMsys in diss1.

    apply swap_ex.
    exists n.

    rewrite state_sm_on_event_unroll2.

    rw @loutput_sm_on_event_unroll2 in diss1.
    fold (@DirectedMsgs _ _ _) in *.
    simpl in *.
    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q1; symmetry in Heqq1
    end.
    destruct q1; simpl in *; ginv; tcsp;[].

    remember (trigger_op e) as trig1; symmetry in Heqtrig1.
    destruct trig1; simpl in *; tcsp.

    unfold op_state; simpl.
    unfold SMupdate in *.
    destruct m0; simpl in *; ginv; subst; tcsp;
      smash_handlers; smash_handlers_concl; ginv;[| | | |];
        try (complete (eexists; dands;[| |eauto]; auto;
                       apply in_snoc in diss0; repndors; simpl; eauto 3 with sm;
                       symmetry in diss0;
                       apply sm_signed_msg2main_auth_data_eq_implies in diss0;
                       subst; simpl in *; auto));
        try (complete (unfold is_commander in *; simpl in *; smash_sm));[].

    exists (add_to_V s (init s)); dands; auto.
    apply sm_signed_msg2main_auth_data_eq_implies in diss0; subst; simpl in *; tcsp.
  Qed.
  Hint Resolve SM_knows_if_disseminate : sm.

  Lemma SM_doesnt_stop :
    forall {eo : EventOrdering} (e : Event) n,
      loc e = n
      -> has_correct_trace_before e n
      -> exists s, state_sm_on_event (SMreplicaSM n) e = Some s.
  Proof.
    intros eo; induction e as [e ind] using predHappenedBeforeInd_type; introv eqloc cor.
    rewrite state_sm_on_event_unroll2.

    match goal with
    | [ |- context[map_option _ ?s] ] =>
      remember s as sop; symmetry in Heqsop; destruct sop;
        simpl in *;[|ginv]
    end.

    { remember (trigger_op e) as trig; symmetry in Heqtrig; destruct trig; simpl;
        unfold op_state; simpl.

      { unfold SMupdate.
        destruct m;
          simpl in *; ginv; subst; tcsp;
            try smash_handlers_concl. }

      { pose proof (cor e) as cor.
        repeat (autodimp cor hyp); eauto 3 with eo.
        pose proof (cor e) as cor; autodimp cor hyp; eauto 3 with eo.
        unfold isCorrect in cor; rewrite Heqtrig in cor; tcsp. } }

    { rewrite <- ite_first_state_sm_on_event_as_before in Heqsop.
      unfold ite_first in Heqsop.
      destruct (dec_isFirst e) as [d|d]; ginv.
      pose proof (ind (local_pred e)) as ind.
      autodimp ind hyp; eauto 3 with eo.
      autorewrite with eo in ind.
      pose proof (ind n) as ind; repeat (autodimp ind hyp); eauto 3 with eo.
      exrepnd.
      rewrite Heqsop in ind0; ginv. }
  Qed.

  Lemma SM_preserves_knows :
    forall eo, AXIOM_preserves_knows eo.
  Proof.
    introv cor lte kn; unfold knows in *; exrepnd; simpl in *.

    assert (loc e1 = loc e2) as eqloc1 by eauto 3 with eo.
    assert (loc e2 = general n) as eqloc2 by congruence.

    pose proof (SM_doesnt_stop e2 n) as q.
    repeat (autodimp q hyp); try congruence;
      try (complete (rewrite <- eqloc2; eauto 3 with eo)).
    exrepnd.
    exists s n.
    dands; auto.
    eapply SM_values_increase_on; eauto.
  Qed.
  Hint Resolve SM_preserves_knows : sm.

  Lemma SM_all_messages_are_disseminated_before_deadline :
    forall (eo : EventOrdering) (gen : Gen),
      AXIOM_SMcorrect_keys eo
      -> is_lieutenant gen = true
      -> AXIOM_all_messages_are_disseminated_before_deadline
           eo
           (fun g => g = general gen)
           (nat2pdt (S F) * (mu + tau))%dtime.
  Proof.
    introv ckeys isl cor xx dis; repnd.
    pose proof (lieutenant_disseminate_signed_msg_implies e d gen) as q.
    repeat (autodimp q hyp).
    exrepnd; auto.
    rename_hyp_with learns_on_time lrn.
    applydup learns_on_time_implies_cond in lrn.
    unfold on_time in lrn0; repnd.
    eapply dt_le_trans;[eauto|]; auto.
    apply dt_mul_le_r; eauto 3 with eo;[].
    apply dt_nat_nat_inj_le; auto.
  Qed.
  Hint Resolve SM_all_messages_are_disseminated_before_deadline : sm.

  Lemma SM_all_messages_are_disseminated_before_deadline2 :
    forall (eo : EventOrdering) (gen : Gen),
      AXIOM_SMcorrect_keys eo
      -> is_lieutenant gen = true
      -> AXIOM_all_messages_are_disseminated_before_deadline
           eo
           (fun g => g = general gen)
           (nat2pdt F * (mu + tau))%dtime.
  Proof.
    introv ckeys isl cor xx dis; repnd.
    pose proof (lieutenant_disseminate_signed_msg_implies e d gen) as q.
    repeat (autodimp q hyp).
    exrepnd; auto.
    rename_hyp_with learns_on_time lrn.
    applydup learns_on_time_implies_cond in lrn.
    unfold on_time in lrn0; repnd.
    eapply dt_le_trans;[eauto|]; auto.
    apply dt_mul_le_r; eauto 3 with eo;[].
    apply dt_nat_nat_inj_le; auto.
  Qed.
  Hint Resolve SM_all_messages_are_disseminated_before_deadline2 : sm.

  (*
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
  Hint Resolve all_messages_are_sent_before_deadline_signed_lieutenant : sm. *)



  Lemma SM_all_containers_satisfy_constraint :
    forall eo, AXIOM_all_containers_satisfy_constraint eo.
  Proof.
    introv xx.
    simpl in *; dands; eauto 3 with sm.
  Qed.
  Hint Resolve SM_all_containers_satisfy_constraint : sm.

  (* never used
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
   *)

  Lemma general_name2gen :
    forall {eo : EventOrdering} e, general (name2gen (loc e)) = loc e.
  Proof.
    introv; destruct (loc e); simpl; auto.
  Qed.
  Hint Rewrite @general_name2gen : sm.

  Lemma SM_lak_verify_implies_verify_authenticated_data :
    forall eo, AXIOM_lak_verify_implies_verify_authenticated_data eo.
  Proof.
    introv xx; tcsp.
    simpl in *; unfold sm_verify in *.
    apply implies_verify_sm_signed_msg2main in xx; simpl in *.
    autorewrite with sm in *; auto.
  Qed.
  Hint Resolve SM_lak_verify_implies_verify_authenticated_data : sm.

  Lemma extend_in_sm_signed_msg2list_auth_data_implies :
    forall v d a,
      In (sm_data2main_auth_data (sm_extend_data d a)) (sm_signed_msg2list_auth_data v)
      -> In (sm_data2main_auth_data d) (sm_signed_msg2list_auth_data v).
  Proof.
    induction v; introv h; simpl in *; tcsp; repndors; tcsp; ginv.
    apply in_snoc.
    apply in_snoc in h; repndors; tcsp.
    { apply IHv in h; tcsp. }
    { unfold sm_data2main_auth_data in *.
      unfold sm_extend_data in *.
      unfold sm_signed_msg2main_auth_data in h.
      inversion h; subst; clear h.
      left.
      destruct v; simpl in *; tcsp.
      apply in_snoc; tcsp. }
  Qed.

  Lemma SM_in_auth_data_trigger_extend :
    forall eo, AXIOM_in_auth_data_trigger_extend eo.
  Proof.
    introv h; simpl in *.
    unfold auth_data_in_trigger in *.
    remember (trigger_op e) as trig; destruct trig; auto.
    destruct m; simpl in *; tcsp.
    apply extend_in_sm_signed_msg2list_auth_data_implies in h; auto.
  Qed.
  Hint Resolve SM_in_auth_data_trigger_extend : sm.

(*  Lemma SM_verify_authenticated_data_lak_verify_implies :
    forall eo, AXIOM_verify_authenticated_data_lak_verify_implies eo.
  Proof.
    introv xx; tcsp.
  Qed.*)

  Lemma SM_verify_dis_extend_data :
    forall g ks d n,
      n = general g
      -> verify_signed_msg g ks d = true
      -> AXIOM_verify_dis_extend_data n ks d.
  Proof.
    introv eqn h v q; simpl in *; subst.
    unfold verify_signed_msg in *.
    unfold verify_signed_msg_sign in *; smash_sm.
    allrw forallb_forall.
    pose proof (h (sm_data2main_auth_data d')) as h; apply h.
    rewrite extend_data_list_as_extend_signed_msg_list.
    apply sm_signed_msg2main_auth_data_in_extend_signed_msg_list.
  Qed.

  Lemma sm_signed_msg2value_sm_extend_data :
    forall a d,
      sm_signed_msg2value (sm_extend_data d a)
      = sm_signed_msg2value d.
  Proof.
    induction a; introv; simpl; tcsp.
  Qed.
  Hint Rewrite sm_signed_msg2value_sm_extend_data : sm.

  Lemma SM_knows_extend :
    AXIOM_knows_extend.
  Proof.
    introv h; simpl in *.
    unfold sm_knows in *; autorewrite with sm; auto.
  Qed.
  Hint Resolve SM_knows_extend : sm.

  Lemma SM_lak_verify_extend_implies :
    forall eo, AXIOM_verify_extend_implies eo.
  Proof.
    introv verif.
    simpl in *.
    unfold sm_verify, sm_extend_data in *; simpl in *.
    unfold verify_signed_msg in *; simpl in *; smash_sm.
    unfold verify_signed_msg_sign in *; simpl in *.

    rewrite forallb_snoc in verif; smash_sm.
    allrw @norepeatsb_snoc; smash_sm.
    allrw @not_inb_snoc_true_iff; repnd.
    dands; tcsp.
  Qed.
  Hint Resolve SM_lak_verify_extend_implies : sm.

  Lemma implies_owns :
    forall {eo : EventOrdering} (e1 e2 : Event) m g2,
      loc e2 = general g2
      -> In g2 (sm_signed_msg2senders m)
      -> owns e1 m (loc e2).
  Proof.
    introv eqloc d.
    applydup in_sm_signed_msg2senders_implies in d as z; exrepnd; subst m.
    exists m' l; simpl; dands; auto;[].
    unfold last_owns; simpl in *.
    rewrite sm_bare_signed_msg2general_sm_signed_msg2bare_eq; try congruence.
  Qed.
  Hint Resolve implies_owns : sm.

  Lemma sm_received_msg_was_sent :
    forall {eo : EventOrdering} (e1 e2 : Event) m g1 g2 s2,
      AXIOM_SMcorrect_keys eo
      -> AXIOM_authenticated_messages_were_sent_or_byz_usys eo SMsys
      -> loc e1 = general g1
      -> loc e2 = general g2
      -> is_lieutenant g2 = true
      -> state_sm_before_event (SMreplicaSM g2) e2 = Some s2
      -> (nat2pdt (S F) * (mu + tau) < time e2)%dtime
      -> ~ In (sm_signed_msg2value m) (V s2)
      -> learns e1 m
      -> verify_signed_msg g1 (keys e1) m = true
      -> In g2 (sm_signed_msg2senders m)
            (* use state_sm_on_event_some_implies_has_correct_trace_before instead *)
      -> has_correct_trace_before e1 (node2name g2)
      -> False.
  Proof.
    introv ckeys sendbyz eqloc1 eqloc2 isl2 eqst2 lttime2;
      introv vcond2 eqtrig1 verif d cle.

    pose proof (dis_message_is_disseminated_before_deadline5
                  e1 e2
                  (fun g => g = g2)
                  m g2
                  (nat2pdt (S F) * (mu + tau))%dtime) as q.
    repeat (autodimp q hyp); eauto 3 with sm;
      try (complete (rewrite eqloc2; auto));
      try (complete (eapply state_sm_before_event_some_implies_has_correct_trace_bounded_lt; eauto));[].

    unfold knew in q; exrepnd; simpl in *.
    rewrite eqloc2 in q0; ginv.
    fold DirectedMsgs in *.
    rewrite eqst2 in q1; ginv.
  Qed.


  Lemma is_lieutenant_true_implies_not_commander :
    forall g,
      is_lieutenant g = true
      -> is_commander g = false.
  Proof.
    introv h.
    unfold is_commander, is_lieutenant, negb in *; smash_sm.
  Qed.

  Lemma events_in_same_epoch_implies_time_old_plus :
    forall (eo    : EventOrdering)
           (e e0  : Event),
      events_in_same_epoch e e0
      -> (time e0 <= time e + (mu + tau))%dtime.
  Proof.
    intros eo e e' H.
    unfold events_in_same_epoch in *. simpl in *.
    unfold max_received in *; unfold epoch_duration in *.
    destruct H. eauto.
  Qed.
  Hint Resolve events_in_same_epoch_implies_time_old_plus : sm.

  Lemma implies_learns_extend_signed_msg :
    forall {eo : EventOrdering} (e1 e : Event) s g1 g2 m,
      (* === general hypotheses === *)
      AXIOM_SMcorrect_keys eo
      -> AXIOM_all_correct_can_verify eo
      -> AXIOM_verified_authenticated eo
      (* ==== [e] is correct === *)
      -> node_has_correct_trace_before e g1
      -> has_correct_trace_before e1 (general g2)
      (* === locations of events === *)
      -> loc e = general g1
      -> loc e1 = general g2
      -> g2 <> g1
      -> is_lieutenant g2 = true
      -> ~ In g2 (sm_signed_msg2senders m)
      (* === [g2] received [m] extend with a signature from [g1] ==== *)
      -> trigger_op e1 = Some (sm_msg_signed (extend_signed_msg m (general g1) (local_keys s)))
      (* === [g1] could verify [m] ==== *)
      -> verify_signed_msg g1 (local_keys s) m = true
      (* === [g1]'s state ==== *)
      -> state_sm_before_event (SMreplicaSM g1) e = Some s
      (* === then [g2] learns the extended data ==== *)
      -> learns e1 (extend_signed_msg m (general g1) (local_keys s)).
  Proof.
    introv ckeys cverif vauth ctrace1 ctrace2 eqloc1 eqloc2 dg isl nim;
      introv trig verifd eqst1.

    unfold verify_signed_msg in *; smash_sm;[].

    pose proof (ckeys e g1 s) as k1.
    repeat (autodimp k1 hyp); eauto 3 with eo;[].
    rewrite <- k1 in verifd.

    pose proof (all_verify_signed_msg_sign e e1 m g1 g2) as vm.
    repeat (autodimp vm hyp); eauto 3 with eo; try (complete (allrw; auto));[].

    pose proof (verified_authenticated_implies vauth e e1) as vad.
    repeat (autodimp vad hyp); eauto 3 with eo; try (complete (allrw; auto));[].

    allrw @norepeatsb_as_no_repeats.
    allrw @not_inb_true_iff.

    unfold learns.
    exists g2.
    rewrite trig; simpl.
    rewrite in_snoc.
    dands; simpl; auto.
    unfold sm_verify.

    rewrite eqloc2; simpl.
    unfold verify_signed_msg in *; smash_sm.
    autorewrite with sm in *.
    allrw @norepeatsb_snoc.
    smash_sm.
    rewrite verify_signed_msg_sign_extend_signed_msg in *; smash_sm.

    rewrite norepeatsb_as_no_repeats.
    repeat (rewrite not_inb_true_iff).
    rewrite in_snoc.
    dands; tcsp.

    match goal with
    | [ |- verify_authenticated_data ?n ?d ?k = true ] =>
      pose proof (vad d) as q; simpl in q
    end.
    autodimp q hyp; try congruence.
    unfold sm_signed_msg2main_auth_data in *; simpl in *.
    unfold sm_signed_msg2auth in *; simpl in *.
    rewrite <- eqloc2, <- k1; auto.
  Qed.

  Lemma verify_signed_msg_cons_implies :
    forall i k m s,
      verify_signed_msg i k (sm_signed_msg_cons m s) = true
      -> verify_signed_msg i k m = true.
  Proof.
    introv verif.
    unfold verify_signed_msg in *; smash_sm.
    autorewrite with sm in *.
    allrw @norepeatsb_snoc; smash_sm.
    unfold verify_signed_msg_sign in *; simpl in *.
    allrw @forallb_snoc; repnd; smash_sm.
    allrw @norepeatsb_as_no_repeats.
    allrw @not_inb_snoc_true_iff; repnd.
    allrw @not_inb_true_iff.
    dands; tcsp.
  Qed.
  Hint Resolve verify_signed_msg_cons_implies : sm.

  Lemma verify_signed_msg_extend_implies :
    forall i k m n ks,
      verify_signed_msg i k (extend_signed_msg m n ks) = true
      -> verify_signed_msg i k m = true.
  Proof.
    introv verif.
    apply verify_signed_msg_cons_implies in verif; auto.
  Qed.
  Hint Resolve verify_signed_msg_extend_implies : sm.

  Lemma sm_verify_extend_implies :
    forall {eo : EventOrdering} e m n ks,
      sm_verify eo e (extend_signed_msg m n ks) = true
      -> sm_verify eo e m = true.
  Proof.
    introv verif.
    unfold sm_verify in *; simpl in *; eauto 3 with sm.
  Qed.
  Hint Resolve sm_verify_extend_implies : sm.

  Lemma in_implies_verify_signed_msg :
    forall n ks m d,
      In (sm_data2main_auth_data d) (sm_signed_msg2list_auth_data m)
      -> verify_signed_msg n ks m = true
      -> verify_signed_msg n ks d = true.
  Proof.
    induction m; introv i verif; simpl in *; repndors; tcsp.

    { symmetry in i; apply sm_signed_msg2main_auth_data_eq_implies in i; subst; auto. }

    apply in_snoc in i; repndors; tcsp.

    { apply IHm in i; tcsp; eauto 3 with sm. }

    symmetry in i; apply sm_signed_msg2main_auth_data_eq_implies in i; subst; auto.
  Qed.

  Lemma implies_in_snoc_verify :
    forall {eo : EventOrdering} (e : Event) m n ks d,
      sm_verify eo e (extend_signed_msg m n ks) = true
      -> In (sm_data2main_auth_data d)
            (snoc (sm_signed_msg2list_auth_data m)
                  (sm_signed_msg2main_auth_data (extend_signed_msg m n ks)))
      -> sm_verify eo e d = true.
  Proof.
    introv verif i.
    apply in_snoc in i; repndors; tcsp;
      [|symmetry in i; apply sm_signed_msg2main_auth_data_eq_implies in i;
        subst; simpl in *; auto];[].
    apply sm_verify_extend_implies in verif.
    unfold sm_verify in *; simpl in *.
    eapply in_implies_verify_signed_msg in i; eauto.
  Qed.

  Lemma implies_verify_signed_msg_extend_signed_msg :
    forall g ks m n k,
      g <> n
      -> ~In g (sm_signed_msg2senders m)
      -> ~In n (sm_signed_msg2senders m)
      -> verify_authenticated_data (general g) (sm_signed_msg2main_auth_data (extend_signed_msg m n k)) ks = true
      -> verify_signed_msg g ks m = true
      -> verify_signed_msg g ks (extend_signed_msg m n k) = true.
  Proof.
    introv dgn ni1 ni2 verif va.
    unfold verify_signed_msg in *; smash_sm.
    rewrite norepeatsb_snoc; smash_sm.
    rewrite @not_inb_snoc_true_iff.
    repeat rewrite not_inb_true_iff.
    dands; auto;[].
    unfold verify_signed_msg_sign in *; simpl in *.
    rewrite forallb_snoc; smash_sm.
  Qed.


  Lemma implies_learns_on_time_extend_signed_msg :
    forall {eo : EventOrdering} (e1 e : Event) g1 g2 m,
      (* === general hypotheses === *)
      AXIOM_SMcorrect_keys eo
      -> AXIOM_all_correct_can_verify eo
      -> AXIOM_verified_authenticated eo
      (* ==== [e] is correct === *)
      -> node_has_correct_trace_before e g1
      -> has_correct_trace_before e1 (general g2)
      (* === locations of events === *)
      -> loc e = general g1
      -> loc e1 = general g2
      -> g2 <> g1
      -> is_lieutenant g2 = true
      -> ~ In g2 (sm_signed_msg2senders m)
      (* === [g2] received [m] extend with a signature from [g1] ==== *)
      -> trigger_op e1 = Some (sm_msg_signed (extend_signed_msg m (general g1) (keys e)))
      (* === [g1] could verify [m] ==== *)
      -> verify_signed_msg g1 (keys e) m = true
      (* === the message is on time ==== *)
      -> message_is_on_time (extend_signed_msg m (general g1) (keys e)) (time e1) = true
      (* === then [g2] learns the extended data ==== *)
      -> learns_on_time e1 (extend_signed_msg m (general g1) (keys e)) sm_signed_msg2size (S F).
  Proof.
    introv ckeys cverif vauth ctrace1 ctrace2 eqloc1 eqloc2 dg isl nim;
      introv trig verifd ontime.

    unfold verify_signed_msg in *; smash_sm;[].

    pose proof (all_verify_signed_msg_sign e e1 m g1 g2) as vm.
    repeat (autodimp vm hyp); eauto 3 with eo; try (complete (allrw; auto));[].

    pose proof (verified_authenticated_implies vauth e e1) as vad.
    repeat (autodimp vad hyp); eauto 3 with eo; try (complete (allrw; auto));[].

    allrw @norepeatsb_as_no_repeats.
    allrw @not_inb_true_iff.

    unfold learns_on_time.
    exists g2.
    rewrite trig; simpl.
    dands; simpl; auto; eauto 3 with sm;[].

    unfold sm_verify; simpl.
    rewrite eqloc2; simpl.
    apply implies_verify_signed_msg_extend_signed_msg; auto.

    { match goal with
      | [ |- verify_authenticated_data ?n ?d ?k = true ] =>
        pose proof (vad d) as q; simpl in q
      end.
      autodimp q hyp; try congruence. }

    unfold verify_signed_msg in *; smash_sm.
    rewrite norepeatsb_as_no_repeats.
    repeat (rewrite not_inb_true_iff).
    dands; tcsp.
  Qed.

  Lemma in_preserves_not_signed_directly_by_commander :
    forall v d,
      In (sm_data2main_auth_data d) (sm_signed_msg2list_auth_data v)
      -> is_sm_signed_msg2directly_from_commander d = false
      -> is_sm_signed_msg2directly_from_commander v = false.
  Proof.
    induction v; introv i h; simpl in *; repndors; tcsp.
    apply sm_signed_msg2main_auth_data_eq_implies in i; subst; simpl in *; auto.
  Qed.
  Hint Resolve in_preserves_not_signed_directly_by_commander : sm.

  Lemma extend_message_is_on_time :
    forall {eo : EventOrdering} (e1 e2 : Event) m n ks,
      events_in_same_epoch e1 e2
      -> length (sm_signed_msg2signs m) < S F
      -> message_is_on_time m (time e1) = true
      -> message_is_on_time (extend_signed_msg m n ks) (time e2) = true.
  Proof.
    introv same len ontime.
    unfold message_is_on_time in *; simpl in *; autorewrite with sm list in *.
    smash_sm;[].
    apply events_in_same_epoch_implies_time_old_plus in same.

    eapply dt_lt_le_trans in d0;[|eauto].

    assert (dt_nat_inj (S (length (sm_signed_msg2signs m))) * (mu + tau)
            < (dt_nat_inj (length (sm_signed_msg2signs m)) * (mu + tau)) + (mu + tau))%dtime as ltt.
    { eapply dt_lt_le_trans;[eauto|].
      apply dt_add_le_compat; eauto 3 with eo.
      apply dt_le_refl. }

    rewrite S_dt_T_mul in ltt.
    apply dt_lt_irrefl in ltt; tcsp.
  Qed.
  Hint Resolve extend_message_is_on_time : sm.

  Lemma SM_learns_on_time_implies_knows :
    forall {eo : EventOrdering},
      AXIOM_SMcorrect_keys eo
      -> AXIOM_learns_on_time_implies_knows
           eo
           (fun n => is_lieutenant n = true)
           (fun d => is_sm_signed_msg2directly_from_commander d = false)
           sm_signed_msg2size (S F).
  Proof.
    introv ckeys cor eqloc isl ndfc lrn.
    unfold learns_on_time in lrn; exrepnd.
    rewrite lrn1 in eqloc; ginv.
    unfold knows; simpl in *.

    pose proof (SM_doesnt_stop e n) as q.
    repeat (autodimp q hyp);[].
    exrepnd.
    exists s n; dands; auto.

    unfold sm_knows; simpl.
    rename q0 into eqst.

    rewrite state_sm_on_event_unroll2 in eqst.
    match goal with
    | [ H : context[map_option _ ?s] |- _ ] =>
      remember s as sop; symmetry in Heqsop; destruct sop; simpl in *;[|ginv]
    end.

    apply op_state_some_iff in eqst; exrepnd.
    rewrite eqst1 in lrn2; simpl in *; ginv.
    simpl in *.

    smash_handlers1; smash_sm1.

    { unfold check_new_value in *; smash_sm; eauto 3 with sm. }

    { rename_hyp_with on_time ontime.
      apply on_time_implies_message_is_on_time in ontime.
      rewrite ontime in *; ginv. }

    { unfold sm_verify in *; simpl in *.
      rewrite lrn1 in *; simpl in *.
      pose proof (ckeys e n s) as q.
      repeat (autodimp q hyp).
      rewrite q in *.
      rewrite lrn3 in *; ginv. }
  Qed.
  Hint Resolve SM_learns_on_time_implies_knows : sm.

  Lemma sm_knew_implies :
    forall {eo : EventOrdering} (e : Event) g s d,
      loc e = general g
      -> state_sm_before_event (SMreplicaSM g) e = Some s
      -> knew e d
      -> In (sm_signed_msg2value d) (V s).
  Proof.
    introv eqloc eqst kn.
    unfold knew in kn; simpl in kn.
    unfold sm_knows in kn; simpl in  kn; exrepnd.
    rewrite eqloc in *; ginv.
    fold DirectedMsgs in *.
    rewrite eqst in kn1; ginv.
  Qed.
  Hint Resolve sm_knew_implies : sm.

  Lemma  nat_pred_F_plus_1 :
    Init.Nat.pred dis_max_sign = F.
  Proof.
    simpl in *.
    unfold sm_max_sign.
    rewrite Nat.add_1_r.
    rewrite Nat.pred_succ. eauto.
  Qed.
  Hint Rewrite nat_pred_F_plus_1 : sm.

  Lemma AXIOM_exists_at_most_f_faulty_pred :
    forall (Eo : EventOrdering) (e1 e2 : Event),
      AXIOM_exists_at_most_f_faulty [e1, e2] (Init.Nat.pred dis_max_sign)
      = AXIOM_exists_at_most_f_faulty [e1, e2] F.
  Proof.
    introv.
    rewrite  nat_pred_F_plus_1. eauto.
  Qed.
  Hint Rewrite AXIOM_exists_at_most_f_faulty_pred : sm.

  Lemma sm_signed_msg2sender_extend_signed_msg :
    forall v n ks,
      sm_signed_msg2sender (extend_signed_msg v n ks) = n.
  Proof.
    introv; tcsp.
  Qed.
  Hint Rewrite sm_signed_msg2sender_extend_signed_msg : sm.

  Lemma implies_message_is_on_time :
    forall (t : PosDTime) v,
      (t <= dt_nat_inj (length (sm_signed_msg2signs v)) * (mu + tau))%dtime
      -> length (sm_signed_msg2signs v) <= F
      -> message_is_on_time v t = true.
  Proof.
    introv h len.
    unfold message_is_on_time.
    repeat (dest_cases w).
    eapply dt_le_lt_trans in h;[|eauto].
    apply dt_lt_irrefl in h; tcsp.
  Qed.
  Hint Resolve implies_message_is_on_time : sm.

  Lemma verify_trig_implies_all_verified :
    forall {eo : EventOrdering} (e : Event) m n ks,
      trigger_op e = Some (sm_msg_signed m)
      -> verify_signed_msg n ks m = true
      -> keys e = ks
      -> loc e = general n
      -> all_verified_in_trigger e.
  Proof.
    introv trig verif eqks eqloc i; subst.
    rewrite trig in i; simpl in i.
    eapply in_implies_verify_signed_msg in i; eauto.
    simpl.
    unfold sm_verify; rewrite eqloc; simpl; auto.
  Qed.
  Hint Resolve verify_trig_implies_all_verified : sm.

  Lemma sm_in_get_contained_authenticated_data_dis_data2msg :
    AXIOM_in_get_contained_authenticated_data_dis_data2msg.
  Proof.
    introv; simpl; eauto 3 with sm.
  Qed.
  Hint Resolve sm_in_get_contained_authenticated_data_dis_data2msg : sm.

  Lemma learns_on_time_implies_verify_signed_msg :
    forall {eo : EventOrdering} (e : Event) m E B g,
      learns_on_time e m E B
      -> loc e = general g
      -> verify_signed_msg g (keys e) m = true.
  Proof.
    introv lrn eqloc.
    unfold learns_on_time in lrn; exrepnd.
    simpl in *.
    unfold sm_verify in *; simpl in *.
    rewrite eqloc in *; ginv.
  Qed.
  Hint Resolve learns_on_time_implies_verify_signed_msg : sm.

  Lemma SM_events_in_same_epoch_implies_verify_extend :
    forall {eo : EventOrdering},
      AXIOM_all_correct_can_verify eo
      -> AXIOM_verified_authenticated eo
      -> AXIOM_events_in_same_epoch_implies_verify_extend eo.
  Proof.
    introv allcor vauth dloc eqloc eqloc' cor cor' ni ni'; introv same verif.
    simpl in *; unfold sm_verify in *.
    rewrite sm_extend_data_as_extend_signed_msg.
    rewrite eqloc in verif; rewrite eqloc'; simpl in *.
    unfold verify_signed_msg in *; smash_sm.
    rewrite norepeatsb_snoc; smash_sm.
    rewrite not_inb_snoc_true_iff; smash_sm.
    rewrite verify_signed_msg_sign_extend_signed_msg; smash_sm.
    allrw <- sm_signed_msg2senders_eq_dis_data2senders.
    dands; tcsp.

    { apply (all_verify_signed_msg_sign e e' _ n n'); auto. }

    { unfold verify_authenticated_data; simpl.
      unfold sm_signed_msg2main_auth_data; simpl.
      pose proof (verified_authenticated_implies vauth e e') as q.
      repeat (autodimp q hyp).
      pose proof (q (sm_bare_msg_signed (sm_bare_signed_msg_cons m n))) as q.
      simpl in q; autodimp q hyp; allrw; auto. }

    { rewrite not_inb_true_iff; auto. }

    { introv xx; subst; simpl in *; tcsp.
      destruct dloc; allrw; simpl; auto. }
  Qed.
  Hint Resolve SM_events_in_same_epoch_implies_verify_extend : sm.

  Lemma dis_extend_data_raises_epoch_sm_signed_msg2size :
    AXIOM_extend_data_raises_epoch sm_signed_msg2size.
  Proof.
    introv; simpl.
    unfold sm_signed_msg2size; simpl; autorewrite with list; auto.
  Qed.
  Hint Resolve dis_extend_data_raises_epoch_sm_signed_msg2size : sm.

  Lemma learns_on_time_implies_not_in_senders :
    forall {eo : EventOrdering} (e : Event) m E B n,
      learns_on_time e m E B
      -> loc e = general n
      -> ~ In n (sm_signed_msg2senders m).
  Proof.
    introv lrn eqloc.
    unfold learns_on_time in lrn; exrepnd; simpl in *.
    unfold sm_verify in *; simpl in *.
    rewrite eqloc in *; ginv; simpl in *.
    unfold verify_signed_msg in *; smash_sm.
    rewrite @not_inb_true_iff in *; auto.
  Qed.
  Hint Resolve learns_on_time_implies_not_in_senders : sm.

  Lemma learns_on_time_implies_verify :
    forall {eo : EventOrdering} (e : Event) m E B,
      learns_on_time e m E B
      -> sm_verify eo e m = true.
  Proof.
    introv lrn.
    unfold learns_on_time in lrn; exrepnd; simpl in *; auto.
  Qed.
  Hint Resolve learns_on_time_implies_verify : sm.

  Lemma learns_on_time_implies_no_repeats_senders :
    forall {eo : EventOrdering} (e : Event) m E B,
      learns_on_time e m E B
      -> no_repeats (sm_signed_msg2senders m).
  Proof.
    introv lrn; apply learns_on_time_implies_verify in lrn.
    unfold sm_verify, verify_signed_msg in *; smash_sm.
    allrw @norepeatsb_as_no_repeats; tcsp.
  Qed.
  Hint Resolve learns_on_time_implies_no_repeats_senders : sm.

  Lemma sm_signed_msg2senders_extend_signed_msg :
    forall d n ks,
      sm_signed_msg2senders (extend_signed_msg d n ks) = snoc (sm_signed_msg2senders d) n.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite sm_signed_msg2senders_extend_signed_msg : sm.

  Lemma implies_is_correct_in_near_future :
    forall {eo : EventOrdering} (e1 e2 : Event) n v E B,
      loc e2 = node2name n
      -> (dt_nat_inj B * (mu + tau) < time e2)%dtime
      -> has_correct_trace_before e2 (node2name n)
      -> E v < B
      -> on_time e1 v E B
      -> is_correct_in_near_future (node2name n) e1.
  Proof.
    introv eqloc cond cor len lrn.
    exists e2; dands; auto.
    unfold learns_on_time, on_time in lrn; exrepnd.
    eapply dt_le_trans;[|apply dt_lt_le_weak;eauto].
    eapply dt_le_trans;[apply dt_add_le_compat;[eauto|apply dt_le_refl] |].
    simpl; rewrite <- S_dt_T_mul; eauto 3 with dtime.
    apply dt_mul_le_compat_r; eauto 3 with dtime;[].
    unfold sm_signed_msg2size; apply dt_nat_nat_inj_le; try omega.
  Qed.
  Hint Resolve implies_is_correct_in_near_future : sm.

  Lemma implies_events_in_later_epoch :
    forall {eo : EventOrdering} (e1 e2 : Event) n v E B,
      (dt_nat_inj B * (mu + tau) < time e2)%dtime
      -> has_correct_trace_before e2 (node2name n)
      -> E v < B
      -> on_time e1 v E B
      -> events_in_later_epoch e1 e2.
  Proof.
    introv cond cor len lrn.
    unfold events_in_later_epoch.
    unfold learns_on_time, on_time in lrn; exrepnd.
    eapply dt_le_lt_trans;[|eauto].
    eapply dt_le_trans;[apply dt_add_le_compat;[eauto|apply dt_le_refl] |].
    simpl; rewrite <- S_dt_T_mul; eauto 3 with dtime.
    apply dt_mul_le_compat_r; eauto 3 with dtime;[].
    unfold sm_signed_msg2size; apply dt_nat_nat_inj_le; try omega.
  Qed.
  Hint Resolve implies_events_in_later_epoch : sm.

  Hint Rewrite @in_snoc : list.
  Hint Rewrite in_app_iff : list.

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

    pose proof sm_in_get_contained_authenticated_data_dis_data2msg as cont.

    pose proof (value_was_received_before v e1) as h.
    repeat (autodimp h hyp); exrepnd.
    { eexists; eexists; dands; simpl; eauto. }
    repndors; exrepnd; subst;
      [|assert (is_lieutenant_e e1) as i by eauto 3 with sm;
        apply is_lieutenant_e_implies_not_is_commander_e in i; tcsp];[].

    assert (loc e' = general g1) as eqloc' by (allrw <-; eauto 3 with eo).

    destruct (in_dec gen_deq g2 (sm_signed_msg2senders m)) as [d|d].

    {
      (* [g2] is one of the generals who signed the message *)

      pose proof (nodes_have_correct_traces_before_two_implies_causal_left e1 e2 e' g1 g2) as cle.
      repeat (autodimp cle hyp).
      apply (sm_received_msg_was_sent e' e2 m g1 g2 s2); auto; try congruence; eauto 3 with diss sm.
      eapply learns_on_time_implies_learns; eauto.
    }

    {
      (* [g2] didn't sign the message *)

      pose proof (nodes_have_correct_traces_before_two_implies_causal_le_right e1 e2 e2 g1 g2) as ce2.
      repeat (autodimp ce2 hyp); eauto 2 with eo.

      rename_hyp_with learns_on_time lrn.
      applydup learns_on_time_implies_cond in lrn.
      unfold on_time in lrn0; repnd.

      apply le_lt_or_eq in lrn0; repndors.

      {
        (* [m] is signed by strictly less than [F+1] generals *)

        (* TODO: do the same thing for the other cases *)
        pose proof (learns_on_time_implies_other_knew
                      e' e2 g1 g2 m
                      (fun n => is_lieutenant n = true)
                      (fun d => is_sm_signed_msg2directly_from_commander d = false)
                      sm_signed_msg2size (S F)) as lot.
        simpl in lot; rewrite <- sm_signed_msg2senders_eq_dis_data2senders in lot.
        rewrite sm_extend_data_as_extend_signed_msg in lot.
        repeat (autodimp lot hyp); auto; eauto 3 with sm eo diss;
          try (complete (unfold dis_nodes_not_in_list; simpl; apply in_diff; dands; auto;
                         apply in_remove; dands; auto; apply gens_prop));
          try (complete (rewrite eqloc'; eauto 3 with eo sm;
                         eapply nodes_have_correct_traces_before_two_implies_causal_left_1 in ctraces; eauto));
          try (complete (exists e2; dands; eauto 3 with eo; eapply time_plus_mu_tau_le; eauto));
          try (complete (eapply implies_events_in_later_epoch; eauto; simpl in *; auto));
          try (complete (split; auto)).
      }

      {
        (* [m] is signed by exactly [F+1] generals.
             There must be 1 correct general among those [F+1] generals. *)

        (* continue here ..... *)
        pose proof(exists_one_correct_implies [e1,e2] e' m g1 F) as xx.
        repeat(autodimp xx hyp);
          try rewrite <- sm_signed_msg2senders_eq_dis_data2senders;
          autorewrite with sm; eauto 3 with sm eo diss;
          try (complete (unfold sm_signed_msg2size in *;
                         rewrite <- length_sm_signed_msg2signs_eq_length_sm_signed_msg2senders;
                         omega));[].
        exrepnd.

        subst; simpl in *.
        rewrite <- sm_signed_msg2senders_eq_dis_data2senders in *.
        rewrite <- sm_signed_msg2sender_eq_dis_data2sender in *.
        rewrite extend_data_list_as_extend_signed_msg_list in *.

        rename d' into m'.
        rename xx0 into w4.
        rename xx2 into cor1.
        rename xx3 into w1.

        remember (is_lieutenant (sm_signed_msg2sender m')) as b; symmetry in Heqb; destruct b.

        {
          dup w4 as out.
          eapply lieutenant_disseminate_signed_msg_implies in out; eauto; exrepnd; subst;[].

          (* Ivana Note: maybe these two can be cleared, so that is a bit more similar to the commander case
             out8 : state_sm_on_event (SMreplicaSM (sm_signed_msg2sender m')) e'0 = Some s3
             out1 : In (sm_signed_msg2value v) (V s3)
           *)


          (* Q : should we use here abstract version or this one?
             Note that new proof of this one is already based on the abstract version *)
          pose proof (extend_signed_msg_list_eq_extend_signed_msg_implies_if_no_repeats
                        l0 m' v (keys e'0) (keys e'0)) as xx.
          repeat (autodimp xx hyp);eauto 3 with sm eo;[].
          subst l0; simpl in *;[].

          pose proof (learns_on_time_implies_other_knew
                        e'0 e2 (sm_signed_msg2sender m') g2 v
                        (fun n => is_lieutenant n = true)
                        (fun d => is_sm_signed_msg2directly_from_commander d = false)
                        sm_signed_msg2size (S F)) as lot.
          simpl in lot; rewrite <- sm_signed_msg2senders_eq_dis_data2senders in lot.
          rewrite sm_extend_data_as_extend_signed_msg in lot.
          repeat (autodimp lot hyp); auto; eauto 3 with sm eo diss;
            try (complete (split; dands; auto; unfold sm_signed_msg2size; omega));
            try (complete (rewrite out2 in *; autorewrite with sm list in *; simpl in *;
                           introv xx; subst; tcsp));
            try (complete (apply (implies_is_correct_in_near_future e'0 e2 g2 v sm_signed_msg2size (S F));
                           unfold sm_signed_msg2size; auto; eauto 3 with sm diss; try omega));
            try (complete (apply (implies_events_in_later_epoch e'0 e2 g2 v sm_signed_msg2size (S F));
                           unfold sm_signed_msg2size; auto; eauto 3 with sm diss; try omega)); [].
          rewrite out2 in *; autorewrite with sm in *.
          eapply sm_knew_implies in lot; eauto; simpl in *; tcsp.
        }

        (* XXXXXXXXXXXXXXX *)


        {
          (* the sender of [m'] is the commander *)

          (* don't do that *)
          unfold disseminate in w4; exrepnd; simpl in *.
          destruct m; simpl in *.
          apply main_in_auth_data_implies_extend_signed_msg_list in w0; exrepnd; simpl in *; subst.

          applydup is_lieutenant_false_implies_is_commander in Heqb.
          dup w2 as out.
          eapply commander_output_signed_msg_implies in out; eauto; exrepnd; subst.

          pose proof (snoc_cases l0) as cs; repndors; exrepnd; subst; tcsp;[|];
            [|rewrite extend_signed_msg_list_snoc in *; inversion out3];[].
          simpl in *; subst; simpl in *; autorewrite with sm in *.
          (*rewrite sm_signed_msg2senders_extend_signed_msg_list in *; simpl in *.*)

          clear Heqb Heqb0.
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

          apply events_in_same_epoch_delay_implies in dlv0.
          unfold events_in_same_epoch in *; unfold min_received in *;
            unfold max_received in *; unfold epoch_duration in *.
          destruct dlv0 as [dlv0 dlv0'].
          rewrite out5 in *.
          rewrite dt_add_0_l in dlv0'.

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

          pose proof (SM_values_increase_on_before e'1 e2 g2 s'1 s2) as ss.
          repeat (autodimp ss hyp);[].

          pose proof (sm_msg_signed_commander_trigger_implies_in_V e'1 g2 s'0 s'1 (init s) (local_keys s)) as inv.
          repeat (autodimp inv hyp); eauto 3 with eo proc;
            try (complete (exists e'0 s; dands; auto)).
        }
      }
    }
  Qed.

  Lemma result_from :
    forall {eo : EventOrdering} (e : Event) g v,
      loc e = general g
      -> In (send_sm_msg_result g v) (output_system_on_event_ldata SMsys e)
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


  Lemma loc_e_is_general_SMcommander_implies_is_commander_true :
    forall  (eo  : EventOrdering) (e   : Event),
      loc e = general SMcommander
      -> is_commander (loc e) = true.
  Proof.
    introv eqloc.
    allrw. simpl in *.
    unfold is_commander.
    destruct (gen_deq SMcommander SMcommander); simpl in *; ginv; subst; tcsp.
  Qed.
  Hint Resolve loc_e_is_general_SMcommander_implies_is_commander_true : sm.

  Lemma learned_sm_msg_signed :
    forall {eo : EventOrdering} (e : Event) i,
      knows_i e i
      -> ~ knew_i e i
      ->
      (exists m,
          trigger_op e = Some (sm_msg_signed m)
          /\ i = sm_signed_msg2value m
          /\ message_is_on_time m (time e) = true
      )
      \/
      (
        exists s,
          state_sm_before_event (SMreplicaSM SMcommander) e = Some s
          /\ trigger_op e = Some sm_msg_init
          /\ i = init s
          /\ (time e == nat2pdt 0)%dtime
          /\ is_commander (loc e) = true
      ).
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
        try (complete (left; eexists; dands; eauto; unfold add_to_V, sm_knows_i in *; simpl in *; repndors; tcsp));
        try (complete (right; exists l; dands; eauto;[unfold sm_knows_i, add_to_V in *; simpl in *; repndors; tcsp| eauto 3 with sm])).
  Qed.

  Lemma SF_gt_0 :
    (nat2pdt 0 < (nat2pdt (S F)))%dtime.
  Proof.
    introv.
    pose proof (Nat.lt_0_succ F) as nat_sf.
    eapply dt_nat_nat_inj_le in nat_sf.
    pose proof dt_lt_0_1 as lt_0_1. simpl in *.
    rewrite <- eq_dt_0 in lt_0_1.
    rewrite <- eq_dt_1 in lt_0_1.
    eapply dt_lt_le_trans; eauto.
  Qed.
  Hint Resolve SF_gt_0 : sm.


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

    pose proof (SM_values_increase_before e1 e2 g s1 s2) as w; repeat (autodimp w hyp); eauto 3 with eo;[].
    apply sm_choice_diff in dc; destruct dc as [dc vcond].
    repndors; repnd.
    { apply w in vcond0; tcsp. }
    clear w.

    pose proof (information_acquired_between_knew e1 e2 dc) as kno; repeat (autodimp kno hyp);
      try (apply sm_know_i_dec);[| |].
    { pose proof (implies_not_knew_i e1 dc g s1) as w; apply w; auto. }
    { pose proof (implies_knew_i e2 dc g s2) as w; apply w; auto. }
    exrepnd.

    pose proof (learned_sm_msg_signed e dc) as lrn; repeat (autodimp lrn hyp);[].
    destruct lrn as [lrn|lrn].
    {
      exrepnd; subst.
      applydup message_is_on_time_implies_qle in lrn0 as tm.
      applydup message_is_on_time_implies_sm_signed_msg2signs in lrn0 as sn.
      apply happened_before_le_implies_le_time in kno2.
      eapply dt_lt_le_trans in ltt1;[|exact kno2].
      eapply dt_lt_le_trans in ltt1;[|exact tm].
      apply dt_mul_lt_r_lt in ltt1; eauto 3 with eo dtime;[].
      apply dt_nat_inj_lt_nat in ltt1; try omega.
    }
    {
      exrepnd. subst.
      dup kno2 as eqloc.
      eapply localLe_implies_loc in eqloc.

      assert (time e1 <= time e)%dtime as xx; eauto 3 with eo.
      rewrite lrn4 in xx.

      assert  (nat2pdt (S F) * (mu + tau) <  nat2pdt 0)%dtime as yy.
      eapply dt_lt_le_trans; eauto.

      pose proof mu_plus_tau_pos as mptp.
      pose proof SF_gt_0 as sft.

      assert  (nat2pdt 0 < nat2pdt (S F) * (mu + tau))%dtime as fin.
      eapply lt_0_twice_implies_lt_prod; eauto.

      assert  (nat2pdt (S F) * (mu + tau) < nat2pdt (S F) * (mu + tau))%dtime as fin2.
      eapply dt_lt_trans; eauto.
      apply dt_lt_irrefl in fin2; eauto.
    }
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
      -> In (send_sm_msg_result g1 v1) (output_system_on_event_ldata SMsys e1)
      -> In (send_sm_msg_result g2 v2) (output_system_on_event_ldata SMsys e2)
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

  Definition all_generals_start (eo : EventOrdering) :=
    forall (g : Gen),
    exists (e : Event),
      (time e == nat2pdt 0)%dtime
      /\ loc e = general g
      /\ trigger_op e = Some sm_msg_init.

  Definition commander_is_correct (eo : EventOrdering) :=
    forall g,
      is_commander g = true
      -> forall (e : Event),
        loc e = general g
        -> node_has_correct_trace_before e g.

  Lemma IC2 :
    forall (eo : EventOrdering),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo SMsys
      -> AXIOM_messages_get_delivered eo SMsys
      -> AXIOM_verified_authenticated eo
      -> AXIOM_all_correct_can_verify eo
      -> AXIOM_SMcorrect_keys eo
      -> (forall (e : Event), AXIOM_exists_at_most_f_faulty [e] F)
      -> all_generals_start eo
      -> commander_is_correct eo
      ->
      exists (v : sm_value),
      forall (g : Gen),
      exists (e' : Event),
        loc e' = general g
        /\
        (
          (node_has_correct_trace_before e' g
           /\ In (send_sm_msg_result g v) (output_system_on_event_ldata SMsys e'))
          \/
          isByz e'
        ).
  Proof.
    introv sendbyz deliv vauth cverif ckeys atmost;
      introv start comcor.

  Abort.

End IC1.
