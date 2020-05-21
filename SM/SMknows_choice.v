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


Require Export SM.
Require Export Disseminate.


Section SMknows_choice.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { sm_context       : SMcontext }.
  Context { sm_auth          : SMauth }.
  Context { sm_initial_keys  : SMinitial_keys }.
  Context { dtc              : @DTimeContext }.
  Context { tc               : @TimeConstraint dtc }.

  Definition sm_data := sm_signed_msg.

  Definition sm_info := sm_value.

  Definition sm_knows (d : sm_data) (s : SMstate) : Prop :=
    In (sm_signed_msg2value d) (V s).

  Definition sm_knows_i (i : sm_info) (s : SMstate) : Prop :=
    In i (V s).

  Lemma sm_knows_i_if : forall d m, sm_knows d m -> sm_knows_i (sm_signed_msg2value d) m.
  Proof.
    tcsp.
  Qed.

  Definition sm_data2main_auth_data (d : sm_data) : AuthenticatedData :=
    sm_signed_msg2main_auth_data d.

  Definition sm_data2main_auth_data_list (d : sm_data) : list AuthenticatedData :=
    sm_signed_msg2list_auth_data d.

  Definition sm_data2loc (d : sm_data) : Gen :=
    sm_signed_msg2sender d.

  Definition name2gen (n : name) : Gen :=
    match n with
    | general g => g
    end.

  Definition sm_verify (eo : EventOrdering) (e : Event) (d : sm_data) : bool :=
    verify_signed_msg (name2gen (loc e)) (keys e) d.
(*    verify_authenticated_data (loc e) (sm_data2main_auth_data d) (keys e).*)

  Lemma sm_no_initial_memory_i :
    forall n d, ~ sm_knows_i d (Process.sm_state (SMreplicaSM n)).
  Proof.
    introv h; simpl in h; auto.
  Qed.

  Definition sm_output2data (m : DirectedMsg) : list sm_data :=
    match dmMsg m with
    | sm_msg_signed v => [v]
    | _ => []
    end.

  Global Instance SM_I_SysOutput : SysOutput.
  Proof.
    exact (MkSysOutput DirectedMsg).
  Defined.

  Global Instance SM_I_LearnAndKnow_pl : LearnAndKnow 0.
  Proof.
    exact (MkLearnAndKnow
             0
             sm_data
             sm_info
             sm_signed_msg2value
             SMstate
             sm_knows
             sm_knows_i
             sm_knows_i_if
             sm_data2loc
             sm_data2main_auth_data
             sm_data2main_auth_data_list
             sm_verify
             _ sm_no_initial_memory_i).
  Defined.

  Lemma sm_know_i_dec : lak_know_i_dec.
  Proof.
    introv; simpl.
    unfold sm_knows_i.
    destruct (in_dec sm_value_deq d (V m)); tcsp.
  Qed.
  Hint Resolve sm_know_i_dec : sm.

  Definition sm_data2sign (d : sm_data) : Sign := sm_signed_msg2sign d.

  Definition sm_extend_info (v : sm_info) (a : Sign) := sm_signed_msg_sing v a.

  Definition sm_extend_data (d : sm_data) (a : Sign) := sm_signed_msg_cons d a.

  Lemma sm__extend_data_inj :
    forall (d1 d2 : sm_data)
           (s1 s2 : Sign),
      sm_extend_data d1 s1 = sm_extend_data d2 s2
      -> d1 = d2 /\ s1 = s2.
  Proof.
    destruct s1, s2.
    introv H; ginv; tcsp.
  Qed.

  Lemma sm__extend_info_inj :
    forall (d1 d2 : sm_info)
           (s1 s2 : Sign),
      sm_extend_info d1 s1 = sm_extend_info d2 s2
      -> d1 = d2 /\ s1 = s2.
  Proof.
    destruct s1, s2.
    introv H; ginv; tcsp.
  Qed.

  Definition sm_max_sign := F + 1.

  Lemma sm_max_sign_strictly_pos : 1 <= sm_max_sign.
  Proof.
    unfold sm_max_sign; omega.
  Qed.

  Definition sm_sys : MUSystem (fun n => SMstate) := SMsys.

  (* Q: How can I do something like this???
  Definition Sign2sm_sign (s : Sign) : sm_sign :=
    match s with
      MkSign n t => MkSmSign n t
    end.
   *)

  Fixpoint sm_data2can (d : sm_data) : list (lak_data_or_info * Sign) :=
    match d with
    | sm_signed_msg_sing v a =>  [(lak_is_info v, a)]
    | sm_signed_msg_cons d' a => snoc (sm_data2can d') (lak_is_data d', a)
    end.

  (* What happens if the list is empty?*)
  (* Q: I am not sure what to do with this one??? Maybe if we would reverse the list
  Fixpoint sm_can2data (l : list (sm_data * sm_sign)) : sm_data :=
    match l with
    | [d, s] => sm_signed_msg_cons d s
    | [d,s] :: l' =>
      let d' = sm_signed_msg_cons d s in
      sm_can2data
    end.
   *)


  Lemma sm_can_prop_empty :
    forall (d : sm_data),
      sm_data2can d <> [].
  Proof.
    introv h.
    destruct d; simpl in *; ginv.
    apply snoc_implies_empty in h; tcsp.
  Qed.

  Lemma sm_can_prop_diff :
    forall (i     : sm_info)
           (d     : sm_data)
           (s s'  : Sign),
      (sm_extend_info i s) <> (sm_extend_data d s').
  Proof.
    induction d; introv H; simpl in *; ginv; tcsp.
  Qed.

  (* MOVE *)
  Lemma pair_eq_snoc_implies :
    forall {T} {T'} (a c :T) (b d : T') (l : list (T * T')),
      [(a, b)] = snoc l (c, d)
      -> l = []
         /\ a = c
         /\ b = d.
  Proof.
    introv h.
    destruct l; simpl in *; repnd; ginv; tcsp.
    inversion h; subst.
    match goal with [ H : [] = snoc _ _ |- _ ] => rename H into bad end.
    symmetry in bad; apply snoc_implies_empty in bad; tcsp.
  Qed.

  Lemma sm_can_prop_snoc :
    forall  (d    : sm_data)
            (l    : list (lak_data_or_info * Sign))
            (ds   : lak_data_or_info)
            (s    : Sign),
      sm_data2can d = snoc l (ds,s)
      ->
      (exists i,
          d = sm_extend_info i s
          /\ l = [])
      \/
      (exists d',
          d = sm_extend_data d' s
          /\ l = sm_data2can d').
  Proof.
    destruct d; introv h; simpl in *; ginv.

    {
      left.
      unfold sm_extend_info.
      eapply pair_eq_snoc_implies in h; repnd; subst; eauto.
    }

    {
      right.
      unfold sm_extend_data.
      eapply snoc_inj in h; exrepnd; subst; ginv; simpl in *; eauto.
    }
  Qed.

  Lemma sm_can_prop_sign :
    forall (d   : lak_data)
           (s   : Sign),
      sm_data2sign d = s <-> exists l d', sm_data2can d = snoc l (d',s).
  Proof.
    split;[|];
      try (complete (revert dependent d;
      induction d; introv H; simpl in *; subst; tcsp;
        [ exrepnd; eapply pair_eq_snoc_implies in H1; exrepnd; auto
        | exrepnd; eapply snoc_inj in H1; exrepnd; inversion H1; eauto ]));[].

      revert dependent d.
      induction d; introv H; simpl in *; subst; tcsp;
        [exists ([] : list (lak_data_or_info * Sign)) (lak_is_info v); eauto|];[].

      unfold sm_data2sign in *.
      eexists; eexists; dands; eauto.
  Qed.

  Definition sm_data2msg (d : sm_data) : msg := sm_msg_signed d.

  Definition sm_data2data (d : sm_data) (n : node_type) : data :=
    sm_bare_msg_signed (sm_bare_signed_msg_cons d (general n)).

  Global Instance SM_I_Disseminate : Disseminate.
  Proof.
    exact (MkDisseminate sm_data2msg).
  Defined.

  Global Instance SM_I_Memory : Memory.
  Proof.
    exact (MkMemory V).
  Defined.

  Global Instance SM_I_AuthKnowledge : AuthKnowledge.
  Proof.
    exact (MkAuthKnowledge
             sm_data2sign
             sm_extend_info
             sm_extend_data
             sm__extend_data_inj
             sm__extend_info_inj
             sm_data2can
             sm_can_prop_sign
             sm_can_prop_empty
             sm_can_prop_snoc
             sm_can_prop_diff
             sm_max_sign
             sm_max_sign_strictly_pos
             sm_data2data).
  Defined.

End SMknows_choice.
