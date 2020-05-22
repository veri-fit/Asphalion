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


Require Export SM2tactics3.


Section SM2well_formed_V.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { sm_context       : SMcontext }.
  Context { sm_auth          : SMauth }.
  Context { sm_initial_keys  : SMinitial_keys }.

(* FIX -- it looks like add_value_to_V_no_order_yet is not used any more
  Lemma add_value_to_V_no_order_yet_well_formed_V :
    forall (L             : list sm_values)
           (val           : sm_value)
           (senders       : Gen),
      no_order_yet L = true
      -> well_formed_V L
      -> well_formed_V (add_value_to_V_no_order_yet val senders L).
  Proof.
    induction L; introv np wf; simpl in *; ginv; tcsp.

    { constructor; simpl; tcsp; eauto.
      sm_destruct_all. }
  Qed.
  Hint Resolve add_value_to_V_no_order_yet_well_formed_V : sm.
 *)

(* FIX -- fix these proofs
 Lemma check_new_value_well_formed_V :
    forall (L             : sm_values)
           (val           : sm_value)
           (i             : Gen)
           (msg           : sm_signed_msg),
      check_new_value i L msg = true
      -> well_formed_V L
      -> well_formed_V (add_value_to_V_order_exists val L).
  Proof.
    induction L; introv cn wf; simpl in *; ginv; tcsp.

    inversion wf as [|? ? imp wfentry wfL]; subst; clear wf.

    unfold check_new_value in *.
    dest_cases x; simpl in *; ginv; tcsp; [].

    pose proof (IHL val i msg) as xx. clear IHL.
    autodimp xx hyp;[ dest_cases x| ].
    autodimp xx hyp.

    apply not_or in n.
    destruct n.
  Abort.
  Hint Resolve check_new_value_well_formed_V : sm.


(* Fix generalize this into tactic *)
  Lemma V_is_well_formed_on_event :
    forall i (eo : EventOrdering) e st,
      state_sm_on_event (SMreplicaSM i) e = Some st
      -> well_formed_V (V st).
  Proof.
  (*  prove_by_ind ind h eqst sop p m eqtrig trig smash_handlers smash_sm_ind. *)
    start_ind ind;
      introv;
      intro_state h eqst;
      try unroll_state;
      simpl in *;
      destruct_unrolled_state sop p;
      op_st_some m eqtrig;
        unfold_update ind trig tac1 tac2;
        try smash_handlers; smash_sm_ind ind; eauto with sm;
          try(
        constructor; simpl; tcsp; eauto;
        sm_destruct_all).
  Qed.
  Hint Resolve V_is_well_formed_on_event : sm.

  Lemma V_is_well_formed :
      forall i (eo : EventOrdering) e st,
      state_sm_before_event (SMreplicaSM i) e = Some st
      -> well_formed_V (V st).
  Proof.
    introv eqst.
    rewrite <- ite_first_state_sm_on_event_as_before in eqst.
    unfold ite_first in *.
    destruct (dec_isFirst e) as [d|d]; ginv; subst; simpl in *; eauto 3 with sm.
  Qed.
  Hint Resolve V_is_well_formed : sm.

  Lemma well_formed_V_entry_implies_no_repeats :
      forall entry,
        well_formed_V_entry entry
        -> no_repeats (senders entry).
  Proof.
    sm_brute_force.
  Qed.
  Hint Resolve well_formed_V_entry_implies_no_repeats : sm.

  Lemma well_formed_V_implies_no_repeats :
    forall entry L,
      well_formed_V L
      -> In entry L
      -> no_repeats (senders entry).
  Proof.
    induction L; introv h1 h2; simpl in *; ginv; tcsp.

    inversion h1. subst. simpl in *.
    apply well_formed_V_entry_implies_no_repeats in H2.

    destruct h2; [subst; auto | autodimp IHL hyp].
  Qed.
  Hint Resolve well_formed_V_implies_no_repeats : sm.
*)

End SM2well_formed_V.

(*
Hint Resolve add_value_to_V_no_order_yet_well_formed_V : sm.
Hint Resolve check_new_value_well_formed_V : sm.
Hint Resolve V_is_well_formed_on_event : sm.
Hint Resolve V_is_well_formed : sm.
Hint Resolve well_formed_V_entry_implies_no_repeats : sm.
Hint Resolve well_formed_V_implies_no_repeats : sm.
*)