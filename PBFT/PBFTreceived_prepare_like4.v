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


Require Export PBFTreceived_prepare_like1.


Section PBFTreceived_prepare_like4.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  Lemma send_pre_prepares_are_in_log :
    forall (eo : EventOrdering) (e : Event) p dst st i,
      loc e = PBFTreplica i
      -> In (send_pre_prepare p dst) (output_system_on_event_ldata PBFTsys e)
      -> state_sm_on_event (PBFTreplicaSM i) e = Some st
      -> pre_prepare_in_log p (pre_prepare2digest p) (log st) = true.
  Proof.
    introv eqloce j eqst.
    eapply in_output_system_on_event_ldata in j; eauto.

    unfold PBFTsys in j.
    try rewrite eqloce in j.

    rw @loutput_sm_on_event_unroll2 in j.
    fold (@DirectedMsgs _ _ _) in *.
    simpl in *.
    rewrite state_sm_on_event_unroll2 in eqst.

    match goal with
    | [ H : context[state_sm_before_event ?a ?b] |- _ ] =>
      remember (state_sm_before_event a b) as q; symmetry in Heqq; hide_hyp Heqq
    end.
    destruct q; simpl in *; ginv;[].

    op_st_some m eqtrig; rewrite eqtrig in *; simpl in *.

    unfold PBFTreplica_update in *.
    destruct m; simpl in *; ginv; subst; tcsp;
      smash_handlers; try conflicting_sends; try (repndors; ginv; smash_pbft).

    {
      (* request *)

      unfold broadcast2others in j; ginv; simpl in *.

      rename_hyp_with check_new_request check.
      applydup check_new_request_preserves_sequence_number in check.
      rewrite check0; clear check0.

      apply implies_same_pre_prepare_in_add_new_pre_prepare2log.
      simpl.
      introv h w.
      destruct p', b; simpl in *; ginv.

      show_hyp Heqq.
      eapply PBFT_A_1_2_3_before in h;[|eauto|]; eauto 3 with pbft.
      simpl in *; try omega.
    }

    {
      (* pre-prepare *)

      allrw in_app_iff; repndors;
        [apply in_check_broadcast_prepare_implies in j;exrepnd;subst;ginv
        |apply in_check_broadcast_commit_implies in j; exrepnd;subst;ginv
        |].

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* prepare *)

      allrw in_app_iff; repndors;
        [apply in_check_broadcast_commit_implies in j; exrepnd;subst;ginv
        |].

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* commit *)

      rename_hyp_with check_send_replies check.
      eapply message_in_check_send_replies_implies in check;[|eauto]; ginv.
    }

    {
      (* check-ready *)

      rename_hyp_with find_and_execute_requests fexec.
      eapply message_in_find_and_execute_requests_implies in fexec;[|eauto].
      repndors; exrepnd; conflicting_sends.
    }

    {
      (* check-bcast-new-view *)

      rename_hyp_with update_state_new_view upd.

      unfold broadcast2others in *; repndors; ginv;[].
      eapply message_in_update_state_new_view_implies in upd;[|eauto].
      exrepnd; ginv.
    }

    {
      (* new_view *)

      rename_hyp_with update_state_new_view upd.
      rename_hyp_with add_prepares_to_log_from_new_view_pre_prepares add.

      allrw in_app_iff; repndors;
        [|eapply message_in_update_state_new_view_implies in upd;
          [|eauto];exrepnd;ginv];[].

      apply send_pre_prepare_in_trim_outputs_with_low_water_mark in j.
      eapply in_add_prepares_to_log_from_new_view_pre_prepares_implies in add;[|eauto].
      repndors; exrepnd; ginv.
    }
  Qed.
  Hint Resolve send_pre_prepares_are_in_log : pbft.

End PBFTreceived_prepare_like4.


Hint Resolve send_pre_prepares_are_in_log : pbft.
