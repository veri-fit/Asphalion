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


Require Export SM.
Require Export LearnAndKnows.


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

  Definition sm_data2loc (d : sm_data) : Gen :=
    sm_signed_msg2sender d.

  Definition sm_verify (eo : EventOrdering) (e : Event) (d : sm_data) : bool :=
    verify_authenticated_data (loc e) (sm_data2main_auth_data d) (keys e).

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
             sm_verify
             _ _ sm_no_initial_memory_i).
  Defined.

  Lemma sm_know_i_dec : lak_know_i_dec.
  Proof.
    introv; simpl.
    unfold sm_knows_i.
    destruct (in_dec sm_value_deq d (V m)); tcsp.
  Qed.
  Hint Resolve sm_know_i_dec : sm.

End SMknows_choice.
