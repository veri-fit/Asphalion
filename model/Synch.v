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


Require Export CorrectTrace.
Require Export Process.


Section Synch.

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
  Context { tc  : @TimeConstraint dtc }.
  Context { iot : @IOTrustedFun }.


  Local Open Scope eo.


  (* CHECK *)
  (* if [e2] and [e1] are correct, [e2] should be able to verify what [e1] authenticated.
     which implies that [e1] is supposed to have a signing key for [e2] and [e2] is supposed
     to have a receiving key for [e1].
     --- Similar to A4.(b) *)
  Definition AXIOM_verified_authenticated (eo : EventOrdering) :=
    forall (e1 e2 : Event) d,
      has_correct_trace_before e1 (loc e1)
      -> has_correct_trace_before e2 (loc e2)
      -> exists rk tok,
          In rk (lookup_receiving_keys (keys e2) (loc e1))
          /\ In tok (authenticate d (keys e1))
          /\ verify d (loc e1) rk tok = true.

  Definition verified_authenticated_data (n1 n2 : name) (lk1 lk2 : local_key_map) :=
    forall d,
      data_auth n2 d = Some n1
      -> verify_authenticated_data n2 (MkAuthData d (authenticate d lk1)) lk2 = true.

  Lemma verified_authenticated_implies :
    forall {eo : EventOrdering},
      AXIOM_verified_authenticated eo
      ->
      forall (e1 e2 : Event),
        has_correct_trace_before e1 (loc e1)
        -> has_correct_trace_before e2 (loc e2)
        -> verified_authenticated_data (loc e1) (loc e2) (keys e1) (keys e2).
  Proof.
    introv verif cor1 cor2 da.
    pose proof (verif e1 e2 d cor1 cor2) as verif; exrepnd.
    unfold verify_authenticated_data; simpl in *; allrw.
    unfold verify_authenticated_data_keys.
    rewrite existsb_exists.
    exists rk; dands; auto.
    unfold verify_authenticated_data_key.
    rewrite existsb_exists.
    exists tok; dands; auto.
  Qed.

  (* CHECK *)
  (* If [e1] has a receiving key to verify [a] then [e2] should also have
     a receiving key to verify [a].
     -- What if there's only a token for [e1] but not for [e2]?  This rules out MACs.
     --- Similar to A4.(b) *)
  Definition AXIOM_all_correct_can_verify (eo : EventOrdering) :=
    forall (e1 e2 : Event) a,
      has_correct_trace_before e1 (loc e1)
      -> has_correct_trace_before e2 (loc e2)
      -> verify_authenticated_data (loc e1) a (keys e1) = true
      -> verify_authenticated_data (loc e2) a (keys e2) = true.

  (* [d] is correct in the neat future of [e] *)
  Definition is_correct_in_near_future
             (d : name)
             {eo : EventOrdering}
             (e : Event) :=
    exists e',
      loc e' = d
      /\ (time e + epoch_duration <= time e')%dtime
      /\ has_correct_trace_before e' d.

  (* a message sent at [t] will be received between
     [min_received t] and [max_received t]
   *)
  Definition min_received (t : PosDTime) := (t + dlt - tau)%dtime.
  Definition max_received (t : PosDTime) := (t + epoch_duration)%dtime.

  Definition events_in_same_epoch
             {eo    : EventOrdering}
             (e e'  : Event) :=
    (min_received (time e) <= time e' <= max_received (time e))%dtime.

  Definition events_in_same_epoch_delay
             {eo    : EventOrdering}
             (e e'  : Event)
             (t     : PosDTime) :=
    (min_received (pdt_plus (time e) t) <= time e' <= max_received (pdt_plus (time e) t))%dtime.

  (*
     This is essentially A1 in "The Byzantine Generals Problem"

     TODO: do something about the delay---for now this is just for when delay=0
   *)
  Definition AXIOM_messages_get_delivered
             (eo : EventOrdering)
             {S  : StateFunType}
             (sm : MUSystem S) :=
    forall (e : Event)
           (m : DirectedMsg)
           (d : name),
      In m (output_system_on_event_ldata sm e)
(*      -> has_correct_trace_before e (loc e)*)
      -> In d (dmDst m)
(*      -> dmDelay m = nat2pdt 0*)
      -> is_correct_in_near_future d e
      ->
      exists e',
        loc e' = d
        /\ trigger_op e' = Some (dmMsg m)
        /\ events_in_same_epoch_delay e e' (dmDelay m).

End Synch.
