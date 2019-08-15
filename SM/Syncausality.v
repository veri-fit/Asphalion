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

Require Export Synch.
Require Export LearnAndKnows.

Section  Syncausality.

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
  Context { iot : @IOTrusted }.
  Context { p : nat }.
  Context { lak : LearnAndKnow p }.


  Local Open Scope eo.

  Definition BoundType := name -> name -> PosDTime.

  (* timeout
     here [b] is the channel bound *)
  Definition before_timer
             (b  : BoundType)
             (eo : EventOrdering) :=
    forall (e1 e2 : Event),
      dt_le (pdt_plus (time e1) (b (loc e1) (loc e2))) (time e2)
      -> e1 ≺ e2.

  (* 2 messages sent at two different events must have different ids *)
  Definition message_uniqueness
             (id : msg -> nat)
             {eo : EventOrdering}
             {S  : StateFunType}
             (sm : MUSystem S) :=
    forall (e1 e2 : Event) (m1 m2 : DirectedMsg),
      In m1 (output_system_on_event_ldata sm e1)
      -> In m2 (output_system_on_event_ldata sm e2)
      -> id (dmMsg m1) = id (dmMsg m2)
      -> e1 = e2.


  Definition sent_and_received_message
             {eo : EventOrdering}
             {S  : StateFunType}
             (m  : DirectedMsg)
             (sm : MUSystem S)
             (e1 : Event) (* sending event *)
             (e2 : Event) (* receiving event *) :=
    In m (output_system_on_event_ldata sm e1)
    /\ trigger_op e2 = Some (dmMsg m)
    /\ In (loc e2) (dmDst m).

  (* Sadly, to talk about runs here, we have to mention the actual code, i.e.,
     the state machines, because event orderings do no include events' outputs. *)

  (* if message was sent at (i,t) and received at (j,t'), then (i,t)⤳(j,t') *)
  (* This is only true when assuming something like [message_uniqueness] *)
  Definition message_precedence
             (eo : EventOrdering)
             {S  : StateFunType}
             (sm : MUSystem S) : Prop :=
    forall (e1 e2 : Event)
           (m     : DirectedMsg),
      sent_and_received_message m sm e1 e2
      -> e1 ≺ e2.

  (* we deine syncausality as constraint over EventOrdering
     here we assume that all channels have the same bounded delay *)
  Definition Syncausality
             (b  : BoundType)
             (eo : EventOrdering)
             {S  : StateFunType}
             (sm : MUSystem S) : Type :=
      before_timer b eo
      /\ message_precedence eo sm.



  Definition kn_occurred
             (eo : EventOrdering)
             (t  : PosDTime)
             (e  : Event) := dt_le (time e) t.

  (* arrival of the external input *)
  Definition external_input
             (eo : EventOrdering)
             (e  : Event) :=
    exists j m,
      is_external_event e = true
      /\ loc e = j
      /\ In (lak_data2auth m) (bind_op_list get_contained_authenticated_data (trigger_op e)).


  (* message delivered strictly before the transmission delay *)
  Definition message_delivered_before_transmission_delay
             (b  : BoundType)
             (eo : EventOrdering)
             {S  : StateFunType}
             (sm : MUSystem S)
             (e  : Event) :=
    exists (e' : Event) (j : name) (m : DirectedMsg),
      sent_and_received_message m sm e' e
      /\ (time e < time e' + b (loc e') (loc e))%dtime. (* FIX: do we add here the lower bound? *)

(*  (* message delivered strictly before the transmission delay *)
  Definition message_delivered_before_transmission_delay_xxx
             (eo : EventOrdering)
             (e  : Event)
             (b  : PosDTime) :=
    exists (e' : Event) (j : name) (m : lak_data),
      loc e' = j
      /\ In (lak_data2auth m) (bind_op_list get_contained_authenticated_data (trigger_op e'))
      /\ (time e' < time e + b)%dtime. (* FIX: do we add here the lower bound? *)
*)

  (* nondeterministic event *)
  (* FIX: Should we add here verify also? *)
  Definition ND
             (b     : BoundType)
             (eo    : EventOrdering)
             {S  : StateFunType}
             (sm : MUSystem S)
             (e     : Event) :=
    is_external_event e = true
    \/ message_delivered_before_transmission_delay b eo sm e.

  Definition kn_ND
             (b  : BoundType)
             (eo : EventOrdering)
             {S  : StateFunType}
             (sm : MUSystem S)
             (t  : PosDTime)
             (e  : Event) :=
    ND b eo sm e /\ kn_occurred eo t e.

  Definition kn_prop :=
    forall (b  : BoundType)
           (eo : EventOrdering)
           {S  : StateFunType}
           (sm : MUSystem S)
           (t  : PosDTime), Prop.


(*  Definition holds
             (eo : EventOrdering)
             (t  : PosDTime)
             (fi : Type) :=
    forall e, time e = t -> fi.*)

  Definition kn_knows
             (b  : BoundType)
             {eo : EventOrdering}
             {S  : StateFunType}
             (sm : MUSystem S)
             (t  : PosDTime)
             (FI : kn_prop) :=
    exists (e : Event),
      time e = t
      /\
      forall (eo' : EventOrdering) e' t' i, (* FIX: this should be only eo', right? *)
        loc e = node2name i
        -> loc e' = node2name i
        -> state_sm_on_event (sm i) e = state_sm_on_event (sm i) e'
        -> time e' = t'
        -> FI b eo' _ sm t'.


(*
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

  (* FIX:  Is this one ok, or we need something like futurexxx (see below) *)
  Definition fut
             (eo : EventOrdering)
             (e  : Event)
             (i  : name) :=
    forall j,
    exists e',
      syncausality (i, time e) (j, time e').


  Definition exists_event_syncausality
             (eo   : EventOrdering)
             (e    : Event)
             (i j  : name) :=
   exists e', syncausality (i, time e) (j, time e').

  (* FIX : NOT COMPILING!!!
  Fixpoint futxx
             (eo : EventOrdering)
             (e  : Event)
             (i  : name)
             (l  : list node_type) : list name :=
    match l with
    | [] => []
    | j :: l' => if exists e', syncausality (i, time e) (node2name j, time e') then [node2name j] ++ fut eo e i l'
                else fut eo e i l'
    end.

  Definition futurexx
             (eo : EventOrdering)
             (e  : Event)
             (i  : name) : list name :=
    futxx eo e i nodes.
   *)


  (* FIX: Similar as for the fut *)
  Definition past
             (eo : EventOrdering)
             (e  : Event)
             (j  : name) : Set :=
    forall i,
    exists e',
      syncausality (i, time e) (j, time e').

  (* FIX: here we should be able to compare the nodes of two past. But we have forall... *)
  Definition past_equality
             (eo eo'   : EventOrdering)
             (e e'     : Event)
             (i j      : name) : bool := false.

  (* FIX: similar here *)
  Definition early_receives_for_all_nodes_of_the_past
             (eo eo'   : EventOrdering)
             (e e'     : Event)
             (i j      : name) : bool := false.


  (* Lemma 1 *)
  (* FIX: not compiling!!!
  Lemma fut_past_intersection :
          forall (eo : EventOrdering)
                 (e  : Event)
                 (i  : name),
            (fut eo e i) /\ (past eo e i) = i. *)

  (* FIX: I have to add to Msg.v decidability of the messages, otherwise this one is not going to compile
  Definition external_inputs_same
             (eo eo'   : EventOrdering)
             (e e'     : Event) : bool :=
    match trigger_op e, trigger_op e' with
    | Some msg, Some msg' => if msg = msg' then true else false
    | _, _  => false
    end. *)

  (* Lemma 2 *)
  Lemma past_agree_states_agree :
    forall (eo eo' : EventOrdering)
           (e e'    : Event)
           (j       : name)
           (k       : node_type)
           (b       : PosDTime),
      past_equality eo eo' e e' j j = true
      -> loc e  = node2name k
      -> loc e' = node2name k
      -> name2node j = Some k
      (*      -> lak_no_initial_memory_i k *) (* FIX: Do we really need something like this? *)
      (* -> external_inputs_same eo eo' e e' = true *) (* FIX: uncomment *)
      -> early_receives_for_all_nodes_of_the_past eo eo' e e' j j = true
      -> state_sm_on_event (lak_system k) e = state_sm_on_event (lak_system k) e'.
  Proof.
    intros.
    unfold past_equality, (* external_inputs_same, *) early_receives_for_all_nodes_of_the_past in *.
  Abort.

  (* Theorem 2*)
  (* FIX : not compiling!
  Lemma two_process_knowledge_gain :
    forall (eo      : EventOrdering)
           (e e'    : Event)
           (i0 i1   : name)
           (k       : node_type)
           (t t'    : PosDTime),
      loc e = i0
      -> time e = t
      -> loc e = node2name k
      -> kn_knows e t i1 k ND(e)
      -> time e' = t'
      -> syncausality (i0, t) (i1, t'). *)

  (* Definition 3. *)
  Class Bounded_guarantee :=
    {
      bounded_guarantee       :  name * PosDTime -> name * PosDTime -> Prop;

      minimal_distance:
        forall {eo    : EventOrdering}
               (e e'  : Event)
               (i j   : name)
               (d     : PosDTime),  (* weighted distance between i and j *)
          dt_le (pdt_plus (time e) d) (time e')
          -> bounded_guarantee (i, time e) (j, time e');
    }.

  Context { bg : Bounded_guarantee }.


XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
*)



  (* Definition 4 (Centripede) *)
  (* FIX !!! *)
  Definition centripede
             (eo    : EventOrdering)
             (l     : list name)
             (k     : nat) (* length of the list *)
             (t t'  : PosDTime) :=
    lt_le t t'
    /\
    forall i,
      In i l,
    bounded_guarantee xxx (i, t')


XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

  Definition kn_occurred
             {eo : EventOrdering}
             (e  : Event)
             (t  : PosDTime) := dt_le (time e) t.


  (* nondeterministic event *)
  Definition ND
             {eo    : EventOrdering}
             (e     : Event)
             (j     : name)
             (m     : lak_data)
             (b     : PosDTime) :=
    (* arrival of the external input *)
    (
      is_external_event e = true (* FIX: is it e here?*)
      /\ loc e = j
      /\ In (lak_data2auth m) (bind_op_list get_contained_authenticated_data (trigger_op e))
    )
    \/
    (* message delivered strictly before the transmission delay *)
    (
      exists e',
        loc e' = j
        /\ In (lak_data2auth m) (bind_op_list get_contained_authenticated_data (trigger_op e'))
        /\ (time e' < time e + b)%dtime (* FIX: do we add here the lower bound? *)
    ).

  Definition kn_ND
             {eo    : EventOrdering}
             (e     : Event)
             (t     : PosDTime)
             (j     : name)
             (m     : lak_data)
             (b     : PosDTime) :=
    ND e j m b /\ kn_occurred e t.

  (* FIX : I don't see the actual difference between the definition introduced in the paper and one that we already have
           check knows_implies in LearnAndKnows.v *)
  (*  Definition kn_sync
             {eo    : EventOrdering}
             (e     : Event)
             (t     : PosDTime)
             {S     : StateFunType}
             (sm    : MUSystem S)
             (j     : name)
             (m     : lak_data)
             (v     : lak_info)
             (b     : PosDTime) :=
    knows e m
    /\ kn_ND e t j m v b
    /\ (time e <= (nat2pdt (length (lak_data2auth m)) * b))%dtime.
*)


End Syncausality.

Notation "(a,time e) ⤳ (b, time e')" := (syncausality (a, time e) (b,time e')) (at level 0).