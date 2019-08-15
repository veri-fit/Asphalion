
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


Require Export LearnAndKnows.


Section Disseminate.

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


  Class Disseminate (n : nat) :=
    MkDisseminate {
        (* known raw data *)
        dis_data : Type;

        (* some distinguished information embedded in the data *)
        dis_info : Type;

        (* to compute the info from the data *)
        dis_data2info : dis_data -> dis_info;

        (* where we store data *)
        dis_memory : Type;

        (* explains what it means to know the data *)
        dis_knows : dis_data -> dis_memory -> Prop;

        (* explains what it means to know some info *)
        dis_knows_i : dis_info -> dis_memory -> Prop;

        (* connects the two knowledge operators *)
        dis_knows_i_if : forall d m, dis_knows d m -> dis_knows_i (dis_data2info d) m;

        (* "owner" of the data *)
        dis_data2owner : dis_data -> node_type;

        (* to verify the authenticity of the data *)
        dis_data2auth : dis_data -> AuthenticatedData;
        dis_verify : forall {eo : EventOrdering} (e : Event) (d : dis_data), bool;

        (* the system *)
        dis_msg2data : DirectedMsg -> list dis_data;
        dis_system : MUSystem (fun _ => dis_memory);
        dis_no_initial_memory_i : forall n i, ~ dis_knows_i i (sm_state (dis_system n));
      }.

  Context { p : nat }.

  Context { dis : Disseminate p }.

  Instance lak : LearnAndKnow p :=
    MkLearnAndKnow
      p
      dis_data
      dis_info
      dis_data2info
      dis_memory
      dis_knows
      dis_knows_i
      dis_knows_i_if
      dis_data2owner
      dis_data2auth
      (fun eo e d => dis_verify e d)
      DirectedMsg
      dis_system
      dis_no_initial_memory_i.

  (* ========== DISSEMINATING ========= *)

  Definition disseminate {eo : EventOrdering} (e : Event) (d : lak_data) :=
    exists n,
      loc e = node2name n
      /\ In d (flat_map dis_msg2data (loutput_sm_on_event (lak_system n) e)).

  Definition disseminate_i {eo : EventOrdering} (e : Event) (i : lak_info) :=
    exists d, disseminate e d /\ i = lak_data2info d.

  (* One often disseminate knowledge that it holds *)
  Definition disseminate_if_knows (eo : EventOrdering) : Prop :=
    forall (e : Event) (d : lak_data),
      disseminate e d -> knows e d.

  Definition disseminate_if_knows_i (eo : EventOrdering) : Prop :=
    forall (e : Event) (i : lak_info),
      disseminate_i e i -> knows_i e i.

  Definition disseminate_before_deadline
             (eo : EventOrdering)
             (M  : lak_data -> Prop)
             (N  : name -> Prop)
             (deadline : dt_T) :=
    forall (e : Event) (d : lak_data),
      has_correct_trace_before e (loc e)
      -> M(d)
      -> N(loc(e))
      -> disseminate e d
      -> (time e <= deadline)%dtime.

  Definition triggers_satisfy_constraint {eo : EventOrdering} (e : Event) (d : lak_data) (M : lak_data -> Prop) :=
    forall (e : Event),
      In (lak_data2auth d) (bind_op_list get_contained_authenticated_data (trigger e))
      -> M(d) /\ is_protocol_event e.

  Lemma message_is_sent_before_deadline :
    forall {eo : EventOrdering} (e : Event)
           (M : lak_data -> Prop) (N : name -> Prop)
           (d : AuthenticatedData) n (deadline : dt_T),
      AXIOM_authenticated_messages_were_sent_or_byz_usys eo dis_system
      -> has_correct_trace_before e n
      -> disseminate_before_deadline eo M N deadline
      (*-> all_containers_satisfy_constraint d M*)
      -> verify_authenticated_data (loc e) d (keys e) = true
      -> In d (bind_op_list get_contained_authenticated_data (trigger e))
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
    apply before in w4; simpl; auto; eauto 3 with eo; try (apply cont; auto);[].
    exists e'; dands; auto.
  Qed.

  (* ========= ========= *)


End Disseminate.
