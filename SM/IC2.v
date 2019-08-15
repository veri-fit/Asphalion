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


Require Export SMat_most_f_byz.
Require Export SMtactics3.
Require Export SMsame_states.


Section IC2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtime           : TimeConstraint }.

  Context { sm_context      : SMcontext }.
  Context { sm_auth         : SMauth }.
  Context { sm_initial_keys : SMinitial_keys }.

  Definition mk_initial_commander_msg
             (vc : sm_value)
             (c  : Gen)
             (a  : SMtokens) :=
    sm_msg_signed (sm_signed_msg_sing vc (MkSmSign (general c) a)).

  Lemma IC2_safety :
    forall (eo    : EventOrdering)
           (e1 e2 : Event)
           (vc vg : sm_value)
           (g c   : Gen)
           (a     : SMtokens)
           (L     : list name),
      authenticated_messages_were_sent_non_byz_usys eo SMsys
      -> SMcorrect_keys eo
      -> exists_at_most_f_faulty [e1,e2] F
      -> node_has_correct_trace_before e1 c
      -> node_has_correct_trace_before e2 g
      -> is_commander c = true
      -> loc e1 = general c
      -> loc e2 = general g
      -> In (general g) L
      -> In (send_sm_msg_commander (mk_initial_commander_msg vc c a) L)
            (output_system_on_event_ldata SMsys e1)
      -> In (send_sm_msg_result g (sm_msg_result vc))
            (output_system_on_event_ldata SMsys e2)
      -> vc = vg.
  Proof.
    introv sendbyz ckeys atmost corrtr eqloc1 eqloc2 out1 out2.

  Abort.

  Lemma IC2:
    forall (eo  : EventOrdering)
           (e1  : Event)
           (vc  : sm_value)
           (g c : Gen)
           (a   : SMtokens)
           (L   : list name),
      authenticated_messages_were_sent_non_byz_usys eo SMsys
      -> SMcorrect_keys eo
      -> node_has_correct_trace_before e1 c
      -> is_commander c = true
      -> loc e1 = general c
      -> In (general g) L
      -> In (send_sm_msg_commander (mk_initial_commander_msg vc c a) L)
            (output_system_on_event_ldata SMsys e1)
      -> exists e2,
          node_has_correct_trace_before e2 g
          /\ exists_at_most_f_faulty [e1, e2] F
          /\ loc e2 = general g
          /\ In (send_sm_msg_result g (sm_msg_result vc))
                (output_system_on_event_ldata SMsys e2).
  Proof.
    introv sendbyz ckeys corrtr iscomm eqloc1 out1 out2.

(*    destruct (sm_value_deq vc vg) as [v|v]; auto.
    assert False; tcsp.
*)

Abort.




End IC2.
