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


Require Export SM2.
Require Export CorrectKeys.


Section SM2at_most_f_byz.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc   : @DTimeContext }.
  Context { dtime : @TimeConstraint dtc }.

  Context { sm_context       : SMcontext }.
  Context { sm_auth          : SMauth }.
  Context { sm_initial_keys  : SMinitial_keys }.


  (* This says that all the events [e] _at all time_ that happen
      at non-faulty locations (not in the [faulty] list) are indeed non-faulty *)
  Definition SM_at_most_f_byz1 (eo : EventOrdering) :=
    exists (faulty : list Gen),
      length faulty <= F
      /\
      forall (e : Event) g,
        loc e = general g
        -> ~ In g faulty
        -> isCorrect e.

  Lemma SM_at_most_f_byz1_implies :
    forall (eo : EventOrdering) L,
      SM_at_most_f_byz1 eo -> AXIOM_exists_at_most_f_faulty L F.
  Proof.
    introv atmost.
    unfold SM_at_most_f_byz1 in *.
    exrepnd.
    exists faulty.
    repnd; dands; auto.
    introv i j k eqn w.
    eapply atmost0; eauto.
    applydup localLe_implies_loc in w; rewrite w0; auto.
  Qed.
  Hint Resolve SM_at_most_f_byz1_implies : sm2.

  Definition AXIOM_SMcorrect_keys (eo : EventOrdering) : Prop :=
    forall (e : Event) (i : Gen) st,
      loc e = node2name i
      -> node_has_correct_trace_before e i
      -> state_sm_before_event (SMreplicaSM i) e = Some st
      -> keys e = local_keys st.

  Definition default_local_key_map : local_key_map :=
    MkLocalKeyMap [] [].

  Definition SMget_keys : forall (g : Gen), SMstate -> local_key_map := fun g s => local_keys s.

  Lemma correct_keys_implies_SMcorrect_keys :
    forall (eo : EventOrdering),
      AXIOM_correct_keys SMsys SMget_keys eo
      -> AXIOM_SMcorrect_keys eo.
  Proof.
    introv cor eqn ctrace eqst.
    apply (cor e i st); auto; eauto 2 with eo.
  Qed.

End SM2at_most_f_byz.


Hint Resolve SM_at_most_f_byz1_implies : sm2.
