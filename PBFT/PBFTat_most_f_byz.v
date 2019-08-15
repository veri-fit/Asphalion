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


Require Export PBFT.
Require Export CorrectKeys.


Section PBFTat_most_f_byz.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pbft_context : PBFTcontext      }.
  Context { pbft_auth    : PBFTauth         }.
  Context { pbft_keys    : PBFTinitial_keys }.
  Context { pbft_hash    : PBFThash         }.


  (* This says that all the events [e] _at all time_ that happen
      at non-faulty locations (not in the [faulty] list are indeed non-faulty *)
  Definition PBFT_at_most_f_byz1 (eo : EventOrdering) :=
    exists (faulty : list Rep),
      length faulty <= F
      /\
      forall (e : Event),
        ~ In (loc e) (map PBFTreplica faulty)
        -> isCorrect e.

  Lemma PBFT_at_most_f_byz1_implies :
    forall (eo : EventOrdering) L,
      PBFT_at_most_f_byz1 eo -> AXIOM_exists_at_most_f_faulty L F.
  Proof.
    introv atmost.
    unfold PBFT_at_most_f_byz1 in *.
    exrepnd.
    exists faulty.
    repnd; dands; auto.
    introv i j k eqn w.
    apply atmost0.
    intro xx; rw in_map_iff in xx; exrepnd.
    applydup localLe_implies_loc in w as zz; rewrite zz in *.
    rewrite k in *; simpl in *; ginv.
  Qed.
  Hint Resolve PBFT_at_most_f_byz1_implies : pbft.

  Definition AXIOM_PBFTcorrect_keys (eo : EventOrdering) : Prop :=
    forall (e e' : Event) i st,
      node_has_correct_trace_before e i
      -> e' ≼ e
      -> loc e' = node2name i
      -> state_sm_before_event (PBFTreplicaSM i) e' = Some st
      -> keys e' = local_keys st.

  Definition default_local_key_map : local_key_map :=
    MkLocalKeyMap [] [].

  Definition PBFTget_keys (i : node_type) : PBFTstate -> local_key_map := local_keys.

  Lemma correct_keys_implies_PBFTcorrect_keys :
    forall (eo : EventOrdering),
      AXIOM_correct_keys PBFTsys PBFTget_keys eo
      -> AXIOM_PBFTcorrect_keys eo.
  Proof.
    introv cor ctrace lee eqi eqst.
    apply (cor e i st); auto.
  Qed.

End PBFTat_most_f_byz.


Hint Resolve PBFT_at_most_f_byz1_implies : pbft.
