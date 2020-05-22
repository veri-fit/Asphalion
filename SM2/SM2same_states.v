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


Require Export SM2at_most_f_byz.
Require Export SM2tactics3.


Section SM2same_states.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc   : DTimeContext }.
  Context { dtime : @TimeConstraint dtc }.

  Context { sm_context       : SMcontext }.
  Context { sm_auth          : SMauth }.
  Context { sm_initial_keys  : SMinitial_keys }.

  Lemma SM_replicas_never_stop :
    forall i (x : SMstate) m t, exists s, fst (sm_update (SMreplicaSM i) x m t) = Some s.
  Proof.
    introv.
    unfold SMreplicaSM; simpl.
    unfold SMupdate; destruct m; simpl in *; ginv; tcsp; eauto.

    { unfold SMhandler_initial; smash_sm; eauto. }
    { unfold SMhandler_alarm; smash_sm; eauto. }
    { unfold SMhandler_lieutenant; smash_sm; eauto. }
  Qed.
  Hint Resolve SM_replicas_never_stop : sm2.

End SM2same_states.


Hint Resolve SM_replicas_never_stop : sm2.
