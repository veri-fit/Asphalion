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


Section SMwell_formed_V_def.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { sm_context       : SMcontext }.
  Context { sm_auth          : SMauth }.
  Context { sm_initial_keys  : SMinitial_keys }.


  (* FIX -- we don't need this any more
  Record well_formed_V_entry (V : sm_values) :=
    {
      (* we never two different values twice *)
      well_formed_V_entry_value :
        no_repeats V;

   }.
   *)
  (* FIX: do we need something like --
     value was created because commander or lieutenant sent some message *)


  Definition entries_have_different_values
             (v1 v2 : sm_values) : Prop :=  v1 <> v2.

  (* FIX : is this correct?
    Do we really need entries_have_different_values? *)
  Inductive well_formed_V : sm_values -> Prop :=
  | well_formed_V_nil : well_formed_V []
  | well_formed_V_cons :
      forall val L,
        (forall val',
            In val' L
            -> val <> val')
(*        -> well_formed_V_entry val *)
        -> well_formed_V L
        -> well_formed_V (val :: L).
  Hint Constructors well_formed_V.

End SMwell_formed_V_def.


Hint Constructors well_formed_V.
