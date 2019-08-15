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


Require Export generic_tactics.
Require Export list_util1.


Section Hash.

  Class Digest :=
    MkDigest
      {
        digest : Set;
        digest_deq : Deq digest;
      }.

  Context { dig : Digest }.

  Class Hash :=
    MkHash
      {
        hash_val    : Set;
        create_hash : hash_val -> digest;
        verify_hash : hash_val -> digest -> bool;
      }.

  Context { h : Hash }.

  Class HashAxioms :=
    {
      create_hash_collision_resistant :
        forall (v1 v2 : hash_val),
          create_hash v2 = create_hash v2
          -> v1 = v2
    }.

End Hash.
