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


Require Import tactics2.
Require Import Ascii String.


Definition print_endline : string -> unit := fun _ => tt.

Definition CR : string := String (ascii_of_nat 13) "".

Fixpoint str_concat (l : list String.string) : String.string :=
  match l with
  | [] => ""
  | s :: ss => String.append s (str_concat ss)
  end.

Definition bool2string (b : bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

Definition nat2string_aux (n : nat) : string :=
  match n with
  | 0  => "0"
  | 1  => "1"
  | 2  => "2"
  | 3  => "3"
  | 4  => "4"
  | 5  => "5"
  | 6  => "6"
  | 7  => "7"
  | 8  => "8"
  | 9  => "9"
  | _  => "-"
  end.

Lemma nat2string : nat -> string.
Proof.
  apply comp_ind_type; introv ind.
  destruct n.
  { exact "0". }
  remember (Nat.modulo (S n) 10) as md.
  remember (Nat.div (S n) 10) as dv.
  pose proof (Nat.div_lt (S n) 10) as h.
  repeat (autodimp h hyp); auto.
  { apply Nat.lt_0_succ. }
  { repeat apply lt_n_S; apply Nat.lt_0_succ. }
  pose proof (ind (S n / 10) h) as x.
  exact (String.append x (nat2string_aux md)).
Defined.

Definition op2string {T} (f : T -> string) (o : option T) : string :=
  match o with
  | Some t => str_concat ["Some(", f t, ")"]
  | None => "None"
  end.
