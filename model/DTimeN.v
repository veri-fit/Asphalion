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


Require Import Arith.
Require Import PeanoNat.
Require Export DTime.


Section DTimeN.

  Definition N_dt_T : Type := nat.

  Definition N_dt_0 : N_dt_T := 0.

  Definition N_dt_1 : N_dt_T := 1.

  Definition N_dt_add : N_dt_T -> N_dt_T -> N_dt_T := plus.

  Definition N_dt_mul : N_dt_T -> N_dt_T -> N_dt_T := mult.

  Definition N_dt_sub : N_dt_T -> N_dt_T -> N_dt_T := minus.

  Definition N_dt_eq : relation N_dt_T := eq.

  Definition N_dt_lt : relation N_dt_T := lt.

  Definition N_dt_le : relation N_dt_T := fun a b => a <=? b = true.

  Definition N_dt_eqv : Equivalence N_dt_eq := Nat.eq_equiv.

  Definition N_dt_ring : semi_ring_theory N_dt_0 N_dt_1 N_dt_add N_dt_mul N_dt_eq.
  Proof.
    exact natSRth.
  Qed.

  Definition N_dt_nat_inj : nat -> N_dt_T := fun n => n.

  Definition N_dt_add_morph : forall x y, N_dt_eq x y -> forall u v, N_dt_eq u v -> N_dt_eq (N_dt_add x u) (N_dt_add y v).
  Proof.
    introv a b; rewrite a, b; reflexivity.
  Qed.

  Definition N_dt_sub_morph : forall x y, N_dt_eq x y -> forall u v, N_dt_eq u v -> N_dt_eq (N_dt_sub x u) (N_dt_sub y v).
  Proof.
    introv a b; rewrite a, b; reflexivity.
  Qed.

  Definition N_dt_mul_morph : forall x y, N_dt_eq x y -> forall u v, N_dt_eq u v -> N_dt_eq (N_dt_mul x u) (N_dt_mul y v).
  Proof.
    introv a b; rewrite a, b; reflexivity.
  Qed.

  Definition N_dt_le_morph : forall x y, N_dt_eq x y -> forall u v, N_dt_eq u v -> N_dt_le x u -> N_dt_le y v.
  Proof.
    introv a b h; rewrite a, b in h; auto.
  Qed.

  Definition N_dt_lt_morph : forall x y, N_dt_eq x y -> forall u v, N_dt_eq u v -> N_dt_lt x u -> N_dt_lt y v.
  Proof.
    introv a b h; rewrite a, b in h; auto.
  Qed.

  Definition N_dt_nat_inj_cond : forall (n : nat), N_dt_eq (N_dt_nat_inj n) (ntimes n N_dt_0 N_dt_1 N_dt_add).
  Proof.
    unfold N_dt_eq, N_dt_nat_inj, N_dt_0; induction n; simpl; auto; try reflexivity.
  Qed.

  Definition N_dt_le_refl : forall t , N_dt_le t t.
  Proof.
    introv; apply Nat.leb_le; apply le_refl.
  Qed.

  Definition N_dt_lt_irrefl : forall t , ~ (N_dt_lt t t).
  Proof.
    apply lt_irrefl.
  Qed.

  Definition N_dt_add_le_compat : forall a b c d, N_dt_le a c -> N_dt_le b d -> N_dt_le (N_dt_add a b) (N_dt_add c d).
  Proof.
    introv p q; apply Nat.leb_le; apply plus_le_compat; apply Nat.leb_le; auto.
  Qed.

  Definition N_dt_add_lt_le_compat : forall a b c d, N_dt_lt a c -> N_dt_le b d -> N_dt_lt (N_dt_add a b) (N_dt_add c d).
  Proof.
    introv p q; apply plus_lt_le_compat;[|apply Nat.leb_le];auto.
  Qed.

  Definition N_dt_mul_le_compat_r : forall a b c, N_dt_le a b -> N_dt_le N_dt_0 c -> N_dt_le (N_dt_mul a c) (N_dt_mul b c).
  Proof.
    introv h q; apply Nat.leb_le; apply mult_le_compat_r; apply Nat.leb_le; auto.
  Qed.

  Definition N_dt_le_trans : forall a b c, N_dt_le a b -> N_dt_le b c -> N_dt_le a c.
  Proof.
    introv p q; apply Nat.leb_le; eapply le_trans; apply Nat.leb_le; eauto.
  Qed.

  Definition N_dt_lt_trans : forall a b c, N_dt_lt a b -> N_dt_lt b c -> N_dt_lt a c.
  Proof.
    introv; apply lt_trans.
  Qed.

  Definition N_dt_le_lt_trans : forall a b c, N_dt_le a b -> N_dt_lt b c -> N_dt_lt a c.
  Proof.
    introv p q; eapply le_lt_trans;[apply Nat.leb_le|]; eauto.
  Qed.

  Definition N_dt_lt_le_trans : forall a b c, N_dt_lt a b -> N_dt_le b c -> N_dt_lt a c.
  Proof.
    introv p q; eapply lt_le_trans;[|apply Nat.leb_le]; eauto.
  Qed.

  Definition N_dt_mul_0_l : forall x, N_dt_eq (N_dt_mul N_dt_0 x) N_dt_0.
  Proof.
    introv; apply mult_0_l.
  Qed.

  Definition N_dt_lt_0_1 : N_dt_lt N_dt_0 N_dt_1.
  Proof.
    unfold N_dt_lt, N_dt_0, N_dt_1; simpl; auto.
  Qed.

  Definition N_dt_lt_le_weak : forall a b, N_dt_lt a b -> N_dt_le a b.
  Proof.
    introv p; apply Nat.leb_le; apply lt_le_weak; auto.
  Qed.

  Definition N_dt_lt_le_dec : forall x y, {N_dt_lt x y} + {N_dt_le y x}.
  Proof.
    introv; destruct (le_lt_dec y x) as [z|z];[right;apply Nat.leb_le|left]; auto.
  Qed.

  Definition N_dt_eq_dec : forall x y, {N_dt_eq x y} + {~ N_dt_eq x y}.
  Proof.
    introv; apply Nat.eq_dec.
  Qed.

  Definition N_dt_nat_inj_add_dist : forall n m, N_dt_eq (N_dt_add (N_dt_nat_inj n) (N_dt_nat_inj m)) (N_dt_nat_inj (n + m)).
  Proof.
    introv; unfold N_dt_eq, N_dt_add, N_dt_nat_inj; simpl; auto.
  Qed.

  Definition N_dt_nat_nat_inj_le : forall n m, n <= m -> N_dt_le (N_dt_nat_inj n) (N_dt_nat_inj m).
  Proof.
    introv h; unfold N_dt_eq, N_dt_add, N_dt_nat_inj, N_dt_le; simpl; auto;apply Nat.leb_le; auto.
  Qed.

  Definition N_dt_nat_nat_inj_lt : forall n m, n < m -> N_dt_lt (N_dt_nat_inj n) (N_dt_nat_inj m).
  Proof.
    introv h; unfold N_dt_eq, N_dt_add, N_dt_nat_inj, N_dt_lt; simpl; auto.
  Qed.

  Definition N_dt_mul_le_r_le : forall x y z, N_dt_lt N_dt_0 z -> N_dt_le (N_dt_mul x z) (N_dt_mul y z) -> N_dt_le x y.
  Proof.
    introv h q.
    apply Nat.leb_le; apply Nat.leb_le in q; apply Nat.mul_le_mono_pos_r in q; auto.
  Qed.

  Definition N_dt_mul_lt_compat_r : forall a b c, N_dt_lt a b -> N_dt_lt N_dt_0 c -> N_dt_lt (N_dt_mul a c) (N_dt_mul b c).
  Proof.
    introv h q.
    apply mult_lt_compat_r; auto.
  Qed.

  Definition N_dt_mul_lt_r_lt : forall x y z, N_dt_lt N_dt_0 z -> N_dt_lt (N_dt_mul x z) (N_dt_mul y z) -> N_dt_lt x y.
  Proof.
    introv h q.
    apply Nat.mul_lt_mono_pos_r in q; auto.
  Qed.

  Definition N_dt_nat_inj_lt_nat : forall n m, N_dt_lt (N_dt_nat_inj n) (N_dt_nat_inj m) -> n < m.
  Proof.
    introv h; unfold N_dt_lt, N_dt_nat_inj in *; auto.
  Qed.

  Definition N_dt_approx (x : nat) : nat := x.

  Definition N_dt_ind :
    forall (P : N_dt_T -> Prop),
      (forall t, (forall u, N_dt_lt u t -> P u) -> P t) -> forall t, P t.
  Proof.
    introv h; introv; apply comp_ind; auto.
  Qed.


  Global Instance DTimeContextN : DTimeContext :=
    MkDTimeContext
      N_dt_T
      N_dt_0
      N_dt_1
      N_dt_add
      N_dt_mul
      N_dt_sub
      N_dt_eq
      N_dt_lt
      N_dt_le
      N_dt_eqv
      N_dt_ring
      N_dt_nat_inj
      N_dt_approx
      N_dt_add_morph
      N_dt_mul_morph
      N_dt_sub_morph
      N_dt_le_morph
      N_dt_lt_morph
      N_dt_nat_inj_cond
      N_dt_le_refl
      N_dt_lt_irrefl
      N_dt_add_le_compat
      N_dt_add_lt_le_compat
      N_dt_mul_le_compat_r
      N_dt_mul_lt_compat_r
      N_dt_le_trans
      N_dt_lt_trans
      N_dt_le_lt_trans
      N_dt_lt_le_trans
      N_dt_mul_0_l
      N_dt_mul_le_r_le
      N_dt_mul_lt_r_lt
      N_dt_lt_0_1
      N_dt_lt_le_weak
      N_dt_lt_le_dec
      N_dt_eq_dec
      N_dt_nat_inj_add_dist
      N_dt_nat_nat_inj_le
      N_dt_nat_nat_inj_lt
      N_dt_nat_inj_lt_nat
      N_dt_ind.

End DTimeN.
