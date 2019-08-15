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


Require Import QArith.
Require Export DTime.


Section DTimeQ.

  Definition Q_dt_T : Type := Q.

  Definition Q_dt_0 : Q_dt_T := 0%Q.

  Definition Q_dt_1 : Q_dt_T := 1%Q.

  Definition Q_dt_add : Q_dt_T -> Q_dt_T -> Q_dt_T := Qplus.

  Definition Q_dt_mul : Q_dt_T -> Q_dt_T -> Q_dt_T := Qmult.

  Definition Q_dt_sub : Q_dt_T -> Q_dt_T -> Q_dt_T := Qminus.

  Definition Q_dt_opp : Q_dt_T -> Q_dt_T := Qopp.

  Definition Q_dt_eq : relation Q_dt_T := Qeq.

  Definition Q_dt_lt : relation Q_dt_T := Qlt.

  Definition Q_dt_le : relation Q_dt_T := Qle.

  Definition Q_dt_eqv : Equivalence Q_dt_eq := Q_Setoid.

  Definition Q_dt_ring : ring_theory Q_dt_0 Q_dt_1 Q_dt_add Q_dt_mul Q_dt_sub Q_dt_opp Q_dt_eq.
  Proof.
    exact Qsrt.
  Qed.

  Definition Q_dt_nat_inj : nat -> Q_dt_T := fun n => inject_Z (Z.of_nat n).

  Definition Q_dt_add_morph : forall x y, Q_dt_eq x y -> forall u v, Q_dt_eq u v -> Q_dt_eq (Q_dt_add x u) (Q_dt_add y v).
  Proof.
    introv a b; rewrite a, b; reflexivity.
  Qed.

  Definition Q_dt_mul_morph : forall x y, Q_dt_eq x y -> forall u v, Q_dt_eq u v -> Q_dt_eq (Q_dt_mul x u) (Q_dt_mul y v).
  Proof.
    introv a b; rewrite a, b; reflexivity.
  Qed.

  Definition Q_dt_opp_morph : forall x y, Q_dt_eq x y -> Q_dt_eq (Q_dt_opp x) (Q_dt_opp y).
  Proof.
    introv a; rewrite a; reflexivity.
  Qed.

  Definition Q_dt_le_morph : forall x y, Q_dt_eq x y -> forall u v, Q_dt_eq u v -> Q_dt_le x u -> Q_dt_le y v.
  Proof.
    introv a b h; rewrite a, b in h; auto.
  Qed.

  Definition Q_dt_lt_morph : forall x y, Q_dt_eq x y -> forall u v, Q_dt_eq u v -> Q_dt_lt x u -> Q_dt_lt y v.
  Proof.
    introv a b h; rewrite a, b in h; auto.
  Qed.

  Definition Q_dt_nat_inj_cond : forall (n : nat), Q_dt_eq (Q_dt_nat_inj n) (ntimes n Q_dt_0 Q_dt_1 Q_dt_add).
  Proof.
    unfold Q_dt_eq, Q_dt_nat_inj, Q_dt_0; induction n; simpl; auto; try reflexivity.
    rewrite <- IHn; clear IHn.
    unfold Q_dt_nat_inj, Q_dt_add, Q_dt_1; simpl.
    assert (1%Q = inject_Z (Z.of_nat 1)) as xx by auto; rewrite xx; clear xx.
    rewrite <- inject_Z_plus.
    rewrite <- Nat2Z.inj_add; simpl; auto; try reflexivity.
  Qed.

  Definition Q_dt_le_refl : forall t , Q_dt_le t t.
  Proof.
    apply Qle_refl.
  Qed.

  Definition Q_dt_lt_irrefl : forall t , ~ (Q_dt_lt t t).
  Proof.
    apply Qlt_irrefl.
  Qed.

  Definition Q_dt_add_le_compat : forall a b c d, Q_dt_le a c -> Q_dt_le b d -> Q_dt_le (Q_dt_add a b) (Q_dt_add c d).
  Proof.
    introv; apply Qplus_le_compat.
  Qed.

  Definition Q_dt_add_lt_le_compat : forall a b c d, Q_dt_lt a c -> Q_dt_le b d -> Q_dt_lt (Q_dt_add a b) (Q_dt_add c d).
  Proof.
    introv; apply Qplus_lt_le_compat.
  Qed.

  Definition Q_dt_mul_le_compat_r : forall a b c, Q_dt_le a b -> Q_dt_le Q_dt_0 c -> Q_dt_le (Q_dt_mul a c) (Q_dt_mul b c).
  Proof.
    introv; apply Qmult_le_compat_r.
  Qed.

  Definition Q_dt_le_trans : forall a b c, Q_dt_le a b -> Q_dt_le b c -> Q_dt_le a c.
  Proof.
    introv; apply Qle_trans.
  Qed.

  Definition Q_dt_lt_trans : forall a b c, Q_dt_lt a b -> Q_dt_lt b c -> Q_dt_lt a c.
  Proof.
    introv; apply Qlt_trans.
  Qed.

  Definition Q_dt_le_lt_trans : forall a b c, Q_dt_le a b -> Q_dt_lt b c -> Q_dt_lt a c.
  Proof.
    introv; apply Qle_lt_trans.
  Qed.

  Definition Q_dt_lt_le_trans : forall a b c, Q_dt_lt a b -> Q_dt_le b c -> Q_dt_lt a c.
  Proof.
    introv; apply Qlt_le_trans.
  Qed.

  Definition Q_dt_mul_0_l : forall x, Q_dt_eq (Q_dt_mul Q_dt_0 x) Q_dt_0.
  Proof.
    introv; apply Qmult_0_l.
  Qed.

  Definition Q_dt_lt_0_1 : Q_dt_lt Q_dt_0 Q_dt_1.
  Proof.
    unfold Q_dt_lt, Q_dt_0, Q_dt_1; simpl.
    assert (1%Q = inject_Z (Z.of_nat 1)) as xx by auto; rewrite xx; clear xx.
    assert (0%Q = inject_Z (Z.of_nat 0)) as xx by auto; rewrite xx; clear xx.
    rewrite <- Zlt_Qlt.
    apply inj_lt; omega.
  Qed.

  Definition Q_dt_lt_le_weak : forall a b, Q_dt_lt a b -> Q_dt_le a b.
  Proof.
    introv; apply Qlt_le_weak.
  Qed.

  Definition Q_dt_lt_le_dec : forall x y, {Q_dt_lt x y} + {Q_dt_le y x}.
  Proof.
    introv; apply Qlt_le_dec.
  Qed.

  Definition Q_dt_eq_dec : forall x y, {Q_dt_eq x y} + {~ Q_dt_eq x y}.
  Proof.
    introv; apply Qeq_dec.
  Qed.

  Definition Q_dt_nat_inj_add_dist : forall n m, Q_dt_eq (Q_dt_add (Q_dt_nat_inj n) (Q_dt_nat_inj m)) (Q_dt_nat_inj (n + m)).
  Proof.
    introv; unfold Q_dt_eq, Q_dt_add, Q_dt_nat_inj; simpl.
    rewrite <- inject_Z_plus.
    rewrite <- Nat2Z.inj_add; simpl; auto; try reflexivity.
  Qed.

  Definition Q_dt_nat_nat_inj_le : forall n m, n <= m -> Q_dt_le (Q_dt_nat_inj n) (Q_dt_nat_inj m).
  Proof.
    introv h; unfold Q_dt_eq, Q_dt_add, Q_dt_nat_inj, Q_dt_le; simpl.
    rewrite <- Zle_Qle; apply inj_le; auto.
  Qed.

  Definition Q_dt_nat_nat_inj_lt : forall n m, n < m -> Q_dt_lt (Q_dt_nat_inj n) (Q_dt_nat_inj m).
  Proof.
    introv h; unfold Q_dt_eq, Q_dt_add, Q_dt_nat_inj, Q_dt_lt; simpl.
    rewrite <- Zlt_Qlt; apply inj_lt; auto.
  Qed.

  Definition Q_dt_mul_le_r_le : forall x y z, Q_dt_lt Q_dt_0 z -> Q_dt_le (Q_dt_mul x z) (Q_dt_mul y z) -> Q_dt_le x y.
  Proof.
    introv h q.
    apply (Qmult_le_r x y z h); auto.
  Qed.

  Definition Q_dt_mul_lt_compat_r : forall a b c, Q_dt_lt a b -> Q_dt_lt Q_dt_0 c -> Q_dt_lt (Q_dt_mul a c) (Q_dt_mul b c).
  Proof.
    introv h q; apply Qmult_lt_r; auto.
  Qed.

  Definition Q_dt_mul_lt_r_lt : forall x y z, Q_dt_lt Q_dt_0 z -> Q_dt_lt (Q_dt_mul x z) (Q_dt_mul y z) -> Q_dt_lt x y.
  Proof.
    introv h q; eapply Qmult_lt_r; eauto.
  Qed.

  Definition Q_dt_nat_inj_lt_nat : forall n m, Q_dt_lt (Q_dt_nat_inj n) (Q_dt_nat_inj m) -> n < m.
  Proof.
    introv h; unfold Q_dt_lt, Q_dt_nat_inj in *.
    rewrite <- Zlt_Qlt in h.
    apply Nat2Z.inj_lt in h; auto.
  Qed.

  Definition Q_dt_approx (x : Q) : nat :=
    Z.abs_nat (Qnum x).

  Global Instance DTimeContextQ : DTimeContext :=
    MkDTimeContext
      Q_dt_T
      Q_dt_0
      Q_dt_1
      Q_dt_add
      Q_dt_mul
      Q_dt_sub
      Q_dt_opp
      Q_dt_eq
      Q_dt_lt
      Q_dt_le
      Q_dt_eqv
      Q_dt_ring
      Q_dt_nat_inj
      Q_dt_approx
      Q_dt_add_morph
      Q_dt_mul_morph
      Q_dt_opp_morph
      Q_dt_le_morph
      Q_dt_lt_morph
      Q_dt_nat_inj_cond
      Q_dt_le_refl
      Q_dt_lt_irrefl
      Q_dt_add_le_compat
      Q_dt_add_lt_le_compat
      Q_dt_mul_le_compat_r
      Q_dt_mul_lt_compat_r
      Q_dt_le_trans
      Q_dt_lt_trans
      Q_dt_le_lt_trans
      Q_dt_lt_le_trans
      Q_dt_mul_0_l
      Q_dt_mul_le_r_le
      Q_dt_mul_lt_r_lt
      Q_dt_lt_0_1
      Q_dt_lt_le_weak
      Q_dt_lt_le_dec
      Q_dt_eq_dec
      Q_dt_nat_inj_add_dist
      Q_dt_nat_nat_inj_le
      Q_dt_nat_nat_inj_lt
      Q_dt_nat_inj_lt_nat.

End DTimeQ.
