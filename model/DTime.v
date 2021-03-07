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


Require Export Omega.
Require Export tactics2.
Require Export Morphisms Setoid Field.


Class Cast A B := cast: A -> B.
Arguments cast _ _ {Cast} _.
Notation "' x" := (cast _ _ x) (at level 20).
Typeclasses Transparent Cast.

Section DTime.

  Fixpoint ntimes {T} (n : nat) (zero one : T) (add : T -> T -> T) : T :=
    match n with
    | 0 => zero
    | S n => add one (ntimes n zero one add)
    end.

  Class DTimeContext :=
    MkDTimeContext
      {
        dt_T                : Type;
        dt_0                : dt_T;
        dt_1                : dt_T;
        dt_add              : dt_T -> dt_T -> dt_T;
        dt_mul              : dt_T -> dt_T -> dt_T;
        dt_sub              : dt_T -> dt_T -> dt_T;
        dt_opp              : dt_T -> dt_T;
        dt_eq               : relation dt_T;
        dt_lt               : relation dt_T;
        dt_le               : relation dt_T;
        dt_eqv              : Equivalence dt_eq;
        dt_ring             : ring_theory dt_0 dt_1 dt_add dt_mul dt_sub dt_opp dt_eq;
        dt_nat_inj          : nat -> dt_T;
        dt_approx           : dt_T -> nat;

        dt_add_morph        : forall x y, dt_eq x y -> forall u v, dt_eq u v -> dt_eq (dt_add x u) (dt_add y v);
        dt_mul_morph        : forall x y, dt_eq x y -> forall u v, dt_eq u v -> dt_eq (dt_mul x u) (dt_mul y v);
        dt_opp_morph        : forall x y, dt_eq x y -> dt_eq (dt_opp x) (dt_opp y);
        dt_le_morph         : forall x y, dt_eq x y -> forall u v, dt_eq u v -> dt_le x u -> dt_le y v;
        dt_lt_morph         : forall x y, dt_eq x y -> forall u v, dt_eq u v -> dt_lt x u -> dt_lt y v;

        dt_nat_inj_cond     : forall (n : nat), dt_eq (dt_nat_inj n) (ntimes n dt_0 dt_1 dt_add);
        dt_le_refl          : forall t , dt_le t t;
        dt_lt_irrefl        : forall x, ~ (dt_lt x x);
        dt_add_le_compat    : forall a b c d, dt_le a c -> dt_le b d -> dt_le (dt_add a b) (dt_add c d);
        dt_add_lt_le_compat : forall a b c d, dt_lt a c -> dt_le b d -> dt_lt (dt_add a b) (dt_add c d);
        dt_mul_le_compat_r  : forall a b c, dt_le a b -> dt_le dt_0 c -> dt_le (dt_mul a c) (dt_mul b c);
        dt_mul_lt_compat_r  : forall a b c, dt_lt a b -> dt_lt dt_0 c -> dt_lt (dt_mul a c) (dt_mul b c);
        dt_le_trans         : forall a b c, dt_le a b -> dt_le b c -> dt_le a c;
        dt_lt_trans         : forall a b c, dt_lt a b -> dt_lt b c -> dt_lt a c;
        dt_le_lt_trans      : forall a b c, dt_le a b -> dt_lt b c -> dt_lt a c;
        dt_lt_le_trans      : forall a b c, dt_lt a b -> dt_le b c -> dt_lt a c;

        dt_mul_0_l          : forall x, dt_eq (dt_mul dt_0 x) dt_0;
        dt_mul_le_r_le      : forall x y z, dt_lt dt_0 z -> dt_le (dt_mul x z) (dt_mul y z) -> dt_le x y;
        dt_mul_lt_r_lt      : forall x y z, dt_lt dt_0 z -> dt_lt (dt_mul x z) (dt_mul y z) -> dt_lt x y;
        dt_lt_0_1           : dt_lt dt_0 dt_1;
        dt_lt_le_weak       : forall a b, dt_lt a b -> dt_le a b;
        dt_lt_le_dec        : forall x y, {dt_lt x y} + {dt_le y x};
        dt_eq_dec           : forall x y, {dt_eq x y} + {~ dt_eq x y};
        dt_nat_inj_add_dist : forall n m, dt_eq (dt_add (dt_nat_inj n) (dt_nat_inj m)) (dt_nat_inj (n + m));
        dt_nat_nat_inj_le   : forall n m, n <= m -> dt_le (dt_nat_inj n) (dt_nat_inj m);
        dt_nat_nat_inj_lt   : forall n m, n < m -> dt_lt (dt_nat_inj n) (dt_nat_inj m); (* FIX: DO we really need this one? *)
        dt_nat_inj_lt_nat   : forall n m, dt_lt (dt_nat_inj n) (dt_nat_inj m) -> n < m;

        dt_ind              : forall (P : dt_T -> Prop), (forall t, (forall u, dt_lt u t -> P u) -> P t) -> forall t, P t
      }.

  Context { dtc : DTimeContext }.

  Global Add Parametric Relation :
    dt_T dt_eq
      reflexivity  proved by (@Equivalence_Reflexive  dt_T dt_eq dt_eqv)
      symmetry     proved by (@Equivalence_Symmetric  dt_T dt_eq dt_eqv)
      transitivity proved by (@Equivalence_Transitive dt_T dt_eq dt_eqv)
    as dt_eq_rel.

  Global Add Parametric Relation :
    dt_T dt_le
      reflexivity  proved by dt_le_refl
      transitivity proved by dt_le_trans
    as dt_le_rel.

  Global Add Parametric Relation :
    dt_T dt_lt
      transitivity proved by dt_lt_trans
    as dt_lt_rel.

  Global Add Morphism dt_add with signature (dt_eq ==> dt_eq ==> dt_eq) as dt_add_ext.
  Proof. exact dt_add_morph. Qed.

  Global Add Morphism dt_mul with signature (dt_eq ==> dt_eq ==> dt_eq) as dt_mul_ext.
  Proof. exact dt_mul_morph. Qed.

  Global Add Morphism dt_opp with signature (dt_eq ==> dt_eq) as dt_opp_ext.
  Proof. exact dt_opp_morph. Qed.

  Add Ring rg_dt : dt_ring.

  Global Instance dt_le_eq : Proper (dt_eq ==> dt_eq ==> flip impl) dt_le.
  Proof.
    introv h1 h2 h3.
    eapply dt_le_morph; try exact h3; symmetry; auto.
  Qed.

  Global Instance dt_le_eq1 : forall x,  Proper (dt_eq ==> flip impl) (dt_le x).
  Proof.
    introv h1 h2.
    eapply dt_le_morph; try exact h2; try symmetry; auto; try reflexivity.
  Qed.

  Global Instance dt_lt_eq : Proper (dt_eq ==> dt_eq ==> flip impl) dt_lt.
  Proof.
    introv h1 h2 h3.
    eapply dt_lt_morph; try exact h3; symmetry; auto.
  Qed.

  Global Instance dt_add_eq : Proper (dt_eq ==> dt_eq ==> dt_eq) dt_add.
  Proof.
    introv h1 h2.
    eapply dt_add_morph; auto.
  Qed.

  (* We use positive rationals to model time *)
  Record PosDTime :=
    MkPosDTime
      {
        pos_dt_t :> dt_T;
        pos_dt_le : dt_le dt_0 pos_dt_t
      }.

  Lemma dt_le_0_ntimes :
    forall n,
      dt_le dt_0 (ntimes n dt_0 dt_1 dt_add).
  Proof.
    induction n; simpl; try reflexivity;[].
    pose proof (Radd_0_l dt_ring dt_0) as z.
    pose proof (dt_add_le_compat dt_0 dt_0 dt_1 (ntimes n dt_0 dt_1 dt_add)) as w.
    repeat (autodimp w hyp).
    { apply dt_lt_le_weak; apply dt_lt_0_1. }
    eapply dt_le_trans;[|exact w].
    rewrite z; reflexivity.
  Qed.

  Definition pdt_lt (q1 q2 : PosDTime) := dt_lt q1 q2.

  Definition pdt_mult (q1 q2 : PosDTime) : PosDTime.
  Proof.
    exists (dt_mul q1 q2).
    destruct q1 as [q1 c1], q2 as [q2 c2]; simpl.
    pose proof (dt_mul_le_compat_r dt_0 q1 q2) as w.
    repeat (autodimp w hyp).
    eapply dt_le_trans;[|exact w]; clear w.
    rewrite dt_mul_0_l; try reflexivity; auto.
  Defined.

  Definition pdt_plus (q1 q2 : PosDTime) : PosDTime.
  Proof.
    exists (dt_add q1 q2).
    destruct q1 as [q1 c1], q2 as [q2 c2]; simpl.
    pose proof (dt_add_le_compat dt_0 dt_0 q1 q2) as w.
    repeat (autodimp w hyp).
    eapply dt_le_trans;[|exact w]; clear w.
    rewrite (Radd_0_l dt_ring dt_0); try reflexivity.
  Defined.

  Delimit Scope dtime with dtime.
  Open Scope dtime.
  Infix "<"  := dt_lt  (at level 70) : dtime.
  Infix "<=" := dt_le  (at level 70) : dtime.
  Infix "+"  := dt_add : dtime.
  Infix "-"  := dt_sub : dtime.
  Infix "*"  := dt_mul : dtime.
  Infix "==" := dt_eq  (at level 70) : dtime.
  Notation "a <= b <= c" := ((a <= b) /\ (b <= c)) : dtime.
  Close Scope dtime.

  Definition nat2pdt : nat -> PosDTime.
  Proof.
    introv n.
    exists (dt_nat_inj n).
    rewrite dt_nat_inj_cond.
    apply dt_le_0_ntimes.
  Defined.

  Global Coercion nat2pdt : nat >-> PosDTime.

  Global Instance n2t : Cast nat PosDTime.
  Proof.
    introv n.
    exists (dt_nat_inj n).
    rewrite dt_nat_inj_cond.
    apply dt_le_0_ntimes.
  Defined.

  Class TimeConstraint :=
    {
      mu  : PosDTime; (* maximum message generation and transmission delay *)
      tau : PosDTime; (* maximum clock drift *)

      dlt : PosDTime; (* minimum message generation and transmission delay *)

      mu_strict_pos  : (0 < mu)%dtime;
      tau_strict_pos : (0 < tau)%dtime;
      dlt_strict_pos : (0 < dlt)%dtime;

      dlt_le_mu      : (dlt <= mu)%dtime;
    }.

  Context { tc : TimeConstraint }.

  (* use this abstraction instead of [mu + tau] *)
  Definition epoch_duration : dt_T := (mu + tau)%dtime.

  Lemma eq_dt_0 : dt_eq (dt_nat_inj 0) dt_0.
  Proof.
    rewrite dt_nat_inj_cond; simpl; auto; try reflexivity.
  Qed.

  Lemma eq_dt_1 : dt_eq (dt_nat_inj 1) dt_1.
  Proof.
    rewrite dt_nat_inj_cond; simpl; auto.
    rewrite (Radd_comm dt_ring).
    rewrite (Radd_0_l dt_ring); reflexivity.
  Qed.

  Lemma mu_plus_tau_pos : (0 < mu + tau)%dtime.
  Proof.
    pose proof (dt_add_lt_le_compat dt_0 dt_0 mu tau) as w.
    rewrite (Radd_0_l dt_ring dt_0) in w.
    rewrite <- eq_dt_0 in w; apply w; auto;
      try (apply mu_strict_pos).
      try (apply dt_lt_le_weak; apply tau_strict_pos).
  Qed.
  Hint Resolve mu_plus_tau_pos : dtime.

  Lemma mu_plus_tau_pos2 : (dt_0 < mu + tau)%dtime.
  Proof.
    rewrite <- eq_dt_0; eauto 2 with dtime.
  Qed.
  Hint Resolve mu_plus_tau_pos2 : dtime.

  Lemma mu_plus_tau_ge_0 : (0 <= mu + tau)%dtime.
  Proof.
    apply dt_lt_le_weak; apply mu_plus_tau_pos.
  Qed.
  Hint Resolve mu_plus_tau_ge_0 : dtime.

  Lemma mu_plus_tau_ge_dt0 : (dt_0 <= mu + tau)%dtime.
  Proof.
    rewrite <- eq_dt_0; eauto 2 with dtime.
  Qed.
  Hint Resolve mu_plus_tau_ge_dt0 : dtime.

  Lemma dt_le_lt_dec : forall x y, {(x <= y)%dtime} + {(y < x)%dtime}.
  Proof.
    introv.
    destruct (dt_lt_le_dec y x); tcsp.
  Defined.

  Definition PosDTime0 : PosDTime.
  Proof.
    exact (MkPosDTime dt_0 (dt_le_refl _)).
  Defined.

  Lemma time_plus_tau_le_aux :
    forall (t : PosDTime) (n1 n2 : nat),
      n1 < S n2
      -> (t <= n1 * (mu + tau))%dtime
      -> (t + (mu + tau) <= (S n2) * (mu + tau))%dtime.
  Proof.
    introv w1 w2.

    eapply dt_le_trans;[apply dt_add_le_compat;[eauto|apply dt_le_refl] |]; clear w2.

    pose proof (Rdistr_l
                  dt_ring
                  n1
                  1
                  (mu + tau)%dtime) as xx.
    simpl in *.
    rewrite eq_dt_1, (Rmul_1_l dt_ring) in xx.
    rewrite <- xx; clear xx.
    apply dt_mul_le_compat_r;[|rewrite <- eq_dt_0;eauto 2 with dtime];[].
    rewrite <- eq_dt_1.
    rewrite dt_nat_inj_add_dist; simpl.
    apply dt_nat_nat_inj_le; try omega.
  Qed.

  Lemma time_plus_mu_tau_lt :
    forall (t1 t2 : PosDTime) (n1 n2 : nat),
      n1 < S n2
      -> (t1 <= n1 * (mu + tau))%dtime
      -> ((S n2) * (mu + tau) < t2)%dtime
      -> (t1 + (mu + tau) < t2)%dtime.
  Proof.
    introv w1 w2 w3.
    eapply dt_le_lt_trans;[|eauto]; clear w3.
    eapply time_plus_tau_le_aux; eauto.
  Qed.

  Lemma time_plus_mu_tau_le :
    forall (t1 t2 : PosDTime) (n1 n2 : nat),
      n1 < S n2
      -> (t1 <= n1 * (mu + tau))%dtime
      -> ((S n2) * (mu + tau) < t2)%dtime
      -> (t1 + (mu + tau) <= t2)%dtime.
  Proof.
    introv w1 w2 w3.
    apply dt_lt_le_weak.
    eapply time_plus_mu_tau_lt; eauto.
  Qed.

  Lemma dt_mul_1_l :
    forall t, (dt_nat_inj 1 * t == t)%dtime.
  Proof.
    introv; simpl.
    rewrite eq_dt_1.
    apply (Rmul_1_l dt_ring).
  Qed.

  Lemma dt_add_0_l :
    forall t, (dt_nat_inj 0 + t == t)%dtime.
  Proof.
    introv; simpl.
    rewrite eq_dt_0.
    apply (Radd_0_l dt_ring).
  Qed.

  Lemma dt_mul_le_r :
    forall x y z, (0 < z)%dtime -> (x * z <= y * z)%dtime <-> (x <= y)%dtime.
  Proof.
    introv gt0; split; intro h.

    { eapply dt_mul_le_r_le;eauto.
      rewrite <- eq_dt_0; auto. }

    { apply dt_mul_le_compat_r; auto.
      apply dt_lt_le_weak.
      rewrite <- eq_dt_0; auto. }
  Qed.


  Lemma lt_0_twice_implies_lt_prod :
    forall a b,
      (nat2pdt 0 < a)%dtime
      -> (nat2pdt 0 < b)%dtime
      -> (nat2pdt 0 < a * b)%dtime.
  Proof.
    introv H1 H2.
    pose proof (dt_mul_lt_compat_r (nat2pdt 0) a b) as xx.
    repeat (autodimp xx hyp);[rewrite <- eq_dt_0; eauto |].
    pose proof (dt_mul_0_l b) as yy.
    rewrite <- eq_dt_0 in yy. simpl in *.
    rewrite yy in xx. clear yy.
    eauto.
  Qed.
  Hint Resolve lt_0_twice_implies_lt_prod : dtime.


  Lemma lt_implies_trans :
    forall a b c d,
      a < b
      -> (dt_0 < c)%dtime
      -> (d <= nat2pdt(S a) * c)%dtime
      -> (d <= nat2pdt(S b) * c)%dtime.
  Proof.
    introv h1 h2 h3.
    eapply dt_lt_le_weak.

    assert (nat2pdt(S a) < nat2pdt(S b))%dtime as temp1
        by (eapply lt_n_S in h1; eapply dt_nat_nat_inj_lt; eauto).

    pose proof(dt_mul_lt_compat_r (nat2pdt(S a)) (nat2pdt(S b)) c) as xx.
    repeat(autodimp xx hyp). clear temp1.

    eapply dt_le_lt_trans in h3; eauto.
  Qed.
  Hint Resolve lt_implies_trans : dtime.

  Lemma S_dt_T_mul :
    forall a b,
      ((dt_nat_inj (S a)) * b == ((dt_nat_inj a) * b) + b)%dtime.
  Proof.
    introv.
    assert (S a = a + 1) as xx by omega.
    rewrite xx; clear xx.
    rewrite <- dt_nat_inj_add_dist.
    pose proof (Rdistr_l dt_ring (dt_nat_inj a) (dt_nat_inj 1) b) as xx.
    rewrite xx; clear xx.
    apply dt_add_ext; try reflexivity.
    rewrite dt_mul_1_l; try reflexivity.
  Qed.

End DTime.


(* What's up with dt_lt_rel? *)
Existing Instances dt_eq_rel dt_le_rel (*dt_lt_rel*).


Hint Resolve mu_plus_tau_pos : dtime.
Hint Resolve mu_plus_tau_ge_0 : dtime.
Hint Resolve mu_plus_tau_pos2 : dtime.
Hint Resolve mu_plus_tau_ge_dt0 : dtime.
Hint Resolve lt_0_twice_implies_lt_prod : dtime.
Hint Resolve lt_implies_trans : dtime.

Delimit Scope dtime with dtime.
Open Scope dtime.
Infix "<"  := dt_lt  (at level 70) : dtime.
Infix "<=" := dt_le  (at level 70) : dtime.
Infix "+"  := dt_add : dtime.
Infix "-"  := dt_sub : dtime.
Infix "*"  := dt_mul : dtime.
Infix "==" := dt_eq  (at level 70) : dtime.
Notation "a <= b <= c" := ((a <= b) /\ (b <= c)) : dtime.
Close Scope dtime.
