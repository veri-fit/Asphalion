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


Require Export list_util.
Require Export generic_tactics.


Hint Rewrite map_map : list.

Lemma norepeatsb_as_no_repeats :
  forall {A} (deq : Deq A) l,
    norepeatsb deq l = true <-> no_repeats l.
Proof.
  induction l; introv; simpl; split; intro h; tcsp; sp_smash_byzeml.

  - constructor; tcsp.
    apply IHl; auto.

  - inversion h; subst; tcsp.

  - inversion h; subst; tcsp.
    apply IHl; auto.
Qed.

Lemma norepeatsb_implies_no_repeats :
  forall {A} (deq : Deq A) l, norepeatsb deq l = true -> no_repeats l.
Proof.
  introv norep; apply norepeatsb_as_no_repeats in norep; auto.
Qed.
Hint Resolve norepeatsb_implies_no_repeats : list.

Lemma no_repeats_mapin :
  forall {A B} (l : list A) (F : forall a (i : In a l), B),
    no_repeats l
    -> (forall a b (i : In a l) (j : In b l), F a i = F b j -> a = b)
    -> no_repeats (mapin l F).
Proof.
  induction l; introv norep imp; simpl in *; auto;[].
  inversion norep as [|? ? ni nr]; subst; clear norep.
  constructor; auto.
  - introv i.
    apply in_mapin in i; exrepnd; tcsp.
    apply imp in i1; subst; tcsp.
  - apply IHl; auto.
    introv k.
    apply imp in k; auto.
Qed.
Hint Resolve no_repeats_mapin : list.

Lemma no_repeats_seq :
  forall l n, no_repeats (seq n l).
Proof.
  induction l; introv; simpl; auto.
  constructor; auto.
  intro i.
  apply in_seq in i; omega.
Qed.
Hint Resolve no_repeats_seq : list.

Record NRlist (A : Type) :=
  MkNRlist
    {
      nrl_list :> list A;
      nrl_no_repeats : no_repeats nrl_list;
    }.

Lemma no_repeats_NRlist :
  forall {A} (l : NRlist A), no_repeats l.
Proof.
  introv.
  destruct l; auto.
Qed.
Hint Resolve no_repeats_NRlist : list.

Ltac bring_no_repeats l nr :=
  assert (no_repeats l) as nr by eauto 2 with list.

Lemma in_remove_iff :
  forall {A} (dec : Deq A) x a l,
    In x (remove dec a l) <-> (In x l /\ x <> a).
Proof.
  induction l; introv; simpl; split; intro h; tcsp;
    sp_smash_byzeml; repndors; subst; tcsp;
      try (complete (apply IHl in h; repnd; tcsp));
      try (complete (apply IHl; tcsp)).
  right; apply IHl; tcsp.
Qed.

Lemma length_remove_le :
  forall {A} (dec : Deq A) a (l : list A),
    length (remove dec a l) <= length l.
Proof.
  induction l; introv; simpl in *; tcsp; sp_smash_byzeml; try omega.
Qed.
Hint Rewrite @length_remove_le : list.

Lemma length_remove_lt :
  forall {A} (dec : Deq A) a (l : list A),
    In a l
    -> length (remove dec a l) < length l.
Proof.
  induction l; introv i; simpl in *; tcsp.
  repndors; subst; tcsp; sp_smash_byzeml;
    try (complete (autodimp IHl hyp; omega)).
  pose proof (length_remove_le dec a l) as q; omega.
Qed.
Hint Resolve length_remove_lt : list.

Lemma member_of_larger_list :
  forall {A} (dec : Deq A) (l2: NRlist A) l1,
    length l1 < length l2
    -> exists x, In x l2 /\ ~ In x l1.
Proof.
  introv dec len.
  destruct l2 as [l2 nr].
  revert dependent l1.

  induction l2; introv len; simpl in *; try omega.

  match goal with
    [ H : no_repeats _ |-_] => rename H into norep
  end.
  inversion norep as [|? ? ni nrep]; subst.
  autodimp IHl2 hyp.

  clear norep.

  destruct (in_dec dec a l1) as [d|d]; eauto;[].

  pose proof (IHl2 (remove dec a l1)) as q; clear IHl2.
  repeat (autodimp q hyp).

  - eapply Nat.lt_le_trans;[apply length_remove_lt;auto|]; omega.

  - exrepnd.
    exists x; dands; auto.
    allrw @in_remove_iff; intro xx; destruct q0; dands; auto; intro zz; subst; tcsp.
Qed.

Lemma member_of_larger_list2 :
  forall {A} (dec : Deq A) (l2 l1 : list A),
    no_repeats l2
    -> length l1 < length l2
    -> exists x, In x l2 /\ ~ In x l1.
Proof.
  induction l2; introv norep len; simpl in *; try omega.
  inversion norep as [|? ? ni nrep]; subst; clear norep.

  destruct (in_dec dec a l1) as [d|d]; eauto;[].

  pose proof (IHl2 (remove dec a l1)) as q; clear IHl2.
  repeat (autodimp q hyp).

  - eapply Nat.lt_le_trans;[apply length_remove_lt;auto|]; omega.

  - exrepnd.
    exists x; dands; auto.
    allrw @in_remove_iff; intro xx; destruct q0; dands; auto; intro zz; subst; tcsp.
Qed.

(** l \ lr -- removes the elements of lr from l  *)
Fixpoint diff {T} (dec : Deq T) (r : list T) (l : list T) : list T :=
  match r with
  | [] => l
  | h :: t => diff dec t (remove dec h l)
  end.

Lemma in_remove :
  forall {T} x y eq (l : list T),
    In x (remove eq y l) <-> (x <> y /\ In x l).
Proof.
  induction l; simpl; split; intro h; repnd; tcsp; sp_smash_byzeml; repndors; subst; tcsp;
    try (apply IHl in h; repnd; tcsp); try (apply IHl; tcsp).
  right; apply IHl; tcsp.
Qed.

Lemma in_diff :
  forall {T} (l1 l2 : list T) x eq,
    In x (diff eq l1 l2)
    <->
    (In x l2 /\ ~In x l1).
Proof.
  induction l1; introv; simpl; split; intro h; tcsp.
  - apply IHl1 in h; repnd.
    apply in_remove in h0; repnd; tcsp.
  - repnd.
    apply IHl1.
    rewrite in_remove.
    apply not_or in h; repnd; tcsp.
Qed.

Lemma subset_diff :
  forall {A} eq (l1 l2 l3 : list A),
    subset (diff eq l1 l2) l3
    <->
    subset l2 (l3 ++ l1).
Proof.
  introv; split; introv h i; allrw in_app_iff.

  - destruct (in_dec eq v l1); tcsp.
    left; apply h.
    apply in_diff; tcsp.

  - apply in_diff in i; repnd.
    apply h in i0; apply in_app_iff in i0; repndors; tcsp.
Qed.

Lemma subset_diff_l_same_r :
  forall {A} eq (l1 l2 : list A),
    subset (diff eq l1 l2) l2.
Proof.
  introv; apply subset_diff.
  apply implies_subset_app_r; tcsp.
Qed.
Hint Resolve subset_diff_l_same_r : list.

Lemma remove_comm :
  forall {T} eq (l : list T) x y,
    remove eq x (remove eq y l) = remove eq y (remove eq x l).
Proof.
  induction l; introv; simpl; tcsp; sp_smash_byzeml.
Qed.

Lemma diff_remove :
  forall {T} eq (l1 l2 : list T) x,
    diff eq l1 (remove eq x l2) = remove eq x (diff eq l1 l2).
Proof.
  induction l1; introv; simpl; tcsp.
  repeat (rewrite IHl1).
  rewrite remove_comm; auto.
Qed.

Lemma disjoint_remove_l :
  forall {A} eq x (l1 l2 : list A),
    disjoint (remove eq x l1) l2 <-> disjoint l1 (remove eq x l2).
Proof.
  introv; split; introv disj i j.

  - apply in_remove in j; repnd.
    applydup disj in j; tcsp.
    apply in_remove; tcsp.

  - apply in_remove in i; repnd.
    applydup disj in i.
    rewrite in_remove in i1; tcsp.
Qed.

Lemma disjoint_diff_l :
  forall {A} eq (l1 l2 l3 : list A),
    disjoint (diff eq l1 l2) l3 <-> disjoint l2 (diff eq l1 l3).
Proof.
  induction l1; introv; simpl; tcsp.
  rewrite IHl1.
  rewrite diff_remove.
  rewrite disjoint_remove_l; tcsp.
Qed.

Lemma diff_nil_if_subset :
  forall {A} eq (l1 l2 : list A),
    subset l2 l1
    -> diff eq l1 l2 = [].
Proof.
  induction l1; introv ss; simpl in *; tcsp; sp_smash_byzeml.
  - apply subset_nil_r; auto.
  - apply IHl1.
    introv i; apply in_remove in i; repnd.
    applydup ss in i; simpl in *; tcsp.
Qed.

Lemma diff_same :
  forall {A} eq (l : list A),
    diff eq l l = [].
Proof.
  introv; apply diff_nil_if_subset; auto.
Qed.
Hint Rewrite @diff_same : list.

Lemma disjoint_nil_r :
  forall {T} (l : list T), disjoint l [].
Proof.
  unfold disjoint; tcsp.
Qed.
Hint Resolve disjoint_nil_r : list.

Lemma disjoint_diff_l_same_l :
  forall {A} eq (l1 l2 : list A),
    disjoint (diff eq l1 l2) l1.
Proof.
  introv; apply disjoint_diff_l.
  autorewrite with list in *; eauto 2 with list.
Qed.
Hint Resolve disjoint_diff_l_same_l : list.

Lemma implies_no_repeats_remove :
  forall {T} dec a (l : list T),
    no_repeats l
    -> no_repeats (remove dec a l).
Proof.
  induction l; introv norep; simpl in *; tcsp.
  inversion norep as [|? ? ni nr]; subst; clear norep.
  sp_smash_byzeml.
  constructor; tcsp.
  rewrite in_remove; tcsp.
Qed.
Hint Resolve implies_no_repeats_remove : list.

Lemma implies_no_repeats_diff :
  forall {T} dec (l1 l2 : list T),
    no_repeats l2 -> no_repeats (diff dec l1 l2).
Proof.
  induction l1; introv norep; simpl in *; auto.
  apply IHl1; eauto 2 with list.
Qed.
Hint Resolve implies_no_repeats_diff : list.

Lemma length_remove_if_no_repeats :
  forall {T} deq (a : T) l,
    no_repeats l
    -> length (remove deq a l)
       = if in_dec deq a l
         then pred (length l)
         else length l.
Proof.
  induction l; simpl; introv norep; auto.
  inversion norep as [|? ? ni nr]; clear norep; subst.
  autodimp IHl hyp.
  repeat (dest_cases w; simpl; repndors; subst; tcsp);
    try (rewrite IHl; simpl; auto); try omega.
  { apply Nat.succ_pred_pos; destruct l; simpl in *; tcsp; try omega. }
  { destruct n0; tcsp. }
  { destruct n0; tcsp. }
Qed.

Lemma no_repeats_implies_le_length_diff :
  forall {A} dec (l1 l2 : list A),
    no_repeats l2
    -> length l2 - length l1 <= length (diff dec l1 l2).
Proof.
  induction l1; introv norep; simpl in *; autorewrite with nat; auto.
  pose proof (IHl1 (remove dec a l2)) as h.
  repeat (autodimp h hyp); eauto 2 with list;[].
  eapply le_trans;[|eauto]; clear h.
  rewrite length_remove_if_no_repeats; auto; sp_smash_byzeml; try omega.
Qed.
Hint Resolve no_repeats_implies_le_length_diff : list.

Lemma members_of_larger_list :
  forall {A} (dec : Deq A) (l2 l1 : list A),
    no_repeats l2
    -> exists l,
      subset l l2
      /\ disjoint l l1
      /\ no_repeats l
      /\ length l2 - length l1 <= length l.
Proof.
  introv dec norep.
  exists (diff dec l1 l2).
  dands; eauto 3 with list.
Qed.

(* no_repeats *)
Lemma members_of_larger_list_2 :
  forall {A} (dec : Deq A) (l2 l1 : NRlist A),
  exists l,
    subset l l2
    /\ disjoint l l1
    /\ no_repeats l
    /\ length l2 - length l1 <= length l.
Proof.
  intros.
  exists (diff dec l1 l2).
  dands; eauto 3 with list.
Qed.

Lemma subset_cons_l_implies_in :
  forall {A} (a : A) l1 l2,
    subset (a :: l1) l2
    -> In a l2.
Proof.
  introv ss; pose proof (ss a) as q; autodimp q hyp; tcsp.
Qed.
Hint Resolve subset_cons_l_implies_in : list.

Lemma length_remove_elt_le :
  forall {A} a (deq : Deq A) l,
    length (remove_elt deq a l) <= length l.
Proof.
  induction l; simpl; auto.
  destruct (deq a a0); simpl; try omega.
Qed.

Lemma eqset_dec :
  forall {A} (l1 l2 : list A) (deq : Deq A), decidable (eqset l1 l2).
Proof.
  intros A l1.
  remember (length l1) as n; revert dependent l1.
  induction n as [? ind] using comp_ind_type; introv len deq.
  destruct n.

  - destruct l1; simpl in *; ginv.
    destruct l2.

    + left; auto.

    + right; introv xx.
      pose proof (xx a) as xx; simpl in xx; destruct xx as [xx1 xx2].
      autodimp xx2 hyp; tcsp.

  - destruct l1; simpl in *; ginv.
    pose proof (ind (length (remove_elt deq a l1))) as ind.

    autodimp ind hyp.
    { eapply le_lt_trans;[apply length_remove_elt_le|]; omega. }

    pose proof (ind (remove_elt deq a l1) eq_refl (remove_elt deq a l2) deq) as ind.

    destruct ind as [ind|ind].

    + destruct (in_dec deq a l2) as [d|d].

      * left; introv; simpl; split; introv h; repndors; subst; tcsp.

        { destruct (deq a x); subst; tcsp.
          pose proof (ind x) as ind.
          allrw @in_remove_elt.
          destruct ind as [u v]; autodimp u hyp; tcsp. }

        { destruct (deq a x); subst; tcsp.
          pose proof (ind x) as ind.
          allrw @in_remove_elt.
          destruct ind as [u v]; autodimp v hyp; tcsp. }

      * right; introv xx; pose proof (xx a) as xx; simpl in *.
        destruct xx as [u v]; clear v; autodimp u hyp; tcsp.

    + destruct (in_dec deq a l2) as [d|d].

      * right; introv xx; destruct ind; introv; split; introv h; allrw @in_remove_elt; repnd; dands; tcsp.

        { apply xx; simpl; tcsp. }

        { apply xx in h0; simpl in *; tcsp. }

      * right; introv xx; pose proof (xx a) as xx; simpl in *.
        destruct xx as [u v]; clear v; autodimp u hyp; tcsp.
Qed.

Lemma not_eqset_implies :
  forall {A} (deq : Deq A) (l1 l2 : list A),
    ~ (eqset l1 l2)
    -> exists v, (In v l1 /\ ~ In v l2) \/ (In v l2 /\ ~ In v l1).
Proof.
  intros A deq l1.
  remember (length l1) as n; revert dependent l1.
  induction n as [? ind] using comp_ind_type; introv len d.
  destruct n.

  - destruct l1; simpl in *; ginv.
    destruct l2.

    + destruct d; auto.

    + exists a; simpl; tcsp.

  - destruct l1; simpl in *; ginv.
    destruct (in_dec deq a l2) as [q|q];[|exists a; tcsp];[].

    pose proof (ind (length (remove_elt deq a l1))) as ind.

    autodimp ind hyp.
    { eapply le_lt_trans;[apply length_remove_elt_le|]; omega. }

    pose proof (ind (remove_elt deq a l1) eq_refl (remove_elt deq a l2)) as ind.

    autodimp ind hyp.
    {
      introv h; destruct d; introv; simpl.
      destruct (deq a x); subst; tcsp.

      - split; tcsp.

      - split; introv w; repndors; subst; tcsp.

        + destruct (h x) as [z1 z2]; allrw @in_remove_elt.
          autodimp z1 hyp; tcsp.

        + destruct (h x) as [z1 z2]; allrw @in_remove_elt.
          autodimp z2 hyp; tcsp.
    }

    exrepnd; repndors; repnd; allrw @in_remove_elt; repnd.

    + exists v; left; tcsp.

    + exists v; right; tcsp.
Qed.

Lemma snoc_list_ind :
  forall (A : Type) (P : list A -> Prop),
    P []
    -> (forall (a : A) (l : list A), P l -> P (snoc l a))
    -> forall l : list A, P l.
Proof.
  intros.
  assert ({n | length l = n}) as e by (exists (length l); auto); sp.
  revert l e.
  induction n; intros.
  { destruct l; simpl in *; ginv; auto. }
  { pose proof (snoc_cases l) as q; repndors; subst; tcsp.
    exrepnd; subst; allrw length_snoc; ginv. }
Qed.

Definition inb {A} deq (a : A) (l : list A) : bool :=
  if in_dec deq a l then true else false.

Definition not_inb {A} deq (a : A) (l : list A) : bool :=
  if in_dec deq a l then false else true.

Hint Rewrite andb_true_r  : bool.
Hint Rewrite andb_false_r : bool.

Lemma forallb_snoc :
  forall {A} f (l : list A) a,
    forallb f (snoc l a) = forallb f l && f a.
Proof.
  induction l; introv; simpl; autorewrite with bool; auto.
  rewrite IHl.
  rewrite andb_assoc; auto.
Qed.

Lemma norepeatsb_snoc :
  forall {A} (a : A) l deq,
    norepeatsb deq (snoc l a)
    = norepeatsb deq l && not_inb deq a l.
Proof.
  induction l; introv; simpl; allrw; tcsp.
  destruct (in_dec deq a0 (snoc l a)).
  { allrw @in_snoc.
    unfold not_inb; simpl.
    destruct (in_dec deq a0 l); destruct (deq a0 a); subst; tcsp.
    autorewrite with bool; auto. }
  { allrw @in_snoc.
    apply not_or in n; repnd.
    destruct (in_dec deq a0 l); tcsp.
    unfold not_inb; simpl.
    destruct (deq a0 a); subst; tcsp; GC.
    destruct (in_dec deq a l); autorewrite with bool; auto. }
Qed.

Lemma norepeatsb_false_iff :
  forall {A} (l : list A) deq,
    norepeatsb deq l = false <-> ~no_repeats l.
Proof.
  introv.
  remember (norepeatsb deq l) as b; symmetry in Heqb; destruct b.
  { apply norepeatsb_as_no_repeats in Heqb; split; tcsp. }
  { split; intro h; tcsp; intro q.
    rewrite <- norepeatsb_as_no_repeats in q; rewrite q in Heqb; ginv. }
Qed.

Lemma not_inb_snoc_true_iff :
  forall {A} deq (a : A) x l,
    not_inb deq a (snoc l x) = true
    <-> (not_inb deq a l = true /\ a <> x).
Proof.
  introv; unfold not_inb; simpl.
  destruct (in_dec deq a (snoc l x)); destruct (in_dec deq a l);
    allrw @in_snoc; repndors; subst; tcsp; split; intro h; repnd; tcsp.
Qed.

Lemma not_inb_snoc_false_iff :
  forall {A} deq (a : A) x l,
    not_inb deq a (snoc l x) = false
    <-> (In a l \/ a = x).
Proof.
  introv; unfold not_inb; simpl.
  destruct (in_dec deq a (snoc l x));
    allrw @in_snoc; repndors; subst; tcsp; split; intro h; repnd; tcsp.
Qed.

Lemma not_inb_true_iff :
  forall {A} deq (a : A) l,
    not_inb deq a l = true
    <-> ~ In a l.
Proof.
  introv; unfold not_inb; simpl.
  destruct (in_dec deq a l); split; intro h; repnd; tcsp.
Qed.

Lemma not_inb_false_iff :
  forall {A} deq (a : A) l,
    not_inb deq a l = false
    <-> In a l.
Proof.
  introv; unfold not_inb; simpl.
  destruct (in_dec deq a l); split; intro h; repnd; tcsp.
Qed.

(* decompose a list [l] into Some(iseg,elt,fseg) such that
       l = iseg ++ elt :: fseg
     and elt is l's nth element *)
Fixpoint decomp_nth {T} (l : list T) (n : nat) : option (list T * T * list T) :=
  match l, n with
  | [], _ => None
  | x :: xs, 0 => Some ([], x, xs)
  | x :: xs, S n =>
    match decomp_nth xs n with
    | None => None
    | Some (iseg, elt, fseg) => Some (x :: iseg, elt, fseg)
    end
  end.
