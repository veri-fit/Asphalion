(* This contains a copy of the tactics in CalculusSM.v.
   Could we instead export them from the Section?
 *)

Require Export CalculusSM.


Local Open Scope kn.


Ltac simp_eq_step :=
  match goal with
  | [ H1 : ?x = node2name ?a, H2 : ?x = node2name ?b |- _ ] => rewrite H1 in H2

  | [ H1 : ?x = Some ?a, H2 : ?x = Some ?b |- _ ] => rewrite H1 in H2

  | [ H : node2name ?a = node2name ?b |- _ ] =>
    apply node2name_inj in H;
    try (first [ subst a
               | subst b
               | rewrite H in *
               | rewrite <- H in * ]);
    GC; auto



  | [ H : Some ?a = Some ?b |- _ ] =>
    apply Some_inj in H;
    try (first [ subst a
               | subst b
               | rewrite H in *
               | rewrite <- H in * ]);
    GC; auto
  end.

Ltac simp_eq := repeat simp_eq_step.

Ltac eq_states :=
  repeat match goal with
         | [ H1 : id_before ?e ?c1
           , H2 : id_before ?e ?c2 |- _ ] =>
           let h := fresh "h" in
           assert (c2 = c1) as h by eauto 3 with kn;
           subst c2

         | [ H1 : id_after ?e ?c1
           , H2 : id_after ?e ?c2 |- _ ] =>
           let h := fresh "h" in
           assert (c2 = c1) as h by eauto 3 with kn;
           subst c2

         | [ H1 : state_before ?e ?mem1
                  , H2 : state_before ?e ?mem2 |- _ ] =>
           let h := fresh "h" in
           assert (mem2 = mem1) as h by eauto 3 with kn;
           subst mem2

         | [ H1 : state_after ?e ?mem1
                  , H2 : state_after ?e ?mem2 |- _ ] =>
           let h := fresh "h" in
           assert (mem2 = mem1) as h by eauto 3 with kn;
           subst mem2

         | [ H1 : trusted_state_before ?e ?mem1
                  , H2 : trusted_state_before ?e ?mem2 |- _ ] =>
           let h := fresh "h" in
           assert (mem2 = mem1) as h by eauto 3 with kn;
           subst mem2

         | [ H1 : trusted_state_after ?e ?mem1
                  , H2 : trusted_state_after ?e ?mem2 |- _ ] =>
           let h := fresh "h" in
           assert (mem2 = mem1) as h by eauto 3 with kn;
           subst mem2
         end.

Ltac norm_with_aux x exp rest F h :=
  match exp with
  | ?H • (x › ?a) => assert (H • (x › a) ⊕ rest = F) as h
  | ?H • (?y › ?a) => norm_with_aux x H (∅ • (y › a) ⊕ rest) F h
  end.

(*Ltac norm_with x :=
    match goal with
    | [ |- context[⟬ _ ⟭ ?exp ⊢ _ ] ] =>
      let h := fresh "h" in
      norm_with_aux x exp ∅ exp h;
      [autorewrite with norm;auto
      |rewrite <- h; clear h]
    end.*)

Ltac norm_with x :=
  match goal with
  | [ |- context[⟬ _ ⟭ (?exp ⊕ ?rest) ⊢ _ ] ] =>
    let h := fresh "h" in
    norm_with_aux x exp rest (exp ⊕ rest) h;
    [autorewrite with norm;auto;fail
    |try rewrite <- h; clear h]
  | [ |- context[⟬ _ ⟭ ?exp ⊢ _ ] ] =>
    let h := fresh "h" in
    norm_with_aux x exp ∅ exp h;
    [autorewrite with norm;auto;fail
    |try rewrite <- h; clear h]
  end.

(*Ltac causal_norm_with_aux x R accum exp hyp :=
  match R with
  | (x ⋈ ?a) :: ?Q => assert (accum ++ (x ⋈ a) :: Q = exp) as hyp
  | (?y ⋈ ?a) :: ?Q => causal_norm_with_aux x Q (snoc accum (y ⋈ a)) exp hyp
  end.

Ltac causal_norm_with x :=
  match goal with
  | [ |- context[⟬ ?Q ++ ?R ⟭ _ ⊢ _ ] ] =>
    let h := fresh "h" in
    causal_norm_with_aux x R Q (Q ++ R) h;
    [autorewrite with norm;simpl;auto;fail
    |try rewrite <- h; clear h]
  | [ |- context[⟬ ?R ⟭ _ ⊢ _ ] ] =>
    let h := fresh "h" in
    causal_norm_with_aux x R (@nil namedCausalRel) R h;
    [autorewrite with norm;simpl;auto;fail
    |try rewrite <- h; clear h]
  end.*)

Ltac causal_norm_with_aux x R accum exp hyp :=
  match R with
  | (x ⋈ ?a) :: ?Q => assert (accum ++ (x ⋈ a) :: Q = exp) as hyp
  | (?y ⋈ ?a) :: ?Q => causal_norm_with_aux x Q (snoc accum (y ⋈ a)) exp hyp
  | ?X ++ ?Q => causal_norm_with_aux x Q (app accum X) exp hyp
  end.

Ltac causal_norm_with x :=
  match goal with
  | [ |- context[⟬ ?R ⟭ _ ⊢ _ ] ] =>
    let h := fresh "h" in
    causal_norm_with_aux x R (@nil namedCausalRel) R h;
    [autorewrite with norm;simpl;auto;fail
    |try rewrite <- h; clear h]
  end.

Ltac simpl_sem_rule :=
  repeat match goal with
         | [ H : rule_e_t_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ _ _ |- _ ] => apply rule_0_t_d_c_n_p_v_hypotheses_true in H
         | [ H : rule_e_t_d_c_n_p_v_hypotheses_true 1 _ _ _ _ _ _ _ |- _ ] => apply rule_1_t_d_c_n_p_v_hypotheses_true in H
         | [ H : rule_t_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ _ |- _ ] => apply rule_0_d_c_n_p_v_hypotheses_true in H
         | [ H : rule_t_d_c_n_p_v_hypotheses_true 1 _ _ _ _ _ _ |- _ ] => apply rule_1_d_c_n_p_v_hypotheses_true in H
         | [ H : rule_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ |- _ ] => apply rule_0_c_n_p_v_hypotheses_true in H
         | [ H : rule_d_c_n_p_v_hypotheses_true 1 _ _ _ _ _ |- _ ] => apply rule_1_c_n_p_v_hypotheses_true in H
         | [ H : rule_c_n_p_v_hypotheses_true 0 _ _ _ _ |- _ ] => apply rule_0_n_p_v_hypotheses_true in H
         | [ H : rule_c_n_p_v_hypotheses_true 1 _ _ _ _ |- _ ] => apply rule_1_n_p_v_hypotheses_true in H
         | [ H : rule_n_p_v_hypotheses_true 0 _ _ _ |- _ ] => apply rule_0_p_v_hypotheses_true in H
         | [ H : rule_n_p_v_hypotheses_true 1 _ _ _ |- _ ] => apply rule_1_p_v_hypotheses_true in H
         | [ H : rule_p_v_hypotheses_true 0 _ _ |- _ ] => apply rule_0_v_hypotheses_true in H
         | [ H : rule_p_v_hypotheses_true 1 _ _ |- _ ] => apply rule_1_v_hypotheses_true in H
         | [ H : rule_v_hypotheses_true 0 _ |- _ ] => apply rule_0_hypotheses_true in H
         | [ H : rule_v_hypotheses_true 1 _ |- _ ] => apply rule_1_hypotheses_true in H

         | [ H : rule__hypotheses_true _ |- _ ] => unfold rule__hypotheses_true in H; simpl in H

         | [ H : rule_1e_t_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ _ |- _ ] => apply rule_1e_0_d_c_n_p_v_hypotheses_true in H
         | [ H : rule_1e_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ |- _ ] => apply rule_1e_0_c_n_p_v_hypotheses_true in H
         | [ H : rule_1e_c_n_p_v_hypotheses_true 0 _ _ _ _ |- _ ] => apply rule_1e_0_n_p_v_hypotheses_true in H
         | [ H : rule_1e_n_p_v_hypotheses_true 0 _ _ _ |- _ ] => apply rule_1e_0_p_v_hypotheses_true in H
         | [ H : rule_1e_p_v_hypotheses_true 0 _ _ |- _ ] => apply rule_1e_0_v_hypotheses_true in H
         | [ H : rule_1e_v_hypotheses_true 0 _ |- _ ] => apply rule_1e_0_hypotheses_true in H

         | [ H : rule_1t_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ |- _ ] => apply rule_1t_0_c_n_p_v_hypotheses_true in H
         | [ H : rule_1t_c_n_p_v_hypotheses_true 0 _ _ _ _ |- _ ] => apply rule_1t_0_n_p_v_hypotheses_true in H
         | [ H : rule_1t_n_p_v_hypotheses_true 0 _ _ _ |- _ ] => apply rule_1t_0_p_v_hypotheses_true in H
         | [ H : rule_1t_p_v_hypotheses_true 0 _ _ |- _ ] => apply rule_1t_0_v_hypotheses_true in H
         | [ H : rule_1t_v_hypotheses_true 0 _ |- _ ] => apply rule_1t_0_hypotheses_true in H

         | [ H : rule_1d_c_n_p_v_hypotheses_true 0 _ _ _ _ |- _ ] => apply rule_1d_0_n_p_v_hypotheses_true in H
         | [ H : rule_1d_n_p_v_hypotheses_true 0 _ _ _ |- _ ] => apply rule_1d_0_p_v_hypotheses_true in H
         | [ H : rule_1d_p_v_hypotheses_true 0 _ _ |- _ ] => apply rule_1d_0_v_hypotheses_true in H
         | [ H : rule_1d_v_hypotheses_true 0 _ |- _ ] => apply rule_1d_0_hypotheses_true in H

         | [ H : rule_1c_n_p_v_hypotheses_true 0 _ _ _ |- _ ] => apply rule_1c_0_p_v_hypotheses_true in H
         | [ H : rule_1c_p_v_hypotheses_true 0 _ _ |- _ ] => apply rule_1c_0_v_hypotheses_true in H
         | [ H : rule_1c_v_hypotheses_true 0 _ |- _ ] => apply rule_1c_0_hypotheses_true in H

         | [ H : rule_1n_p_v_hypotheses_true 0 _ _ |- _ ] => apply rule_1n_0_v_hypotheses_true in H
         | [ H : rule_1n_v_hypotheses_true 0 _ |- _ ] => apply rule_1n_0_hypotheses_true in H

         | [ H : rule_1p_v_hypotheses_true 0 _ |- _ ] => apply rule_1p_0_hypotheses_true in H

         | [ H : Vector.t _ 0 -> _ |- _ ] => pose proof (H (Vector.nil _)) as H
         | [ H : Vector.t _ 0 |- _ ] => induction H using Vector.case0; simpl in *
         | [ H : Vector.t _ 1 |- _ ] => induction H using Vector.caseS'; simpl in *
         end.

Ltac intro_sem_rule :=
  repeat match goal with
         | [ |- rule_e_t_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ _ _ ] => apply rule_0_t_d_c_n_p_v_hypotheses_true
         | [ |- rule_e_t_d_c_n_p_v_hypotheses_true 1 _ _ _ _ _ _ _ ] => apply rule_1_t_d_c_n_p_v_hypotheses_true
         | [ |- rule_t_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ _ ] => apply rule_0_d_c_n_p_v_hypotheses_true
         | [ |- rule_t_d_c_n_p_v_hypotheses_true 1 _ _ _ _ _ _ ] => apply rule_1_d_c_n_p_v_hypotheses_true
         | [ |- rule_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ ] => apply rule_0_c_n_p_v_hypotheses_true
         | [ |- rule_d_c_n_p_v_hypotheses_true 1 _ _ _ _ _ ] => apply rule_1_c_n_p_v_hypotheses_true
         | [ |- rule_c_n_p_v_hypotheses_true 0 _ _ _ _ ] => apply rule_0_n_p_v_hypotheses_true
         | [ |- rule_c_n_p_v_hypotheses_true 1 _ _ _ _ ] => apply rule_1_n_p_v_hypotheses_true
         | [ |- rule_n_p_v_hypotheses_true 0 _ _ _ ] => apply rule_0_p_v_hypotheses_true
         | [ |- rule_n_p_v_hypotheses_true 1 _ _ _ ] => apply rule_1_p_v_hypotheses_true
         | [ |- rule_p_v_hypotheses_true 0 _ _ ] => apply rule_0_v_hypotheses_true
         | [ |- rule_p_v_hypotheses_true 1 _ _ ] => apply rule_1_v_hypotheses_true
         | [ |- rule_v_hypotheses_true 0 _ ] => apply rule_0_hypotheses_true
         | [ |- rule_v_hypotheses_true 1 _ ] => apply rule_1_hypotheses_true

         | [ |- rule__hypotheses_true _ ] => unfold rule__hypotheses_true; simpl

         | [ |- rule_1e_t_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ _ ] => apply rule_1e_0_d_c_n_p_v_hypotheses_true
         | [ |- rule_1e_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ ] => apply rule_1e_0_c_n_p_v_hypotheses_true
         | [ |- rule_1e_c_n_p_v_hypotheses_true _ _ 0 _ _ ] => apply rule_1e_0_n_p_v_hypotheses_true
         | [ |- rule_1e_n_p_v_hypotheses_true 0 _ _ _ ] => apply rule_1e_0_p_v_hypotheses_true
         | [ |- rule_1e_p_v_hypotheses_true 0 _ _ ] => apply rule_1e_0_v_hypotheses_true
         | [ |- rule_1e_v_hypotheses_true 0 _ ] => apply rule_1e_0_hypotheses_true

         | [ |- rule_1t_d_c_n_p_v_hypotheses_true 0 _ _ _ _ _ ] => apply rule_1t_0_c_n_p_v_hypotheses_true
         | [ |- rule_1t_c_n_p_v_hypotheses_true 0 _ _ _ _ ] => apply rule_1t_0_n_p_v_hypotheses_true
         | [ |- rule_1t_n_p_v_hypotheses_true 0 _ _ _ ] => apply rule_1t_0_p_v_hypotheses_true
         | [ |- rule_1t_p_v_hypotheses_true 0 _ _ ] => apply rule_1t_0_v_hypotheses_true
         | [ |- rule_1t_v_hypotheses_true 0 _ ] => apply rule_1t_0_hypotheses_true

         | [ |- rule_1d_c_n_p_v_hypotheses_true 0 _ _ _ _ ] => apply rule_1d_0_n_p_v_hypotheses_true
         | [ |- rule_1d_n_p_v_hypotheses_true 0 _ _ _ ] => apply rule_1d_0_p_v_hypotheses_true
         | [ |- rule_1d_p_v_hypotheses_true 0 _ _ ] => apply rule_1d_0_v_hypotheses_true
         | [ |- rule_1d_v_hypotheses_true 0 _ ] => apply rule_1d_0_hypotheses_true

         | [ |- rule_1c_n_p_v_hypotheses_true 0 _ _ _ ] => apply rule_1c_0_p_v_hypotheses_true
         | [ |- rule_1c_p_v_hypotheses_true 0 _ _ ] => apply rule_1c_0_v_hypotheses_true
         | [ |- rule_1c_v_hypotheses_true 0 _ ] => apply rule_1c_0_hypotheses_true

         | [ |- rule_1n_p_v_hypotheses_true 0 _ _ ] => apply rule_1n_0_v_hypotheses_true
         | [ |- rule_1n_v_hypotheses_true 0 _ ] => apply rule_1n_0_hypotheses_true

         | [ |- rule_1p_v_hypotheses_true 0 _ ] => apply rule_1p_0_hypotheses_true

         | [ |- rule_1e_hypotheses_true _ ] =>
           let e := fresh "e" in
           intro e; try clear e

         | [ |- rule_1t_hypotheses_true _ ] =>
           let t := fresh "t" in
           intro t; try clear t

         | [ |- rule_1c_hypotheses_true _ ] =>
           let c := fresh "c" in
           intro c; try clear c

         | [ |- rule_1n_hypotheses_true _ ] =>
           let n := fresh "n" in
           intro n; try clear n

         | [ |- Vector.t _ 0 -> _ ] =>
           let l := fresh "l" in
           intro l; try clear l
         | [ |- Vector.t _ 1 -> _ ] =>
           let l := fresh "l" in
           intro l; try clear l
         end.

Ltac simseqs a :=
  simpl; auto;
  intro_sem_rule;
  simpl_sem_rule;
  introv a; simpl in a;
  repndors; subst; tcsp;
  autorewrite with norm;
  simpl_sem_rule; auto.

Ltac inst_hyp t h :=
  match goal with
  | [ H : rule_1e_hypotheses_true _ |- _ ] =>
    let H' := fresh H in
    dup H as H';
    pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

  | [ H : rule_1t_hypotheses_true _ |- _ ] =>
    let H' := fresh H in
    dup H as H';
    pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

  | [ H : rule_1d_hypotheses_true _ |- _ ] =>
    let H' := fresh H in
    dup H as H';
    pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

  | [ H : rule_1c_hypotheses_true _ |- _ ] =>
    let H' := fresh H in
    dup H as H';
    pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

  | [ H : rule_1n_hypotheses_true _ |- _ ] =>
    let H' := fresh H in
    dup H as H';
    pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

  | [ H : rule_1p_hypotheses_true _ |- _ ] =>
    let H' := fresh H in
    dup H as H';
    pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

  | [ H : rule_1v_hypotheses_true _ |- _ ] =>
    let H' := fresh H in
    dup H as H';
    pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto
  end.

(* To prove primitive rules *)
Ltac start_proving_primitive st ct ht :=
  introv st ct ht; simpl in *;
  simpl_sem_rule;
  dLin_hyp st; simpl in *.

(* To prove derived rules *)
Ltac start_proving_derived st :=
  introv st; simpl in *; simpl_sem_rule; dLin_hyp st.



Tactic Notation "LOCKapply" constr(x) :=
  let j := fresh "j" in
  apply x; simseqs j.

Tactic Notation "LOCKapply@" constr(y) constr(x) :=
  first [norm_with y | causal_norm_with y]; LOCKapply x.

Tactic Notation "LOCKapply@" constr(y) constr(x) constr(z) :=
  first [norm_with y | causal_norm_with y]; LOCKapply@ x z.

Ltac LOCKcut1 v t :=
  LOCKapply (PRIMITIVE_RULE_cut_true v t).

Ltac LOCKcut2 v w t :=
  LOCKapply (PRIMITIVE_RULE_cut_after_true v w t).

Tactic Notation "LOCKcut" constr(v) constr(t) := LOCKcut1 v t.
Tactic Notation "LOCKcut" constr(v) constr(w) constr(t) := LOCKcut2 v w t.

(* Eventually move to tactics file *)
Ltac LOCKintro0 :=
  match goal with
  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_AND ?a ?b @ ?e)] =>
    LOCKapply PRIMITIVE_RULE_and_intro_true

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_ID ?f @ ?e)] =>
    LOCKapply PRIMITIVE_RULE_all_id_intro_true

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_DATA ?f @ ?e)] =>
    LOCKapply PRIMITIVE_RULE_all_data_intro_true

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_TRUST ?f @ ?e)] =>
    LOCKapply PRIMITIVE_RULE_all_trust_intro_true

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_NODE ?f @ ?e)] =>
    LOCKapply PRIMITIVE_RULE_all_node_intro_true

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_TIME ?f @ ?e)] =>
    LOCKapply PRIMITIVE_RULE_all_time_intro_true

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_VOUCHERS ?f @ ?e)] =>
    LOCKapply PRIMITIVE_RULE_all_vouchers_intro_true

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro0
  end.

Ltac LOCKintro1 x :=
  match goal with
  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_IMPLIES ?a ?b @ ?e)] =>
    LOCKapply (PRIMITIVE_RULE_implies_intro_true x)

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_OR ?a ?b @ ?e)] =>
    match x with
    | 0 => LOCKapply PRIMITIVE_RULE_or_intro_left_true
    | _ => LOCKapply PRIMITIVE_RULE_or_intro_right_true
    end

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_NODE ?f @ ?e)] =>
    LOCKapply (PRIMITIVE_RULE_exists_node_intro_true x)

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_TIME ?f @ ?e)] =>
    LOCKapply (PRIMITIVE_RULE_exists_time_intro_true x)

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_VOUCHERS ?f @ ?e)] =>
    LOCKapply (PRIMITIVE_RULE_exists_vouchers_intro_true x)

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_ID ?f @ ?e)] =>
    LOCKapply (PRIMITIVE_RULE_exists_id_intro_true x)

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_DATA ?f @ ?e)] =>
    LOCKapply (PRIMITIVE_RULE_exists_data_intro_true x)

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_TRUST ?f @ ?e)] =>
    LOCKapply (PRIMITIVE_RULE_exists_trust_intro_true x)

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ @ ?e)] =>
    unfold a; LOCKintro1 x
  end.

Tactic Notation "LOCKintro" := LOCKintro0.
Tactic Notation "LOCKintro" constr(x) := LOCKintro1 x.

Tactic Notation "LOCKintros" :=
  repeat LOCKintro0.
Tactic Notation "LOCKintros" constr(x1) :=
  repeat LOCKintro0; LOCKintro1 x1;
  repeat LOCKintro0.
Tactic Notation "LOCKintros" constr(x1) constr(x2) :=
  repeat LOCKintro0; LOCKintro1 x1;
  repeat LOCKintro0; LOCKintro1 x2;
  repeat LOCKintro0.
Tactic Notation "LOCKintros" constr(x1) constr(x2) constr(x3) :=
  repeat LOCKintro0; LOCKintro1 x1;
  repeat LOCKintro0; LOCKintro1 x2;
  repeat LOCKintro0; LOCKintro1 x3;
  repeat LOCKintro0.
Tactic Notation "LOCKintros" constr(x1) constr(x2) constr(x3) constr(x4) :=
  repeat LOCKintro0; LOCKintro1 x1;
  repeat LOCKintro0; LOCKintro1 x2;
  repeat LOCKintro0; LOCKintro1 x3;
  repeat LOCKintro0; LOCKintro1 x4;
  repeat LOCKintro0.

Ltac LOCKelim1 v :=
  norm_with v;
  match goal with
  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_IMPLIES ?a ?b @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply PRIMITIVE_RULE_implies_elim_true

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_OR ?a ?b @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply PRIMITIVE_RULE_or_elim_true

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_NODE ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_exists_node_elim_true v)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_TIME ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_exists_time_elim_true v)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_VOUCHERS ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_exists_vouchers_elim_true v)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_ID ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_exists_id_elim_true v)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_DATA ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_exists_data_elim_true v)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_TRUST ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_exists_trust_elim_true v)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim1 v
  end.

Ltac LOCKelim2 v w :=
  norm_with v;
  match goal with
  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_AND ?a ?b @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_and_elim_true v w)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_NODE ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_all_node_elim_true v w)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_TIME ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_all_time_elim_true v w)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_VOUCHERS ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_all_vouchers_elim_true v w)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_ID ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_all_id_elim_true v w)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_DATA ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_all_data_elim_true v w)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_TRUST ?f @ ?e) ⊕ ?J ⊢ ?c)] =>
    LOCKapply (PRIMITIVE_RULE_all_trust_elim_true v w)

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w

  | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  @ ?e) ⊕ ?J ⊢ ?c)] =>
    unfold a; LOCKelim2 v w
  end.

Tactic Notation "LOCKelim" constr(x) := LOCKelim1 x.
Tactic Notation "LOCKelim" constr(x) constr(y) := LOCKelim2 x y.

Ltac LOCKauto :=
  match goal with
  | [ |- sequent_true (⟬ _ ⟭ _ ⊢ KE_NODE @ ?e)] =>
    LOCKapply DERIVED_RULE_node_true

  | [ |- sequent_true (⟬ _ ⟭ _ ⊢ KE_AT _ @ ?e)] =>
    LOCKapply PRIMITIVE_RULE_at_true

  | [ |- sequent_true (⟬ _ ⟭ _ ⊢ KE_TRUE @ ?e)] =>
    LOCKapply DERIVED_RULE_true_true

  | [ |- sequent_true (⟬ _ ⟭ _ ⊢ KE_ID_EQ ?c ?c @ _)] =>
    LOCKapply PRIMITIVE_RULE_id_eq_refl_true

  | [ |- sequent_true (⟬ _ ⟭ _ ⊢ KE_OR KE_FIRST KE_NOT_FIRST @ ?e)] =>
    LOCKapply PRIMITIVE_RULE_first_dec_true

  | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a) ] =>
    match H with
    | context[?v › a] =>
      norm_with v; LOCKapply PRIMITIVE_RULE_hypothesis_true

    | context[?v › KE_FALSE @ ?e] =>
      norm_with v; LOCKapply DERIVED_RULE_false_elim_true

    | context[?v › KE_ID_LT ?i ?i @ ?e] =>
      norm_with v; LOCKapply PRIMITIVE_RULE_id_lt_elim_true
    end
  end.

Ltac LOCKclearH :=
  match goal with
  | [ |- sequent_true (⟬ ?R ⟭ (?H • (?v › _ @ _)) ⊢ _)] =>
    norm_with v; LOCKapply PRIMITIVE_RULE_thin_true
  end.

Ltac LOCKclearG :=
  match goal with
  | [ |- sequent_true (⟬ ?R ++ (?x ⋈ ?c) :: ?Q ⟭ _ ⊢ _)] =>
    causal_norm_with x; LOCKapply PRIMITIVE_RULE_remove_causal_true
  | [ |- sequent_true (⟬ (?x ⋈ ?c) :: ?Q ⟭ _ ⊢ _)] =>
    causal_norm_with x; LOCKapply PRIMITIVE_RULE_remove_causal_true
  end.

Ltac LOCKclearH_at x :=
  norm_with x;
  match goal with
  | [ |- sequent_true (⟬ ?R ⟭ ?H • (x › ?a) ⊕ ?J ⊢ _)] =>
    LOCKapply PRIMITIVE_RULE_thin_true
  end.

Ltac LOCKclearG_at x :=
  causal_norm_with x;
  match goal with
  | [ |- sequent_true (⟬ ?R ++ (x ⋈ ?c) :: ?Q ⟭ _ ⊢ _)] =>
    LOCKapply PRIMITIVE_RULE_remove_causal_true
  end.

Tactic Notation "LOCKclearone" := first [LOCKclearH | LOCKclearG].
Tactic Notation "LOCKclearall" := repeat LOCKclearone.

Tactic Notation "LOCKclear" := LOCKclearH.
Tactic Notation "LOCKclear" constr(x) := first [LOCKclearG_at x | LOCKclearH_at x].
Tactic Notation "LOCKclear" constr(x1) constr(x2) :=
  first [LOCKclearG_at x1 | LOCKclearH_at x1];
  first [LOCKclearG_at x2 | LOCKclearH_at x2].
Tactic Notation "LOCKclear" constr(x1) constr(x2) constr(x3) :=
  first [LOCKclearG_at x1 | LOCKclearH_at x1];
  first [LOCKclearG_at x2 | LOCKclearH_at x2];
  first [LOCKclearG_at x3 | LOCKclearH_at x3].
Tactic Notation "LOCKclear" constr(x1) constr(x2) constr(x3) constr(x4) :=
  first [LOCKclearG_at x1 | LOCKclearH_at x1];
  first [LOCKclearG_at x2 | LOCKclearH_at x2];
  first [LOCKclearG_at x3 | LOCKclearH_at x3];
  first [LOCKclearG_at x4 | LOCKclearH_at x4].
Tactic Notation "LOCKclear" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) :=
  first [LOCKclearG_at x1 | LOCKclearH_at x1];
  first [LOCKclearG_at x2 | LOCKclearH_at x2];
  first [LOCKclearG_at x3 | LOCKclearH_at x3];
  first [LOCKclearG_at x4 | LOCKclearH_at x4];
  first [LOCKclearG_at x5 | LOCKclearH_at x5].



Hint Rewrite @cons_as_addHyp : norm.
Hint Rewrite @addHyps_cons_as_addHyp : norm.
Hint Rewrite @addHyps_addHyp_em_eq1 : norm.
Hint Rewrite @addHyps_addHyp_em_eq2 : norm.
Hint Rewrite @addHyps_addHyp_eq3 : norm.
Hint Rewrite @nil_as_emHyps : norm.
Hint Rewrite @addHyps_em : norm kc.
Hint Rewrite @snoc_app_eq : norm.

Hint Rewrite @rule_0_t_d_c_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_0_d_c_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_0_c_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_0_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_0_p_v_hypotheses_true : rule.
Hint Rewrite @rule_0_v_hypotheses_true : rule.
Hint Rewrite @rule_0_hypotheses_true : rule.

Hint Rewrite @rule_1_t_d_c_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1e_0_d_c_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1e_0_c_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1e_0_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1e_0_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1e_0_v_hypotheses_true : rule.
Hint Rewrite @rule_1e_0_hypotheses_true : rule.

Hint Rewrite @rule_1_d_c_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1t_0_c_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1t_0_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1t_0_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1t_0_v_hypotheses_true : rule.
Hint Rewrite @rule_1t_0_hypotheses_true : rule.

Hint Rewrite @rule_1_c_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1d_0_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1t_0_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1t_0_v_hypotheses_true : rule.
Hint Rewrite @rule_1t_0_hypotheses_true : rule.

Hint Rewrite @rule_1_n_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1c_0_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1c_0_v_hypotheses_true : rule.
Hint Rewrite @rule_1c_0_hypotheses_true : rule.

Hint Rewrite @rule_1_p_v_hypotheses_true : rule.
Hint Rewrite @rule_1n_0_v_hypotheses_true : rule.
Hint Rewrite @rule_1n_0_hypotheses_true : rule.

Hint Rewrite @rule_1_v_hypotheses_true : rule.
Hint Rewrite @rule_1p_0_hypotheses_true : rule.

Hint Rewrite @rule_1_hypotheses_true : rule.
