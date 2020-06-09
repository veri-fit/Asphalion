Require Export CalculusSM.
Require Export CalculusSM_tacs.


Section CalculusSM_derived0.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pm  : @Msg }.
  Context { qc  : @Quorum_context pn}.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pda : @DataAuth pd pn }.
  Context { cad : @ContainedAuthData pd pat pm }.
  Context { dtc : @DTimeContext }.
  Context { iot : @IOTrustedFun }.
  Context { ctp : @ComponentTrust pd pn pat qc iot }.
  Context { cap : @ComponentAuth pd pn pk pat pm dtc iot }.

  Local Open Scope eo.
  Local Open Scope proc.


  Context { base_fun_io       : baseFunIO           }.
  Context { base_state_fun    : baseStateFun        }.
  Context { trusted_state_fun : trustedStateFun     }.
  Context { pkc               : KnowledgeComponents }.
  Context { gms               : MsgStatus           }.


  Local Open Scope kn.


  (*  ****** DERIVED RULES ****** *)


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_forall_before_hyp u x {eo : EventOrdering} e' e Q R H J a b :=
    MkRule0
      [⟬Q ++ (u ⋈ e' □ e) :: R⟭ H • (x › a @ e') » J ⊢ b]
      (⟬Q ++ (u ⋈ e' □ e) :: R⟭ H • (x › KE_LOCAL_FORALL_BEFORE a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unlocal_forall_before_hyp_true :
    forall u x {eo : EventOrdering} e' e Q R H J a b,
      rule_true (DERIVED_RULE_unlocal_forall_before_hyp u x e' e Q R H J a b).
  Proof.
    start_proving_derived st.
    LOCKelim x.
    LOCKelim x "x".
    LOCKapply@ u (PRIMITIVE_RULE_duplicate_guard_true u "u").
    LOCKapply@ "u" PRIMITIVE_RULE_local_if_causal_true.
    LOCKapply@ "u" x PRIMITIVE_RULE_forall_before_elim_true.
    LOCKelim x.
    { LOCKapply@ u PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ u PRIMITIVE_RULE_at_change_localle_fwd_true; try LOCKauto. }
    LOCKclear "x".
    LOCKclear "u".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owns_implies_local x t {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ▷ e2) :: Q⟭ H ⊢ KE_OWNS t @ e1,
       ⟬R ++ (x ⋈ e1 ▷ e2) :: Q⟭ H ⊢ KE_OWNS t @ e2,
       ⟬R ++ (x ⋈ e1 □ e2) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e1 ▷ e2) :: Q⟭ H ⊢ a).

  Lemma DERIVED_RULE_owns_implies_local_true :
    forall x t {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_owns_implies_local x t e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "o1" (KE_OWNS t @ e1).
    LOCKcut "o2" (KE_OWNS t @ e2).
    { LOCKclear "o1". }
    Transparent KE_OWNS.
    LOCKelim "o1".
    LOCKelim "o2".
    Opaque KE_OWNS.
    LOCKelim "o1" "o1'".
    LOCKelim "o2" "o2'".
    LOCKcut "eq" (KE_NODE_EQ n n0 @ e2).
    { LOCKapply (PRIMITIVE_RULE_has_owner_implies_eq_true t); try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_has_owner_change_event_true e2 e1); try LOCKauto. }
    LOCKapply@ x (PRIMITIVE_RULE_at_implies_local_true x n); try LOCKauto.
    { LOCKapply (PRIMITIVE_RULE_subst_node_in_at_true n0); try LOCKauto.
      LOCKapply PRIMITIVE_RULE_node_eq_sym_true; try LOCKauto. }
    LOCKclear "o1" "o1'" "o2" "o2'" "eq".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owns_implies_localle x t {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ▶ e2) :: Q⟭ H ⊢ KE_OWNS t @ e1,
       ⟬R ++ (x ⋈ e1 ▶ e2) :: Q⟭ H ⊢ KE_OWNS t @ e2,
       ⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e1 ▶ e2) :: Q⟭ H ⊢ a).

  Lemma DERIVED_RULE_owns_implies_localle_true :
    forall x t {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_owns_implies_localle x t e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "o1" (KE_OWNS t @ e1).
    LOCKcut "o2" (KE_OWNS t @ e2).
    { LOCKclear "o1". }
    Transparent KE_OWNS.
    LOCKelim "o1".
    LOCKelim "o2".
    Opaque KE_OWNS.
    LOCKelim "o1" "o1'".
    LOCKelim "o2" "o2'".
    LOCKcut "eq" (KE_NODE_EQ n n0 @ e2).
    { LOCKapply (PRIMITIVE_RULE_has_owner_implies_eq_true t); try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_has_owner_change_event_true e2 e1); try LOCKauto. }
    LOCKapply@ x (PRIMITIVE_RULE_at_implies_localle_true x n); try LOCKauto.
    { LOCKapply (PRIMITIVE_RULE_subst_node_in_at_true n0); try LOCKauto.
      LOCKapply PRIMITIVE_RULE_node_eq_sym_true; try LOCKauto. }
    LOCKclear "o1" "o1'" "o2" "o2'" "eq".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_hyp u x {eo : EventOrdering} e R H J a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' □ e) :: R⟭ H • (x › a @ e') » J ⊢ b])
      (⟬R⟭ H • (x › KE_LOCAL_BEFORE a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unlocal_before_hyp_true :
    forall u x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unlocal_before_hyp u x e R H J a b).
  Proof.
    start_proving_derived st.
    LOCKelim x.
    LOCKelim x "x".
    LOCKapply@ x (PRIMITIVE_RULE_unhappened_before_hyp_true u).
    LOCKelim x "y".
    inst_hyp e0 hyp.
    LOCKapply@ u (PRIMITIVE_RULE_at_implies_local_true u n); try LOCKauto.
    LOCKclear "x" "y".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_if_causal x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE a @ e).

  Lemma DERIVED_RULE_unlocal_before_if_causal_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_if_causal x e' e R Q H a).
  Proof.
    start_proving_derived st.
    destruct (implies_ex_node e) as [n cond].
    LOCKintro n.
    LOCKintro; try LOCKauto.
    LOCKapply@ x (PRIMITIVE_RULE_duplicate_guard_true x "u").
    LOCKapply@ "u" PRIMITIVE_RULE_local_if_causal_true.
    LOCKapply@ "u" PRIMITIVE_RULE_unhappened_before_if_causal_true.
    LOCKintro.
    { LOCKapply@ x PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ x PRIMITIVE_RULE_at_change_localle_fwd_true; try LOCKauto. }
    LOCKapply@ "u" PRIMITIVE_RULE_remove_causal_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_if_local_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE a @ e).

  Lemma DERIVED_RULE_unlocal_before_if_causal_local_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_if_local_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_LOCAL_BEFORE a @ e').
    LOCKelim "x".
    LOCKintro n.
    LOCKelim "x" "y".
    LOCKintro.
    { LOCKapply@ x PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ x PRIMITIVE_RULE_at_change_localle_true; try LOCKauto. }
    LOCKapply@ "x" (PRIMITIVE_RULE_unhappened_before_hyp_true "u").
    LOCKapply@ x (PRIMITIVE_RULE_duplicate_guard_true x "v").
    LOCKapply@ "v" PRIMITIVE_RULE_local_if_causal_true.
    LOCKapply@ "v" PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq_true.
    LOCKapply@ "u" PRIMITIVE_RULE_unhappened_before_if_causal_true; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knew_before_implies_knows
             {eo : EventOrdering} (e : EventN) R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_KNEW i @ e]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE (KE_KNOWS i) @ e).

  Lemma DERIVED_RULE_knew_before_implies_knows_true :
    forall {eo : EventOrdering} (e : EventN) R H (i : kc_data),
      rule_true (DERIVED_RULE_knew_before_implies_knows e R H i).
  Proof.
    start_proving_derived st; auto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knows_before_implies_knew
             {eo : EventOrdering} (e : EventN) R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE (KE_KNOWS i) @ e]
      (⟬R⟭ H ⊢ KE_KNEW i @ e).

  Lemma DERIVED_RULE_knows_before_implies_knew_true :
    forall {eo : EventOrdering} (e : EventN) R H (i : kc_data),
      rule_true (DERIVED_RULE_knows_before_implies_knew e R H i).
  Proof.
    start_proving_derived st; auto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knew_implies_knows
             {eo : EventOrdering} (e : EventN) R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_KNEW i @ e]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_KNOWS i) @ e).

  Lemma DERIVED_RULE_knew_implies_knows_true :
    forall {eo : EventOrdering} (e : EventN) R H (i : kc_data),
      rule_true (DERIVED_RULE_knew_implies_knows e R H i).
  Proof.
    start_proving_derived st.
    LOCKintro 0.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_knew_implies_knows {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TKNEW t @ e]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_TKNOWS t) @ e).

  Lemma DERIVED_RULE_trusted_knew_implies_knows_true :
    forall {eo : EventOrdering} (e : EventN) R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_knew_implies_knows e R H t).
  Proof.
    introv; apply DERIVED_RULE_knew_implies_knows_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_revert x {eo : EventOrdering} e R H c J (a : KExpression) :=
    MkRule0
      [⟬R⟭ H » J ⊢ KE_IMPLIES c a @ e]
      (⟬R⟭ H • (x › c @ e) » J ⊢ a @ e).

  Lemma DERIVED_RULE_revert_true :
    forall x {eo : EventOrdering} (e : EventN) R H c J a,
      rule_true (DERIVED_RULE_revert x e R H c J a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" x (KE_IMPLIES c a @ e).
    { LOCKclear x. }
    LOCKelim "x"; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_revert_last {eo : EventOrdering} e R H x a (b : KExpression) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_IMPLIES a b @ e]
      (⟬R⟭ H • (x › a @ e) ⊢ b @ e).

  Lemma DERIVED_RULE_revert_last_true :
    forall {eo : EventOrdering} (e : EventN) R H x a b,
      rule_true (DERIVED_RULE_revert_last e R H x a b).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_IMPLIES a b @ e); try complete LOCKclear.
    LOCKelim "x"; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_thin_last {eo : EventOrdering} R H h a :=
    MkRule0
      [⟬R⟭ H ⊢ a]
      (⟬R⟭ H • h ⊢ a).

  Lemma DERIVED_RULE_thin_last_true :
    forall {eo : EventOrdering} R H h a,
      rule_true (DERIVED_RULE_thin_last R H h a).
  Proof.
    start_proving_derived st.
    destruct h as [x h]; LOCKapply@ x PRIMITIVE_RULE_thin_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_implies_elim x {eo : EventOrdering} e R H a b c :=
    MkRule0
      [⟬R⟭ H ⊢ a @ e,
       ⟬R⟭ H • (x › b @ e) ⊢ c]
      (⟬R⟭ H • (x › KE_IMPLIES a b @ e) ⊢ c).

  Lemma DERIVED_RULE_implies_elim_true :
    forall x {eo : EventOrdering} e R H a b c,
      rule_true (DERIVED_RULE_implies_elim x e R H a b c).
  Proof.
    start_proving_derived st.
    LOCKelim x.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_or_elim x {eo : EventOrdering} e R H A B c :=
    MkRule0
      [⟬R⟭ H • (x › A @ e) ⊢ c,
       ⟬R⟭ H • (x › B @ e) ⊢ c]
      (⟬R⟭ H • (x › KE_OR A B @ e) ⊢ c).

  Lemma DERIVED_RULE_or_elim_true :
    forall x {eo : EventOrdering} e R H A B c,
      rule_true (DERIVED_RULE_or_elim x e R H A B c).
  Proof.
    start_proving_derived st.
    LOCKelim x.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_and_elim x y {eo : EventOrdering} e R H A B c :=
    MkRule0
      [⟬R⟭ H • (x › B @ e) • (y › A @ e) ⊢ c]
      (⟬R⟭ H • (x › KE_AND A B @ e) ⊢ c).

  Lemma DERIVED_RULE_and_elim_true :
    forall x y {eo : EventOrdering} e R H A B c,
      rule_true (DERIVED_RULE_and_elim x y e R H A B c).
  Proof.
    start_proving_derived st.
    LOCKelim x y.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_hypothesis_last {eo : EventOrdering} R H x a :=
    MkRule0
      []
      (⟬R⟭ H • (x › a) ⊢ a).

  Lemma DERIVED_RULE_hypothesis_last_true :
    forall {eo : EventOrdering} R H x a,
      rule_true (DERIVED_RULE_hypothesis_last R H x a).
  Proof.
    start_proving_derived st; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_implies_not_first a {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE a @ e]
      (⟬R⟭ H ⊢ KE_NOT_FIRST @ e).

  Lemma DERIVED_RULE_right_before_implies_not_first_true :
    forall a {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_right_before_implies_not_first a e R H).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_RIGHT_BEFORE a @ e).
    LOCKapply@ "x" (PRIMITIVE_RULE_unright_before_hyp_if_causal_true "u").
    LOCKapply@ "u" PRIMITIVE_RULE_direct_pred_if_local_pred_true.
    LOCKapply@ "u" DERIVED_RULE_not_first_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knew_implies_not_first c {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_KNEW c @ e]
      (⟬R⟭ H ⊢ KE_NOT_FIRST @ e).

  Lemma DERIVED_RULE_knew_implies_not_first_true :
    forall c {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_knew_implies_not_first c e R H).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_KNEW c @ e).
    LOCKcut "y" (KE_RIGHT_BEFORE (KE_KNOWS c) @ e).
    { LOCKapply DERIVED_RULE_knew_before_implies_knows_true; try LOCKauto. }
    LOCKapply (DERIVED_RULE_right_before_implies_not_first_true (KE_KNOWS c)); try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_first_implies_at_local_pred {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ e,
       ⟬R⟭ H ⊢ KE_FIRST @ e]
      (⟬R⟭ H ⊢ a @ local_pred_n e).

  Lemma DERIVED_RULE_first_implies_at_local_pred_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_first_implies_at_local_pred e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_eq_true "u" e).
    LOCKapply@ "u" PRIMITIVE_RULE_causal_eq_sym_true.
    LOCKapply@ "u" PRIMITIVE_RULE_subst_causal_eq_concl_true.
    LOCKclear "u".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_at_local_pred_first_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ local_pred_n e,
       ⟬R⟭ H ⊢ KE_FIRST @ e]
      (⟬R⟭ H ⊢ a @ e).

  Lemma DERIVED_RULE_at_local_pred_first_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_at_local_pred_first_implies e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_eq_true "u" e).
    LOCKapply@ "u" PRIMITIVE_RULE_subst_causal_eq_concl_true.
    LOCKclear "u".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_add_local_pred_localle x {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬(x ⋈ local_pred_n e ■ e) :: R⟭ H ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma DERIVED_RULE_add_local_pred_localle_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_add_local_pred_localle x e R H a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_OR KE_FIRST KE_NOT_FIRST @ e); try LOCKauto.
    LOCKelim "x".
    { LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_eq_true x e); try LOCKauto.
      LOCKclear.
      causal_norm_with x; LOCKapply PRIMITIVE_RULE_localle_if_eq_true. }
    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_true x e); try LOCKauto.
    LOCKapply@ "x" (PRIMITIVE_RULE_thin_true "x").
    LOCKapply@ x PRIMITIVE_RULE_direct_pred_if_local_pred_true.
    LOCKapply@ x PRIMITIVE_RULE_local_if_localle_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_add_local_pred_local x {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬(x ⋈ local_pred_n e □ e) :: R⟭ H ⊢ a,
       ⟬R⟭ H ⊢ KE_NOT_FIRST @ e]
      (⟬R⟭ H ⊢ a).

  Lemma DERIVED_RULE_add_local_pred_local_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_add_local_pred_local x e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_true x e).
    LOCKapply@ x PRIMITIVE_RULE_direct_pred_if_local_pred_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unright_before_eq_hyp x {eo : EventOrdering} e R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › a @ local_pred_n e) » J ⊢ b]
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unright_before_eq_hyp_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unright_before_eq_hyp x e R H J a b).
  Proof.
    start_proving_derived st.
    LOCKcut "x" x (a @ local_pred_n e).
    { LOCKelim x.
      { LOCKapply PRIMITIVE_RULE_unright_before_hyp_true; try LOCKauto. }
      LOCKelim x "y".
      LOCKapply DERIVED_RULE_first_implies_at_local_pred_true; try LOCKauto. }
    LOCKclear x.
    LOCKapply@ "x"(PRIMITIVE_RULE_rename_hyp_true "x" x).
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_add_localle_refl x {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬(x ⋈ e ■ e) :: R⟭ H ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma DERIVED_RULE_add_localle_refl_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_add_localle_refl x e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_add_eq_refl_true x e).
    LOCKapply@ x PRIMITIVE_RULE_localle_if_eq_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_hyp u x {eo : EventOrdering} e R H J a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ■ e) :: R⟭ H • (x › a @ e') » J ⊢ b])
      (⟬R⟭ H • (x › KE_LOCAL_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unlocal_before_eq_hyp_true :
    forall u x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unlocal_before_eq_hyp u x e R H J a b).
  Proof.
    start_proving_derived st.
    LOCKelim x.

    { LOCKapply (DERIVED_RULE_unlocal_before_hyp_true u).
      LOCKapply@ u PRIMITIVE_RULE_local_if_localle_true.
      inst_hyp e0 st. }

    { LOCKelim x "x".
      LOCKclear x.
      LOCKapply@ "x"(PRIMITIVE_RULE_rename_hyp_true "x" x).
      LOCKapply (DERIVED_RULE_add_localle_refl_true u e).
      inst_hyp e st. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_eq_hyp u x {eo : EventOrdering} e R H J a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ▶ e) :: R⟭ H • (x › a @ e') » J ⊢ b])
      (⟬R⟭ H • (x › KE_HAPPENED_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unhappened_before_eq_hyp_true :
    forall u x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unhappened_before_eq_hyp u x e R H J a b).
  Proof.
    start_proving_derived st.
    LOCKelim x.

    { LOCKapply (PRIMITIVE_RULE_unhappened_before_hyp_true u).
      LOCKapply@ u PRIMITIVE_RULE_causal_if_causalle_true.
      inst_hyp e0 st. }

    { LOCKapply (DERIVED_RULE_add_localle_refl_true u e).
      LOCKapply@ u (PRIMITIVE_RULE_localle_if_causalle_true u).
      LOCKelim x "y".
      LOCKclear x.
      LOCKapply@ "y"(PRIMITIVE_RULE_rename_hyp_true "y" x).
      inst_hyp e st. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_remove_first_causal {eo : EventOrdering} c R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a]
      (⟬c :: R⟭ H ⊢ a).

  Lemma DERIVED_RULE_remove_first_causal_true :
    forall {eo : EventOrdering} c R H a,
      rule_true (DERIVED_RULE_remove_first_causal c R H a).
  Proof.
    start_proving_derived st.
    destruct c as [n r].
    LOCKclear n.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_causalle x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_causalle_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_causalle x e' e R Q H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_duplicate_guard_true x "u").
    LOCKapply PRIMITIVE_RULE_split_local_before_eq2_true.
    { LOCKintro 1.
      LOCKapply PRIMITIVE_RULE_subst_causal_eq_concl_true.
      LOCKapply@ "u" PRIMITIVE_RULE_remove_causal_true.
      LOCKintro; try LOCKauto. }
    { LOCKintro 0.
      LOCKapply@ "u" DERIVED_RULE_unlocal_before_if_causal_true.
      LOCKapply@ "u" PRIMITIVE_RULE_remove_causal_true. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_causal x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_causal_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_causal x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
    apply DERIVED_RULE_unlocal_before_if_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_causal_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_causal_trans_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_causal_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_LOCAL_BEFORE_EQ a @ e').
    LOCKapply (PRIMITIVE_RULE_duplicate_guard_true x "u").
    LOCKapply PRIMITIVE_RULE_split_local_before_eq2_true.

    { LOCKapply PRIMITIVE_RULE_subst_causal_eq_concl_true; try LOCKauto. }

    LOCKelim "x".

    { LOCKintro 0.
      LOCKapply DERIVED_RULE_unlocal_before_if_causal_local_true; try LOCKauto. }

    LOCKapply DERIVED_RULE_unlocal_before_eq_if_causal_true.
    LOCKapply@ "u" PRIMITIVE_RULE_remove_causal_true; try LOCKauto.
    LOCKelim "x" "y"; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_if_causal_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE a @ e).

  Lemma DERIVED_RULE_unlocal_before_if_causal_trans_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_if_causal_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE_EQ a @ e')); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.

    { apply DERIVED_RULE_unlocal_before_if_causal_local_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    apply DERIVED_RULE_unlocal_before_if_causal_true; simseqs j.
    LOCKelim "x" "y".
    norm_with "y"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (* DISCUSS *)
  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_if_causalle_trans_eq x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e']
      (⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma DERIVED_RULE_unhappened_before_if_causalle_trans_eq_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unhappened_before_if_causalle_trans_eq x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE a @ e')); simseqs j.
    apply (PRIMITIVE_RULE_duplicate_guard_true x "u"); simseqs j.

    causal_norm_with "u"; apply PRIMITIVE_RULE_split_happened_before_eq2_true; simseqs j.
    { causal_norm_with "u"; apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    causal_norm_with "u"; apply PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq_true; simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_if_causal_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma DERIVED_RULE_unhappened_before_if_causal_trans_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unhappened_before_if_causal_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE_EQ a @ e')); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.

    { apply PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    apply PRIMITIVE_RULE_unhappened_before_if_causal_true; simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    norm_with "c"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_eq_if_causalle x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unhappened_before_eq_if_causalle_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unhappened_before_eq_if_causalle x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (a @ e')); simseqs j.
    apply (PRIMITIVE_RULE_duplicate_guard_true x "u"); simseqs j.

    apply PRIMITIVE_RULE_split_happened_before_eq2_true; simseqs j.
    { apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_and_intro_true; simseqs j.
      { norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
      apply DERIVED_RULE_node_true; simseqs j. }

    apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
    apply PRIMITIVE_RULE_unhappened_before_if_causal_true; simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_eq_if_causalle_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unhappened_before_eq_if_causalle_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE_EQ a @ e')); simseqs j.
    apply (PRIMITIVE_RULE_duplicate_guard_true x "u"); simseqs j.
    apply PRIMITIVE_RULE_split_happened_before_eq2_true; simseqs j.

    { apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
    apply DERIVED_RULE_unhappened_before_if_causal_trans_true; simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_add_happenedle_refl x {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬(x ⋈ e ▶ e) :: R⟭ H ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma DERIVED_RULE_add_happenedle_refl_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_add_happenedle_refl x e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_localle_refl_true x e); simseqs j.
    apply add_nil2guards.
    apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_weaken_local_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_weaken_local_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_weaken_local_before_eq e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply PRIMITIVE_RULE_or_intro_right_true.
    LOCKintro; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_pred {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ (local_pred_n e)]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_pred_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_pred e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_local_pred_localle_true "x" e); simseqs j.
    causal_norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_if_causalle_true "x"); simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_causal_lt x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_causal_lt_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_causal_lt x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (a @ e')); simseqs j.
    apply PRIMITIVE_RULE_local_if_localle_true; simseqs j.
    apply DERIVED_RULE_unlocal_before_eq_if_causalle_true; simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_pred {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ (local_pred_n e)]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_pred_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_pred e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_local_pred_localle_true "v" e); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_unlocal_before_eq_if_causal_trans_true "v"); simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_eq_if_pred {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ (local_pred_n e)]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unhappened_before_eq_if_pred_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unhappened_before_eq_if_pred e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_local_pred_localle_true "v" e); simseqs j.
    causal_norm_with "v"; apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    causal_norm_with "v"; apply DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true; simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unright_before {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ local_pred_n e,
       ⟬R⟭ H ⊢ KE_NOT_FIRST @ e]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE a @ e).

  Lemma DERIVED_RULE_unright_before_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unright_before e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e); simseqs j.
    causal_norm_with "u"; apply PRIMITIVE_RULE_unright_before_if_causal_true; simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unright_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ (local_pred_n e)]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unright_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unright_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_OR KE_FIRST KE_NOT_FIRST @ e)); simseqs j.
    { apply PRIMITIVE_RULE_first_dec_true; simseqs j. }
    apply (DERIVED_RULE_or_elim_true "x"); simseqs j.
    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_and_intro_true; simseqs j.
      { apply DERIVED_RULE_at_local_pred_first_implies_true; simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j. }
        apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
    apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
    apply DERIVED_RULE_unright_before_true; simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j. }
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_before_implies_happened_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE a @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_before_implies_happened_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_before_implies_happened_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE a @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_hyp_true "u" "x"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_local_if_causal_true); simseqs j.
    causal_norm_with "u"; apply PRIMITIVE_RULE_causal_if_causalle_true; simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "u"); simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_implies {eo : EventOrdering} e R H a b :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_IMPLIES a b) @ e]
      (⟬R⟭ H ⊢ KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e).

  Lemma DERIVED_RULE_right_before_over_implies_true :
    forall {eo : EventOrdering} e R H a b,
      rule_true (DERIVED_RULE_right_before_over_implies e R H a b).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_IMPLIES a b) @ e)).
    LOCKintro "y".
    LOCKapply@ "x" DERIVED_RULE_unright_before_eq_hyp_true.
    LOCKapply@ "y" DERIVED_RULE_unright_before_eq_hyp_true.
    LOCKapply DERIVED_RULE_unright_before_eq_true.
    LOCKapply@ "x" PRIMITIVE_RULE_implies_elim_true; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_forall_before_eq_hyp u x {eo : EventOrdering} e' e Q R H J a b :=
    MkRule0
      [⟬Q ++ (u ⋈ e' ■ e) :: R⟭ H • (x › a @ e') » J ⊢ b]
      (⟬Q ++ (u ⋈ e' ■ e) :: R⟭ H • (x › KE_LOCAL_FORALL_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unlocal_forall_before_eq_hyp_true :
    forall u x {eo : EventOrdering} e' e Q R H J a b,
      rule_true (DERIVED_RULE_unlocal_forall_before_eq_hyp u x e' e Q R H J a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_duplicate_guard_true u "v"); simseqs j.
    causal_norm_with "v"; apply PRIMITIVE_RULE_split_local_before_eq2_true; simseqs j.
    { apply PRIMITIVE_RULE_causal_eq_sym_true; simseqs j.
      apply PRIMITIVE_RULE_subst_causal_eq_hyp_true; simseqs j.
      apply (PRIMITIVE_RULE_and_elim_true x "y"); simseqs j.
      norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j.
      causal_norm_with "v"; apply PRIMITIVE_RULE_remove_causal_true; simseqs j. }
    apply (PRIMITIVE_RULE_and_elim_true x "y"); simseqs j.
    causal_norm_with "v"; norm_with "y"; apply (DERIVED_RULE_unlocal_forall_before_hyp_true "v" "y"); simseqs j.
    norm_with x; apply (PRIMITIVE_RULE_thin_true x); simseqs j.
    norm_with "y"; apply (PRIMITIVE_RULE_rename_hyp_true "y" x); simseqs j.
    causal_norm_with "v"; apply PRIMITIVE_RULE_remove_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_happened_before_over_implies {eo : EventOrdering} e R H a b :=
    MkRule0
      [⟬R⟭ H ⊢ KE_FORALL_BEFORE (KE_IMPLIES a b) @ e]
      (⟬R⟭ H ⊢ KE_IMPLIES (KE_HAPPENED_BEFORE a) (KE_HAPPENED_BEFORE b) @ e).

  Lemma DERIVED_RULE_happened_before_over_implies_true :
    forall {eo : EventOrdering} e R H a b,
      rule_true (DERIVED_RULE_happened_before_over_implies e R H a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_FORALL_BEFORE (KE_IMPLIES a b) @ e)); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    norm_with "y"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "u" "y"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true "u" e0); simseqs j.
    causal_norm_with "u"; norm_with "x"; apply (PRIMITIVE_RULE_forall_before_elim_true "u" "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { norm_with "y"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (* NOTE: We don't need [KE_FORALL_BEFORE] as in [DERIVED_RULE_happened_before_over_implies] *)
  (***********************************************************)
  Definition DERIVED_RULE_happened_before_over_implies2 u {eo : EventOrdering} e R H a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ▷ e) :: R⟭ H ⊢ KE_IMPLIES a b @ e'])
      (⟬R⟭ H ⊢ KE_IMPLIES (KE_HAPPENED_BEFORE a) (KE_HAPPENED_BEFORE b) @ e).

  Lemma DERIVED_RULE_happened_before_over_implies2_true :
    forall u {eo : EventOrdering} e R H a b,
      rule_true (DERIVED_RULE_happened_before_over_implies2 u e R H a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    norm_with "y"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true u "y"); simseqs j.
    causal_norm_with u; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true u e0); simseqs j.
    inst_hyp e0 st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_IMPLIES a b @ e0)); simseqs j.
    { norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j. }
    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { norm_with "y"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_or {eo : EventOrdering} e R H a b :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_OR a b) @ e]
      (⟬R⟭ H ⊢ KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e).

  Lemma DERIVED_RULE_right_before_over_or_true :
    forall {eo : EventOrdering} e R H a b,
      rule_true (DERIVED_RULE_right_before_over_or e R H a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_OR a b) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unright_before_eq_hyp_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.
    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply DERIVED_RULE_unright_before_eq_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
    apply DERIVED_RULE_unright_before_eq_true; simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_implies_seq x {eo : EventOrdering} e R H J a b :=
    MkRule0
      []
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ (KE_IMPLIES a b) @ e) » J ⊢ KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e).

  Lemma DERIVED_RULE_right_before_over_implies_seq_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_right_before_over_implies_seq x e R H J a b).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_right_before_over_implies_true; simseqs j.
    apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_or_seq x {eo : EventOrdering} e R H J a b :=
    MkRule0
      []
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ (KE_OR a b) @ e) » J ⊢ KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e).

  Lemma DERIVED_RULE_right_before_over_or_seq_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_right_before_over_or_seq x e R H J a b).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_right_before_over_or_true; simseqs j.
    apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_implies_hyp x {eo : EventOrdering} e R H J a b c :=
    MkRule0
      [⟬R⟭ H • (x › KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e) » J ⊢ c]
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ (KE_IMPLIES a b) @ e) » J ⊢ c).

  Lemma DERIVED_RULE_right_before_over_implies_hyp_true :
    forall x {eo : EventOrdering} e R H J a b c,
      rule_true (DERIVED_RULE_right_before_over_implies_hyp x e R H J a b c).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_after_true "z" x (KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e)); simseqs j.
    { apply DERIVED_RULE_right_before_over_implies_seq_true; simseqs j. }
    norm_with x; apply (PRIMITIVE_RULE_thin_true x); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_rename_hyp_true "z" x); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_or_hyp x {eo : EventOrdering} e R H J a b c :=
    MkRule0
      [⟬R⟭ H • (x › KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e) » J ⊢ c]
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ (KE_OR a b) @ e) » J ⊢ c).

  Lemma DERIVED_RULE_right_before_over_or_hyp_true :
    forall x {eo : EventOrdering} e R H J a b c,
      rule_true (DERIVED_RULE_right_before_over_or_hyp x e R H J a b c).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "z" (KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e)); simseqs j.
    { apply DERIVED_RULE_right_before_over_or_seq_true; simseqs j. }
    (* FIX *)
    introv ct ht; apply st0; simpl in *; tcsp.
    introv i; allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; simpl in *; tcsp;
      try (complete (apply ht; allrw hyp_in_add; allrw hyp_in_adds; allrw hyp_in_add; simpl in *; tcsp)).
    unfold hyp_event; simpl.
    pose proof (ht ("z" › KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e)) as ht;
      allrw hyp_in_add; allrw hyp_in_adds; allrw hyp_in_add; simpl in *; tcsp.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_happened_before_eq {eo : EventOrdering} e R H c :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ c) @ e,
       ⟬R⟭ H ⊢ KE_NOT_FIRST @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE c @ e).

  Lemma DERIVED_RULE_right_before_happened_before_eq_true :
    forall {eo : EventOrdering} e R H c,
      rule_true (DERIVED_RULE_right_before_happened_before_eq e R H c).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_local_pred_local_true "u" e); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "z" (KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ c) @ e)); simseqs j.
    { apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
    norm_with "z"; apply (DERIVED_RULE_unright_before_eq_hyp_true "z"); simseqs j.
    norm_with "z"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "v" "z"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_local_if_causal_true "u"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_if_causal_trans_true "u"); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "v"); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_not_first_implies_not_first {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_NOT_FIRST @ e]
      (⟬R⟭ H ⊢ KE_NOT KE_FIRST @ e).

  Lemma DERIVED_RULE_not_first_implies_not_first_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_not_first_implies_not_first e R H).
  Proof.
    start_proving_derived st.
    LOCKintro "x".
    LOCKelim "x"; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_first_implies_not_knew {eo : EventOrdering} e R H c :=
    MkRule0
      [⟬R⟭ H ⊢ KE_FIRST @ e]
      (⟬R⟭ H ⊢ KE_NOT (KE_KNEW c) @ e).

  Lemma DERIVED_RULE_first_implies_not_knew_true :
    forall {eo : EventOrdering} e R H c,
      rule_true (DERIVED_RULE_first_implies_not_knew e R H c).
  Proof.
    start_proving_derived st.
    LOCKcut "y" (KE_FIRST @ e).
    LOCKintro "x".
    LOCKelim "y"; try LOCKauto.
    LOCKapply (DERIVED_RULE_knew_implies_not_first_true c); try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_exists_before_idem {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_LOCAL_BEFORE_EQ a) @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_exists_before_idem_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_exists_before_idem e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE_EQ (KE_LOCAL_BEFORE_EQ a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "v" "x"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causal_trans_true "u"); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_unlocal_before_eq_if_causalle_true "v"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_learned_local_pred_implies {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_LEARNED i) @ e]
      (⟬R⟭ H ⊢ KE_LEARNED i @ e).

  Lemma DERIVED_RULE_learned_local_pred_implies_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_learned_local_pred_implies e R H i).
  Proof.
    introv; apply DERIVED_RULE_exists_before_idem_true.
  Qed.


  (****************************************************************************************)
  Definition DERIVED_RULE_trusted_learned_local_pred_implies {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_TLEARNED t) @ e]
      (⟬R⟭ H ⊢ KE_TLEARNED t @ e).

  Lemma DERIVED_RULE_trusted_learned_local_pred_implies_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_learned_local_pred_implies e R H t).
  Proof.
    introv; apply DERIVED_RULE_exists_before_idem_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owns_change_localle x {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_OWNS a @ e1]
      (⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_OWNS a @ e2).

  Lemma DERIVED_RULE_owns_change_localle_true :
    forall x {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_owns_change_localle x e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_OWNS a @ e1).
    Transparent KE_OWNS.
    LOCKelim "x".
    LOCKintro n.
    Opaque KE_OWNS.
    LOCKelim "x" "y".
    LOCKintro.
    { LOCKapply PRIMITIVE_RULE_at_change_localle_true; try LOCKauto. }
    LOCKapply (PRIMITIVE_RULE_has_owner_change_event_true e2 e1); try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_owns_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_OWNS a) @ e]
      (⟬R⟭ H ⊢ KE_OWNS a @ e).

  Lemma DERIVED_RULE_right_before_owns_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_right_before_owns_implies e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_OWNS a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unright_before_eq_hyp_true "x"); simseqs j.
    apply (DERIVED_RULE_add_local_pred_localle_true "u" e); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_owns_change_localle_true "u"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owns_local_pred_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_OWNS a @ local_pred_n e]
      (⟬R⟭ H ⊢ KE_OWNS a @ e).

  Lemma DERIVED_RULE_owns_local_pred_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_owns_local_pred_implies e R H a).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_right_before_owns_implies_true; simseqs j.
    apply DERIVED_RULE_unright_before_eq_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owned_happened_before_tgens_implies_before {eo : EventOrdering} e R H t :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TOWNED t @ e,
       ⟬R⟭ H ⊢ KE_HAPPENED_BEFORE (KE_TDISS_OWN t) @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE (KE_TDISS_OWN t) @ e).

  Lemma DERIVED_RULE_owned_happened_before_tgens_implies_before_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_owned_happened_before_tgens_implies_before e R H t).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE (KE_TDISS_OWN t) @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "o" (KE_TOWNED t @ e)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    norm_with "o"; apply (DERIVED_RULE_unright_before_eq_hyp_true "o"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "u" "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_owns_implies_local_true "u" (kc_trust2data t)); simseqs j.

    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    { apply DERIVED_RULE_owns_local_pred_implies_true; simseqs j.
      norm_with "o"; apply (PRIMITIVE_RULE_hypothesis_true "o"); simseqs j. }

    causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_if_causal_true "u"); simseqs j.

    apply PRIMITIVE_RULE_and_intro_true; simseqs j.
    { norm_with "c"; apply (PRIMITIVE_RULE_hypothesis_true "c"); simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_knew {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_gen t @ local_pred_n e,
       ⟬R⟭ H ⊢ KE_TKNEW t @ e,
       ⟬R⟭ H ⊢ KE_TOWNED t @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE (KE_TDISS_OWN t) @ e).

  Lemma DERIVED_RULE_trusted_knew_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_knew e R H t).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_TKNOWS t) @ e)); simseqs j.

    apply (PRIMITIVE_RULE_cut_true
             "y"
             (KE_IMPLIES
                (KE_RIGHT_BEFORE_EQ (KE_TKNOWS t))
                (KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ (KE_TDISS_OWN t))) @ e)); simseqs i.

    { apply DERIVED_RULE_right_before_over_implies_true; simseqs i.
      apply DERIVED_RULE_unright_before_eq_true; simseqs i.
      apply DERIVED_RULE_thin_last_true; simseqs i. }

    apply DERIVED_RULE_implies_elim_true; simseqs i.

    { apply DERIVED_RULE_hypothesis_last_true; simseqs i. }

    apply (PRIMITIVE_RULE_cut_true
             "z"
             (KE_HAPPENED_BEFORE (KE_TDISS_OWN t) @ e)); simseqs i.

    { apply DERIVED_RULE_right_before_happened_before_eq_true; simseqs i.

      { apply PRIMITIVE_RULE_thin_but_last_true; simseqs i.
        apply DERIVED_RULE_hypothesis_last_true; simseqs i. }

      { apply DERIVED_RULE_thin_last_true; simseqs i.
        apply DERIVED_RULE_thin_last_true; simseqs i.
        apply (DERIVED_RULE_knew_implies_not_first_true (kc_trust2data t)); simseqs i. } }

    apply DERIVED_RULE_owned_happened_before_tgens_implies_before_true; simseqs i.

    { apply DERIVED_RULE_thin_last_true; simseqs i.
      apply DERIVED_RULE_thin_last_true; simseqs i.
      apply DERIVED_RULE_thin_last_true; simseqs i. }

    apply DERIVED_RULE_hypothesis_last_true; simseqs i.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_pred_eq_induction {eo : EventOrdering} e R H a :=
    MkRule1
      (fun e => [⟬R⟭ H ⊢ KE_IMPLIES KE_FIRST a @ e,
                 ⟬R⟭ H ⊢ KE_IMPLIES KE_NOT_FIRST (KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) a) @ e])
      (⟬R⟭ H ⊢ a @ e).

  Lemma DERIVED_RULE_pred_eq_induction_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_pred_eq_induction e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_pred_induction_true "x"); simseqs j; inst_hyp e0 st;
      apply DERIVED_RULE_remove_first_causal_true; simseqs j; auto;[].
    apply (PRIMITIVE_RULE_cut_true "x" (KE_IMPLIES KE_NOT_FIRST (KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) a) @ e0)); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { apply (DERIVED_RULE_right_before_implies_not_first_true a); simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs i. }
    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs i. }
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_decidable_knew {eo : EventOrdering} e R H a :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_OR (KE_KNEW a) (KE_NOT (KE_KNEW a)) @ e).

  Lemma DERIVED_RULE_decidable_knew_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_decidable_knew e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "or" (KE_OR KE_FIRST KE_NOT_FIRST @ e)); simseqs j.
    { apply PRIMITIVE_RULE_first_dec_true; simseqs j. }
    norm_with "or"; apply PRIMITIVE_RULE_or_elim_true; simseqs j.
    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply DERIVED_RULE_first_implies_not_knew_true; simseqs j.
      norm_with "or"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e); simseqs j.
    { norm_with "or"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "h" (KE_OR (KE_KNOWS a) (KE_NOT (KE_KNOWS a)) @ local_pred_n e)); simseqs j.
    { apply PRIMITIVE_RULE_decidable_knows_true; simseqs j. }
    norm_with "h"; apply PRIMITIVE_RULE_or_elim_true; simseqs j.
    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_unright_before_if_causal_true; simseqs j.
      norm_with "h"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "q"); simseqs j.
    LOCKelim "h"; try LOCKauto.
    norm_with "q"; apply PRIMITIVE_RULE_unright_before_hyp_true; simseqs j.
    norm_with "q"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_local_before_eq_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_LOCAL_BEFORE_EQ a) @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_right_before_local_before_eq_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_right_before_local_before_eq_implies e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_LOCAL_BEFORE_EQ a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unright_before_eq_hyp_true "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    apply DERIVED_RULE_unlocal_before_eq_if_pred_true; simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causalle_true "u"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_happened_before_eq_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ a) @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_right_before_happened_before_eq_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_right_before_happened_before_eq_implies e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unright_before_eq_hyp_true "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "u" "x"); simseqs j.
    apply DERIVED_RULE_unhappened_before_eq_if_pred_true; simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "u"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knowledge_acquired {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_KNOWS i @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_AND (KE_KNOWS i) (KE_NOT (KE_KNEW i))) @ e).

  Lemma DERIVED_RULE_knowledge_acquired_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_knowledge_acquired e R H i).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "k" (KE_KNOWS i @ e)); simseqs j;[].
    clear st0.

    apply DERIVED_RULE_revert_last_true; simseqs j;[].

    apply DERIVED_RULE_pred_eq_induction_true; simseqs j.

    { apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
      apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
      apply DERIVED_RULE_weaken_local_before_eq_true; simseqs j.
      apply PRIMITIVE_RULE_and_intro_true; simseqs j.

      { apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

      apply DERIVED_RULE_thin_last_true; simseqs j.
      apply DERIVED_RULE_first_implies_not_knew_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "z"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true
             "w"
             (KE_IMPLIES
                (KE_RIGHT_BEFORE_EQ (KE_KNOWS i))
                (KE_RIGHT_BEFORE_EQ (KE_LOCAL_BEFORE_EQ (KE_AND (KE_KNOWS i) (KE_NOT (KE_KNEW i))))) @ e0)); simseqs j.

    { norm_with "y".
      apply (DERIVED_RULE_right_before_over_implies_seq_true "y"); simseqs j. }

    norm_with "y".
    apply (PRIMITIVE_RULE_thin_true "y"); simseqs j.

    apply (PRIMITIVE_RULE_cut_true "y" (KE_OR (KE_KNEW i) (KE_NOT (KE_KNEW i)) @ e0)); simseqs j.

    { apply DERIVED_RULE_decidable_knew_true; simseqs j. }

    apply (DERIVED_RULE_or_elim_true "y"); simseqs j.

    { norm_with "w".
      apply (PRIMITIVE_RULE_implies_elim_true "w"); simseqs j.

      { apply DERIVED_RULE_knew_implies_knows_true; simseqs j.
        apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

      apply DERIVED_RULE_right_before_local_before_eq_implies_true; simseqs j.
      norm_with "w".
      apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }

    apply DERIVED_RULE_weaken_local_before_eq_true; simseqs j.
    apply PRIMITIVE_RULE_and_intro_true; simseqs j.

    { norm_with "z".
      apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }

    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_learns_or_knows_implies_learns_or_knows_if_knew {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns i @ local_pred_n e]
      (⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns_if_knew i @ e).

  Lemma DERIVED_RULE_learns_or_knows_implies_learns_or_knows_if_new_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_learns_or_knows_implies_learns_or_knows_if_knew e R H i).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (KE_RIGHT_BEFORE_EQ (KE_KNOWS i) @ e)); simseqs j.

    { apply DERIVED_RULE_knew_implies_knows_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
    norm_with "y"; apply DERIVED_RULE_unright_before_eq_hyp_true; simseqs j.

    apply (PRIMITIVE_RULE_cut_true "z" (KE_RIGHT_BEFORE_EQ (KE_OR (KE_LEARNED i) (KE_OWNS i)) @ e)); simseqs j.
    { apply DERIVED_RULE_unright_before_eq_true; simseqs j.
      norm_with "y"; apply (DERIVED_RULE_revert_true "y"); simseqs j. }

    norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "w" (KE_OR (KE_RIGHT_BEFORE_EQ (KE_LEARNED i)) (KE_RIGHT_BEFORE_EQ (KE_OWNS i)) @ e)); simseqs j.

    { norm_with "z"; apply (DERIVED_RULE_right_before_over_or_seq_true "z"); simseqs j. }

    apply PRIMITIVE_RULE_thin_but_last_true; simseqs j.

    apply (DERIVED_RULE_or_elim_true "w"); simseqs j.

    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply DERIVED_RULE_right_before_local_before_eq_implies_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply DERIVED_RULE_right_before_owns_implies_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_happened_before {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_HAPPENED_BEFORE a) @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_happened_before_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_happened_before e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE_EQ (KE_HAPPENED_BEFORE a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "v" "x"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_localle_if_causalle_true "u"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_if_causalle_trans_eq_true "u"); simseqs j.
    causal_norm_with "v"; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true "v"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_happened_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ a) @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_happened_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_happened_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "v" "x"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_localle_if_causalle_true "u"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true "u"); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "v"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unall_before_correct_trace_before_eq_hyp x {eo : EventOrdering} e R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › KE_LOCAL_FORALL_BEFORE_EQ (KE_CORRECT_TRACE_BEFORE a) @ e) » J ⊢ b]
      (⟬R⟭ H • (x › KE_CORRECT_TRACE_BEFORE a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unall_before_correct_trace_before_eq_hyp_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unall_before_correct_trace_before_eq_hyp x e R H J a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_after_true "x" x (KE_LOCAL_FORALL_BEFORE_EQ (KE_CORRECT_TRACE_BEFORE a) @ e)); simseqs j.
    { apply PRIMITIVE_RULE_and_intro_true; simseqs j.
      { apply PRIMITIVE_RULE_unall_before_correct_trace_before_hyp_true; simseqs j.
        norm_with x; apply (PRIMITIVE_RULE_hypothesis_true x); simseqs j. }
      norm_with x; apply (PRIMITIVE_RULE_hypothesis_true x); simseqs j. }
    norm_with x; apply (PRIMITIVE_RULE_thin_true x); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_rename_hyp_true "x" x); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_happened_before_if_local_eq x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e']
      (⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma DERIVED_RULE_happened_before_if_local_eq_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_happened_before_if_local_eq x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE a @ e')); simseqs j.
    apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    apply DERIVED_RULE_unhappened_before_if_causalle_trans_eq_true; simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_happened_before_eq_if_local_eq x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_happened_before_eq_if_local_eq_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_happened_before_eq_if_local_eq x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE_EQ a @ e')); simseqs j.
    apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    apply DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true; simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_learns_if_knows_implies_learned_if_knows {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule1
      (fun e => [⟬R⟭ H ⊢ ASSUMPTION_learns_if_knows i @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_learned_if_knows i @ e).

  Lemma DERIVED_RULE_learns_if_knows_implies_learned_if_knows_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_learns_if_knows_implies_learned_if_knows e R H i).
  Proof.
    introv st; simpl in *.
    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "z" (ASSUMPTION_learns_if_knows i @ e0)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j.
      apply DERIVED_RULE_thin_last_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      inst_hyp e0 st. }

    norm_with "z"; apply (PRIMITIVE_RULE_implies_elim_true "z"); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "z"; apply (PRIMITIVE_RULE_implies_elim_true "z"); simseqs j.
    { causal_norm_with "u"; apply (PRIMITIVE_RULE_correct_trace_before_if_causal_true "u"); simseqs j.
      norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

    norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "v" "z"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_happened_before_if_local_eq_true "u"); simseqs j.
    causal_norm_with "v"; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true "v"); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_knowledge_acquired {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TKNOWS t @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_AND (KE_TKNOWS t) (KE_NOT (KE_TKNEW t))) @ e).

  Lemma DERIVED_RULE_trusted_knowledge_acquired_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_knowledge_acquired e R H t).
  Proof.
    introv exe h; simpl in *.
    apply DERIVED_RULE_knowledge_acquired_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_knows_implies_correct (t : kc_trust) {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TKNOWS t @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_CORRECT_TRACE_BEFORE @ e).

  Lemma DERIVED_RULE_trusted_knows_implies_correct_true :
    forall (t : kc_trust) {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_trusted_knows_implies_correct t e R H).
  Proof.
    introv; apply PRIMITIVE_RULE_knows_implies_correct_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_happened_before_implies_happened_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_HAPPENED_BEFORE a @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_happened_before_implies_happened_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_happened_before_implies_happened_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE a @ e)); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "u" "x"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_causal_if_causalle_true "u"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "u"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_weaken_happened_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_weaken_happened_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_weaken_happened_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_happenedle_refl_true "u" e); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "u"); simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (****************************************************************)
  Definition DERIVED_RULE_knows_propagates {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [
        ⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns i @ e,
        ⟬R⟭ H ⊢ KE_LOCAL_FORALL_BEFORE_EQ (ASSUMPTION_learns_if_knows i) @ e,
        ⟬R⟭ H ⊢ KE_KNOWS i @ e,
        ⟬R⟭ H ⊢ KE_CORRECT_TRACE_BEFORE (kc_data2owner i) @ e
      ]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ (KE_AND (KE_KNOWS i) (KE_OWNS i)) @ e).

  Lemma DERIVED_RULE_knows_propagates_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_knows_propagates e R H i).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    dLin_hyp st.

    apply (PRIMITIVE_RULE_cut_true "k" (KE_KNOWS i @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (ASSUMPTION_learns_or_owns i @ e)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    apply DERIVED_RULE_implies_elim_true; simseqs j.
    { apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
    apply (DERIVED_RULE_or_elim_true "y"); simseqs j.

    { norm_with "y"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "y"); simseqs j.
      apply (PRIMITIVE_RULE_cut_true "z" (KE_LOCAL_FORALL_BEFORE_EQ (ASSUMPTION_learns_if_knows i) @ e)); simseqs j.
      { apply DERIVED_RULE_thin_last_true; simseqs j.
        apply DERIVED_RULE_thin_last_true; simseqs j.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
      norm_with "z"; causal_norm_with "u"; apply (DERIVED_RULE_unlocal_forall_before_eq_hyp_true "u" "z"); simseqs j.
      norm_with "z"; apply (PRIMITIVE_RULE_implies_elim_true "z"); simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      norm_with "z"; apply (PRIMITIVE_RULE_implies_elim_true "z"); simseqs j.
      { apply (PRIMITIVE_RULE_cut_true "z" (KE_CORRECT_TRACE_BEFORE (kc_data2owner i) @ e)); simseqs j.
        { apply DERIVED_RULE_thin_last_true; simseqs j.
          apply DERIVED_RULE_thin_last_true; simseqs j.
          apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
        causal_norm_with "u"; apply (PRIMITIVE_RULE_correct_trace_before_if_causal_true "u"); simseqs j.
        norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
      causal_norm_with "u"; apply (DERIVED_RULE_happened_before_eq_if_local_eq_true "u"); simseqs j.
      apply DERIVED_RULE_happened_before_implies_happened_before_eq_true; simseqs j.
      norm_with "z"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "v" "z"); simseqs j.
      causal_norm_with "v"; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true "v"); simseqs j.
      norm_with "z"; apply (PRIMITIVE_RULE_and_elim_true "z" "w"); simseqs j.
      apply PRIMITIVE_RULE_and_intro_true; simseqs j.
      { norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
      norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }

    apply DERIVED_RULE_weaken_happened_before_eq_true; simseqs j.
    apply PRIMITIVE_RULE_and_intro_true; simseqs j.
    { norm_with "k"; apply (PRIMITIVE_RULE_hypothesis_true "k"); simseqs j. }
    norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_learns_or_knows_implies_learns_or_knows_if_knew {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_or_owns t @ local_pred_n e]
      (⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_or_owns_if_knew t @ e).

  Lemma DERIVED_RULE_trusted_learns_or_knows_implies_learns_or_knows_if_knew_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_learns_or_knows_implies_learns_or_knows_if_knew e R H t).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    dLin_hyp st.

    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (KE_RIGHT_BEFORE_EQ (KE_TKNOWS t) @ e)); simseqs j.

    { apply DERIVED_RULE_knew_implies_knows_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
    norm_with "y"; apply (DERIVED_RULE_unright_before_eq_hyp_true "y"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "z" (KE_OR (KE_TLEARNED t) (KE_TOWNS t) @ local_pred_n e)); simseqs j.
    { apply (PRIMITIVE_RULE_cut_true "w" (ASSUMPTION_trusted_learns_or_owns t @ local_pred_n e)); simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j. }
      norm_with "w"; apply (PRIMITIVE_RULE_implies_elim_true "w"); simseqs j.
      { apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    apply (DERIVED_RULE_or_elim_true "z"); simseqs j.

    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      norm_with "z"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "z"); simseqs j.
      apply DERIVED_RULE_unlocal_before_eq_if_pred_true; simseqs j.
      causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causalle_true "u"); simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
    apply DERIVED_RULE_owns_local_pred_implies_true; simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.



(*  (* NOT USED *)
  (****************************************************************)
  Definition OLD_RULE_TGEN_MONOTONICITY_local_trusted_component {eo : EventOrdering} e R H t1 t2 c1 c2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ KE_TGENS t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_TGENS t1) @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e])
      (⟬R⟭ H ⊢ KE_ID_LE c1 c2 @ e).

  Lemma OLD_RULE_TGEN_MONOTONICITY_local_trusted_component_true :
    forall {eo : EventOrdering} e R H t1 t2 c1 c2,
      rule_true (OLD_RULE_TGEN_MONOTONICITY_local_trusted_component e R H t1 t2 c1 c2).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (st (mk_v1 e)) as st'; simpl_sem_rule; dLin_hyp st'.
    unfold sequent_true in *; simpl in *.
    clear st'0.
    repeat (autodimp st'1 hyp); tcsp.
    repeat (autodimp st'2 hyp); tcsp.
    repeat (autodimp st'3 hyp); tcsp.
    repeat (autodimp st'4 hyp); tcsp.
    exrepnd.
    allrw interpret_tgens.
    unfold seq_event in *; simpl in *.

    assert (monotonicity eo) as mon.
    { introv exe.
      pose proof (st (mk_v1 (MkEventN e0 exe))) as st; simpl_sem_rule; dLin_hyp st; simpl in *.
      clear st1 st2.
      repeat (autodimp st0 hyp); tcsp.
      allrw interpret_no_tgens; allrw interpret_exists_tgens; tcsp. }

    assert (c1 ⋘ c2) as q; try omega; subst; tcsp.
    eapply generates_trusted_kc_id_increases; eauto; tcsp; eauto 3 with kn.
  Qed.*)


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition OLD_RULE_trusted_learns_or_gens {eo : EventOrdering} e R H (t : kc_trust):=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_or_owns t @ e,
       ⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_gen t @ e,
       ⟬R⟭ H ⊢ KE_TKNOWS t @ e]
      (⟬R⟭ H ⊢ KE_OR
           (KE_TLEARNED t)
           (KE_LOCAL_BEFORE_EQ (KE_DISS_OWN t)) @ e).

  Lemma OLD_RULE_trusted_learns_or_gens_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (OLD_RULE_trusted_learns_or_gens e R H t).
  Proof.
    start_proving_primitive st ct ht.
    unfold sequent_true in *; simpl in *.
    repeat (autodimp st0 hyp); tcsp.
    repeat (autodimp st1 hyp); tcsp.
    repeat (autodimp st2 hyp); tcsp.
    unfold seq_event in *; simpl in *.

    destruct st0 as [LER|OWN].

    { (* learned *)
      clear st1.
      exrepnd.
      left.
      exists e'; dands; eauto.
    }

    {
      (* owned *)
      allrw interp_towns.
      exrepnd.
      right; exists e'; dands; auto.
      allrw interpret_tgens.
      applydup generates_trusted_implies_data_is_owned in st0.
      assert (loc e' = loc e) as eqloc; eauto 3 with kn eo.
    }
  Qed.*)


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition OLD_RULE_learns_or_gens {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns i @ e,
       ⟬R⟭ H ⊢ ASSUMPTION_knows_and_owns i @ e,
       ⟬R⟭ H ⊢ KE_KNOWS i @ e]
      (⟬R⟭ H ⊢ KE_OR
           (KE_LEARNED i)
           (KE_LOCAL_BEFORE_EQ (KE_GENS i)) @ e).

  Lemma OLD_RULE_learns_or_gens_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (OLD_RULE_learns_or_gens e R H i).
  Proof.
    start_proving_primitive st ct ht.
    unfold sequent_true in *; simpl in *.
    repeat (autodimp st0 hyp); tcsp.
    autodimp st1 hyp; tcsp.
    autodimp st1 hyp; tcsp.
    repeat (autodimp st2 hyp); tcsp.
    unfold seq_event in *; simpl in *.

    destruct st0 as [LER|OWN].

    { (* learned *)
      exrepnd.
      left.
      exists e'; dands; eauto.
    }

    {
      (* owned *)
      autodimp st1 hyp; eauto 3 with kn.
    }
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_it_owns_owned_implies_at d {eo : EventOrdering} e p R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_OWNS d @ e,
       ⟬R⟭ H ⊢ KE_HAS_OWNER d p @ e]
      (⟬R⟭ H ⊢ KE_AT p @ e).

  Lemma DERIVED_RULE_it_owns_owned_implies_at_true :
    forall d {eo : EventOrdering} e p R H,
      rule_true (DERIVED_RULE_it_owns_owned_implies_at d e p R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_OWNS d @ e)); simseqs j.
    Transparent KE_OWNS.
    norm_with "x"; apply (PRIMITIVE_RULE_exists_node_elim_true "x"); simseqs j.
    Opaque KE_OWNS.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "z" (KE_HAS_OWNER d p @ e)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    apply (PRIMITIVE_RULE_cut_true "w" (KE_NODE_EQ n p @ e)); simseqs j.
    { apply (PRIMITIVE_RULE_has_owner_implies_eq_true d); simseqs j.
      { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
    apply (PRIMITIVE_RULE_subst_node_in_at_true n); simseqs j.
    { norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
    norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knows_and_not_owns_implies_learns {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns i @ e,
       ⟬R⟭ H ⊢ KE_KNOWS i @ e,
       ⟬R⟭ H ⊢ KE_NOT (KE_OWNS i) @ e]
      (⟬R⟭ H ⊢ KE_LEARNED i @ e).

  Lemma DERIVED_RULE_knows_and_not_owns_implies_learns_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_knows_and_not_owns_implies_learns e R H i).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_learns_or_owns i @ e)); simseqs j.
    norm_with "ass"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j.
    norm_with "ass"; apply PRIMITIVE_RULE_or_elim_true; simseqs j.
    { norm_with "ass"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "not" (KE_NOT (KE_OWNS i) @ e)); simseqs j.
    { norm_with "ass"; apply PRIMITIVE_RULE_thin_true; simseqs j. }
    LOCKelim "not"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knows_and_not_owns_implies_learns2
             p a {eo : EventOrdering} e R H d :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns d @ e,
       ⟬R⟭ H ⊢ KE_KNOWS d        @ e,
       ⟬R⟭ H ⊢ KE_HAS_OWNER d p  @ e,
       ⟬R⟭ H ⊢ KE_AT a           @ e,
       ⟬R⟭ H ⊢ KE_NOT (KE_NODE_EQ p a) @ e]
      (⟬R⟭ H ⊢ KE_LEARNED d       @ e).

  Lemma DERIVED_RULE_knows_and_not_owns_implies_learns2_true :
    forall p a {eo : EventOrdering} (e : EventN) R H (d : kc_data),
      rule_true (DERIVED_RULE_knows_and_not_owns_implies_learns2 p a e R H d).
  Proof.
    start_proving_derived st.

    apply DERIVED_RULE_knows_and_not_owns_implies_learns_true; simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "own"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "ho" (KE_AT p @ e)); simseqs j.
    { apply (DERIVED_RULE_it_owns_owned_implies_at_true d); simseqs j.
      { norm_with "own"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
      norm_with "own"; apply PRIMITIVE_RULE_thin_true; simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "d" (KE_NOT (KE_NODE_EQ p a) @ e)); simseqs j.
    { norm_with "own"; apply PRIMITIVE_RULE_thin_true; simseqs j.
      norm_with "ho"; apply PRIMITIVE_RULE_thin_true; simseqs j. }

    norm_with "d"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j.

    { apply PRIMITIVE_RULE_at_implies_same_node_true; simseqs j.
      { norm_with "own"; apply PRIMITIVE_RULE_thin_true; simseqs j.
        norm_with "ho"; apply PRIMITIVE_RULE_thin_true; simseqs j. }
      norm_with "ho"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    norm_with "d"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_knows_and_not_owns_implies_learns {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_or_owns t @ e,
       ⟬R⟭ H ⊢ KE_TKNOWS t @ e,
       ⟬R⟭ H ⊢ KE_NOT (KE_TOWNS t) @ e]
      (⟬R⟭ H ⊢ KE_TLEARNED t @ e).

  Lemma DERIVED_RULE_trusted_knows_and_not_owns_implies_learns_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_knows_and_not_owns_implies_learns e R H t).
  Proof.
    start_proving_derived st; apply DERIVED_RULE_knows_and_not_owns_implies_learns_true; simseqs j.
  Qed.



  (***************************************************************************)
  Definition DERIVED_RULE_implies_learned_if_gen
             {eo : EventOrdering} e d R H :=
    MkRule1
      (fun e' => [⟬R⟭ H ⊢ ASSUMPTION_learns_if_gen d @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_learned_if_gen d @ e).

  Lemma DERIVED_RULE_implies_learned_if_gen_true :
    forall {eo : EventOrdering} (e : EventN) d R H,
      rule_true (DERIVED_RULE_implies_learned_if_gen e d R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (ASSUMPTION_learns_if_gen d @ e0)); simseqs j.
    { inst_hyp e0 h.
      norm_with "x"; apply PRIMITIVE_RULE_thin_true; simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_remove_causal_true; simseqs j. }
    norm_with "y"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j.
    { norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    causal_norm_with "u"; apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    causal_norm_with "u"; apply DERIVED_RULE_unhappened_before_if_causalle_trans_eq_true; simseqs j.
    norm_with "y"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition OLD_RULE_trusted_learned_implies_generates_and_owns {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_if_gen t @ e',
          ⟬R⟭ H ⊢ KE_TLEARNED t @ e])
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE
           (KE_AND
              (KE_TGENS t)
              (KE_TOWNS t)) @ e).

  Lemma OLD_RULE_trusted_learned_implies_generates_trusted_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (OLD_RULE_trusted_learned_implies_generates_and_owns e R H t).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (st (mk_v1 e)) as st'; simpl_sem_rule; dLin_hyp st'; simpl in *.
    clear st'0.
    unfold sequent_true in *; simpl in *.
    repeat (autodimp st'1 hyp); tcsp.
    unfold seq_event in *; simpl in *.
    exrepnd.

    assert (ex_node_e e') as exe by eauto 3 with kn.
    pose proof (st (mk_v1 (MkEventN e' exe))) as st; simpl_sem_rule; dLin_hyp st; simpl in *.
    clear st1.

    repeat (autodimp st0 hyp); exrepnd.
    exists e'0; dands; eauto 3 with eo; eauto.
    allrw interp_towns.
    allrw interpret_tgens; eauto 3 with kn.
  Qed.*)


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition OLD_RULE_learned_implies_generates {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_learned_if_knows i @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_knows_and_owns i @ e',
          ⟬R⟭ H ⊢ KE_LEARNED i @ e,
          ⟬R⟭ H ⊢ KE_CORRECT_TRACE_BEFORE (kc_data2name i) @ e])
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE (KE_GENS i) @ e).

  Lemma OLD_RULE_learned_implies_generated_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (OLD_RULE_learned_implies_generates e R H i).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (st (mk_v1 e)) as st'; simpl_sem_rule; dLin_hyp st'; simpl in *.
    unfold sequent_true in *; simpl in *.
    clear st'1.
    repeat (autodimp st'0 hyp); tcsp.
    repeat (autodimp st'2 hyp); tcsp.
    repeat (autodimp st'3 hyp); tcsp.
    unfold seq_event in *; simpl in *.
    exrepnd.

    pose proof (st (mk_v1 (MkEventN e'0 st'0))) as st; simpl_sem_rule; dLin_hyp st; simpl in *.
    clear st0 st2 st3.
    repeat (autodimp st1 hyp); tcsp; eauto 3 with kn;[].
    exrepnd.

    exists e'1; dands; eauto 3 with kn eo.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_local_before_implies_not_first u x {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 □ e2) :: R⟭ H • (x › KE_NOT_FIRST @ e2) ⊢ a]
      (⟬Q ++ (u ⋈ e1 □ e2) :: R⟭ H ⊢ a).

  Lemma DERIVED_RULE_local_before_implies_not_first_true :
    forall u x {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_local_before_implies_not_first u x e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut x (KE_NOT_FIRST @ e2).
    LOCKapply DERIVED_RULE_not_first_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_after_is_id_before u {eo : EventOrdering} e1 e2 c Q R H :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_AFTER c @ e1]
      (⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_BEFORE c @ e2).

  Lemma DERIVED_RULE_id_after_is_id_before_true :
    forall u {eo : EventOrdering} e1 e2 c Q R H,
      rule_true (DERIVED_RULE_id_after_is_id_before u e1 e2 c Q R H).
  Proof.
    start_proving_derived st.
    LOCKintro 0.
    LOCKapply@ u PRIMITIVE_RULE_unright_before_if_causal_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_ids_before_imply_eq_ids {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_BEFORE c1 @ e,
       ⟬R⟭ H ⊢ KE_ID_BEFORE c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e).

  Lemma DERIVED_RULE_ids_before_imply_eq_ids_true :
    forall {eo : EventOrdering} e c1 c2 R H,
      rule_true (DERIVED_RULE_ids_before_imply_eq_ids e c1 c2 R H).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_ID_BEFORE c1 @ e).
    LOCKcut "q" (KE_ID_BEFORE c2 @ e).
    { LOCKclear "h". }
    LOCKelim "h"; LOCKelim "q".
    { LOCKapply@ "h" PRIMITIVE_RULE_unright_before_hyp_true.
      LOCKapply@ "q" PRIMITIVE_RULE_unright_before_hyp_true.
      LOCKapply (PRIMITIVE_RULE_id_eq_change_event_true e (local_pred_n e)).
      LOCKapply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; try LOCKauto. }
    { LOCKelim "q" "x".
      LOCKelim "x"; try LOCKauto.
      LOCKapply (DERIVED_RULE_right_before_implies_not_first_true (KE_ID_AFTER c1)); try LOCKauto. }
    { LOCKelim "h" "x".
      LOCKelim "x"; try LOCKauto.
      LOCKapply (DERIVED_RULE_right_before_implies_not_first_true (KE_ID_AFTER c2)); try LOCKauto. }
    { LOCKelim "h" "x".
      LOCKelim "h" "y".
      LOCKelim "q" "a".
      LOCKelim "q" "b".
      LOCKapply PRIMITIVE_RULE_has_init_id_unique_true; try LOCKauto. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_elim u x {eo : EventOrdering} e e' Q R H J a b :=
    MkRule0
      [⟬Q ++ (u ⋈ e' ⋄ e) :: R⟭ H • (x › a @ e') » J ⊢ b]
      (⟬Q ++ (u ⋈ e' ⋄ e) :: R⟭ H • (x › KE_RIGHT_BEFORE a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_right_before_elim_true :
    forall u x {eo : EventOrdering} e e' Q R H J a b,
      rule_true (DERIVED_RULE_right_before_elim u x e e' Q R H J a b).
  Proof.
    start_proving_derived st.
    LOCKapply@ x PRIMITIVE_RULE_unright_before_hyp_true.
    LOCKapply@ u (PRIMITIVE_RULE_duplicate_guard_true u "u").
    LOCKapply@ "u" PRIMITIVE_RULE_weaken_direct_pred_to_local_pred_true.
    LOCKapply@ "u" PRIMITIVE_RULE_causal_eq_sym_true.
    LOCKapply@ "u" x PRIMITIVE_RULE_subst_causal_eq_hyp_true.
    LOCKclear "u".
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_move_to_concl x {eo : EventOrdering} e b c R H J :=
    MkRule0
      [⟬R⟭ H » J ⊢ KE_IMPLIES b c @ e]
      (⟬R⟭ H • (x › b @ e) » J ⊢ c @ e).

  Lemma DERIVED_RULE_move_to_concl_true :
    forall x {eo : EventOrdering} e b c R H J,
      rule_true (DERIVED_RULE_move_to_concl x e b c R H J).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_IMPLIES b c @ e).
    { LOCKclear x. }
    LOCKelim "h"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_before_is_id_after u {eo : EventOrdering} e1 e2 c Q R H :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_BEFORE c @ e2]
      (⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_AFTER c @ e1).

  Lemma DERIVED_RULE_id_before_is_id_after_true :
    forall u {eo : EventOrdering} e1 e2 c Q R H,
      rule_true (DERIVED_RULE_id_before_is_id_after u e1 e2 c Q R H).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_ID_BEFORE c @ e2).
    LOCKelim "h".
    { LOCKapply@ u "h" DERIVED_RULE_right_before_elim_true; LOCKauto. }
    LOCKelim "h" "x".
    LOCKelim "h" "y".
    LOCKelim "x"; try LOCKauto.
    LOCKapply PRIMITIVE_RULE_direct_pred_if_local_pred_true.
    LOCKapply DERIVED_RULE_not_first_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_causalle_is_equal_if_first u {eo : EventOrdering} e1 e2 R H a :=
    MkRule0
      [⟬ (u ⋈ e1 ■ e2) :: R ⟭ H ⊢ KE_FIRST @ e2,
       ⟬ (u ⋈ e1 ≡ e2) :: R ⟭ H ⊢ a]
      (⟬ (u ⋈ e1 ■ e2) :: R ⟭ H ⊢ a).

  Lemma DERIVED_RULE_causalle_is_equal_if_first_true :
    forall u {eo : EventOrdering} e1 e2 R H a,
      rule_true (DERIVED_RULE_causalle_is_equal_if_first u e1 e2 R H a).
  Proof.
    start_proving_derived st.
    LOCKcut "w" (KE_FIRST @ e2).
    LOCKapply@ u PRIMITIVE_RULE_split_local_before_eq2_true.
    { LOCKclear "w". }
    LOCKelim "w"; try LOCKauto.
    LOCKapply@ u DERIVED_RULE_not_first_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_split_local_before_eq u {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ≡ e2) :: R⟭ H ⊢ a,
       ⟬Q ++ (u ⋈ e1 ■ local_pred_n e2) :: R⟭ H ⊢ a]
      (⟬Q ++ (u ⋈ e1 ■ e2) :: R⟭ H ⊢ a).

  Lemma DERIVED_RULE_split_local_before_eq_true :
    forall u {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_split_local_before_eq u e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    apply PRIMITIVE_RULE_split_local_before_eq2_true; simseqs j.
    apply (PRIMITIVE_RULE_split_local_before2_true u "v" "w"); simseqs j.
    causal_norm_with "w"; apply PRIMITIVE_RULE_remove_causal_true; simseqs j.
    causal_norm_with u; apply PRIMITIVE_RULE_remove_causal_true; simseqs j.
    apply (PRIMITIVE_RULE_rename_causal_true u); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_relocal_before_eq_hyp u x {eo : EventOrdering} e e' R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › KE_LOCAL_BEFORE_EQ a @ e) » J ⊢ b]
      (⟬(u ⋈ e' ■ e) :: R⟭ H • (x › a @ e') » J ⊢ b).

  Lemma DERIVED_RULE_relocal_before_eq_hyp_true :
    forall u x {eo : EventOrdering} e e' R H J a b,
      rule_true (DERIVED_RULE_relocal_before_eq_hyp u x e e' R H J a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_after_true "z" x (KE_LOCAL_BEFORE_EQ a @ e)); simseqs j.
    { causal_norm_with u; apply DERIVED_RULE_unlocal_before_eq_if_causalle_true; simseqs j.
      norm_with x; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    norm_with x; apply (PRIMITIVE_RULE_thin_true x); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_rename_hyp_true "z" x); simseqs j.
    causal_norm_with u; apply PRIMITIVE_RULE_remove_causal_true; simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_le_trans c {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_LE c1 c @ e,
       ⟬R⟭ H ⊢ KE_ID_LE c c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_LE c1 c2 @ e).

  Lemma DERIVED_RULE_id_le_trans_true :
    forall c {eo : EventOrdering} e c1 c2 R H,
      rule_true (DERIVED_RULE_id_le_trans c e c1 c2 R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_ID_LE c1 c @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (KE_ID_LE c c2 @ e)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.

    { norm_with "y"; apply (PRIMITIVE_RULE_or_elim_true "y"); simseqs j.

      { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
        apply (PRIMITIVE_RULE_id_lt_trans_lt_lt_true c); simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

      { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
        apply (PRIMITIVE_RULE_id_lt_trans_lt_eq_true c); simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. } }

    { norm_with "y"; apply (PRIMITIVE_RULE_or_elim_true "y"); simseqs j.

      { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
        apply (PRIMITIVE_RULE_id_lt_trans_eq_lt_true c); simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

      { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
        apply (PRIMITIVE_RULE_id_eq_trans_true c); simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. } }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_le_change_event {eo : EventOrdering} e1 e2 c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_LE c1 c2 @ e2]
      (⟬R⟭ H ⊢ KE_ID_LE c1 c2 @ e1).

  Lemma DERIVED_RULE_id_le_change_event_true :
    forall {eo : EventOrdering} e1 e2 c1 c2 R H,
      rule_true (DERIVED_RULE_id_le_change_event e1 e2 c1 c2 R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_ID_LE c1 c2 @ e2)); simseqs j.

    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.

    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply (PRIMITIVE_RULE_id_lt_change_event_true _ e2); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply (PRIMITIVE_RULE_id_eq_change_event_true _ e2); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
  Qed.

End CalculusSM_derived0.
