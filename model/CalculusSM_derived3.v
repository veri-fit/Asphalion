Require Export CalculusSM_tacs.


Section CalculusSM_derived3.

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

  Local Open Scope kn.


  (***********************************************************)
  Definition DERIVED_RULE_local_before_implies_not_first a {eo : EventOrdering} e R H :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_IMPLIES (KE_LOCAL_BEFORE a) KE_NOT_FIRST @ e).

  Lemma DERIVED_RULE_local_before_implies_not_first_true :
    forall a {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_local_before_implies_not_first a e R H).
  Proof.
    start_proving_derived st.
    LOCKintro "x".
    LOCKapply@ "x" (PRIMITIVE_RULE_unlocal_before_hyp_true "u" "x").
    LOCKapply@ "u" PRIMITIVE_RULE_not_first_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_twice_local_before_implies_once {eo : EventOrdering} e R H a :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_IMPLIES (KE_LOCAL_BEFORE (KE_LOCAL_BEFORE a)) (KE_LOCAL_BEFORE a) @ e).

  Lemma DERIVED_RULE_twice_local_before_implies_once_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_twice_local_before_implies_once e R H a).
  Proof.
    start_proving_derived st.
    LOCKintro "x".
    LOCKapply@ "x" (PRIMITIVE_RULE_unlocal_before_hyp_true "u").
    LOCKapply@ "x" (PRIMITIVE_RULE_unlocal_before_hyp_true "v").
    LOCKapply@ "u" PRIMITIVE_RULE_unlocal_before_if_causal_local_true.
    LOCKapply@ "v" PRIMITIVE_RULE_unlocal_before_if_causal_true; LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_at_pred_implies_local_before_eq x {eo : EventOrdering} e R H J a :=
    MkRule0
      []
      (⟬R⟭ H • (x › a @ local_pred_n e) » J ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_at_pred_implies_local_before_eq_true :
    forall x {eo : EventOrdering} e R H J a,
      rule_true (DERIVED_RULE_at_pred_implies_local_before_eq x e R H J a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_cut_after_true "o" x (KE_OR KE_FIRST KE_NOT_FIRST @ e)).
    { LOCKapply PRIMITIVE_RULE_first_dec_true. }

    LOCKelim "o".
    { LOCKintro 1.
      LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_eq_true "u" e); try LOCKauto.
      LOCKapply@ x "u" PRIMITIVE_RULE_subst_causal_eq_hyp_true; try LOCKauto. }

    LOCKintro 0.
    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e); try LOCKauto.
    LOCKapply@ "u" PRIMITIVE_RULE_direct_pred_if_local_pred_true.
    LOCKapply@ "u" PRIMITIVE_RULE_unlocal_before_if_causal_true; try LOCKauto.
  Qed.

End CalculusSM_derived3.
