Require Export CalculusSM.
Require Export CalculusSM_tacs.


Section CalculusSM3.

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
  Context { iot : @IOTrusted }.
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


  (*  ****** PRIMITIVE RULES ****** *)


  (***********************************************************)
  Definition PRIMITIVE_RULE_beforele_if_eq x {eo : EventOrdering} e1 e2 Q R H a :=
    MkRule0
      [⟬Q ++ (x ⋈ e1 ▶ e2) :: R⟭ H ⊢ a]
      (⟬Q ++ (x ⋈ e1 ≡ e2) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_beforele_if_eq_true :
    forall x {eo : EventOrdering} e1 e2 Q R H a,
      rule_true (PRIMITIVE_RULE_beforele_if_eq x e1 e2 Q R H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; simpl in *; tcsp.
    pose proof (ct (x ⋈ e1 ≡ e2)) as w.
    rewrite in_app_iff in w; simpl in w; autodimp w hyp; subst.
    introv i; apply in_app_iff in i; simpl in *; repndors; subst; simpl in *; tcsp; eauto 3 with eo;
      try (complete (apply ct; apply in_app_iff; simpl; tcsp)).
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_forall_before_intro u {eo : EventOrdering} e R H t :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ▷ e) :: R⟭ H ⊢ t @ e'])
      (⟬R⟭ H ⊢ KE_FORALL_BEFORE t @ e).

  Lemma PRIMITIVE_RULE_forall_before_intro_true :
    forall u {eo : EventOrdering} e R H t,
      rule_true (PRIMITIVE_RULE_forall_before_intro u e R H t).
  Proof.
    start_proving_primitive st ct ht.
    introv lte; unfold seq_event in *; simpl in *.
    inst_hyp e' st'.
    apply st'; simpl; tcsp.
    introv h; repndors; subst; simpl in *; auto.
  Qed.

End CalculusSM3.
