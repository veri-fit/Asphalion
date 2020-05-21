Require Export CalculusSM2.
Require Export CalculusSM3.
Require Export CalculusSM_tacs.


Section CalculusSM4.

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



  (************************************************************************************************)
  Definition ASSUMPTION_knowledge_preserved_step : KExpression :=
    KE_ALL_DATA
      (fun d =>
         KE_IMPLIES
           KE_CORRECT
           (KE_IMPLIES
              (KE_RIGHT_BEFORE (KE_KNOWS d))
              (KE_KNOWS d))).

  Definition ASSUMPTION_knowledge_preserved_local_before : KExpression :=
    KE_ALL_DATA
      (fun d =>
         KE_IMPLIES
           KE_LOCAL_CORRECT_TRACE_BEFORE
           (KE_IMPLIES
              (KE_LOCAL_BEFORE (KE_KNOWS d))
              (KE_KNOWS d))).

  Definition ASSUMPTION_disseminate_new : KExpression :=
    KE_ALL_DATA
      (fun d =>
         KE_IMPLIES
           (KE_AND (KE_DISS d) KE_NODE)
           (KE_KNOWS d)).

  Definition ASSUMPTION_knows_unique : KExpression :=
    KE_ALL_DATA2
      (fun d1 d2 =>
         KE_IMPLIES
           (KE_AND3
              (KE_KNOWS d1)
              (KE_KNOWS d2)
              (KE_SIMILAR_DATA d1 d2))
           (KE_DATA_EQ d1 d2)).

  (****************************************************************)
  Definition DERIVED_RULE_local_correct_trace_before_implies_correct {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_CORRECT_TRACE_BEFORE @ e]
      (⟬R⟭ H ⊢ KE_CORRECT @ e).

  Lemma DERIVED_RULE_local_correct_trace_before_implies_correct_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_local_correct_trace_before_implies_correct e R H).
  Proof.
    start_proving_derived st.
    LOCKcut "cor" (KE_LOCAL_CORRECT_TRACE_BEFORE @ e).
    LOCKelim "cor" "cor'"; try LOCKauto.
  Qed.

  (***********************************************************)
  Definition DERIVED_RULE_correct_trace_before_if_right_before u {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (u ⋈ e' ⋄ e) :: Q⟭ H ⊢ KE_CORRECT_TRACE_BEFORE a @ e]
      (⟬R ++ (u ⋈ e' ⋄ e) :: Q⟭ H ⊢ KE_CORRECT_TRACE_BEFORE a @ e').

  Lemma DERIVED_RULE_correct_trace_before_if_right_before_true :
    forall u {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_correct_trace_before_if_right_before u e' e R Q H a).
  Proof.
    start_proving_derived st.
    LOCKapply@ u (PRIMITIVE_RULE_duplicate_guard_true u "v").
    LOCKapply@ "v" PRIMITIVE_RULE_direct_pred_if_local_pred_true.
    LOCKapply@ "v" PRIMITIVE_RULE_local_if_localle_true.
    LOCKapply@ "v" PRIMITIVE_RULE_correct_trace_before_if_causal_true.
    LOCKclear "v".
  Qed.

  (************************************************************************************************)
  Definition DERIVED_RULE_implies_knowledge_preserves_local_before
             {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_knowledge_preserved_step @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_knowledge_preserved_local_before @ e).

  Lemma DERIVED_RULE_implies_knowledge_preserves_local_before_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_implies_knowledge_preserves_local_before e R H).
  Proof.
    start_proving_derived st.

    LOCKintro.
    LOCKapply (PRIMITIVE_RULE_pred_induction_true "v").

    { LOCKintro "fst".
      LOCKintro "cor".
      LOCKintro "kn".
      LOCKapply@ "kn" (DERIVED_RULE_unlocal_before_hyp_true "u").

      LOCKcut "nf" (KE_NOT_FIRST @ e0).
      { LOCKapply@ "u" DERIVED_RULE_not_first_true. }
      LOCKcut "nf'" (KE_NOT KE_FIRST @ e0).
      { LOCKapply DERIVED_RULE_not_first_implies_not_first_true; LOCKauto. }
      LOCKelim "nf'"; try LOCKauto. }

    LOCKintro "ind".
    LOCKintro "cor".
    LOCKintro "bef".

    LOCKapply@ "bef" (DERIVED_RULE_unlocal_before_hyp_true "u").
    LOCKapply@ "bef" "u" (PRIMITIVE_RULE_split_local_before_true "u" "w").

    { inst_hyp e0 hyp.
      LOCKcut "ass" (ASSUMPTION_knowledge_preserved_step @ e0).
      { repeat LOCKclear; LOCKclear "u" "v". }
      LOCKelim "ass" d.
      repeat LOCKelim "ass"; try LOCKauto.
      { LOCKapply DERIVED_RULE_local_correct_trace_before_implies_correct_true; LOCKauto. }
      LOCKapply@ "u" PRIMITIVE_RULE_unright_before_if_causal_true; try LOCKauto. }

    LOCKapply@ "w" "ind" DERIVED_RULE_right_before_elim_true.
    repeat LOCKelim "ind"; try LOCKauto.
    { LOCKapply@ "w" DERIVED_RULE_correct_trace_before_if_right_before_true; LOCKauto. }
    { LOCKapply@ "u" DERIVED_RULE_unlocal_before_if_causal_true; try LOCKauto. }

    inst_hyp e0 hyp.
    LOCKcut "ass" (ASSUMPTION_knowledge_preserved_step @ e0).
    { repeat LOCKclear; LOCKclear "u" "v" "w". }
    LOCKelim "ass" d.
    repeat LOCKelim "ass"; try LOCKauto.
    { LOCKapply DERIVED_RULE_local_correct_trace_before_implies_correct_true; LOCKauto. }
    LOCKapply@ "w" PRIMITIVE_RULE_unright_before_if_causal_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_disseminate_once_before
             n u {eo : EventOrdering} e e1 e2 R H (d1 d2 : kc_data) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_knowledge_preserved_step @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_new          @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_knows_unique             @ e',
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2 @ e,
          ⟬R⟭ H ⊢ KE_AT n @ e1,
          ⟬R⟭ H ⊢ KE_AT n @ e2,
          ⟬R⟭ H ⊢ KE_DISS d1 @ e1,
          ⟬R⟭ H ⊢ KE_DISS d2 @ e2])
      (⟬ (u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_disseminate_once_before_true :
    forall n u {eo : EventOrdering} e e1 e2 R H (d1 d2 : kc_data),
      rule_true (DERIVED_RULE_disseminate_once_before n u e e1 e2 R H d1 d2).
  Proof.
    start_proving_derived st.
    inst_hyp e1 st.

    LOCKcut "ass" (ASSUMPTION_knowledge_preserved_local_before @ e2).
    { LOCKapply DERIVED_RULE_implies_knowledge_preserves_local_before_true.
      inst_hyp e0 st; LOCKclear u. }

    LOCKelim "ass" d1.
    repeat LOCKelim "ass".
    { LOCKcut "diss" (KE_DISS d2 @ e2).
      { repeat LOCKclear; LOCKclear u. }
      LOCKcut "new" (ASSUMPTION_disseminate_new @ e2).
      { inst_hyp e2 st; repeat LOCKclear; LOCKclear u. }
      LOCKelim "new" d2.
      LOCKelim "new"; try LOCKauto.
      { repeat LOCKintro; try LOCKauto. }
      LOCKapply (PRIMITIVE_RULE_knows_implies_correct_true d2); LOCKauto. }

    { LOCKapply@ u DERIVED_RULE_unlocal_before_if_causal_true.
      LOCKcut "diss" (KE_DISS d1 @ e1).
      { LOCKclear u. }
      LOCKcut "new" (ASSUMPTION_disseminate_new @ e1).
      { repeat LOCKclear; LOCKclear u. }
      LOCKelim "new" d1.
      LOCKelim "new"; try LOCKauto.
      repeat LOCKintro; try LOCKauto. }

    LOCKcut "diss" (KE_DISS d2 @ e2).
    { repeat LOCKclear; LOCKclear u. }
    LOCKcut "new" (ASSUMPTION_disseminate_new @ e2).
    { inst_hyp e2 st; repeat LOCKclear; LOCKclear u. }
    LOCKelim "new" d2.
    LOCKelim "new"; try LOCKauto.
    { repeat LOCKintro; try LOCKauto. }

    LOCKcut "uniq" (ASSUMPTION_knows_unique @ e2).
    { inst_hyp e2 st; repeat LOCKclear; LOCKclear u. }
    LOCKelim "uniq" d1.
    LOCKelim "uniq" d2.
    LOCKelim "uniq".
    { unfold KE_AND3; repeat LOCKintro; try LOCKauto.
      repeat LOCKclear; LOCKclear u. }

    LOCKapply (PRIMITIVE_RULE_data_eq_change_event_true e e2); LOCKauto.
  Qed.

  (************************************************************************************************)
  Definition DERIVED_RULE_disseminate_once
             n {eo : EventOrdering} e e1 e2 R H (d1 d2 : kc_data) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_knowledge_preserved_step @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_new          @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_knows_unique             @ e',
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2 @ e,
          ⟬R⟭ H ⊢ KE_AT n @ e1,
          ⟬R⟭ H ⊢ KE_AT n @ e2,
          ⟬R⟭ H ⊢ KE_DISS d1 @ e1,
          ⟬R⟭ H ⊢ KE_DISS d2 @ e2])
      (⟬R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_disseminate_once_true :
    forall n {eo : EventOrdering} e e1 e2 R H (d1 d2 : kc_data),
      rule_true (DERIVED_RULE_disseminate_once n e e1 e2 R H d1 d2).
  Proof.
    start_proving_derived st.
    inst_hyp e1 st.

    apply (PRIMITIVE_RULE_tri_if_towned_true "u" n e1 e2); simseqs j.

    { (* e1 = e2 *)
      LOCKcut "assa" (ASSUMPTION_disseminate_new @ e1).
      { LOCKclear "u". }
      LOCKelim "assa" d1.
      LOCKelim "assa".
      { LOCKintro; try LOCKauto.
        LOCKclear "u". }

      LOCKcut "assb" (ASSUMPTION_disseminate_new @ e1).
      { repeat LOCKclear; LOCKclear "u". }
      LOCKelim "assb" d2.
      LOCKelim "assb".
      { LOCKapply@ "u" PRIMITIVE_RULE_causal_eq_sym_true.
        LOCKapply@ "u" PRIMITIVE_RULE_subst_causal_eq_concl_true.
        LOCKintro; try LOCKauto.
        repeat LOCKclear; LOCKclear "u". }

      LOCKcut "assc" (ASSUMPTION_knows_unique @ e1).
      { repeat LOCKclear; LOCKclear "u". }
      LOCKelim "assc" d1.
      LOCKelim "assc" d2.
      LOCKelim "assc".
      { unfold KE_AND3; repeat LOCKintro; try LOCKauto.
        repeat LOCKclear; LOCKclear "u". }

      LOCKapply (PRIMITIVE_RULE_data_eq_change_event_true e e1); LOCKauto.
    }

    { (* (e1) ⊏ (e2) *)
      LOCKapply (DERIVED_RULE_disseminate_once_before_true n); try LOCKauto; inst_hyp e0 st.
    }

    { (* (e2) ⊏ (e1) *)
      LOCKapply PRIMITIVE_RULE_data_eq_sym_true.
      LOCKapply (DERIVED_RULE_disseminate_once_before_true n); try LOCKauto; inst_hyp e0 st.
      LOCKapply PRIMITIVE_RULE_similar_data_sym_true.
    }
  Qed.


End CalculusSM4.
