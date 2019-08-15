Require Export CalculusSM_tacs.


Section CalculusSM_derived2.

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

  Local Open Scope kn.


  Definition ASSUMPTION_know_data_implies_know_trust :=
    KE_ALL_DATA
      (fun d =>
         KE_IMPLIES
           (KE_KNOWS d)
           (KE_EX_TRUST
              (fun t =>
                 KE_ANDS
                   [KE_TKNOWS t,
                    KE_GEN_FOR d t,
                    KE_HAPPENED_BEFORE_EQ (KE_TDISS_OWN t)]))).


  Definition ASSUMPTION_gen_for_implies_tknows :=
    KE_ALL_DATA
      (fun d =>
         KE_ALL_TRUST
           (fun t =>
              KE_IMPLIES
                (KE_KNOWS d)
                (KE_IMPLIES
                   (KE_GEN_FOR d t)
                   (KE_TKNOWS t)))).

  Definition ASSUMPTION_diss_own_gen_for :=
    KE_ALL_DATA
      (fun d =>
         KE_IMPLIES
           (KE_DISS_OWN d)
           (KE_EX_TRUST
              (fun t =>
                 KE_AND
                   (KE_GEN_FOR d t)
                   (KE_TDISS_OWN t)))).

  Definition ASSUMPTION_all_knew_or_learns_or_gen : KExpression :=
    KE_ALL_DATA ASSUMPTION_knew_or_learns_or_gen.

  Definition ASSUMPTION_all_learns_if_trusted_gen_for: KExpression :=
    KE_ALL_DATA ASSUMPTION_learns_if_trusted_gen_for.


  (************************************************************************************************)
  Definition DERIVED_RULE_implies_know_trust {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_all_knew_or_learns_or_gen     @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_all_learns_if_trusted_gen_for @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_gen_for_implies_tknows        @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_diss_own_gen_for              @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_know_data_implies_know_trust @ e).

  Lemma DERIVED_RULE_implies_know_trust_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_implies_know_trust e R H).
  Proof.
    start_proving_derived st.

    LOCKapply (PRIMITIVE_RULE_all_data_intro_true).
    LOCKintro "kn".

    LOCKapply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_knows_implies_learned_or_gen d @ e)).

    { LOCKapply DERIVED_RULE_KLD_implies_or_true.
      inst_hyp e0 st'.
      LOCKapply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_all_knew_or_learns_or_gen @ e0)).
      { repeat LOCKclear. }

      LOCKapply@ "ass" (PRIMITIVE_RULE_all_data_elim_true "ass" d); try LOCKauto. }

    LOCKelim "ass"; try LOCKauto.
    LOCKelim "ass".

    { LOCKapply@ "ass" (DERIVED_RULE_unlocal_before_eq_hyp_true "u").
      LOCKapply (PRIMITIVE_RULE_cut_true "ass'" (ASSUMPTION_all_learns_if_trusted_gen_for @ e0)).
      { inst_hyp e0 st'; LOCKapply DERIVED_RULE_remove_first_causal_true; repeat LOCKclear. }

      LOCKapply@ "ass'" (PRIMITIVE_RULE_all_data_elim_true "ass'" d).
      LOCKelim "ass'"; try LOCKauto.

      LOCKapply@ "ass'" PRIMITIVE_RULE_exists_trust_elim_true.
      LOCKapply (PRIMITIVE_RULE_exists_trust_intro_true t).
      LOCKelim "ass'" "ass2".

      repeat LOCKintro; try LOCKauto.

      { LOCKapply (PRIMITIVE_RULE_cut_true "ass2" (ASSUMPTION_gen_for_implies_tknows @ e)).
        { inst_hyp e st'; LOCKapply DERIVED_RULE_remove_first_causal_true; repeat LOCKclear. }
        LOCKapply@ "ass2" (PRIMITIVE_RULE_all_data_elim_true "ass2" d).
        LOCKapply@ "ass2" (PRIMITIVE_RULE_all_trust_elim_true "ass2" t).
        repeat (LOCKelim "ass2"; try LOCKauto).
        LOCKapply (PRIMITIVE_RULE_gen_for_change_event_true e e0); try LOCKauto. }

      { LOCKapply (PRIMITIVE_RULE_gen_for_change_event_true e e0); try LOCKauto. }

      { LOCKapply@ "u" DERIVED_RULE_happened_before_eq_if_local_eq_true.
        LOCKapply DERIVED_RULE_happened_before_implies_happened_before_eq_true; try LOCKauto. } }

    LOCKapply@ "ass" (DERIVED_RULE_unlocal_before_eq_hyp_true "u").
    LOCKapply (PRIMITIVE_RULE_cut_true "ass'" (ASSUMPTION_diss_own_gen_for @ e0)).
    { inst_hyp e0 st'; LOCKapply DERIVED_RULE_remove_first_causal_true; repeat LOCKclear. }

    LOCKapply@ "ass'" (PRIMITIVE_RULE_all_data_elim_true "ass'" d).
    LOCKelim "ass'"; try LOCKauto.

    LOCKapply@ "ass'" PRIMITIVE_RULE_exists_trust_elim_true.
    LOCKapply (PRIMITIVE_RULE_exists_trust_intro_true t).
    LOCKelim "ass'" "ass2".

    repeat LOCKintro; try LOCKauto.

    { LOCKapply (PRIMITIVE_RULE_cut_true "ass2" (ASSUMPTION_gen_for_implies_tknows @ e)).
      { inst_hyp e st'; LOCKapply DERIVED_RULE_remove_first_causal_true; repeat LOCKclear. }
      LOCKapply@ "ass2" (PRIMITIVE_RULE_all_data_elim_true "ass2" d).
      LOCKapply@ "ass2" (PRIMITIVE_RULE_all_trust_elim_true "ass2" t).
      repeat (LOCKelim "ass2"; try LOCKauto).
      LOCKapply (PRIMITIVE_RULE_gen_for_change_event_true e e0); try LOCKauto. }

    { LOCKapply (PRIMITIVE_RULE_gen_for_change_event_true e e0); try LOCKauto. }

    { LOCKapply@ "u" PRIMITIVE_RULE_localle_if_causalle_true.
      LOCKapply@ "u" DERIVED_RULE_unhappened_before_eq_if_causalle_true; try LOCKauto. }
  Qed.

End CalculusSM_derived2.
