Require Export CalculusSM_derived4.


Section CalculusSM_derived5.

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
  Definition DERIVED_RULE_implies_know_trust2 {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_all_knew_or_learns_or_gen     @ e',  (* DONE *)
          ⟬R⟭ H ⊢ ASSUMPTION_all_learns_if_trusted_gen_for @ e',  (* SIMPLIFY *)
          ⟬R⟭ H ⊢ ASSUMPTION_gen_for_implies_tknows        @ e',  (* EASY *)
          ⟬R⟭ H ⊢ ASSUMPTION_diss_own_gen_for              @ e']) (* REPLACE *)
      (⟬R⟭ H ⊢ ASSUMPTION_know_data_implies_know_trust @ e).

  Lemma DERIVED_RULE_implies_know_trust2_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_implies_know_trust2 e R H).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_all_data_intro_true); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "kn"); simseqs j.

    apply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_knows_implies_learned_or_gen d @ e)); simseqs j.

    { apply DERIVED_RULE_KLD_implies_or_true; simseqs j.
      inst_hyp e0 st'.
      apply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_all_knew_or_learns_or_gen @ e0)); simseqs j.
      { repeat LOCKclear. }

      norm_with "ass"; apply (PRIMITIVE_RULE_all_data_elim_true "ass" d); simseqs j; try LOCKauto. }

    norm_with "ass"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j; try LOCKauto.
    norm_with "ass"; apply PRIMITIVE_RULE_or_elim_true; simseqs j.

    { norm_with "ass"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u"); simseqs j.



XXXXXXXXXXX
      apply (PRIMITIVE_RULE_cut_true "ass'" (ASSUMPTION_all_learns_if_trusted_gen_for @ e0)); simseqs j.
      { inst_hyp e0 st'; apply DERIVED_RULE_remove_first_causal_true; simseqs j; repeat LOCKclear. }

      norm_with "ass'"; apply (PRIMITIVE_RULE_all_data_elim_true "ass'" d); simseqs j.
      norm_with "ass'"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j; try LOCKauto.

      norm_with "ass'"; apply PRIMITIVE_RULE_exists_trust_elim_true; simseqs j.
      apply (PRIMITIVE_RULE_exists_trust_intro_true t); simseqs j.
      norm_with "ass'"; apply (PRIMITIVE_RULE_and_elim_true "ass'" "ass2"); simseqs j.

      repeat LOCKintro; try LOCKauto.

      { apply (PRIMITIVE_RULE_cut_true "ass2" (ASSUMPTION_gen_for_implies_tknows @ e)); simseqs j.
        { inst_hyp e st'; apply DERIVED_RULE_remove_first_causal_true; simseqs j; repeat LOCKclear. }
        norm_with "ass2"; apply (PRIMITIVE_RULE_all_data_elim_true "ass2" d); simseqs j.
        norm_with "ass2"; apply (PRIMITIVE_RULE_all_trust_elim_true "ass2" t); simseqs j.
        repeat (norm_with "ass2"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j; try LOCKauto).
        apply (PRIMITIVE_RULE_gen_for_change_event_true _ e0); simseqs j; try LOCKauto. }

      { apply (PRIMITIVE_RULE_gen_for_change_event_true _ e0); simseqs j; try LOCKauto. }

      { causal_norm_with "u"; apply DERIVED_RULE_happened_before_eq_if_local_eq_true; simseqs j.
        apply DERIVED_RULE_happened_before_implies_happened_before_eq_true; simseqs j; try LOCKauto. } }

    norm_with "ass"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "ass'" (ASSUMPTION_diss_own_gen_for @ e0)); simseqs j.
    { inst_hyp e0 st'; apply DERIVED_RULE_remove_first_causal_true; simseqs j; repeat LOCKclear. }

    norm_with "ass'"; apply (PRIMITIVE_RULE_all_data_elim_true "ass'" d); simseqs j.
    norm_with "ass'"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j; try LOCKauto.

    norm_with "ass'"; apply PRIMITIVE_RULE_exists_trust_elim_true; simseqs j.
    apply (PRIMITIVE_RULE_exists_trust_intro_true t); simseqs j.
    norm_with "ass'"; apply (PRIMITIVE_RULE_and_elim_true "ass'" "ass2"); simseqs j.

    repeat LOCKintro; try LOCKauto.

    { apply (PRIMITIVE_RULE_cut_true "ass2" (ASSUMPTION_gen_for_implies_tknows @ e)); simseqs j.
      { inst_hyp e st'; apply DERIVED_RULE_remove_first_causal_true; simseqs j; repeat LOCKclear. }
      norm_with "ass2"; apply (PRIMITIVE_RULE_all_data_elim_true "ass2" d); simseqs j.
      norm_with "ass2"; apply (PRIMITIVE_RULE_all_trust_elim_true "ass2" t); simseqs j.
      repeat (norm_with "ass2"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j; try LOCKauto).
      apply (PRIMITIVE_RULE_gen_for_change_event_true _ e0); simseqs j; try LOCKauto. }

    { apply (PRIMITIVE_RULE_gen_for_change_event_true _ e0); simseqs j; try LOCKauto. }

    { causal_norm_with "u"; apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
      causal_norm_with "u"; apply DERIVED_RULE_unhappened_before_eq_if_causalle_true; simseqs j; try LOCKauto. }
  Qed.

End CalculusSM_derived5.
