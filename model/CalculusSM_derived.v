Require Export CalculusSM_tacs.


Section CalculusSM_derived.

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



  (************************************************************************************************)
  Definition DERIVED_RULE_KLD_implies_or_owns {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_knew_or_learns_or_gen d @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns d @ e).

  Lemma DERIVED_RULE_KLD_implies_or_owns_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_KLD_implies_or_owns e R H d).
  Proof.
    start_proving_derived st.

    LOCKapply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_knows_implies_learned_or_gen d @ e)).
    { LOCKapply DERIVED_RULE_KLD_implies_or_true; inst_hyp e0 w. }

    LOCKintro1 "y".
    LOCKelim "x"; try LOCKauto.

    LOCKelim "x".
    { LOCKintro 0; try LOCKauto. }

    LOCKintro 1.
    LOCKapply@ "x" (DERIVED_RULE_unlocal_before_eq_hyp_true "u").
    LOCKelim "x" "z".
    LOCKapply@ "u" DERIVED_RULE_owns_change_localle_true; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owns_dec {eo : EventOrdering} e d R H :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_OR (KE_OWNS d) (KE_NOT (KE_OWNS d)) @ e).

  Lemma DERIVED_RULE_owns_dec_true :
    forall {eo : EventOrdering} e d R H,
      rule_true (DERIVED_RULE_owns_dec e d R H).
  Proof.
    start_proving_derived st.
    destruct (implies_ex_node e) as [n cond].
    LOCKapply (PRIMITIVE_RULE_cut_true "x" (KE_OR (KE_HAS_OWNER d n) (KE_NOT (KE_HAS_OWNER d n)) @ e)).
    { LOCKapply PRIMITIVE_RULE_has_owner_dec_true. }
    LOCKelim "x".
    { LOCKintro 0.
      LOCKapply (PRIMITIVE_RULE_exists_node_intro_true n).
      LOCKintro; try LOCKauto. }
    LOCKintro 1.
    LOCKintro "o".
    LOCKelim "x"; try LOCKauto.
    LOCKapply@ "o" PRIMITIVE_RULE_exists_node_elim_true.
    LOCKapply@ "o" (PRIMITIVE_RULE_and_elim_true "o" "x").
    LOCKapply (PRIMITIVE_RULE_subst_node_in_has_owner_true n0); try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_cut_true "a" (KE_AT n @ e)); try LOCKauto.
    LOCKapply PRIMITIVE_RULE_at_implies_same_node_true; try LOCKauto.
  Qed.


  (***************************************************************************)
  Definition DERIVED_RULE_disseminate_if_learned_and_disseminated
             p a {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_disseminate_if_knows d   @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_knew_or_learns_or_gen d  @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_learns_if_gen d          @ e',
          ⟬R⟭ H ⊢ KE_AT a                 @ e,
          ⟬R⟭ H ⊢ KE_DISS d               @ e,
          ⟬R⟭ H ⊢ KE_HAS_OWNER d p        @ e,
          ⟬R⟭ H ⊢ KE_NOT (KE_NODE_EQ p a) @ e])
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE (KE_DISS_OWN d) @ e).

  Lemma DERIVED_RULE_disseminate_if_learned_and_disseminated_true :
    forall p a {eo : EventOrdering} (e : EventN) R H (d : kc_data),
      rule_true(DERIVED_RULE_disseminate_if_learned_and_disseminated p a e R H d).
  Proof.
    start_proving_derived st.
    inst_hyp e w.

    LOCKapply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_learned_if_gen d @ e)).
    { LOCKapply DERIVED_RULE_implies_learned_if_gen_true; inst_hyp e0 q. }

    LOCKelim "ass"; try LOCKauto.
    LOCKapply (DERIVED_RULE_knows_and_not_owns_implies_learns2_true p a).
    { LOCKapply DERIVED_RULE_KLD_implies_or_owns_true; inst_hyp e0 w. }

    LOCKapply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_disseminate_if_knows d @ e)).

    LOCKelim "ass"; try LOCKauto.
    LOCKintro; try LOCKauto.
  Qed.


  (***************************************************************************)
  Definition ASSUMPTION_disseminate_if_knows_trusted (d : kc_data) : KExpression :=
    KE_IMPLIES
      (KE_ANDS
         [KE_DISS d,
          KE_NODE,
          KE_LOCAL_CORRECT_TRACE_BEFORE])
      (KE_EX_TRUST
         (fun t =>
            KE_AND
              (KE_TKNOWS t)
              (KE_GEN_FOR d t))).

  Definition ASSUMPTION_trusted_learned_if_gen (t : kc_trust) :=
    KE_IMPLIES
      (KE_TLEARNED t)
      (KE_HAPPENED_BEFORE (KE_TDISS_OWN t)).


  (***************************************************************************)
  Definition DERIVED_RULE_disseminate_if_learned_and_disseminated2
             {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_ALL_DATA ASSUMPTION_disseminate_if_knows_trusted @ e',
          ⟬R⟭ H ⊢ KE_ALL_DATA ASSUMPTION_knew_or_learns_or_gen        @ e',
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen       @ e',
          ⟬R⟭ H ⊢ KE_LOCAL_CORRECT_TRACE_BEFORE @ e,
          ⟬R⟭ H ⊢ KE_DISS d @ e])
      (⟬R⟭ H ⊢ KE_EX_TRUST (fun t =>
                              KE_ANDS
                                [KE_GEN_FOR d t,
                                 KE_TKNOWS t,
                                 KE_OR
                                   (KE_HAPPENED_BEFORE (KE_TDISS_OWN t))
                                   (KE_TOWNS t)]) @ e).

  Lemma DERIVED_RULE_disseminate_if_learned_and_disseminated2_true :
    forall {eo : EventOrdering} (e : EventN) R H (d : kc_data),
      rule_true (DERIVED_RULE_disseminate_if_learned_and_disseminated2 e R H d).
  Proof.
    start_proving_derived st.
    inst_hyp e w.

    LOCKapply (PRIMITIVE_RULE_cut_true "ass" (KE_ALL_DATA ASSUMPTION_disseminate_if_knows_trusted @ e)).
    LOCKapply@ "ass" (PRIMITIVE_RULE_all_data_elim_true "ass" d).
    LOCKelim "ass"; repeat LOCKintro; try LOCKauto.
    LOCKapply@ "ass" PRIMITIVE_RULE_exists_trust_elim_true.
    LOCKelim "ass" "kn".
    LOCKapply (PRIMITIVE_RULE_exists_trust_intro_true t).
    repeat LOCKintro; try LOCKauto.

    LOCKapply (PRIMITIVE_RULE_cut_true "o" (KE_OR (KE_TOWNS t) (KE_NOT (KE_TOWNS t)) @ e)).
    { LOCKapply DERIVED_RULE_owns_dec_true. }

    LOCKelim "o".
    { LOCKintro 1; try LOCKauto. }
    LOCKintro 0.

    LOCKapply (PRIMITIVE_RULE_cut_true "lrn" (KE_TLEARNED t @ e)).
    { LOCKapply DERIVED_RULE_knows_and_not_owns_implies_learns_true; try LOCKauto.
      LOCKapply DERIVED_RULE_KLD_implies_or_owns_true.
      inst_hyp e0 z.
      repeat LOCKclear.
      LOCKapply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_DATA ASSUMPTION_knew_or_learns_or_gen @ e0)).
      LOCKapply@ "x" (PRIMITIVE_RULE_all_data_elim_true "x" (kc_trust2data t)); LOCKauto. }

    LOCKapply (PRIMITIVE_RULE_cut_true "lid" (ASSUMPTION_trusted_learned_if_gen t @ e)).
    { repeat LOCKclear.
      LOCKapply DERIVED_RULE_implies_learned_if_gen_true.
      inst_hyp e0 z.
      LOCKapply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e0)).
      LOCKapply@ "x" (PRIMITIVE_RULE_all_trust_elim_true "x" t); LOCKauto. }

    LOCKelim "lid"; try LOCKauto.
  Qed.


  (***************************************************************************)
  Definition DERIVED_RULE_knows_if_learned_and_disseminated
             p a {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_disseminate_if_knows d   @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_knew_or_learns_or_gen d  @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_learns_if_gen d          @ e',
          ⟬R⟭ H ⊢ KE_AT a                 @ e,
          ⟬R⟭ H ⊢ KE_DISS d               @ e,
          ⟬R⟭ H ⊢ KE_HAS_OWNER d p        @ e,
          ⟬R⟭ H ⊢ KE_NOT (KE_NODE_EQ p a) @ e])
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE (KE_KNOWS_OWN d) @ e).

  Lemma DERIVED_RULE_knows_if_learned_and_disseminated_true :
    forall p a {eo : EventOrdering} (e : EventN) R H (d : kc_data),
      rule_true (DERIVED_RULE_knows_if_learned_and_disseminated p a e R H d).
  Proof.
    start_proving_derived st.

    LOCKapply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE (KE_DISS_OWN d) @ e)).
    { LOCKapply (DERIVED_RULE_disseminate_if_learned_and_disseminated_true p a); inst_hyp e0 q. }
    LOCKapply@ "x" (PRIMITIVE_RULE_unhappened_before_hyp_true "u").
    LOCKapply@ "u" PRIMITIVE_RULE_unhappened_before_if_causal_true.
    LOCKelim "x" "y".

    LOCKintro; try LOCKauto.

    LOCKapply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_disseminate_if_knows d @ e0)).
    { inst_hyp e0 h.
      LOCKclear "x".
      LOCKclear "y".
      LOCKclear "u". }

    LOCKelim "ass"; try LOCKauto.
    LOCKintro; try LOCKauto.
  Qed.


  (***************************************************************************)
  Definition DERIVED_RULE_knows_if_learned_and_disseminated2
             p {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_disseminate_if_knows d   @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_knew_or_learns_or_gen d  @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_learns_if_gen d          @ e',
          ⟬R⟭ H ⊢ KE_DISS d        @ e,
          ⟬R⟭ H ⊢ KE_HAS_OWNER d p @ e])
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ (KE_KNOWS_OWN d) @ e).

  Lemma DERIVED_RULE_knows_if_learned_and_disseminated2_true :
    forall p {eo : EventOrdering} (e : EventN) R H (d : kc_data),
      rule_true (DERIVED_RULE_knows_if_learned_and_disseminated2 p e R H d).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_cut_true "y" (KE_OR (KE_OWNS d) (KE_NOT (KE_OWNS d)) @ e)).
    { LOCKapply DERIVED_RULE_owns_dec_true. }
    LOCKelim "y".
    { LOCKintro 1; try LOCKintro; try LOCKauto.
      LOCKintro; try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_disseminate_if_knows d @ e)).
      { LOCKclear "y"; inst_hyp e h. }
      LOCKelim "x"; try LOCKauto.
      LOCKintro; try LOCKauto.
      LOCKclear "y"; inst_hyp e h. }

    destruct (implies_ex_node e) as [n cond].

    LOCKintro 0.
    LOCKapply (DERIVED_RULE_knows_if_learned_and_disseminated_true p n); try LOCKauto;
      try (complete (LOCKclear "y"; inst_hyp e0 h)).
    LOCKintro "o".
    LOCKelim "y"; try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_exists_node_intro_true n); try LOCKintro; try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_subst_node_in_has_owner_true p); try LOCKauto.
    LOCKclear "o"; inst_hyp e h.
  Qed.

End CalculusSM_derived.
