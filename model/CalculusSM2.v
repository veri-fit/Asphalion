Require Export CalculusSM.
Require Export CalculusSM_tacs.


Section CalculusSM2.

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


  (*  ****** PRIMITIVE RULES ****** *)


  (***********************************************************)
  Definition PRIMITIVE_RULE_induction {eo : EventOrdering} e R H a :=
    MkRule1
      (fun e => [⟬R⟭ H ⊢ KE_IMPLIES (KE_FORALL_BEFORE a) a @ e])
      (⟬R⟭ H ⊢ a @ e).

  Lemma PRIMITIVE_RULE_induction_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (PRIMITIVE_RULE_induction e R H a).
  Proof.
    start_proving_primitive st ct ht.

    unfold seq_event in *; simpl in *.
    destruct e as [e exn]; simpl in *.
    induction e as [e ind] using HappenedBeforeInd.

    inst_hyp (MkEventN e exn) st; simpl in *.
    unfold sequent_true in st1; simpl in st1.
    apply st1; simpl in *; tcsp.
    introv lte.
    destruct e' as [e' exe']; simpl in *.
    apply ind; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_forall_before_elim_trans u x {eo : EventOrdering} e e' R Q H J t a :=
    MkRule0
      [⟬R ++ (u ⋈ e' ▷ e) :: Q⟭ H • (x › KE_FORALL_BEFORE_EQ t @ e') » J ⊢ a]
      (⟬R ++ (u ⋈ e' ▷ e) :: Q⟭ H • (x › KE_FORALL_BEFORE t @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_forall_before_elim_trans_true :
    forall u x {eo : EventOrdering} e e' R Q H J t a,
      rule_true (PRIMITIVE_RULE_forall_before_elim_trans u x e e' R Q H J t a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_FORALL_BEFORE t @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    unfold hyp_event, seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e' ▷ e)) as w; simpl in w; autodimp w hyp.
    { apply in_app_iff; simpl; tcsp. }
    apply st0; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
    introv; simpl in *.
    unfold hyp_event in *; simpl in *; dands; tcsp.
    introv lt.
    apply h; eauto 3 with eo.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_data_eq_change_event {eo : EventOrdering} e1 e2 R H d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_DATA_EQ d1 d2 @ e2]
      (⟬ R ⟭ H ⊢ KE_DATA_EQ d1 d2 @ e1).

  Lemma PRIMITIVE_RULE_data_eq_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H d1 d2,
      rule_true (PRIMITIVE_RULE_data_eq_change_event e1 e2 R H d1 d2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_node_eq_change_event {eo : EventOrdering} e1 e2 R H n1 n2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_NODE_EQ n1 n2 @ e2]
      (⟬ R ⟭ H ⊢ KE_NODE_EQ n1 n2 @ e1).

  Lemma PRIMITIVE_RULE_node_eq_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H n1 n2,
      rule_true (PRIMITIVE_RULE_node_eq_change_event e1 e2 R H n1 n2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (*  ****** DEFINITIONS ****** *)


  Definition KE_OWNS_DEC (d : kc_data) := KE_OR (KE_OWNS d) (KE_NOT (KE_OWNS d)).

  Definition KE_TOWNS_DEC (t : kc_trust) := KE_OWNS_DEC (kc_trust2data t).

  Definition KE_HAS_OWNER_DEC (d : kc_data) (n : node_type) :=
    KE_OR (KE_HAS_OWNER d n) (KE_NOT (KE_HAS_OWNER d n)).

  Definition ASSUMPTION_has_owner_dec :=
    KE_ALL_DATA (fun d => KE_ALL_NODE (fun n => KE_HAS_OWNER_DEC d n)).

  Definition ASSUMPTION_owns_dec :=
    KE_ALL_DATA (fun d => KE_OWNS_DEC d).

  Definition ASSUMPTION_trusted_owns_dec :=
    KE_ALL_TRUST (fun t => KE_OWNS_DEC (kc_trust2data t)).


  (*  ****** DERIVED RULES ****** *)


  (************************************************************************************************)
  Definition DERIVED_RULE_forall_before_eq_elim_local_eq u x {eo : EventOrdering} e e' R Q H J t a :=
    MkRule0
      [⟬R ++ (u ⋈ e' ■ e) :: Q⟭ H • (x › t @ e') » J ⊢ a]
      (⟬R ++ (u ⋈ e' ■ e) :: Q⟭ H • (x › KE_FORALL_BEFORE_EQ t @ e) » J ⊢ a).

  Lemma DERIVED_RULE_forall_before_eq_elim_local_eq_true :
    forall u x {eo : EventOrdering} e e' R Q H J t a,
      rule_true (DERIVED_RULE_forall_before_eq_elim_local_eq u x e e' R Q H J t a).
  Proof.
    start_proving_derived st.
    LOCKelim x "y".
    LOCKapply@ u PRIMITIVE_RULE_split_local_before_eq2_true.

    { LOCKapply@ u PRIMITIVE_RULE_causal_eq_sym_true.
      LOCKapply@ x u PRIMITIVE_RULE_subst_causal_eq_hyp_true.
      LOCKclear "y".
      LOCKapply@ u PRIMITIVE_RULE_causal_eq_sym_true.
      LOCKapply@ u PRIMITIVE_RULE_localle_if_eq_true. }

    LOCKapply@ u (PRIMITIVE_RULE_duplicate_guard_true u "v").
    LOCKapply@ "v" PRIMITIVE_RULE_local_if_causal_true.

    LOCKapply@ "y" "v" PRIMITIVE_RULE_forall_before_elim_true.
    LOCKapply@ "v" PRIMITIVE_RULE_remove_causal_true.

    LOCKapply@ u PRIMITIVE_RULE_local_if_localle_true.
    LOCKclear x.
    LOCKapply@ "y" (PRIMITIVE_RULE_rename_hyp_true "y" x).
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_towns_dec t {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_has_owner_dec @ e',
          ⟬R⟭ H ⊢ KE_NODE @ e])
      (⟬R⟭ H ⊢ KE_TOWNS_DEC t @ e).

  Lemma DERIVED_RULE_towns_dec_true :
    forall t {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_towns_dec t e R H).
  Proof.
    start_proving_derived st.

    LOCKcut "at" (KE_NODE @ e).
    { inst_hyp e st'; repeat LOCKclear. }

    LOCKelim "at"; try LOCKauto.

    LOCKcut "dec" (ASSUMPTION_has_owner_dec @ e).
    { inst_hyp e st'; repeat LOCKclear. }

    LOCKelim "dec" (kc_trust2data t).
    LOCKelim "dec" n.

    LOCKelim "dec".

    { LOCKintro 0.
      LOCKintro n.
      LOCKintro; try LOCKauto. }

    LOCKintro 1.
    LOCKintro "o".
    LOCKelim "o".
    LOCKelim "o" "a".

    LOCKcut "neq" (KE_NODE_EQ n n0 @ e).
    { LOCKapply PRIMITIVE_RULE_at_implies_same_node_true; try LOCKauto. }

    LOCKelim "dec"; try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_subst_node_in_has_owner_true n0); try LOCKauto.
    LOCKapply PRIMITIVE_RULE_node_eq_sym_true; try LOCKauto.
  Qed.


End CalculusSM2.
