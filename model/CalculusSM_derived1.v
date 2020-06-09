Require Export CalculusSM_derived0.


Section CalculusSM_derived1.

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


(*  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_implies_id_after t {eo : EventOrdering} e c R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TGENS t @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c @ e]
      (⟬R⟭ H ⊢ KE_ID_AFTER c @ e).

  Lemma DERIVED_RULE_generates_trusted_implies_id_after_true :
    forall t {eo : EventOrdering} e c R H,
      rule_true (DERIVED_RULE_generates_trusted_implies_id_after t e c R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "w" (KE_TRUST_HAS_ID t c @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_TGENS t @ e)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    Transparent KE_TGENS.
    norm_with "x"; apply (PRIMITIVE_RULE_unexists_id_true "x"); simseqs j.
    Opaque KE_TGENS.
    norm_with "x"; apply (PRIMITIVE_RULE_unexists_id_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "z"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "u"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "p" (KE_ID_EQ c h0 @ e)); simseqs j.
    { apply (PRIMITIVE_RULE_has_ids_imply_eq_ids_true t); simseqs j.
      { norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
      norm_with "u"; apply (PRIMITIVE_RULE_hypothesis_true "u"); simseqs j. }
    apply (PRIMITIVE_RULE_id_after_subst_true h0); simseqs j.
    { norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }
    norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j.
  Qed.*)


  (* Lemma generates_trusted_implies_id_after :
    forall {eo : EventOrdering} (e : Event) (t : kc_trust),
      generates_trusted e t
      -> id_after e (kc_id t).
  Proof.
    introv gen.
    unfold generates_trusted in *; exrepnd; allrw; auto.
  Qed.*)



  (************************************************************************************************)
  Definition KE_EX_ID_BETWEEN c :=
    KE_EX_ID2 (fun c1 c2 => KE_ANDS
                                 [KE_ID_BEFORE c1,
                                  KE_ID_AFTER c2,
                                  KE_ID_LT c1 c,
                                  KE_ID_LE c c2]).

  Definition DERIVED_RULE_disseminate_implies_id
             t {eo : EventOrdering} e c R H :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
       ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e,
       ⟬R⟭ H ⊢ KE_TDISS_OWN t @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c @ e]
      (⟬R⟭ H ⊢ KE_EX_ID_BETWEEN c @ e).

  Lemma DERIVED_RULE_disseminate_implies_id_true :
    forall t {eo : EventOrdering} e c R H,
      rule_true (DERIVED_RULE_disseminate_implies_id
                   t e c R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "dis" (KE_TDISS_OWN t @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "hid" (KE_TRUST_HAS_ID t c @ e)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    apply (PRIMITIVE_RULE_cut_true "new" (ASSUMPTION_generates_new @ e)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    apply (PRIMITIVE_RULE_cut_true "mon" (ASSUMPTION_monotonicity @ e)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    apply (DERIVED_RULE_or_elim_true "mon"); simseqs j.

    { Transparent KE_NO_TGENS.
      LOCKelim "mon".
      Opaque KE_NO_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".

      LOCKelim "new" t.
      LOCKelim "new" c.
      LOCKelim "new" c0.
      LOCKelim "new" c0.

      norm_with "new"; apply (PRIMITIVE_RULE_implies_elim_true "new"); simseqs j.
      { repeat (LOCKintro; try LOCKauto). }

      norm_with "new"; apply (PRIMITIVE_RULE_and_elim_true "new" "new1"); simseqs j.

      LOCKcut "p" (KE_ID_LT c c @ e); try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c0); try LOCKauto. }

    { Transparent KE_TGENS.
      LOCKelim "mon".
      LOCKelim "mon".
      Opaque KE_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".
      LOCKelim "mon" "mon3".

      LOCKelim "new" t.
      LOCKelim "new" c.
      LOCKelim "new" c0.
      LOCKelim "new" c1.

      LOCKelim "new".
      { repeat (LOCKintro; try LOCKauto). }

      LOCKelim "new" "new1".
      LOCKintro c0.
      LOCKintro c1.

      repeat (LOCKintro; try LOCKauto). }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred
             u t2 {eo : EventOrdering} e1 e2 e c1 c2 Q R H :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e2,
       ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ ASSUMPTION_generates_new @ e2,
       ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
       ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
       ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_AFTER c1 @ e1]
      (⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred_true :
    forall u t2 {eo : EventOrdering} e1 e2 e c1 c2 Q R H,
      rule_true (DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred
                   u t2 e1 e2 e c1 c2 Q R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "bid" (KE_ID_BEFORE c1 @ e2)); simseqs j.
    { apply DERIVED_RULE_id_after_is_id_before_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "hid" (KE_TRUST_HAS_ID t2 c2 @ e2)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "dis" (KE_TDISS_OWN t2 @ e2)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    apply (PRIMITIVE_RULE_cut_true "between" (KE_EX_ID_BETWEEN c2 @ e2)); simseqs j.
    { apply (DERIVED_RULE_disseminate_implies_id_true t2); simseqs j;
        try (complete (repeat (apply DERIVED_RULE_thin_last_true; simseqs j))). }
    LOCKelim "between".
    LOCKelim "between".
    LOCKelim "between" "between1".
    LOCKelim "between" "between2".
    LOCKelim "between" "between3".
    LOCKelim "between" "between4".

    apply (PRIMITIVE_RULE_cut_true "p" (KE_ID_EQ c1 c @ e)); simseqs j.
    { apply (PRIMITIVE_RULE_id_eq_change_event_true _ e2); simseqs j.
      apply DERIVED_RULE_ids_before_imply_eq_ids_true; simseqs j.
      { norm_with "bid"; apply (PRIMITIVE_RULE_hypothesis_true "bid"); simseqs j. }
      norm_with "between1"; apply (PRIMITIVE_RULE_hypothesis_true "between1"); simseqs j. }

    apply (PRIMITIVE_RULE_id_lt_trans_eq_lt_true c); simseqs j.
    { norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }
    apply (PRIMITIVE_RULE_id_lt_change_event_true _ e2); simseqs j.
    norm_with "between3"; apply (PRIMITIVE_RULE_hypothesis_true "between3"); simseqs j.
  Qed.

  (*Lemma generates_trusted_kc_id_increases_direct_pred :
    forall {eo : EventOrdering} (e1 e2 : Event) (c : nat) (t2 : kc_trust),
      e1 ⊂ e2
      -> id_after e1 c
      -> generates_trusted e2 t2
      -> c < kc_id t2.
  Proof.
    introv dp gt1 gt2.
    dup dp as dp'.
    eapply pred_implies_local_pred in dp.
    rewrite dp in *.
    unfold generates_trusted, id_after, id_before in *.
    exrepnd; subst.

    pose proof (trusted_state_before_implies_trusted_state_after_not_first e2 mem0) as xx.
    repeat (autodimp xx hyp); eauto 3 with eo.
    eq_states; tcsp; try omega.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred2
             u t1 t2 {eo : EventOrdering} e1 e2 e c1 c2 Q R H :=
    MkRule1
      (fun e' =>
         [⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TDISS_OWN t1 @ e1,
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2])
      (⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred2_true :
    forall u t1 t2 {eo : EventOrdering} e1 e2 e c1 c2 Q R H,
      rule_true (DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred2 u t1 t2 e1 e2 e c1 c2 Q R H).
  Proof.
    start_proving_derived st.

    inst_hyp e1 sta; inst_hyp e2 stb; clear st1; GC.

    apply (PRIMITIVE_RULE_cut_true "hida" (KE_TRUST_HAS_ID t1 c1 @ e1)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "hidb" (KE_TRUST_HAS_ID t2 c2 @ e2)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "disa" (KE_TDISS_OWN t1 @ e1)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    apply (PRIMITIVE_RULE_cut_true "disb" (KE_TDISS_OWN t2 @ e2)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    apply (PRIMITIVE_RULE_cut_true "betweena" (KE_EX_ID_BETWEEN c1 @ e1)); simseqs j.
    { apply (DERIVED_RULE_disseminate_implies_id_true t1); simseqs j;
        try (complete (repeat (apply DERIVED_RULE_thin_last_true; simseqs j))). }
    LOCKelim "betweena".
    LOCKelim "betweena".
    LOCKelim "betweena" "betweena1".
    LOCKelim "betweena" "betweena2".
    LOCKelim "betweena" "betweena3".
    LOCKelim "betweena" "betweena4".

    apply (PRIMITIVE_RULE_cut_true "betweenb" (KE_EX_ID_BETWEEN c2 @ e2)); simseqs j.
    { apply (DERIVED_RULE_disseminate_implies_id_true t2); simseqs j;
        try (complete (repeat (apply DERIVED_RULE_thin_last_true; simseqs j))). }
    LOCKelim "betweenb".
    LOCKelim "betweenb".
    LOCKelim "betweenb" "betweenb1".
    LOCKelim "betweenb" "betweenb2".
    LOCKelim "betweenb" "betweenb3".
    LOCKelim "betweenb" "betweenb4".

    apply (PRIMITIVE_RULE_cut_true "id" (KE_ID_AFTER c3 @ e1)); simseqs j.
    { apply DERIVED_RULE_id_before_is_id_after_true; simseqs j.
      norm_with "betweenb1"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb1"); simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "p" (KE_ID_EQ c3 c0 @ e)); simseqs j.
    { apply (PRIMITIVE_RULE_id_eq_change_event_true _ e1); simseqs j.
      apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
      { norm_with "id"; apply (PRIMITIVE_RULE_hypothesis_true "id"); simseqs j. }
      norm_with "betweena2"; apply (PRIMITIVE_RULE_hypothesis_true "betweena2"); simseqs j. }

    apply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c0); simseqs j.
    { apply (DERIVED_RULE_id_le_change_event_true _ e1); simseqs j.
      norm_with "betweena4"; apply (PRIMITIVE_RULE_hypothesis_true "betweena4"); simseqs j. }
    apply (PRIMITIVE_RULE_id_lt_trans_eq_lt_true c3); simseqs j.
    { apply PRIMITIVE_RULE_id_eq_sym_true; simseqs j.
      norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }
    apply (PRIMITIVE_RULE_id_lt_change_event_true _ e2); simseqs j.
    norm_with "betweenb3"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb3"); simseqs j.
  Qed.


  (*Lemma generates_trusted_kc_id_increases_direct_pred2 :
    forall {eo : EventOrdering} (e1 e2 : Event) (t1 t2 : kc_trust),
      e1 ⊂ e2 (* this implies that the events have the same location *)
      -> generates_trusted e1 t1
      -> generates_trusted e2 t2
      -> kc_id t1 < kc_id t2.
  Proof.
    introv dp gt1 gt2.
    apply generates_trusted_implies_id_after in gt1.
    eapply generates_trusted_kc_id_increases_direct_pred; eauto.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_no_trusted_generation_implies_id_after {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_NO_TGENS @ e]
      (⟬R⟭ H ⊢ KE_EX_ID (fun c => KE_ID_AFTER c) @ e).

  Lemma DERIVED_RULE_no_trusted_generation_implies_id_after_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_no_trusted_generation_implies_id_after e R H).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_NO_TGENS @ e).
    Transparent KE_NO_TGENS.
    LOCKelim "x".
    Opaque KE_NO_TGENS.
    LOCKelim "x" "y".
    LOCKelim "x" "z".
    LOCKintro c; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_split_local_before_eq_hyp x {eo : EventOrdering} e R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › a @ e) » J ⊢ b,
       ⟬R⟭ H • (x › KE_LOCAL_BEFORE_EQ a @ local_pred_n e) » J ⊢ b]
      (⟬R⟭ H • (x › KE_LOCAL_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_split_local_before_hyp_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_split_local_before_eq_hyp x e R H J a b).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u"); simseqs j.
    causal_norm_with "u"; apply DERIVED_RULE_split_local_before_eq_true; simseqs j.
    { causal_norm_with "u"; apply PRIMITIVE_RULE_subst_causal_eq_hyp_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
    apply DERIVED_RULE_relocal_before_eq_hyp_true; simseqs j.
  Qed.


  (************************************************************************************************)
  Definition ID_INCREASES c1 :=
    KE_IMPLIES
      (KE_LOCAL_BEFORE_EQ (KE_ID_AFTER c1))
      (KE_ALL_ID (fun c2 =>
                    KE_IMPLIES
                      (KE_ID_AFTER c2)
                      (KE_ID_LE c1 c2))).

  Definition DERIVED_RULE_id_after_increases0 {eo : EventOrdering} e c1 R H :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e'])
      (⟬R⟭ H ⊢ ID_INCREASES c1 @ e).

  Lemma DERIVED_RULE_id_after_increases0_true :
    forall {eo : EventOrdering} e c1 R H,
      rule_true (DERIVED_RULE_id_after_increases0 e c1 R H).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_pred_eq_induction_true; simseqs j.

    { apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
      apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
      apply PRIMITIVE_RULE_all_id_intro_true; simseqs j.
      rename c into c2.
      apply (PRIMITIVE_RULE_implies_intro_true "z"); simseqs j.
      norm_with "y"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "y"); simseqs j.
      apply DERIVED_RULE_causalle_is_equal_if_first_true; simseqs j.
      { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      causal_norm_with "u"; norm_with "y"; apply (PRIMITIVE_RULE_subst_causal_eq_hyp_true "u" "y"); simseqs j.
      apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }

    apply (PRIMITIVE_RULE_implies_intro_true "nf"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "rb"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "lb"); simseqs j.
    apply PRIMITIVE_RULE_all_id_intro_true; simseqs j.
    rename c into c2.
    apply (PRIMITIVE_RULE_implies_intro_true "ca"); simseqs j.
    norm_with "rb"; apply (DERIVED_RULE_unright_before_eq_hyp_true "rb"); simseqs j.
    norm_with "lb"; apply DERIVED_RULE_split_local_before_hyp_true; simseqs j.

    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
      { norm_with "lb"; apply (PRIMITIVE_RULE_hypothesis_true "lb"); simseqs j. }
      norm_with "ca"; apply (PRIMITIVE_RULE_hypothesis_true "ca"); simseqs j. }

    norm_with "rb"; apply (PRIMITIVE_RULE_implies_elim_true "rb"); simseqs j.
    { norm_with "lb"; apply (PRIMITIVE_RULE_hypothesis_true "lb"); simseqs j. }

    inst_hyp e0 st.
    apply (PRIMITIVE_RULE_cut_true "mon" (ASSUMPTION_monotonicity @ e0)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    apply (DERIVED_RULE_or_elim_true "mon"); simseqs j.

    { Transparent KE_NO_TGENS.
      LOCKelim "mon".
      Opaque KE_NO_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".
      apply (PRIMITIVE_RULE_cut_true "mon" (KE_ID_EQ c2 c @ e0)); simseqs j.
      { apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
        { norm_with "ca"; apply (PRIMITIVE_RULE_hypothesis_true "ca"); simseqs j. }
        norm_with "mon2"; apply (PRIMITIVE_RULE_hypothesis_true "mon2"); simseqs j. }
      norm_with "rb"; apply (PRIMITIVE_RULE_all_id_elim_true "rb" c); simseqs j.
      norm_with "rb"; apply (PRIMITIVE_RULE_implies_elim_true "rb"); simseqs j.
      { apply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e0); simseqs j.
        { norm_with "nf"; apply (PRIMITIVE_RULE_hypothesis_true "nf"); simseqs j. }
        causal_norm_with "u"; apply DERIVED_RULE_id_before_is_id_after_true; simseqs j.
        norm_with "mon1"; apply (PRIMITIVE_RULE_hypothesis_true "mon1"); simseqs j. }
      apply (DERIVED_RULE_id_le_trans_true c); simseqs j.
      { apply (DERIVED_RULE_id_le_change_event_true _ (local_pred_n e0)); simseqs j.
        norm_with "rb"; apply (PRIMITIVE_RULE_hypothesis_true "rb"); simseqs j. }
      apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_id_eq_sym_true; simseqs j.
      norm_with "mon"; apply (PRIMITIVE_RULE_hypothesis_true "mon"); simseqs j. }

    { Transparent KE_TGENS.
      LOCKelim "mon".
      LOCKelim "mon".
      Opaque KE_TGENS.
      LOCKelim "mon" "mon0".
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".
      apply (PRIMITIVE_RULE_cut_true "mon" (KE_ID_EQ c2 c0 @ e0)); simseqs j.
      { apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
        { norm_with "ca"; apply (PRIMITIVE_RULE_hypothesis_true "ca"); simseqs j. }
        norm_with "mon2"; apply (PRIMITIVE_RULE_hypothesis_true "mon2"); simseqs j. }
      norm_with "rb"; apply (PRIMITIVE_RULE_all_id_elim_true "rb" c); simseqs j.
      norm_with "rb"; apply (PRIMITIVE_RULE_implies_elim_true "rb"); simseqs j.
      { apply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e0); simseqs j.
        { norm_with "nf"; apply (PRIMITIVE_RULE_hypothesis_true "nf"); simseqs j. }
        causal_norm_with "u"; apply DERIVED_RULE_id_before_is_id_after_true; simseqs j.
        norm_with "mon1"; apply (PRIMITIVE_RULE_hypothesis_true "mon1"); simseqs j. }
      apply (DERIVED_RULE_id_le_trans_true c); simseqs j.
      { apply (DERIVED_RULE_id_le_change_event_true _ (local_pred_n e0)); simseqs j.
        norm_with "rb"; apply (PRIMITIVE_RULE_hypothesis_true "rb"); simseqs j. }
      apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply (PRIMITIVE_RULE_id_lt_trans_lt_eq_true c0); simseqs j.
      { norm_with "mon0"; apply (PRIMITIVE_RULE_hypothesis_true "mon0"); simseqs j. }
      apply (PRIMITIVE_RULE_id_eq_sym_true); simseqs j.
      norm_with "mon"; apply (PRIMITIVE_RULE_hypothesis_true "mon"); simseqs j. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_after_increases u {eo : EventOrdering} e1 e2 e c1 c2 R H :=
    MkRule1
      (fun e' =>
         [⟬(u ⋈ e1 ■ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬(u ⋈ e1 ■ e2) :: R⟭ H ⊢ KE_ID_AFTER c1 @ e1,
          ⟬(u ⋈ e1 ■ e2) :: R⟭ H ⊢ KE_ID_AFTER c2 @ e2])
      (⟬(u ⋈ e1 ■ e2) :: R⟭ H ⊢ KE_ID_LE c1 c2 @ e).

  Lemma DERIVED_RULE_id_after_increases_true :
    forall u {eo : EventOrdering} e1 e2 e c1 c2 R H,
      rule_true (DERIVED_RULE_id_after_increases u e1 e2 e c1 c2 R H).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (ID_INCREASES c1 @ e2)); simseqs j.
    { apply DERIVED_RULE_id_after_increases0_true; simseqs j.
      inst_hyp e0 st. }

    inst_hyp e1 st.

    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { causal_norm_with u; apply DERIVED_RULE_unlocal_before_eq_if_causalle_true; simseqs j. }
    norm_with "x"; apply (PRIMITIVE_RULE_all_id_elim_true "x" c2); simseqs j.

    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    apply (DERIVED_RULE_id_le_change_event_true _ e2); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_after_increases2 u {eo : EventOrdering} e1 e2 e c1 c2 R H :=
    MkRule1
      (fun e' =>
         [⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_ID_AFTER c1 @ e1,
          ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_ID_BEFORE c2 @ e2])
      (⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_ID_LE c1 c2 @ e).

  Lemma DERIVED_RULE_id_after_increases2_true :
    forall u {eo : EventOrdering} e1 e2 e c1 c2 R H,
      rule_true (DERIVED_RULE_id_after_increases2 u e1 e2 e c1 c2 R H).
  Proof.
    start_proving_derived st.
    inst_hyp e2 sta.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_ID_AFTER c1 @ e1)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (KE_ID_BEFORE c2 @ e2)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    causal_norm_with u; apply (PRIMITIVE_RULE_split_local_before2_true u "v" "w"); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_id_after_increases_true "v"); simseqs j.
    { inst_hyp e0 st.
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j).
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j). }
    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
    causal_norm_with "w"; apply (DERIVED_RULE_id_before_is_id_after_true "w"); simseqs j.
    norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j.
  Qed.

  (*Lemma id_after_increases :
    forall {eo : EventOrdering} e1 e2 c1 c2,
      ex_node_e e2
      -> monotonicity eo
      -> e1 ⊑ e2
      -> id_after e2 c2
      -> id_after e1 c1
      -> c1 <= c2.
  Proof.
    introv exe mon lte sbe2 sbe1.

    revert dependent c2.
    revert dependent e2.

    induction e2 as [e2 ind] using predHappenedBeforeInd.
    introv exe lte sbe2.

    applydup @localHappenedBeforeLe_implies_or in lte; repndors; subst; eq_states; tcsp;[].

    destruct (dec_isFirst e2) as [d|d]; ginv; simpl in *;[|].

    { apply isFirst_localHappenedBeforeLe_implies_eq in lte; subst; auto; eq_states; auto. }

    pose proof (ind (local_pred e2)) as ind; repeat (autodimp ind hyp); eauto 3 with eo kn;[].

    pose proof (mon e2) as mon; repeat (autodimp mon hyp);[].
    repndors; exrepnd;[|].

    {
      unfold no_trusted_generation in *; exrepnd; eq_states.
      apply id_before_implies_id_after in mon1; auto.
    }

    {
      unfold generates_trusted in *; exrepnd; eq_states.
      apply id_before_implies_id_after in mon0; auto.
    }
  Qed.*)


(*  (************************************************************************************************)
  Definition DERIVED_RULE_tgens_implies_has_id {eo : EventOrdering} e R H t :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TGENS t @ e]
      (⟬R⟭ H ⊢ KE_EX_ID (fun c => KE_AND (KE_TRUST_HAS_ID t c) (KE_ID_AFTER c)) @ e).

  Lemma DERIVED_RULE_tgens_implies_has_id_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_tgens_implies_has_id e R H t).
  Proof.
    introv st; simpl in *; simpl_sem_rule; dLin_hyp st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TGENS t @ e)); simseqs j.
    clear st0.
    Transparent KE_TGENS.
    norm_with "x"; apply (PRIMITIVE_RULE_unexists_id_true "x"); simseqs j.
    Opaque KE_TGENS.
    norm_with "x"; apply (PRIMITIVE_RULE_unexists_id_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "z"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "w"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "u"); simseqs j.
    apply (PRIMITIVE_RULE_exists_id_intro_true h0); simseqs j.
    apply PRIMITIVE_RULE_and_intro_true; simseqs j.
    { norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
    norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_kc_id_increases_strict_before
             u t1 t2 {eo : EventOrdering} e1 e2 e c1 c2 R H :=
    MkRule1
      (fun e' => [⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_generates_new @ e',
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TDISS_OWN t1 @ e1,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2])
      (⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_true :
    forall u t1 t2 {eo : EventOrdering} e1 e2 e c1 c2 R H,
      rule_true (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before u t1 t2 e1 e2 e c1 c2 R H).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "betweena" (KE_EX_ID_BETWEEN c1 @ e1)); simseqs j.
    { inst_hyp e1 sta.
      apply (DERIVED_RULE_disseminate_implies_id_true t1); simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "betweenb" (KE_EX_ID_BETWEEN c2 @ e2)); simseqs j.
    { inst_hyp e2 stb.
      apply DERIVED_RULE_thin_last_true; simseqs j.
      apply (DERIVED_RULE_disseminate_implies_id_true t2); simseqs j. }

    LOCKelim "betweena".
    LOCKelim "betweena".
    LOCKelim "betweena" "betweena1".
    LOCKelim "betweena" "betweena2".
    LOCKelim "betweena" "betweena3".
    LOCKelim "betweena" "betweena4".

    LOCKelim "betweenb".
    LOCKelim "betweenb".
    LOCKelim "betweenb" "betweenb1".
    LOCKelim "betweenb" "betweenb2".
    LOCKelim "betweenb" "betweenb3".
    LOCKelim "betweenb" "betweenb4".

    apply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c0); simseqs j.
    { apply (DERIVED_RULE_id_le_change_event_true _ e1); simseqs j.
      norm_with "betweena4"; apply (PRIMITIVE_RULE_hypothesis_true "betweena4"); simseqs j. }

    apply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c3); simseqs j.
    { apply (DERIVED_RULE_id_after_increases2_true u); simseqs j.
      { inst_hyp e0 sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "betweena2"; apply (PRIMITIVE_RULE_hypothesis_true "betweena2"); simseqs j. }
      norm_with "betweenb1"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb1"); simseqs j. }

    apply (PRIMITIVE_RULE_id_lt_change_event_true _ e2); simseqs j.
    norm_with "betweenb3"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb3"); simseqs j.
  Qed.


  (*Lemma generates_trusted_kc_id_increases_strict_before :
    forall {eo : EventOrdering} (e1 e2 : Event) (t1 t2 : kc_trust),
      ex_node_e e2
      -> monotonicity eo
      -> e1 ⊏ e2  (* this implies that the location is same *)
      -> generates_trusted e2 t2
      -> generates_trusted e1 t1 (* This could be replaced by [id_after] *)
      -> kc_id t1 < kc_id t2.
  Proof.
    introv exe mon lte gen2 gen1.

    apply local_implies_pred_or_local in lte; repndors; exrepnd;[|].

    { eapply generates_trusted_kc_id_increases_direct_pred2; eauto. }

    dup lte1 as lteb.
    pose proof (mon e) as q; repeat (autodimp q hyp); eauto 3 with eo kn; repndors; exrepnd;[|].

    { apply no_trusted_generation_implies_id_after in q; exrepnd.
      eapply generates_trusted_kc_id_increases_direct_pred in lte1;
        try exact q0; try exact gen2.
      apply generates_trusted_implies_id_after in gen1.
      eapply id_after_increases in gen1; try exact q0; eauto 3 with eo kn; try omega. }

    { eapply generates_trusted_kc_id_increases_direct_pred2 in lte1;
        try exact q0; try exact gen2.
      pose proof (generates_trusted_kc_id_increases e1 e t1 t) as h.
      repeat (autodimp h hyp); eauto 3 with eo kn; try omega. }
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_same_output_before_implies_false t1 t2 c1 c2 {eo : EventOrdering} e R H :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_same_output_before_implies_false t1 t2 c1 c2 @ e).

  Lemma DERIVED_RULE_same_output_before_implies_false_true :
    forall t1 t2 c1 c2 {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_same_output_before_implies_false t1 t2 c1 c2 e R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "z"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "w"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "p"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "q"); simseqs j.
    norm_with "z"; apply (DERIVED_RULE_unlocal_before_hyp_true "u" "z"); simseqs j.

    apply (PRIMITIVE_RULE_cut_true "lt" (KE_ID_LT c1 c2 @ e)); simseqs j.
    { causal_norm_with "u"; apply (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_true "u" t1 t2); simseqs j.
      { inst_hyp e1 st.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { inst_hyp e1 st.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      { apply (PRIMITIVE_RULE_has_id_change_event_true _ e); simseqs j.
        norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
      norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }

    LOCKcut "lt" (KE_ID_LT c1 c1 @ e); try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_id_lt_trans_lt_eq_true c2); try LOCKauto.
    LOCKapply PRIMITIVE_RULE_id_eq_sym_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_same_event_same_output_implies_same_input {eo : EventOrdering} e R H t1 t2 c1 c2 :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_same_event_same_output_implies_same_input t1 t2 c1 c2 @ e).

  Lemma DERIVED_RULE_same_event_same_output_implies_same_input_true :
    forall {eo : EventOrdering} e R H t1 t2 c1 c2,
      rule_true (DERIVED_RULE_same_event_same_output_implies_same_input e R H t1 t2 c1 c2).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_implies_intro_true "x").
    LOCKelim "x" "y".
    LOCKelim "x" "z".
    LOCKelim "x" "w".
    LOCKelim "x" "p".
    LOCKelim "x" "q".

    LOCKelim "z".
    { LOCKapply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_same_output_before_implies_false t1 t2 c1 c2 @ e)).
      { repeat LOCKclear.
        LOCKapply DERIVED_RULE_same_output_before_implies_false_true; inst_hyp e0 st. }
      LOCKapply@ "ass" PRIMITIVE_RULE_implies_elim_true; try LOCKauto.
      repeat (LOCKintro; try LOCKauto). }

    apply (PRIMITIVE_RULE_unicity_true c1 c2); simseqs j; try LOCKauto.
    { inst_hyp e st; repeat LOCKclear. }
    LOCKelim "z" "u"; try LOCKauto.
  Qed.


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition DERIVED_RULE_TGEN_MONOTONICITY_local_trusted_component_strictly_less {eo : EventOrdering} e R H t1 t2 c1 c2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ KE_TGENS t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE (KE_TGENS t1) @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e])
      (⟬R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma DERIVED_RULE_TGEN_MONOTONICITY_local_trusted_component_strictly_less_true :
    forall {eo : EventOrdering} e R H t1 t2 c1 c2,
      rule_true (DERIVED_RULE_TGEN_MONOTONICITY_local_trusted_component_strictly_less e R H t1 t2 c1 c2).
  Proof.
    start_proving_derived st.

    pose proof (st (mk_v1 e)) as st'; simpl_sem_rule; dLin_hyp st'; simpl in *.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE (KE_TGENS t1) @ e)); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_unlocal_before_hyp_true "x"); simseqs j.

    apply (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_true "x" t1 t2 h e); simseqs j;
      try (complete (apply DERIVED_RULE_remove_first_causal_true; simseqs j;
                     apply DERIVED_RULE_thin_last_true; simseqs j)).

    { apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      apply DERIVED_RULE_thin_last_true; simseqs j.
      pose proof (st (mk_v1 h0)) as st; simpl_sem_rule; dLin_hyp st; simpl in *; auto. }

    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_same_id_before_implies_false c1 c2 {eo : EventOrdering} e R H t1 t2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE (KE_TDISS_OWN t1) @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e])
      (⟬R⟭ H ⊢ KE_FALSE @ e).

  Lemma DERIVED_RULE_same_id_before_implies_false_true :
    forall c1 c2 {eo : EventOrdering} e R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_same_id_before_implies_false c1 c2 e R H t1 t2).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    inst_hyp e st'.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_same_output_before_implies_false t1 t2 c1 c2 @ e)); simseqs j.
    { apply DERIVED_RULE_same_output_before_implies_false_true; simseqs j;
        inst_hyp e0 st. }

    apply DERIVED_RULE_implies_elim_true; simseqs j; repeat LOCKintro; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_same_input_if_same_id c1 c2 {eo : EventOrdering} e R H t1 t2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_TDISS_OWN t1) @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma DERIVED_RULE_trusted_same_input_if_same_id_true :
    forall c1 c2 {eo : EventOrdering} e R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_trusted_same_input_if_same_id c1 c2 e R H t1 t2).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    inst_hyp e st'.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_same_event_same_output_implies_same_input t1 t2 c1 c2 @ e)); simseqs j.
    { apply DERIVED_RULE_same_event_same_output_implies_same_input_true; simseqs j;
        inst_hyp e0 st. }

    apply DERIVED_RULE_implies_elim_true; simseqs j; try LOCKauto.
    repeat (LOCKintro;[]); LOCKauto.
  Qed.


(*
(* NOT USED *)

  (************************************************************************************************)
  Lemma OLD_RULE_trusted_same_input_if_same_id_true_from_mon :
    forall {eo : EventOrdering} (t' t'' : kc_trust),
      assume_eo eo (ASSUMPTION_monotonicity)
      -> rule_true_eo eo (OLD_RULE_trusted_same_input_if_same_id t' t'').
  Proof.
    introv mon exe ht h; simpl in *.
    dLin_hyp h.
    unfold sequent_true_at_event in *; simpl in *.
    autodimp h0 hyp; tcsp.
    autodimp h1 hyp; tcsp.
    autodimp h2 hyp; tcsp.
    simpl in *.
    exrepnd.

    eapply localHappenedBeforeLe_implies_or2 in h1; repndors; subst.

    { eapply generates_trusted_unique in h0; try exact h3; subst; auto. }

    apply (OLD_RULE_TGEN_MONOTONICITY_local_trusted_component_strictly_less_true t' t'') in mon.

    pose proof (mon e) as mon; simpl in mon; autodimp mon hyp.
    unfold rule_true_at_event in mon; simpl in *.
    repeat (autodimp mon hyp); eauto 3 with kn;
      try (complete (unfold sequent_true_at_event in *; simpl in *;
                     autodimp mon hyp; tcsp; omega)).
    introv q ht; repndors; tcsp; subst; simpl; auto.
    exists e'; dands; auto.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_tgens_implies_towns {eo : EventOrdering} e R H t :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TDISS_OWN t @ e]
      (⟬R⟭ H ⊢ KE_TOWNS t @ e).

  Lemma DERIVED_RULE_tgens_implies_towns_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_tgens_implies_towns e R H t).
  Proof.
    introv st; simpl in *; simpl_sem_rule; dLin_hyp st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TDISS_OWN t @ e)); simseqs j.
    clear st0.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_disseminate_unique
             c1 c2 n {eo : EventOrdering} e1 e2 R H (t1 t2 : kc_trust) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t1 @ e1,
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
          ⟬R⟭ H ⊢ KE_AT n @ e1,
          ⟬R⟭ H ⊢ KE_AT n @ e2,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e2])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e2).

  Lemma DERIVED_RULE_trusted_disseminate_unique_true :
    forall c1 c2 n {eo : EventOrdering} e1 e2 R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_trusted_disseminate_unique c1 c2 n e1 e2 R H t1 t2).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    inst_hyp e1 st'.

    apply (PRIMITIVE_RULE_tri_if_towned_true "u" n e1 e2); simseqs j.

    { (* e1 = e2 *)
      apply (DERIVED_RULE_trusted_same_input_if_same_id_true c1 c2); simseqs j;
      try (complete (inst_hyp e st; apply DERIVED_RULE_remove_first_causal_true; simseqs j)).

      inst_hyp e st.
      apply DERIVED_RULE_weaken_local_before_eq_true; simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

    { (* (e1) ⊏ (e2) *)
      apply (PRIMITIVE_RULE_cut_true "x" (KE_FALSE @ e2)); simseqs j; try LOCKauto.
      apply (DERIVED_RULE_same_id_before_implies_false_true c1 c2 _ _ _ t1 t2); simseqs j;
        try (complete (apply DERIVED_RULE_remove_first_causal_true; simseqs j; inst_hyp e st)).
      causal_norm_with "u"; apply DERIVED_RULE_unlocal_before_if_causal_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

    { (* (e2) ⊏ (e1) *)
      apply PRIMITIVE_RULE_trust_eq_sym_true; simseqs j.
      apply (PRIMITIVE_RULE_trust_eq_change_event_true e2 e1); simseqs j.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_FALSE @ e1)); simseqs j; try LOCKauto.
      apply (DERIVED_RULE_same_id_before_implies_false_true c2 c1 _ _ _ t2 t1); simseqs j;
        try (complete (apply DERIVED_RULE_remove_first_causal_true; simseqs j; inst_hyp e st)).
      { causal_norm_with "u"; apply DERIVED_RULE_unlocal_before_if_causal_true; simseqs j.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
      apply PRIMITIVE_RULE_id_eq_sym_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knows_implies_learned_or_gen_implies_gen {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_learns_if_gen d @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_knows_implies_learned_or_gen d @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_knows_implies_gen d @ e).

  Lemma DERIVED_RULE_knows_implies_learned_or_gen_implies_gen_true :
    forall (eo : EventOrdering) e R H d,
      rule_true (DERIVED_RULE_knows_implies_learned_or_gen_implies_gen e R H d).
  Proof.
    start_proving_derived st.
    inst_hyp e st'.

    apply (PRIMITIVE_RULE_cut_true "a" (ASSUMPTION_knows_implies_learned_or_gen d @ e)); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "kn"); simseqs j.
    norm_with "a"; apply (PRIMITIVE_RULE_implies_elim_true "a"); simseqs j.
    { norm_with "kn"; apply (PRIMITIVE_RULE_hypothesis_true "kn"); simseqs j. }

    norm_with "a"; apply (PRIMITIVE_RULE_or_elim_true "a"); simseqs j.

    { norm_with "a"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "a"); simseqs j.
      inst_hyp e0 st.
      apply (PRIMITIVE_RULE_cut_true "b" (ASSUMPTION_learns_if_gen d @ e0)); simseqs j.
      { apply DERIVED_RULE_remove_first_causal_true; simseqs j.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      norm_with "b"; apply (PRIMITIVE_RULE_implies_elim_true "b"); simseqs j.
      { norm_with "a"; apply (PRIMITIVE_RULE_hypothesis_true "a"); simseqs j. }
      norm_with "b"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "v" "b"); simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
      causal_norm_with "u"; apply DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true; simseqs j.
      causal_norm_with "v"; apply PRIMITIVE_RULE_causal_if_causalle_true; simseqs j.
      causal_norm_with "v"; apply DERIVED_RULE_unhappened_before_eq_if_causalle_true; simseqs j.
      norm_with "b"; apply (PRIMITIVE_RULE_hypothesis_true "b"); simseqs j. }

    norm_with "a"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u"); simseqs j.
    causal_norm_with "u"; apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    causal_norm_with "u"; apply DERIVED_RULE_unhappened_before_eq_if_causalle_true; simseqs j.
    norm_with "a"; apply (PRIMITIVE_RULE_hypothesis_true "a"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_knows_implies_learned_or_gen_implies_gen {eo : EventOrdering} e R H t :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_if_gen t @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_learned_or_gen t @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_gen t @ e).

  Lemma DERIVED_RULE_trusted_knows_implies_learned_or_gen_implies_gen_true :
    forall (eo : EventOrdering) e R H t,
      rule_true (DERIVED_RULE_trusted_knows_implies_learned_or_gen_implies_gen e R H t).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_knows_implies_learned_or_gen_implies_gen_true; simseqs j;
      inst_hyp e0 st'.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_KLD_implies_or {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_knew_or_learns_or_gen d @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_knows_implies_learned_or_gen d @ e).

  Lemma DERIVED_RULE_KLD_implies_or_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_KLD_implies_or e R H d).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_pred_eq_induction_true; simseqs j.

    { inst_hyp e0 st'.
      apply (PRIMITIVE_RULE_cut_true "z" (ASSUMPTION_knew_or_learns_or_gen d @ e0)); simseqs j.
      apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
      apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.

      LOCKelim "z"; try LOCKauto.
      LOCKelim "z".
      { LOCKelim "x"; try LOCKauto.
        LOCKapply (DERIVED_RULE_knew_implies_not_first_true d); try LOCKauto. }
      LOCKelim "z".
      { LOCKintro 0.
        LOCKapply DERIVED_RULE_weaken_local_before_eq_true; try LOCKauto. }
      LOCKelim "z"; try LOCKauto.
      LOCKintro 1.
      LOCKapply DERIVED_RULE_weaken_local_before_eq_true; try LOCKauto. }

    inst_hyp e0 st'.
    LOCKcut "z" (ASSUMPTION_knew_or_learns_or_gen d @ e0).
    LOCKintro "x".
    LOCKintro "w".
    LOCKintro "y".

    LOCKelim "z"; try LOCKauto.

    LOCKelim "z".
    { LOCKapply@ "w" DERIVED_RULE_right_before_over_implies_hyp_true.
      LOCKelim "w".
      { LOCKapply DERIVED_RULE_knew_implies_knows_true; try LOCKauto. }
      LOCKapply@ "w" DERIVED_RULE_right_before_over_or_hyp_true.
      LOCKelim "w".
      { LOCKintro 0.
        LOCKapply DERIVED_RULE_right_before_local_before_eq_implies_true; try LOCKauto. }
      LOCKintro 1.
      LOCKapply DERIVED_RULE_right_before_local_before_eq_implies_true; try LOCKauto. }

    LOCKelim "z".
    { LOCKintro 0.
      LOCKapply DERIVED_RULE_weaken_local_before_eq_true; try LOCKauto. }

    LOCKelim "z"; try LOCKauto.
    { LOCKintro 1.
      LOCKapply DERIVED_RULE_weaken_local_before_eq_true; try LOCKauto. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_KLD_implies_or {eo : EventOrdering} e R H t :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_trusted_knew_or_learns_or_gen t @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_learned_or_gen t @ e).

  Lemma DERIVED_RULE_trusted_KLD_implies_or_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_trusted_KLD_implies_or e R H t).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_KLD_implies_or_true; simseqs j; inst_hyp e0 st'.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_KLD_implies_gen {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_learns_if_gen d @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_knew_or_learns_or_gen d @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_knows_implies_gen d @ e).

  Lemma DERIVED_RULE_KLD_implies_gen_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_KLD_implies_gen e R H d).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_knows_implies_learned_or_gen_implies_gen_true; simseqs j.
    { inst_hyp e0 st. }
    apply DERIVED_RULE_KLD_implies_or_true; simseqs j.
    inst_hyp e1 st.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_KLD_implies_gen {eo : EventOrdering} e R H t :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_if_gen t @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_trusted_knew_or_learns_or_gen t @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_gen t @ e).

  Lemma DERIVED_RULE_trusted_KLD_implies_gen_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_trusted_KLD_implies_gen e R H t).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_KLD_implies_gen_true; simseqs j; inst_hyp e0 st'.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_it_owns_tgens_implies_at t {eo : EventOrdering} e p R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TDISS_OWN t @ e,
       ⟬R⟭ H ⊢ KE_HAS_TOWNER t p @ e]
      (⟬R⟭ H ⊢ KE_AT p @ e).

  Lemma DERIVED_RULE_it_owns_tgens_implies_at_true :
    forall t {eo : EventOrdering} e p R H,
      rule_true (DERIVED_RULE_it_owns_tgens_implies_at t e p R H).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "o" (KE_HAS_TOWNER t p @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_TDISS_OWN t @ e)); simseqs j.
    { norm_with "o"; apply (PRIMITIVE_RULE_thin_true "o"); simseqs j. }
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    apply (DERIVED_RULE_it_owns_owned_implies_at_true (kc_trust2data t)); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
    norm_with "o"; apply (PRIMITIVE_RULE_hypothesis_true "o"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_knowledge_unique
             p c1 c2 {eo : EventOrdering} e1 e2 e R H t1 t2 :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ KE_TKNOWS t1 @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2 @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e,
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique_true :
    forall p c1 c2 {eo : EventOrdering} e1 e2 e R H t1 t2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique p c1 c2 e1 e2 e R H t1 t2).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_trusted_knows_implies_gen t1 @ e1)); simseqs j.
    { apply DERIVED_RULE_trusted_KLD_implies_gen_true; simseqs j.
      { inst_hyp e0 st'.
        apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e0)); simseqs j.
        norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t1); simseqs j.
        norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      inst_hyp e0 st'.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e0)); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t1); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { inst_hyp e st'. }

    norm_with "x"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "u" "x"); simseqs j.

    apply (PRIMITIVE_RULE_cut_true "y" (ASSUMPTION_trusted_knows_implies_gen t2 @ e2)); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
      apply (DERIVED_RULE_remove_first_causal_true); simseqs j.
      apply DERIVED_RULE_trusted_KLD_implies_gen_true; simseqs j.
      { inst_hyp e3 st'.
        apply (PRIMITIVE_RULE_cut_true "y" (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e3)); simseqs j.
        norm_with "y"; apply (PRIMITIVE_RULE_all_trust_elim_true "y" t2); simseqs j.
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      inst_hyp e3 st'.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e3)); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t2); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "y"; apply (PRIMITIVE_RULE_implies_elim_true "y"); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
      apply (DERIVED_RULE_remove_first_causal_true); simseqs j.
      inst_hyp e st'. }

    norm_with "y"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "v" "y"); simseqs j.
    apply (PRIMITIVE_RULE_trust_eq_change_event_true e e3); simseqs j.
    apply (DERIVED_RULE_trusted_disseminate_unique_true c1 c2 p e0 e3); simseqs j;
      try (complete (repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j);
                     repeat (apply DERIVED_RULE_thin_last_true; simseqs j);
                     inst_hyp e4 st)).

    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

    { apply (DERIVED_RULE_it_owns_tgens_implies_at_true t1); simseqs j.
      { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      inst_hyp e3 st.
      apply (PRIMITIVE_RULE_has_owner_change_event_true _ e1); simseqs j.
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j).
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    { apply (DERIVED_RULE_it_owns_tgens_implies_at_true t2); simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      inst_hyp e4 st.
      apply (PRIMITIVE_RULE_has_owner_change_event_true _ e1); simseqs j.
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j).
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
  Qed.


  Definition DERIVED_RULE_trusted_knowledge_unique2
             {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e',
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TKNOWS t1           @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p     @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2           @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p     @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e2,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2    @ e,
          ⟬R⟭ H ⊢ KE_GEN_FOR d1 t1       @ e,
          ⟬R⟭ H ⊢ KE_GEN_FOR d2 t2       @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2  @ e])
      (⟬R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique2_true :
    forall (eo : EventOrdering) e1 e2 e R H p t1 t2 c1 c2 d1 d2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique2 e1 e2 e R H p t1 t2 c1 c2 d1 d2).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TRUST_EQ t1 t2 @ e)); simseqs j.
    { apply (DERIVED_RULE_trusted_knowledge_unique_true p c1 c2 e1 e2); simseqs j; inst_hyp e0 st. }

    apply (PRIMITIVE_RULE_collision_resistant_true t1 t2); simseqs j; try LOCKauto;
      norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j;
        inst_hyp e st.
  Qed.


  Definition DERIVED_RULE_trusted_knowledge_unique3
             {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e',
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TKNOWS t1           @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p     @ e1,
          ⟬R⟭ H ⊢ KE_GEN_FOR d1 t1       @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2           @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p     @ e2,
          ⟬R⟭ H ⊢ KE_GEN_FOR d2 t2       @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e2,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2         @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2  @ e])
      (⟬R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique3_true :
    forall {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique3 e1 e2 e R H p t1 t2 c1 c2 d1 d2).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TRUST_EQ t1 t2 @ e)); simseqs j.
    { apply (DERIVED_RULE_trusted_knowledge_unique_true p c1 c2 e1 e2); simseqs j; inst_hyp e0 st. }

    apply (PRIMITIVE_RULE_collision_resistant_true t1 t2); simseqs j; try LOCKauto;
      norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j;
        inst_hyp e st.
  Qed.


  (************************************************************************************************)
  Definition KE_EX_TRUST_BETWEEN t :=
    KE_EX_ID3 (fun i i1 i2 => KE_ANDS
                                [KE_ID_BEFORE i1,
                                 KE_ID_AFTER i2,
                                 KE_TRUST_HAS_ID t i,
                                 KE_TRUST_DOESNT_HAVE_ID t i1,
                                 KE_ID_LT i1 i,
                                 KE_ID_LE i i2]).

  Definition DERIVED_RULE_disseminate_implies_id_ex
             {eo : EventOrdering} e t R H :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
       ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex @ e,
       ⟬R⟭ H ⊢ KE_TDISS_OWN t @ e]
      (⟬R⟭ H ⊢ KE_EX_TRUST_BETWEEN t @ e).

  Lemma DERIVED_RULE_disseminate_implies_id_ex_true :
    forall {eo : EventOrdering} e t R H,
      rule_true (DERIVED_RULE_disseminate_implies_id_ex
                   e t R H).
  Proof.
    start_proving_derived st.
    LOCKcut "dis" (KE_TDISS_OWN t @ e).
    LOCKcut "new" (ASSUMPTION_generates_new_ex @ e).
    { repeat LOCKclear. }
    LOCKcut "mon" (ASSUMPTION_monotonicity @ e).
    { repeat LOCKclear. }

    LOCKelim "mon".

    { Transparent KE_NO_TGENS.
      LOCKelim "mon".
      Opaque KE_NO_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".

      LOCKelim "new" t.
      LOCKelim "new" c.
      LOCKelim "new" c.

      LOCKelim "new".
      { repeat (LOCKintro; try LOCKauto). }

      LOCKelim "new".
      LOCKelim "new" "new1".
      LOCKelim "new" "new2".
      LOCKelim "new" "new3".
      LOCKelim "new" "new4".

      LOCKcut "p" (KE_ID_LT c0 c0 @ e); try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c); try LOCKauto. }

    { Transparent KE_TGENS.
      LOCKelim "mon".
      LOCKelim "mon".
      Opaque KE_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".
      LOCKelim "mon" "mon3".

      LOCKelim "new" t.
      LOCKelim "new" c.
      LOCKelim "new" c0.

      LOCKelim "new".
      { repeat (LOCKintro; try LOCKauto). }

      LOCKelim "new".
      LOCKelim "new" "new1".
      LOCKelim "new" "new2".
      LOCKelim "new" "new3".
      LOCKelim "new" "new4".

      LOCKintro c1.
      LOCKintro c.
      LOCKintro c0.

      repeat (LOCKintro; try LOCKauto). }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_ex
             u t1 t2 {eo : EventOrdering} e1 e2 e c R H :=
    MkRule1
      (fun e' => [⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity     @ e',
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_generates_new_ex @ e',
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TDISS_OWN t1        @ e1,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TDISS_OWN t2        @ e2,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t1 c   @ e1,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t2 c   @ e2])
      (⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_FALSE @ e).

  Lemma DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_ex_true :
    forall u t1 t2 {eo : EventOrdering} e1 e2 e c R H,
      rule_true (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_ex u t1 t2 e1 e2 e c R H).
  Proof.
    start_proving_derived st.

    LOCKcut "betweena" (KE_EX_TRUST_BETWEEN t1 @ e1).
    { inst_hyp e1 sta.
      apply DERIVED_RULE_disseminate_implies_id_ex_true; simseqs j. }

    LOCKcut "betweenb" (KE_EX_TRUST_BETWEEN t2 @ e2).
    { inst_hyp e2 stb.
      apply DERIVED_RULE_thin_last_true; simseqs j.
      apply DERIVED_RULE_disseminate_implies_id_ex_true; simseqs j. }

    LOCKelim "betweena".
    LOCKelim "betweena".
    LOCKelim "betweena".
    LOCKelim "betweena" "betweena1".
    LOCKelim "betweena" "betweena2".
    LOCKelim "betweena" "betweena3".
    LOCKelim "betweena" "betweena4".
    LOCKelim "betweena" "betweena5".
    LOCKelim "betweena" "betweena6".

    LOCKelim "betweenb".
    LOCKelim "betweenb".
    LOCKelim "betweenb".
    LOCKelim "betweenb" "betweenb1".
    LOCKelim "betweenb" "betweenb2".
    LOCKelim "betweenb" "betweenb3".
    LOCKelim "betweenb" "betweenb4".
    LOCKelim "betweenb" "betweenb5".
    LOCKelim "betweenb" "betweenb6".

    apply (PRIMITIVE_RULE_cut_true "ile1" (KE_ID_LE c2 c4 @ e1)); simseqs j.
    { apply (DERIVED_RULE_id_after_increases2_true u); simseqs j.
      { inst_hyp e0 sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "betweena2"; apply (PRIMITIVE_RULE_hypothesis_true "betweena2"); simseqs j. }
      norm_with "betweenb1"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb1"); simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "ile2" (KE_ID_LE c0 c4 @ e1)); simseqs j.
    { apply (DERIVED_RULE_id_le_trans_true c2); simseqs j.
      { norm_with "betweena6"; apply (PRIMITIVE_RULE_hypothesis_true "betweena6"); simseqs j. }
      norm_with "ile1"; apply (PRIMITIVE_RULE_hypothesis_true "ile1"); simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "thi1" (KE_TRUST_HAS_ID t1 c3 @ e2)); simseqs j.
    { apply (PRIMITIVE_RULE_similar_trust_preserves_true t2 c); simseqs j.
      { apply (PRIMITIVE_RULE_similar_trust_change_event_true _ e); simseqs j.
        inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "betweenb3"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb3"); simseqs j. }
      { apply (PRIMITIVE_RULE_has_id_change_event_true _ e1); simseqs j.
        inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). } }

    apply (PRIMITIVE_RULE_cut_true "thi2" (KE_TRUST_HAS_ID t1 c4 @ e2)); simseqs j.
    { apply (PRIMITIVE_RULE_trust_has_id_preserves_true c0 c3); simseqs j.
      { apply (PRIMITIVE_RULE_has_id_change_event_true _ e1); simseqs j.
        norm_with "betweena3"; apply (PRIMITIVE_RULE_hypothesis_true "betweena3"); simseqs j. }
      { norm_with "thi1"; apply (PRIMITIVE_RULE_hypothesis_true "thi1"); simseqs j. }
      { apply (DERIVED_RULE_id_le_change_event_true _ e1); simseqs j.
        norm_with "ile2"; apply (PRIMITIVE_RULE_hypothesis_true "ile2"); simseqs j. }
      { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
        norm_with "betweenb5"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb5"); simseqs j. } }

    apply (PRIMITIVE_RULE_cut_true "thi3" (KE_TRUST_HAS_ID t2 c4 @ e2)); simseqs j.
    { apply (PRIMITIVE_RULE_similar_trust_preserves_true t1 c); simseqs j.
      { apply (PRIMITIVE_RULE_similar_trust_change_event_true _ e); simseqs j.
        apply PRIMITIVE_RULE_similar_trust_sym_true; simseqs j.
        inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "thi2"; apply (PRIMITIVE_RULE_hypothesis_true "thi2"); simseqs j. }
      { inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). } }

    LOCKelim "betweenb4"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_same_event_same_output_implies_same_input_ex {eo : EventOrdering} e R H t1 t2 c1 c2 :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity       @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex   @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2        @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_same_event_same_output_implies_same_input t1 t2 c1 c2 @ e).

  Lemma DERIVED_RULE_same_event_same_output_implies_same_input_ex_true :
    forall {eo : EventOrdering} e R H t1 t2 c1 c2,
      rule_true (DERIVED_RULE_same_event_same_output_implies_same_input_ex e R H t1 t2 c1 c2).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "z"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "w"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "p"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "q"); simseqs j.
    norm_with "z"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "z"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_split_local_before_eq2_true "u"); simseqs j.

    { causal_norm_with "u"; norm_with "z"; apply (PRIMITIVE_RULE_subst_causal_eq_hyp_true "u" "z"); simseqs j.
      apply (PRIMITIVE_RULE_unicity_true c1 c2); simseqs j.
      { inst_hyp e st.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      { norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
      { norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }
      norm_with "q"; apply (PRIMITIVE_RULE_hypothesis_true "q"); simseqs j. }

    LOCKcut "false" (KE_FALSE @ e); try LOCKauto.
    LOCKapply@ "u" (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_ex_true "u" t1 t2 e0 e e c1); try LOCKauto.
    { inst_hyp e1 st.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    { inst_hyp e1 st.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    { inst_hyp e1 st.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    { LOCKapply (PRIMITIVE_RULE_has_id_change_event_true e0 e); LOCKauto. }

    LOCKapply (PRIMITIVE_RULE_trust_has_id_subst_id_true c2); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_same_input_if_same_id_ex c1 c2 {eo : EventOrdering} e R H t1 t2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity       @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex   @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_TDISS_OWN t1) @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2    @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma DERIVED_RULE_trusted_same_input_if_same_id_ex_true :
    forall c1 c2 {eo : EventOrdering} e R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_trusted_same_input_if_same_id_ex c1 c2 e R H t1 t2).
  Proof.
    start_proving_derived st.
    inst_hyp e st'.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_same_event_same_output_implies_same_input t1 t2 c1 c2 @ e)); simseqs j.
    { apply DERIVED_RULE_same_event_same_output_implies_same_input_ex_true; simseqs j; inst_hyp e0 st. }

    apply DERIVED_RULE_implies_elim_true; simseqs j; try LOCKauto.
    repeat (apply PRIMITIVE_RULE_and_intro_true; simseqs j;[]); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_disseminate_unique_ex
             c1 c2 n {eo : EventOrdering} e1 e2 R H (t1 t2 : kc_trust) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity       @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex   @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t1 @ e1,
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
          ⟬R⟭ H ⊢ KE_AT n @ e1,
          ⟬R⟭ H ⊢ KE_AT n @ e2,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e2,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2    @ e2])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e2).

  Lemma DERIVED_RULE_trusted_disseminate_unique_ex_true :
    forall c1 c2 n {eo : EventOrdering} e1 e2 R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_trusted_disseminate_unique_ex c1 c2 n e1 e2 R H t1 t2).
  Proof.
    start_proving_derived st.
    inst_hyp e1 st'.

    apply (PRIMITIVE_RULE_tri_if_towned_true "u" n e1 e2); simseqs j.

    { (* e1 = e2 *)
      apply (DERIVED_RULE_trusted_same_input_if_same_id_ex_true c1 c2); simseqs j;
        try (complete (inst_hyp e st; apply DERIVED_RULE_remove_first_causal_true; simseqs j)).

      inst_hyp e st.
      apply DERIVED_RULE_weaken_local_before_eq_true; simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

    { (* (e1) ⊏ (e2) *)
      apply (DERIVED_RULE_trusted_same_input_if_same_id_ex_true c1 c2); simseqs j;
        try (complete (inst_hyp e st; apply DERIVED_RULE_remove_first_causal_true; simseqs j)).

      inst_hyp e st.
      causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causal_lt_true "u"); simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

    { (* (e2) ⊏ (e1) *)
      apply PRIMITIVE_RULE_trust_eq_sym_true; simseqs j.
      apply (PRIMITIVE_RULE_trust_eq_change_event_true e2 e1); simseqs j.
      apply (DERIVED_RULE_trusted_same_input_if_same_id_ex_true c2 c1); simseqs j;
        try (complete (inst_hyp e st; apply DERIVED_RULE_remove_first_causal_true; simseqs j)).

      { inst_hyp e st.
        causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causal_lt_true "u"); simseqs j.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

      { inst_hyp e st.
        apply PRIMITIVE_RULE_id_eq_sym_true; simseqs j.
        apply (DERIVED_RULE_remove_first_causal_true); simseqs j. }

      { apply PRIMITIVE_RULE_similar_trust_sym_true; simseqs j.
        apply (PRIMITIVE_RULE_similar_trust_change_event_true _ e2); simseqs j.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j. } }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_knowledge_unique_ex
             p c1 c2 {eo : EventOrdering} e1 e2 e R H t1 t2 :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ KE_TKNOWS t1          @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p    @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2          @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p    @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e,
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen         @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity                               @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex                           @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique                         @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2                                @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2                                        @ e])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique_ex_true :
    forall p c1 c2 {eo : EventOrdering} e1 e2 e R H t1 t2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique_ex p c1 c2 e1 e2 e R H t1 t2).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_trusted_knows_implies_gen t1 @ e1)); simseqs j.
    { apply DERIVED_RULE_trusted_KLD_implies_gen_true; simseqs j.
      { inst_hyp e0 st'.
        apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e0)); simseqs j.
        norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t1); simseqs j.
        norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      inst_hyp e0 st'.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e0)); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t1); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { inst_hyp e st'. }

    norm_with "x"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "u" "x"); simseqs j.

    apply (PRIMITIVE_RULE_cut_true "y" (ASSUMPTION_trusted_knows_implies_gen t2 @ e2)); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
      apply (DERIVED_RULE_remove_first_causal_true); simseqs j.
      apply DERIVED_RULE_trusted_KLD_implies_gen_true; simseqs j.
      { inst_hyp e3 st'.
        apply (PRIMITIVE_RULE_cut_true "y" (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e3)); simseqs j.
        norm_with "y"; apply (PRIMITIVE_RULE_all_trust_elim_true "y" t2); simseqs j.
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      inst_hyp e3 st'.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e3)); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t2); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "y"; apply (PRIMITIVE_RULE_implies_elim_true "y"); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
      apply (DERIVED_RULE_remove_first_causal_true); simseqs j.
      inst_hyp e st'. }

    norm_with "y"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "v" "y"); simseqs j.
    apply (PRIMITIVE_RULE_trust_eq_change_event_true e e3); simseqs j.

    apply (DERIVED_RULE_trusted_disseminate_unique_ex_true c1 c2 p e0 e3); simseqs j;
      try (complete (repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j);
                     repeat (apply DERIVED_RULE_thin_last_true; simseqs j);
                     inst_hyp e4 st)).

    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

    { apply (DERIVED_RULE_it_owns_tgens_implies_at_true t1); simseqs j.
      { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      inst_hyp e4 st.
      apply (PRIMITIVE_RULE_has_owner_change_event_true _ e1); simseqs j.
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j).
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    { apply (DERIVED_RULE_it_owns_tgens_implies_at_true t2); simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      inst_hyp e4 st.
      apply (PRIMITIVE_RULE_has_owner_change_event_true _ e1); simseqs j.
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j).
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
  Qed.

  Definition DERIVED_RULE_trusted_knowledge_unique2_ex
             {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen         @ e',
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity                               @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex                           @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique                         @ e',
          ⟬R⟭ H ⊢ KE_TKNOWS t1           @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p     @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2           @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p     @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e2,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2         @ e,
          ⟬R⟭ H ⊢ KE_GEN_FOR d1 t1       @ e,
          ⟬R⟭ H ⊢ KE_GEN_FOR d2 t2       @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2  @ e])
      (⟬R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique2_ex_true :
    forall (eo : EventOrdering) e1 e2 e R H p t1 t2 c1 c2 d1 d2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique2_ex e1 e2 e R H p t1 t2 c1 c2 d1 d2).
  Proof.
    introv st; simpl in *.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TRUST_EQ t1 t2 @ e)); simseqs j.
    { apply (DERIVED_RULE_trusted_knowledge_unique_ex_true p c1 c2 e1 e2); simseqs j;inst_hyp e0 st. }

    apply (PRIMITIVE_RULE_collision_resistant_true t1 t2); simseqs j; try LOCKauto;
      norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j;
        inst_hyp e st.
  Qed.

  Definition DERIVED_RULE_trusted_knowledge_unique3_ex
             {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen         @ e',
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity                               @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex                           @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique                         @ e',
          ⟬R⟭ H ⊢ KE_TKNOWS t1           @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p     @ e1,
          ⟬R⟭ H ⊢ KE_GEN_FOR d1 t1       @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2           @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p     @ e2,
          ⟬R⟭ H ⊢ KE_GEN_FOR d2 t2       @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e2,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2  @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2         @ e])
      (⟬R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique3_ex_true :
    forall {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique3_ex e1 e2 e R H p t1 t2 c1 c2 d1 d2).
  Proof.
    introv st; simpl in *.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TRUST_EQ t1 t2 @ e)); simseqs j.
    { apply (DERIVED_RULE_trusted_knowledge_unique_ex_true p c1 c2 e1 e2); simseqs j; inst_hyp e0 st. }

    apply (PRIMITIVE_RULE_collision_resistant_true t1 t2); simseqs j; try LOCKauto;
      norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j;
        inst_hyp e st.
   Qed.

End CalculusSM_derived1.
