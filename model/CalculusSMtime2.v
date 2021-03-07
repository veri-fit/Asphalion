Require Export CalculusSMtime.


Section CalculusSMtime2.

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


  (***********************************************************)
  Definition DERIVED_RULE_local_after_elim u x {eo : EventOrdering} e R H J a (t : PosDTime) b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e ¦□t¦ e') :: R⟭ H • (x › a @ e') ⊕ J ⊢ b])
      (⟬R⟭ H • (x › KE_LOCAL_AFTER a (Some t) @ e) ⊕ J ⊢ b).

  Lemma DERIVED_RULE_local_after_elim_true :
    forall u x {eo : EventOrdering} e R H J a t b,
      rule_true (DERIVED_RULE_local_after_elim u x e R H J a t b).
  Proof.
    start_proving_derived st.
    LOCKelim x.
    LOCKelim x "x".
    LOCKapply@ x (PRIMITIVE_RULE_happened_after_elim_true u).
    LOCKelim x "y".
    inst_hyp e0 hyp.
    LOCKapply@ u (PRIMITIVE_RULE_at_implies_local_time_true u n); try LOCKauto.
    LOCKclear "x" "y".
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_correct_after_implies_correct {eo : EventOrdering} e R H :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_CORRECT_AFTER @ e]
      (⟬ R ⟭ H ⊢ KE_CORRECT @ e).

  Lemma DERIVED_RULE_correct_after_implies_correct_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_correct_after_implies_correct e R H).
  Proof.
    start_proving_derived st.
    LOCKcut "c" (KE_CORRECT_AFTER @ e).
    LOCKelim "c" "c'"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_correct_after_implies_correct_local u t {eo : EventOrdering} e e' R Q H :=
    MkRule0
      [⟬ R ++ (u ⋈ e ¦□t¦ e') :: Q ⟭ H ⊢ KE_CORRECT_AFTER @ e]
      (⟬ R ++ (u ⋈ e ¦□t¦ e') :: Q ⟭ H ⊢ KE_CORRECT @ e').

  Lemma DERIVED_RULE_correct_after_implies_correct_local_true :
    forall u t {eo : EventOrdering} e e' R Q H,
      rule_true (DERIVED_RULE_correct_after_implies_correct_local u t e e' R Q H).
  Proof.
    start_proving_derived st.
    LOCKcut "c" (KE_CORRECT_AFTER @ e).
    LOCKelim "c" "c1"; try LOCKauto.
    LOCKelim "c1".
    LOCKelim "c1" "c2".
    LOCKapply@ u PRIMITIVE_RULE_weaken_local_before_time_true.
    LOCKcut "at" (KE_AT n @ e').
    { LOCKapply@ u PRIMITIVE_RULE_at_change_local_true; try LOCKauto. }
    LOCKapply@ u PRIMITIVE_RULE_local_if_causal_true.
    LOCKapply@ u "c1" PRIMITIVE_RULE_forall_after_elim_true.
    LOCKelim "c1"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_payload_eq_refl {eo : EventOrdering} e R H d :=
    MkRule0
      []
      (⟬ R ⟭ H ⊢ KE_PAYLOAD_EQ d d @ e).

  Lemma DERIVED_RULE_payload_eq_refl_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_payload_eq_refl e R H d).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_EX_DATA (fun p => KE_HAS_PAYLOAD d p) @ e).
    { LOCKapply PRIMITIVE_RULE_ex_payload_true. }
    LOCKelim "h".
    LOCKintros d0 d0;
      try LOCKauto;
      try LOCKapply PRIMITIVE_RULE_data_eq_refl_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knows_at_least_vouchers_implies_knows v k {eo : EventOrdering} e R H d :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_KNOWS_AT_LEAST_VOUCHERS d v k @ e]
      (⟬ R ⟭ H ⊢ KE_KNOWS d @ e).

  Lemma DERIVED_RULE_knows_at_least_vouchers_implies_knows_true :
    forall v k {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_knows_at_least_vouchers_implies_knows v k e R H d).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_KNOWS_AT_LEAST_VOUCHERS d v k @ e); try LOCKauto.
    LOCKelim "h" "h'"; LOCKelim "h'" "h''"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knows_ex_at_least_vouchers_implies_knows k {eo : EventOrdering} e R H d :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_KNOWS_EX_AT_LEAST_VOUCHERS d k @ e]
      (⟬ R ⟭ H ⊢ KE_KNOWS d @ e).

  Lemma DERIVED_RULE_knows_ex_at_least_vouchers_implies_knows_true :
    forall k {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_knows_ex_at_least_vouchers_implies_knows k e R H d).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_KNOWS_EX_AT_LEAST_VOUCHERS d k @ e); try LOCKauto.
    LOCKelim "h".
    LOCKapply (DERIVED_RULE_knows_at_least_vouchers_implies_knows_true v k); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knew_at_least_vouchers_implies_knows v k {eo : EventOrdering} e R H d :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_KNEW_AT_LEAST_VOUCHERS d v k @ e]
      (⟬ R ⟭ H ⊢ KE_KNEW d @ e).

  Lemma DERIVED_RULE_knew_at_least_vouchers_implies_knows_true :
    forall v k {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_knew_at_least_vouchers_implies_knows v k e R H d).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_KNEW_AT_LEAST_VOUCHERS d v k @ e); try LOCKauto.
    LOCKelim "h" "h'"; LOCKelim "h'" "h''"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knew_ex_at_least_vouchers_implies_knows k {eo : EventOrdering} e R H d :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_KNEW_EX_AT_LEAST_VOUCHERS d k @ e]
      (⟬ R ⟭ H ⊢ KE_KNEW d @ e).

  Lemma DERIVED_RULE_knew_ex_at_least_vouchers_implies_knows_true :
    forall k {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_knew_ex_at_least_vouchers_implies_knows k e R H d).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_KNEW_EX_AT_LEAST_VOUCHERS d k @ e); try LOCKauto.
    LOCKelim "h".
    LOCKapply (DERIVED_RULE_knew_at_least_vouchers_implies_knows_true v k); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_sim_data_refl {eo : EventOrdering} e R H d :=
    MkRule0
      []
      (⟬ R ⟭ H ⊢ KE_SIM_DATA d d @ e).

  Lemma DERIVED_RULE_sim_data_refl_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_sim_data_refl e R H d).
  Proof.
    start_proving_derived st.
    LOCKintros;
      try LOCKapply PRIMITIVE_RULE_same_cat_refl_true;
      try LOCKapply DERIVED_RULE_payload_eq_refl_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_sim_data_sym {eo : EventOrdering} e R H d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_SIM_DATA d1 d2 @ e]
      (⟬ R ⟭ H ⊢ KE_SIM_DATA d2 d1 @ e).

  Lemma DERIVED_RULE_sim_data_sym_true :
    forall {eo : EventOrdering} e R H d1 d2,
      rule_true (DERIVED_RULE_sim_data_sym e R H d1 d2).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_SIM_DATA d1 d2 @ e).
    LOCKelims "h" 0.
    LOCKintros.
    { LOCKapply PRIMITIVE_RULE_same_cat_sym_true; try LOCKauto. }
    LOCKintros d0 d; try LOCKauto.
    LOCKapply PRIMITIVE_RULE_data_eq_sym_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_sim_data_change_event {eo : EventOrdering} e1 e2 R H d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_SIM_DATA d1 d2 @ e2]
      (⟬ R ⟭ H ⊢ KE_SIM_DATA d1 d2 @ e1).

  Lemma DERIVED_RULE_sim_data_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H d1 d2,
      rule_true (DERIVED_RULE_sim_data_change_event e1 e2 R H d1 d2).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_SIM_DATA d1 d2 @ e2).
    LOCKelims "h" 0.
    LOCKintros.
    { LOCKapply (PRIMITIVE_RULE_same_cat_change_event_true e1 e2); try LOCKauto. }
    LOCKintros d d0;
      try LOCKapply (PRIMITIVE_RULE_has_payload_change_event_true e1 e2);
      try LOCKapply (PRIMITIVE_RULE_data_eq_change_event_true e1 e2);
      try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_sim_data_trans {eo : EventOrdering} e R H d1 d2 d3 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_SIM_DATA d1 d2 @ e,
       ⟬ R ⟭ H ⊢ KE_SIM_DATA d2 d3 @ e]
      (⟬ R ⟭ H ⊢ KE_SIM_DATA d1 d3 @ e).

  Lemma DERIVED_RULE_sim_data_trans_true :
    forall d2 {eo : EventOrdering} e R H d1 d3,
      rule_true (DERIVED_RULE_sim_data_trans e R H d1 d2 d3).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_SIM_DATA d1 d2 @ e).
    LOCKcut "q" (KE_SIM_DATA d2 d3 @ e).
    { repeat LOCKclear. }
    LOCKelims "h" 0.
    LOCKelims "q" 0.
    LOCKintros.
    { LOCKapply (PRIMITIVE_RULE_same_cat_trans_true d2); try LOCKauto. }
    LOCKintros d d5; try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_data_eq_trans_true d0); try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_data_eq_trans_true d4); try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_has_payload_implies_eq_true d2); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_payload_eq_change_event {eo : EventOrdering} e1 e2 R H d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_PAYLOAD_EQ d1 d2 @ e2]
      (⟬ R ⟭ H ⊢ KE_PAYLOAD_EQ d1 d2 @ e1).

  Lemma DERIVED_RULE_payload_eq_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H d1 d2,
      rule_true (DERIVED_RULE_payload_eq_change_event e1 e2 R H d1 d2).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_PAYLOAD_EQ d1 d2 @ e2).
    LOCKelims "h" 0.
    LOCKintros d d0;
      try LOCKapply (PRIMITIVE_RULE_has_payload_change_event_true e1 e2);
      try LOCKapply (PRIMITIVE_RULE_data_eq_change_event_true e1 e2);
      try LOCKauto.
  Qed.


  (************************************************************************************************)
  (* This should be derivable from specs *)
  Definition vouchers_increase :=
    KE_ALL_DATA
      (fun d1 =>
         KE_ALL_VOUCHERS
           (fun v1 =>
              KE_IMPLIES
                (KE_KNEW_VOUCHED d1 v1)
                (KE_EX_DATA
                   (fun d2 =>
                      KE_EX_VOUCHERS
                        (fun v2 =>
                           KE_ANDS
                             [KE_KNOWS_VOUCHED d2 (kc_add_vouchers v1 v2),
                              KE_SIM_DATA d1 d2]))))).

  (* This should be derivable from specs *)
  Definition knows_step :=
    KE_ALL_DATA
      (fun d =>
         KE_IMPLIES
           (KE_KNOWS d)
           (KE_OR
              (* We didn't know about a similar piece of data right before *)
              (KE_NOT (KE_EX_DATA (fun d' => KE_AND (KE_KNEW d') (KE_SIM_DATA d d'))))
              (* or we knew about a similar piece of data, and we added more vouchers *)
              (KE_EX_DATA
                 (fun d' =>
                    KE_EX_VOUCHERS
                      (fun v' =>
                         KE_ANDS
                           [KE_KNEW_VOUCHED d' v',
                            KE_SIM_DATA d d',
                            KE_EX_VOUCHERS (fun v => KE_VOUCHED d (kc_add_vouchers v' v))]))))).

  Definition ex_sim_knows_ex_at_least_vouchers d k :=
    KE_EX_DATA
      (fun d' =>
         KE_AND
           (KE_KNOWS_EX_AT_LEAST_VOUCHERS d' k)
           (KE_SIM_DATA d d')).

  Definition dec_ex_sim_knows_ex_at_least_vouchers k :=
    KE_ALL_DATA (fun d => KE_DEC (ex_sim_knows_ex_at_least_vouchers d k)).

  Definition ex_sim_knew_ex_at_least_vouchers d k :=
    KE_EX_DATA
      (fun d' =>
         KE_AND
           (KE_KNEW_EX_AT_LEAST_VOUCHERS d' k)
           (KE_SIM_DATA d d')).

  Definition dec_ex_sim_knew_ex_at_least_vouchers k :=
    KE_ALL_DATA (fun d => KE_DEC (ex_sim_knew_ex_at_least_vouchers d k)).

  Definition known_vouchers_increase k :=
    KE_ALL_DATA
      (fun d =>
         KE_IMPLIES
           (KE_KNOWS_EX_AT_LEAST_VOUCHERS d k)
           (KE_LOCAL_BEFORE_EQ
              (KE_AND
                 (ex_sim_knows_ex_at_least_vouchers d k)
                 (KE_NOT (ex_sim_knew_ex_at_least_vouchers d k))))).


  (************************************************************************************************)
  Definition DERIVED_RULE_sim_data_preserves_ex_sim_knows_ex_at_least_vouchers {eo : EventOrdering} e R H d1 d2 k :=
    MkRule0
      [ ⟬ R ⟭ H ⊢ KE_SIM_DATA d1 d2 @ e,
        ⟬ R ⟭ H ⊢ ex_sim_knows_ex_at_least_vouchers d2 k @ e]
      (⟬ R ⟭ H ⊢ ex_sim_knows_ex_at_least_vouchers d1 k @ e).

  Lemma DERIVED_RULE_sim_data_preserves_ex_sim_knows_ex_at_least_vouchers_true :
    forall d2 {eo : EventOrdering} e R H d1 k,
      rule_true (DERIVED_RULE_sim_data_preserves_ex_sim_knows_ex_at_least_vouchers e R H d1 d2 k).
  Proof.
    start_proving_derived st.

    LOCKcut "sim" (KE_SIM_DATA d1 d2 @ e).

    LOCKcut "h" (ex_sim_knows_ex_at_least_vouchers d2 k @ e).
    { repeat LOCKclear. }

    LOCKelim "h".
    LOCKelim "h" "h'".
    LOCKintro d; try LOCKauto.
    LOCKintro; try LOCKauto.

    LOCKapply (DERIVED_RULE_sim_data_trans_true d2); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_sim_data_preserves_ex_sim_knew_ex_at_least_vouchers {eo : EventOrdering} e R H d1 d2 k :=
    MkRule0
      [ ⟬ R ⟭ H ⊢ KE_SIM_DATA d1 d2 @ e,
        ⟬ R ⟭ H ⊢ ex_sim_knew_ex_at_least_vouchers d2 k @ e]
      (⟬ R ⟭ H ⊢ ex_sim_knew_ex_at_least_vouchers d1 k @ e).

  Lemma DERIVED_RULE_sim_data_preserves_ex_sim_knew_ex_at_least_vouchers_true :
    forall d2 {eo : EventOrdering} e R H d1 k,
      rule_true (DERIVED_RULE_sim_data_preserves_ex_sim_knew_ex_at_least_vouchers e R H d1 d2 k).
  Proof.
    start_proving_derived st.

    LOCKcut "sim" (KE_SIM_DATA d1 d2 @ e).

    LOCKcut "h" (ex_sim_knew_ex_at_least_vouchers d2 k @ e).
    { repeat LOCKclear. }

    LOCKelim "h".
    LOCKelim "h" "h'".
    LOCKintro d; try LOCKauto.
    LOCKintro; try LOCKauto.

    LOCKapply (DERIVED_RULE_sim_data_trans_true d2); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_ex_sim_knows_ex_at_least_vouchers u {eo : EventOrdering} e1 e2 R Q H d k :=
    MkRule0
      [⟬ R ++ (u ⋈ e1 ⋄ e2) :: Q ⟭ H ⊢ ex_sim_knew_ex_at_least_vouchers d k @ e2]
      (⟬ R ++ (u ⋈ e1 ⋄ e2) :: Q ⟭ H ⊢ ex_sim_knows_ex_at_least_vouchers d k @ e1).

  Lemma DERIVED_RULE_ex_sim_knows_ex_at_least_vouchers_true :
    forall u {eo : EventOrdering} e1 e2 R Q H d k,
      rule_true (DERIVED_RULE_ex_sim_knows_ex_at_least_vouchers u e1 e2 R Q H d k).
  Proof.
    start_proving_derived st.
    LOCKcut "d" (ex_sim_knew_ex_at_least_vouchers d k @ e2).

    LOCKelims "d" 0.
    LOCKintros d0; try LOCKauto.
    { LOCKelims "d01" 0.
      LOCKelims "d0101" 0.
      LOCKintros v; try LOCKauto.
      { LOCKapply@ u "d010101" DERIVED_RULE_right_before_elim_true; try LOCKauto. }
      { LOCKapply (PRIMITIVE_RULE_vouched_change_event_true e1 e2); try LOCKauto. }
      LOCKapply (PRIMITIVE_RULE_at_least_vouchers_change_event_true e1 e2); try LOCKauto. }
    { LOCKapply (PRIMITIVE_RULE_same_cat_change_event_true e1 e2); try LOCKauto. }
    { LOCKapply (DERIVED_RULE_payload_eq_change_event_true e1 e2); try LOCKauto.
      LOCKintros d1 d2; try LOCKauto. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_ex_sim_knew_ex_at_least_vouchers u {eo : EventOrdering} e1 e2 R Q H d k :=
    MkRule0
      [⟬ R ++ (u ⋈ e1 ⋄ e2) :: Q ⟭ H ⊢ ex_sim_knows_ex_at_least_vouchers d k @ e1]
      (⟬ R ++ (u ⋈ e1 ⋄ e2) :: Q ⟭ H ⊢ ex_sim_knew_ex_at_least_vouchers d k @ e2).

  Lemma DERIVED_RULE_ex_sim_knew_ex_at_least_vouchers_true :
    forall u {eo : EventOrdering} e1 e2 R Q H d k,
      rule_true (DERIVED_RULE_ex_sim_knew_ex_at_least_vouchers u e1 e2 R Q H d k).
  Proof.
    start_proving_derived st.
    LOCKcut "q" (ex_sim_knows_ex_at_least_vouchers d k @ e1).

    LOCKelims "q" 0.
    LOCKintros d0; try LOCKauto.
    { LOCKelims "q01" 0.
      LOCKelims "q0101" 0.
      LOCKintros v; try LOCKauto.
      { LOCKapply@ u PRIMITIVE_RULE_unright_before_if_causal_true; try LOCKauto. }
      { LOCKapply (PRIMITIVE_RULE_vouched_change_event_true e2 e1); try LOCKauto. }
      LOCKapply (PRIMITIVE_RULE_at_least_vouchers_change_event_true e2 e1); try LOCKauto. }
    { LOCKapply (PRIMITIVE_RULE_same_cat_change_event_true e2 e1); try LOCKauto. }
    { LOCKapply (DERIVED_RULE_payload_eq_change_event_true e2 e1); try LOCKauto.
      LOCKintros d1 d2; try LOCKauto. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_dec_ex_sim_knows_ex_at_least_vouchers u {eo : EventOrdering} e1 e2 R Q H k :=
    MkRule0
      [⟬ R ++ (u ⋈ e1 ⋄ e2) :: Q ⟭ H ⊢ dec_ex_sim_knew_ex_at_least_vouchers k @ e2]
      (⟬ R ++ (u ⋈ e1 ⋄ e2) :: Q ⟭ H ⊢ dec_ex_sim_knows_ex_at_least_vouchers k @ e1).

  Lemma DERIVED_RULE_dec_ex_sim_knows_ex_at_least_vouchers_true :
    forall u {eo : EventOrdering} e1 e2 R Q H k,
      rule_true (DERIVED_RULE_dec_ex_sim_knows_ex_at_least_vouchers u e1 e2 R Q H k).
  Proof.
    start_proving_derived st.
    LOCKcut "d" (dec_ex_sim_knew_ex_at_least_vouchers k @ e2).
    LOCKintro.
    LOCKelim "d" d.
    LOCKelim "d".

    { LOCKintro 0.
      LOCKapply@ u DERIVED_RULE_ex_sim_knows_ex_at_least_vouchers_true; try LOCKauto. }

    { LOCKintros 1 "q"; LOCKelim "d"; try LOCKauto.
      LOCKapply@ u DERIVED_RULE_ex_sim_knew_ex_at_least_vouchers_true; try LOCKauto. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_dec_ex_sim_knew_ex_at_least_vouchers k {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' => [⟬ R ⟭ H ⊢ dec_ex_sim_knows_ex_at_least_vouchers k @ e'])
      (⟬ R ⟭ H ⊢ dec_ex_sim_knew_ex_at_least_vouchers k @ e).

  Lemma DERIVED_RULE_dec_ex_sim_knew_ex_at_least_vouchers_true :
    forall k {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_dec_ex_sim_knew_ex_at_least_vouchers k e R H).
  Proof.
    start_proving_derived st.
    LOCKcut "d" (KE_OR KE_FIRST KE_NOT_FIRST @ e).
    { LOCKapply PRIMITIVE_RULE_first_dec_true. }
    LOCKelim "d".

    { LOCKintros 1 "h".
      LOCKelims "h" 0.
      LOCKelims "h01" 0.
      LOCKelims "h0101" 0.
      LOCKcut "nf" (KE_NOT KE_FIRST @e).
      { LOCKapply DERIVED_RULE_not_first_implies_not_first_true.
        LOCKapply (DERIVED_RULE_knew_implies_not_first_true d0); try LOCKauto. }
      LOCKelim "nf"; try LOCKauto. }

    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e); try LOCKauto.
    LOCKcut "h" (dec_ex_sim_knows_ex_at_least_vouchers k @ local_pred_n e).
    { inst_hyp (local_pred_n e) hyp; LOCKclear "u" "d". }

    LOCKintros.
    LOCKelim "h" d.
    LOCKelim "h".

    { LOCKintro 0.
      LOCKapply@ "u" DERIVED_RULE_ex_sim_knew_ex_at_least_vouchers_true; try LOCKauto. }

    { LOCKintros 1 "q"; LOCKelim "h"; try LOCKauto.
      LOCKapply@ "u" DERIVED_RULE_ex_sim_knows_ex_at_least_vouchers_true; try LOCKauto. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_known_vouchers_increase k {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' => [⟬ R ⟭ H ⊢ dec_ex_sim_knows_ex_at_least_vouchers k @ e'])
      (⟬ R ⟭ H ⊢ known_vouchers_increase k @ e).

  Lemma DERIVED_RULE_known_vouchers_increase_true :
    forall k {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_known_vouchers_increase k e R H).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_pred_induction_true "u").

    { LOCKintros "fst" "kn".
      LOCKelim "kn".
      LOCKapply DERIVED_RULE_weaken_local_before_eq_true.
      LOCKintros.

      { LOCKintro d; LOCKintros.
        { LOCKintro v; try LOCKauto. }
        { LOCKapply PRIMITIVE_RULE_same_cat_refl_true. }
        { LOCKapply DERIVED_RULE_payload_eq_refl_true. } }

      LOCKintro "q".
      LOCKelims "q" 0.
      LOCKelims "q01" 0.
      LOCKelims "q0101" 0.
      LOCKcut "nf" (KE_NOT KE_FIRST @e0).
      { LOCKapply DERIVED_RULE_not_first_implies_not_first_true.
        LOCKapply (DERIVED_RULE_knew_implies_not_first_true d0); try LOCKauto. }
      LOCKelim "nf"; try LOCKauto. }

    LOCKintros "ind" "kn".
    LOCKelim "kn".
    LOCKapply@ "ind" (PRIMITIVE_RULE_unright_before_hyp_if_causal_true "v").
    LOCKcut "d" (dec_ex_sim_knows_ex_at_least_vouchers k @ e1).
    { LOCKclearall; inst_hyp e1 hyp. }

    LOCKelim "d" d.
    LOCKelim "d".

    { LOCKelim "d".
      LOCKelim "d" "d0".
      LOCKelim "d0".
      LOCKelim "ind" d0.
      LOCKelim "ind".
      { LOCKintro v0; try LOCKauto. }

      LOCKapply@ "ind" (DERIVED_RULE_unlocal_before_eq_hyp_true "w").
      LOCKapply@ "v" PRIMITIVE_RULE_direct_pred_if_local_pred_true.
      LOCKapply@ "v" PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ "v" DERIVED_RULE_unlocal_before_eq_if_causal_trans_true.
      LOCKapply@ "w" DERIVED_RULE_unlocal_before_eq_if_causalle_true.

      LOCKelim "ind" "ind'".
      LOCKintro.

      { LOCKapply (DERIVED_RULE_sim_data_preserves_ex_sim_knows_ex_at_least_vouchers_true d0);
          try LOCKapply@ "ind'" PRIMITIVE_RULE_hypothesis_true.
        LOCKapply (DERIVED_RULE_sim_data_change_event_true e2 e1); try LOCKauto. }

      LOCKintro "q"; LOCKelim "ind"; try LOCKauto.
      LOCKapply (DERIVED_RULE_sim_data_preserves_ex_sim_knew_ex_at_least_vouchers_true d); try LOCKauto.
      LOCKapply DERIVED_RULE_sim_data_sym_true.
      LOCKapply (DERIVED_RULE_sim_data_change_event_true e2 e1); try LOCKauto. }

    LOCKapply DERIVED_RULE_weaken_local_before_eq_true.
    LOCKintro.

    { LOCKintro d; LOCKintro; try LOCKauto.
      { LOCKintro v; try LOCKauto. }
      LOCKapply DERIVED_RULE_sim_data_refl_true. }

    LOCKintro "q"; LOCKelim "d"; try LOCKauto.
    LOCKapply@ "v" DERIVED_RULE_ex_sim_knows_ex_at_least_vouchers_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_bi_if_same_loc u n {eo : EventOrdering} e1 e2 R H a :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_AT n @ e1,
       ⟬ R ⟭ H ⊢ KE_AT n @ e2,
       ⟬ (u ⋈ e2 □ e1) :: R ⟭ H ⊢ a,
       ⟬ (u ⋈ e1 ■ e2) :: R ⟭ H ⊢ a]
      (⟬ R ⟭ H ⊢ a).

  Lemma DERIVED_RULE_bi_if_same_loc_true :
    forall u n {eo : EventOrdering} e1 e2 R H a,
      rule_true (DERIVED_RULE_bi_if_same_loc u n e1 e2 R H a).
  Proof.
    start_proving_derived st; simpl in *.
    LOCKapply (PRIMITIVE_RULE_tri_if_towned_true u n e1 e2).
    { LOCKapply@ u PRIMITIVE_RULE_localle_if_eq_true. }
    LOCKapply@ u PRIMITIVE_RULE_local_if_localle_true.
  Qed.


  (************************************************************************************************)
  Definition perfect_memory_step :=
    KE_ALL_DATA (fun d => KE_IMPLIES (KE_KNEW d) (KE_KNOWS d)).

  Definition perfect_memory :=
    KE_ALL_DATA (fun d => KE_IMPLIES (KE_LOCAL_BEFORE_EQ (KE_KNOWS d)) (KE_KNOWS d)).


  (************************************************************************************************)
  Definition DERIVED_RULE_perfect_memory {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' => [⟬R⟭ H ⊢ perfect_memory_step @ e'])
      (⟬R⟭ H ⊢ perfect_memory @ e).

  Lemma DERIVED_RULE_perfect_memory_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_perfect_memory e R H).
  Proof.
    start_proving_derived st.
    LOCKintro.
    LOCKapply (PRIMITIVE_RULE_pred_induction_true "v").

    { LOCKintros "f" "b".
      LOCKapply@ "b" (DERIVED_RULE_unlocal_before_eq_hyp_true "u").
      LOCKapply@ "u" DERIVED_RULE_causalle_is_equal_if_first_true; try LOCKauto.
      LOCKapply@ "u" PRIMITIVE_RULE_subst_causal_eq_concl_true; try LOCKauto. }

    LOCKintros "ind" "b".
    LOCKelim "b";[|LOCKelims "b" 0; try LOCKauto];[].

    LOCKapply@ "b" (DERIVED_RULE_unlocal_before_hyp_true "u").
    LOCKapply@ "u" (PRIMITIVE_RULE_split_local_before_true "u" "w").

    { inst_hyp e0 hyp.
      LOCKcut "step" (perfect_memory_step @ e0).
      { LOCKclearall. }
      LOCKelim "step" d.
      LOCKelim "step"; try LOCKauto.
      LOCKapply@ "u" PRIMITIVE_RULE_unright_before_if_causal_true; try LOCKauto. }

    LOCKapply@ "w" "ind" DERIVED_RULE_right_before_elim_true.
    LOCKelim "ind".

    { LOCKintro 0.
      LOCKapply@ "u" DERIVED_RULE_unlocal_before_if_causal_true; try LOCKauto. }

    inst_hyp e0 hyp.
    LOCKcut "step" (perfect_memory_step @ e0).
    { LOCKclearall. }
    LOCKelim "step" d.
    LOCKelim "step"; try LOCKauto.
    LOCKapply@ "w" PRIMITIVE_RULE_unright_before_if_causal_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_payload_eq_trans {eo : EventOrdering} e R H d1 d2 d3 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_PAYLOAD_EQ d1 d2 @ e,
       ⟬ R ⟭ H ⊢ KE_PAYLOAD_EQ d2 d3 @ e]
      (⟬ R ⟭ H ⊢ KE_PAYLOAD_EQ d1 d3 @ e).

  Lemma DERIVED_RULE_payload_eq_trans_true :
    forall d2 {eo : EventOrdering} e R H d1 d3,
      rule_true (DERIVED_RULE_payload_eq_trans e R H d1 d2 d3).
  Proof.
    start_proving_derived st; auto.
    LOCKcut "h" (KE_PAYLOAD_EQ d1 d2 @ e).
    LOCKcut "q" (KE_PAYLOAD_EQ d2 d3 @ e).
    { repeat LOCKclear. }
    LOCKelims "h" 0.
    LOCKelims "q" 0.
    LOCKintros d d5; try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_data_eq_trans_true d0); try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_data_eq_trans_true d4); try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_has_payload_implies_eq_true d2); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_correct_after_implies_correct_localle u {eo : EventOrdering} e e' R Q H :=
    MkRule0
      [⟬ R ++ (u ⋈ e ■ e') :: Q ⟭ H ⊢ KE_CORRECT_AFTER @ e]
      (⟬ R ++ (u ⋈ e ■ e') :: Q ⟭ H ⊢ KE_CORRECT @ e').

  Lemma DERIVED_RULE_correct_after_implies_correct_localle_true :
    forall u {eo : EventOrdering} e e' R Q H,
      rule_true (DERIVED_RULE_correct_after_implies_correct_localle u e e' R Q H).
  Proof.
    start_proving_derived st.
    LOCKcut "c" (KE_CORRECT_AFTER @ e).
    LOCKelim "c" "c1"; try LOCKauto.
    LOCKelim "c1".
    LOCKelim "c1" "c2".
    LOCKcut "at" (KE_AT n @ e').
    { LOCKapply@ u PRIMITIVE_RULE_at_change_localle_true; try LOCKauto. }
    LOCKapply@ u PRIMITIVE_RULE_split_local_before_eq2_true.
    { LOCKapply@ u PRIMITIVE_RULE_subst_causal_eq_concl_true; try LOCKauto. }
    LOCKapply@ u PRIMITIVE_RULE_local_if_causal_true.
    LOCKapply@ u "c1" PRIMITIVE_RULE_forall_after_elim_true.
    LOCKelim "c1"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_perfect_memory_implies_knew_local u {eo : EventOrdering} e1 e2 R Q H d :=
    MkRule1
      (fun e' => [⟬R ++ (u ⋈ e1 □ e2) :: Q⟭ H ⊢ perfect_memory_step @ e',
                  ⟬R ++ (u ⋈ e1 □ e2) :: Q⟭ H ⊢ KE_KNOWS d @ e1])
      (⟬R ++ (u ⋈ e1 □ e2) :: Q⟭ H ⊢ KE_KNEW d @ e2).

  Lemma DERIVED_RULE_perfect_memory_implies_knew_local_true :
    forall u {eo : EventOrdering} e1 e2 R Q H d,
      rule_true (DERIVED_RULE_perfect_memory_implies_knew_local u e1 e2 R Q H d).
  Proof.
    start_proving_derived st.
    LOCKcut "kn" (KE_KNOWS d @ e1).
    { inst_hyp e1 hyp. }

    LOCKapply@ u (PRIMITIVE_RULE_duplicate_guard_true u "w").
    LOCKapply@ u (PRIMITIVE_RULE_split_local_before_true u "v").

    { LOCKapply@ u PRIMITIVE_RULE_unright_before_if_causal_true; try LOCKauto. }

    LOCKapply@ "v" PRIMITIVE_RULE_unright_before_if_causal_true.
    LOCKcut "p" (perfect_memory @ e).
    { LOCKclear u "v" "kn".
      LOCKapply@ "w" (PRIMITIVE_RULE_rename_causal_true u).
      LOCKapply DERIVED_RULE_perfect_memory_true.
      inst_hyp e0 hyp. }

    LOCKelim "p" d.
    LOCKelim "p"; try LOCKauto.
    LOCKapply@ u PRIMITIVE_RULE_local_if_localle_true.
    LOCKapply@ u DERIVED_RULE_unlocal_before_eq_if_causalle_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_localle_implies_local_after_eq_none u {eo : EventOrdering} e1 e2 R Q H t :=
    MkRule0
      [⟬ R ++ (u ⋈ e1 ■ e2) :: Q ⟭ H ⊢ t @ e2]
      (⟬ R ++ (u ⋈ e1 ■ e2) :: Q ⟭ H ⊢ KE_LOCAL_AFTER_EQ t None @ e1).

  Lemma DERIVED_RULE_localle_implies_local_after_eq_none_true :
    forall u {eo : EventOrdering} e1 e2 R Q H t,
      rule_true (DERIVED_RULE_localle_implies_local_after_eq_none u e1 e2 R Q H t).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (t @ e2).
    LOCKapply@ u PRIMITIVE_RULE_split_local_before_eq2_true.
    { LOCKapply@ u PRIMITIVE_RULE_causal_eq_sym_true.
      LOCKapply@ u PRIMITIVE_RULE_subst_causal_eq_concl_true.
      LOCKintros 1; try LOCKauto. }
    LOCKintro 0.

    LOCKcut "n" (KE_NODE @ e1); try LOCKauto.
    LOCKelim "n".
    LOCKintros n; try LOCKauto.
    LOCKapply@ u (PRIMITIVE_RULE_duplicate_guard_true u "v").
    LOCKapply@ "v" PRIMITIVE_RULE_local_if_causal_true.
    LOCKapply@ "v" PRIMITIVE_RULE_happened_after_none_intro_true; LOCKintros; try LOCKauto.
    LOCKapply@ u PRIMITIVE_RULE_local_if_localle_true.
    LOCKapply@ u PRIMITIVE_RULE_at_change_localle_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  (* We don't know any piece of data that has the same payload *)
  Definition new_data d :=
    KE_NOT (KE_EX_DATA
              (fun d' =>
                 KE_AND
                   (KE_KNEW d')
                   (KE_PAYLOAD_EQ d d'))).

  Definition new_sim_data d :=
    KE_NOT (KE_EX_DATA (fun d' => KE_AND (KE_KNEW d') (KE_SIM_DATA d d'))).

  Definition upon_event_broadcast (t : PosDTime) (* timeout *) (k : nat) (* threshold *) :=
    KE_ALL_DATA
      (fun bcast =>
         KE_ALL_NODE
           (fun node =>
              KE_IMPLIESn
                [KE_HAS_CAT bcast "bcast",
                 KE_AT node,
                 KE_CORRECT,
                 KE_LEARNS bcast,
                 new_data bcast]
                (KE_EX_DATA
                   (fun echo =>
                      KE_ANDS
                        [KE_HAS_CAT echo "echo",
                         KE_PAYLOAD_EQ bcast echo,
                         KE_KNOWS_VOUCHED echo (kc_mk_vouchers node),
                         KE_TIME_OUT t echo k,
                         KE_DISS echo])))).

  Definition upon_event_echo (t : PosDTime) (* timeout *) (k : nat) (* threshold *) :=
    KE_ALL_DATA
      (fun echo =>
         KE_ALL_NODE
           (fun node =>
              KE_ALL_VOUCHERS
                (fun v =>
                   KE_IMPLIESn
                     [KE_HAS_CAT echo "echo",
                      KE_AT node,
                      KE_CORRECT,
                      KE_LEARNS echo,
                      KE_VOUCHED echo v]
                     (KE_ORS
                        [KE_ANDS
                           [new_sim_data echo,
                            KE_NOT (KE_AT_LEAST_VOUCHERS v k),
                            KE_EX_DATA
                              (fun echo' =>
                                 KE_ANDS
                                   [KE_SIM_DATA echo echo',
                                    KE_KNOWS_VOUCHED echo' (kc_add_vouchers v (kc_mk_vouchers node)),
                                    KE_TIME_OUT t echo' k,
                                    KE_DISS echo'])],
                         KE_ANDS
                           [new_sim_data echo,
                            KE_AT_LEAST_VOUCHERS v k,
                            KE_EX_DATA
                              (fun deliver =>
                                 KE_ANDS
                                   [KE_HAS_CAT deliver "deliver",
                                    KE_PAYLOAD_EQ echo deliver,
                                    KE_TIME_OUT (pdt_mult (n2t 2) t) deliver k,
                                    KE_DISS deliver])]
                           (* There are other cases *)
                        ]
      )))).

  (* This should be derivable from the [upon_event_] specs *)
  Definition cross_threshold_on_echo k :=
    KE_ALL_DATA
      (fun echo =>
         KE_IMPLIESn
           [KE_CORRECT,
            KE_HAS_CAT echo "echo",
            ex_sim_knows_ex_at_least_vouchers echo k,
            KE_NOT (ex_sim_knew_ex_at_least_vouchers echo k)]
           (KE_EX_DATA
              (fun echo' =>
                 KE_ANDS
                   [KE_SIM_DATA echo echo',
                    KE_LEARNS echo']))).

  Definition event_kinds :=
    KE_IMPLIES
      KE_CORRECT
      (KE_EX_DATA
         (fun d =>
            KE_AND
              (KE_LEARNS d)
              (KE_ORS [KE_HAS_CAT d "bcast", KE_HAS_CAT d "echo", KE_HAS_CAT d "deliver"]))).

  Definition cannot_learn_bcast_and_echo :=
    KE_ALL_DATA2
      (fun d1 d2 =>
         KE_IMPLIESn
           [KE_LEARNS d1,
            KE_HAS_CAT d1 "bcast",
            KE_LEARNS d2,
            KE_HAS_CAT d2 "echo"]
           KE_FALSE).

  (* This one is for new broadcast for now *)
  Definition validity :=
    KE_ALL_DATA
      (fun bcast =>
         KE_IMPLIESn
           [KE_HAS_CAT bcast "bcast",
            KE_CORRECT_AFTER,
            KE_LEARNS bcast,
            new_data bcast]
           (KE_EX_DATA
              (fun deliver =>
                 KE_ANDS
                   [KE_HAS_CAT deliver "deliver",
                    KE_LOCAL_AFTER_EQ (KE_DISS deliver) None,
                    KE_PAYLOAD_EQ bcast deliver]))).


  (************************************************************************************************)
  Definition DERIVED_RULE_validity t k {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' => [⟬ R ⟭ H ⊢ upon_event_broadcast t k @ e',
                  ⟬ R ⟭ H ⊢ upon_event_echo t k @ e',
                  ⟬ R ⟭ H ⊢ event_kinds @ e',
                  ⟬ R ⟭ H ⊢ perfect_memory_step @ e',
                  ⟬ R ⟭ H ⊢ cannot_learn_bcast_and_echo @ e',
                  ⟬ R ⟭ H ⊢ cross_threshold_on_echo k @ e', (* This one should be derivable from the above *)
                  ⟬ R ⟭ H ⊢ dec_ex_sim_knows_ex_at_least_vouchers k @ e'])
      (⟬ R ⟭ H ⊢ validity @ e).

  Lemma DERIVED_RULE_validity_true :
    forall t k {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_validity t k e R H).
  Proof.
    start_proving_derived st.
    unfold validity.
    LOCKintros "cat" "cor" "lrn" "new".
    inst_hyp e st'.
    LOCKcut "bc" (upon_event_broadcast t k @ e); try complete repeat LOCKclear.
    LOCKelim "bc" d.
    LOCKcut "nd" (KE_NODE @ e); try LOCKauto.
    LOCKelim "nd".
    LOCKelim "bc" n.
    LOCKelims "bc" 0; try LOCKauto.
    { LOCKapply DERIVED_RULE_correct_after_implies_correct_true; try LOCKauto. }

    LOCKapply@ "bc04" (DERIVED_RULE_local_after_elim_true "u").
    LOCKelim "bc04" "bc4".
    LOCKclear "bc04".
    LOCKelims "bc4" 0.
    { LOCKapply@ "u" DERIVED_RULE_correct_after_implies_correct_local_true; try LOCKauto. }

    LOCKcut "h" (known_vouchers_increase k @ e0).
    { LOCKapply DERIVED_RULE_known_vouchers_increase_true.
      inst_hyp e1 hyp; LOCKclearall. }
    LOCKelim "h" d1.
    LOCKelim "h"; try LOCKauto.

    LOCKapply@ "h" (DERIVED_RULE_unlocal_before_eq_hyp_true "v").
    LOCKelim "h" "h'".

    LOCKcut "cross" (cross_threshold_on_echo k @ e1).
    { LOCKclearall; inst_hyp e1 hyp. }

    LOCKapply (DERIVED_RULE_bi_if_same_loc_true "z" n e e1); try LOCKauto.
    { LOCKapply@ "v" PRIMITIVE_RULE_at_change_localle_rev_true.
      LOCKapply@ "u" PRIMITIVE_RULE_weaken_local_before_time_true.
      LOCKapply@ "u" PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ "u" PRIMITIVE_RULE_at_change_localle_true; try LOCKauto. }

    { LOCKelim "new"; try LOCKauto.
      LOCKelim "h'".
      LOCKelim "h'" "h2".
      LOCKintros d2.

      { LOCKapply@ "z" (PRIMITIVE_RULE_split_local_before_as_localle_right_before_true "z" "w").
        LOCKapply@ "w" PRIMITIVE_RULE_unright_before_if_causal_true.
        LOCKcut "m" (perfect_memory @ e2).
        { LOCKapply DERIVED_RULE_perfect_memory_true.
          LOCKclearall.
          inst_hyp e3 hyp. }
        LOCKelim "m" d2; LOCKelim "m"; try LOCKauto.
        LOCKapply@ "z" DERIVED_RULE_unlocal_before_eq_if_causalle_true.
        LOCKapply (DERIVED_RULE_knows_ex_at_least_vouchers_implies_knows_true k); try LOCKauto. }

      LOCKapply (DERIVED_RULE_payload_eq_trans_true d0); try LOCKauto.
      LOCKcut "sim" (KE_SIM_DATA d0 d2 @ e).
      { LOCKapply (DERIVED_RULE_sim_data_trans_true d1); try LOCKauto.
        { LOCKapply (DERIVED_RULE_sim_data_change_event_true e e0); try LOCKauto. }
        LOCKapply (DERIVED_RULE_sim_data_change_event_true e e1); try LOCKauto. }

      LOCKelim "sim" "sim'"; try LOCKauto. }

    LOCKelim "cross" d1.
    repeat (LOCKelim "cross"); try LOCKauto.

    { LOCKapply@ "z" DERIVED_RULE_correct_after_implies_correct_localle_true; try LOCKauto. }

    { LOCKapply (PRIMITIVE_RULE_same_cat_preserves_has_cat_true d0); try LOCKauto.
      { LOCKapply (PRIMITIVE_RULE_same_cat_change_event_true e1 e0).
        LOCKelim "bc402" "xx"; try LOCKauto. }
      LOCKapply (PRIMITIVE_RULE_has_cat_change_event_true e1 e); try LOCKauto. }

    LOCKelims "cross" 0.

    LOCKapply@ "z" PRIMITIVE_RULE_split_local_before_eq2_true.
    { LOCKcut "cl" (cannot_learn_bcast_and_echo @ e).
      { LOCKclearall; inst_hyp e hyp. }
      LOCKelim "cl" d.
      LOCKelim "cl" d2.
      LOCKelims "cl" 0; try LOCKauto.
      { LOCKapply@ "z" PRIMITIVE_RULE_causal_eq_sym_true.
        LOCKapply@ "z" PRIMITIVE_RULE_subst_causal_eq_concl_true; try LOCKauto. }
      LOCKapply (PRIMITIVE_RULE_same_cat_preserves_has_cat_true d0); try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_same_cat_trans_true d1).
      { LOCKapply (PRIMITIVE_RULE_same_cat_change_event_true e e0).
        LOCKelim "bc402" "xx"; try LOCKauto. }
      LOCKapply (PRIMITIVE_RULE_same_cat_change_event_true e e1).
      LOCKelim "cross01" "xx"; try LOCKauto. }

    LOCKcut "ech" (upon_event_echo t k @ e1).
    { LOCKclearall; inst_hyp e1 hyp. }

    LOCKcut "vch" (KE_EX_VOUCHERS (fun v => KE_VOUCHED d2 v) @ e1).
    { LOCKapply PRIMITIVE_RULE_ex_vouchers_true. }
    LOCKelim "vch".

    LOCKelim "ech" d2.
    LOCKelim "ech" n.
    LOCKelim "ech" v.
    repeat (LOCKelim "ech"); try LOCKauto.

    { LOCKapply (PRIMITIVE_RULE_same_cat_preserves_has_cat_true d1).
      { LOCKelim "cross01" "z"; try LOCKauto. }
      LOCKapply (PRIMITIVE_RULE_same_cat_preserves_has_cat_true d0).
      { LOCKapply (PRIMITIVE_RULE_same_cat_change_event_true e1 e0).
        LOCKelim "bc402" "z"; try LOCKauto. }
      LOCKapply (PRIMITIVE_RULE_has_cat_change_event_true e1 e); try LOCKauto. }

    { LOCKapply@ "v" PRIMITIVE_RULE_at_change_localle_fwd_true.
      LOCKapply@ "u" PRIMITIVE_RULE_weaken_local_before_time_true.
      LOCKapply@ "u" PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ "u" PRIMITIVE_RULE_at_change_localle_true; try LOCKauto. }

    { LOCKapply@ "z" PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ "z" DERIVED_RULE_correct_after_implies_correct_localle_true; try LOCKauto. }

    { LOCKelim "ech" "ech1".
      LOCKelim "ech" "ech1".
      LOCKcut "kn" (KE_KNEW d0 @ e1).
      { LOCKapply@ "z" DERIVED_RULE_perfect_memory_implies_knew_local_true; try LOCKauto.
        { LOCKclearall; inst_hyp e2 hyp. }
        LOCKelim "bc03" "xx"; try LOCKauto. }

      LOCKelim "ech1"; try LOCKauto.
      LOCKintro d0; try LOCKauto.
      LOCKintro; try LOCKauto.
      LOCKapply DERIVED_RULE_sim_data_sym_true.
      LOCKapply (DERIVED_RULE_sim_data_trans_true d1); try LOCKauto.
      LOCKapply (DERIVED_RULE_sim_data_change_event_true e1 e0); try LOCKauto. }

    LOCKelim "ech" "ech1".
    LOCKelim "ech" "ech2".
    LOCKelim "ech" "ech3".
    LOCKelims "ech3" 0.
    LOCKintros d3; try LOCKauto.
    { LOCKapply (PRIMITIVE_RULE_has_cat_change_event_true e e1); try LOCKauto. }
    { LOCKapply@ "z" PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ "z" DERIVED_RULE_localle_implies_local_after_eq_none_true; try LOCKauto. }

    LOCKapply (DERIVED_RULE_payload_eq_trans_true d0); try LOCKauto.
    LOCKapply (DERIVED_RULE_payload_eq_trans_true d1); try LOCKauto.
    { LOCKapply (DERIVED_RULE_payload_eq_change_event_true e e0).
      LOCKelim "bc402" "xx"; try LOCKauto. }
    LOCKapply (DERIVED_RULE_payload_eq_trans_true d2); try LOCKauto.
    { LOCKapply (DERIVED_RULE_payload_eq_change_event_true e e1).
      LOCKelim "cross01" "xx"; try LOCKauto. }
    LOCKapply (DERIVED_RULE_payload_eq_change_event_true e e1); try LOCKauto.
  Qed.

End CalculusSMtime2.
