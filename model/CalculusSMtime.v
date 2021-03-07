Require Export toString.
Require Export CalculusSM_derived0.


Section CalculusSMtime.

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


  Definition KE_FORALL_AFTER_EQ e := KE_AND (KE_FORALL_AFTER e) e.

  Definition KE_LOCAL_AFTER e t :=
    KE_EX_NODE
      (fun n =>
         KE_AND
           (KE_AT n)
           (KE_HAPPENED_AFTER (KE_AND (KE_AT n) e) t)).

  Definition KE_LOCAL_AFTER_EQ e t := KE_OR (KE_LOCAL_AFTER e t) (KE_AND e KE_NODE).

  Definition KE_LOCAL_FORALL_AFTER (e : KExpression) :=
    KE_EX_NODE
      (fun n =>
         KE_AND
           (KE_AT n)
           (KE_FORALL_AFTER (KE_IMPLIES (KE_AT n) e))).

  Definition KE_LOCAL_FORALL_AFTER_EQ t := KE_AND (KE_LOCAL_FORALL_AFTER t) t.

  Definition KE_CORRECT_AFTER := KE_LOCAL_FORALL_AFTER_EQ KE_CORRECT.

  (* NOTE: instead of having time as an option in the after operator, we could define
       the none case as exists t:time... *)

  Fixpoint KE_IMPLIESn (l : list KExpression) (e : KExpression) : KExpression :=
    match l with
    | [] => e
    | h :: l => KE_IMPLIES h (KE_IMPLIESn l e)
    end.

  Definition KE_PAYLOAD_EQ (d1 d2 : kc_data) :=
    KE_EX_DATA2
      (fun p1 p2 =>
         KE_ANDS
           [KE_HAS_PAYLOAD d1 p1,
            KE_HAS_PAYLOAD d2 p2,
            KE_DATA_EQ p1 p2]).

  Definition KE_IFF (a b : KExpression) := KE_AND (KE_IMPLIES a b) (KE_IMPLIES b a).

  Definition KE_KNOWS_VOUCHED d v :=
    KE_AND (KE_KNOWS d) (KE_VOUCHED d v).

  Definition KE_KNOWS_AT_LEAST_VOUCHERS d v k :=
    KE_ANDS
      [KE_KNOWS_VOUCHED d v,
       KE_AT_LEAST_VOUCHERS v k].

  Definition KE_KNEW_VOUCHED d v :=
    KE_AND (KE_KNEW d) (KE_VOUCHED d v).

  Definition KE_KNEW_AT_LEAST_VOUCHERS d v k :=
    KE_ANDS
      [KE_KNEW_VOUCHED d v,
       KE_AT_LEAST_VOUCHERS v k].

  Definition KE_KNOWS_EX_AT_LEAST_VOUCHERS d k :=
    KE_EX_VOUCHERS (fun v => KE_KNOWS_AT_LEAST_VOUCHERS d v k).

  Definition KE_KNEW_EX_AT_LEAST_VOUCHERS d k :=
    KE_EX_VOUCHERS (fun v => KE_KNEW_AT_LEAST_VOUCHERS d v k).

  Definition KE_SIM_DATA d1 d2 :=
    KE_AND (KE_SAME_CAT d1 d2) (KE_PAYLOAD_EQ d1 d2).

  Definition KE_TIME_OUT_IFF (d : kc_data) (k : nat) :=
    KE_IFF
      KE_CORRECT
      (KE_EX_DATA
         (fun d' =>
            KE_ANDS
              [KE_KNOWS_EX_AT_LEAST_VOUCHERS d' k,
               KE_SIM_DATA d d'])).

  Definition KE_TIME_OUT (t : PosDTime) (d : kc_data) (k : nat) :=
    KE_LOCAL_AFTER
      (KE_TIME_OUT_IFF d k)
      (Some t).


  (***********************************************************)
  Definition PRIMITIVE_RULE_happened_after_elim u x {eo : EventOrdering} e R H J a (t : PosDTime) b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e ¦▷t¦ e') :: R⟭ H • (x › a @ e') ⊕ J ⊢ b])
      (⟬R⟭ H • (x › KE_HAPPENED_AFTER a (Some t) @ e) ⊕ J ⊢ b).

  Lemma PRIMITIVE_RULE_happened_after_elim_true :
    forall u x {eo : EventOrdering} e R H J a t b,
      rule_true (PRIMITIVE_RULE_happened_after_elim u x e R H J a t b).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_HAPPENED_AFTER a (Some t) @ e)) as q.
    allrw hyp_in_adds; allrw hyp_in_add; simpl in *.
    repeat (autodimp q hyp); exrepnd; unfold hyp_event, seq_event in *; simpl in *.
    inst_hyp e' ht.
    apply ht0; simpl; introv j; allrw hyp_in_adds; allrw hyp_in_add;
      repndors; subst; simpl in *; tcsp;
        try apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_at_implies_local_time x n {eo : EventOrdering} e1 e2 t R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ¦▷t¦ e2) :: Q⟭ H ⊢ KE_AT n @ e1,
       ⟬R ++ (x ⋈ e1 ¦▷t¦ e2) :: Q⟭ H ⊢ KE_AT n @ e2,
       ⟬R ++ (x ⋈ e1 ¦□t¦ e2) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e1 ¦▷t¦ e2) :: Q⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_at_implies_local_time_true :
    forall x n {eo : EventOrdering} e1 e2 t R Q H a,
      rule_true (PRIMITIVE_RULE_at_implies_local_time x n e1 e2 t R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; clear st0.
    applydup st1 in ht; simpl in *; tcsp; clear st1.
    unfold seq_event in *; simpl in *.
    apply st2; simpl in *; tcsp.
    introv i; allrw in_app_iff; simpl in *; repndors; subst; simpl in *; tcsp;
      try (complete (apply ct; allrw in_app_iff; simpl in *; repndors; subst; tcsp)).
    pose proof (ct (x ⋈ e1 ¦▷t¦ e2)) as ct; allrw in_app_iff; simpl in *.
    autodimp ct hyp; tcsp; repnd; dands; eauto 3 with eo; split; auto; try congruence.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_forall_after_elim u x {eo : EventOrdering} e e' R Q H J t a :=
    MkRule0
      [⟬R ++ (u ⋈ e ▷ e') :: Q⟭ H • (x › t @ e') ⊕ J ⊢ a]
      (⟬R ++ (u ⋈ e ▷ e') :: Q⟭ H • (x › KE_FORALL_AFTER t @ e) ⊕ J ⊢ a).

  Lemma PRIMITIVE_RULE_forall_after_elim_true :
    forall u x {eo : EventOrdering} e e' R Q H J t a,
      rule_true (PRIMITIVE_RULE_forall_after_elim u x e e' R Q H J t a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_FORALL_AFTER t @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    unfold hyp_event, seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e ▷ e')) as w; simpl in w; autodimp w hyp; repnd; GC.
    { apply in_app_iff; simpl; tcsp. }
    pose proof (h e') as h; autodimp h hyp.
    apply st0; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_weaken_local_before_time u t {eo : EventOrdering} e e1 e2 R Q H a :=
    MkRule0
      [⟬ R ++ (u ⋈ e1 □ e2) :: Q ⟭ H ⊢ a @ e]
      (⟬ R ++ (u ⋈ e1 ¦□t¦ e2) :: Q ⟭ H ⊢ a @ e).

  Lemma PRIMITIVE_RULE_weaken_local_before_time_true :
    forall u t {eo : EventOrdering} e e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_weaken_local_before_time u t e e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; simpl; tcsp.
    introv i; allrw in_app_iff; simpl in *; repndors; subst; tcsp;
      try (complete (apply ct; simpl; allrw in_app_iff; simpl in *; tcsp)).
    simpl; dands; tcsp.
    pose proof (ct (u ⋈ e1 ¦□ t ¦ e2)) as ct; simpl in *; allrw in_app_iff; simpl in *.
    autodimp ct hyp; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_at_change_local x {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 □ e2) :: Q⟭ H ⊢ KE_AT a @ e1]
      (⟬R ++ (x ⋈ e1 □ e2) :: Q⟭ H ⊢ KE_AT a @ e2).

  Lemma PRIMITIVE_RULE_at_change_local_true :
    forall x {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_at_change_local x e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; clear st0; auto;[].
    simpl in *; exrepnd.
    unfold seq_event in *; simpl in *; eauto 3 with kn.
    allrw interp_owns.
    pose proof (ct (x ⋈ e1 □ e2)) as ct; allrw in_app_iff; simpl in *.
    autodimp ct hyp; repnd.
    rewrite <- ht; symmetry; eauto 3 with eo.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_same_cat_refl {eo : EventOrdering} e R H d :=
    MkRule0
      []
      (⟬ R ⟭ H ⊢ KE_SAME_CAT d d @ e).

  Lemma PRIMITIVE_RULE_same_cat_refl_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (PRIMITIVE_RULE_same_cat_refl e R H d).
  Proof.
    start_proving_primitive st ct ht; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_ex_payload {eo : EventOrdering} e R H d :=
    MkRule0
      []
      (⟬ R ⟭ H ⊢ KE_EX_DATA (fun p => KE_HAS_PAYLOAD d p) @ e).

  Lemma PRIMITIVE_RULE_ex_payload_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (PRIMITIVE_RULE_ex_payload e R H d).
  Proof.
    start_proving_primitive st ct ht; eauto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_data_eq_refl {eo : EventOrdering} e R H d :=
    MkRule0
      []
      (⟬ R ⟭ H ⊢ KE_DATA_EQ d d @ e).

  Lemma PRIMITIVE_RULE_data_eq_refl_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (PRIMITIVE_RULE_data_eq_refl e R H d).
  Proof.
    start_proving_primitive st ct ht; auto.
  Qed.


  (* MOVE *)
  Definition KE_DEC a := KE_OR a (KE_NOT a).

  (* MOVE *)
  Ltac LOCKelims h n :=
    first [LOCKelim h; LOCKelims h n
          |let n' := constr:(S n) in
           let h' := constr:(String.append h (nat2string n')) in
           LOCKelim h h';
           LOCKelims h n'
          |idtac].


  (***********************************************************)
  Definition PRIMITIVE_RULE_at_least_vouchers_dec {eo : EventOrdering} e R H v k :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_DEC (KE_AT_LEAST_VOUCHERS v k) @ e).

  Lemma PRIMITIVE_RULE_at_least_vouchers_dec_true :
    forall {eo : EventOrdering} e R H v k,
      rule_true (PRIMITIVE_RULE_at_least_vouchers_dec e R H v k).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    destruct (lt_dec k (kc_num_vouchers v)) as [d|d]; auto.
    right; intro xx; ginv; destruct d; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_vouched_change_event {eo : EventOrdering} e1 e2 R H d v :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_VOUCHED d v @ e2]
      (⟬ R ⟭ H ⊢ KE_VOUCHED d v @ e1).

  Lemma PRIMITIVE_RULE_vouched_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H d v,
      rule_true (PRIMITIVE_RULE_vouched_change_event e1 e2 R H d v).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_at_least_vouchers_change_event {eo : EventOrdering} e1 e2 R H v k :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_AT_LEAST_VOUCHERS v k @ e2]
      (⟬ R ⟭ H ⊢ KE_AT_LEAST_VOUCHERS v k @ e1).

  Lemma PRIMITIVE_RULE_at_least_vouchers_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H v k,
      rule_true (PRIMITIVE_RULE_at_least_vouchers_change_event e1 e2 R H v k).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_same_cat_sym {eo : EventOrdering} e R H d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_SAME_CAT d1 d2 @ e]
      (⟬ R ⟭ H ⊢ KE_SAME_CAT d2 d1 @ e).

  Lemma PRIMITIVE_RULE_same_cat_sym_true :
    forall {eo : EventOrdering} e R H d1 d2,
      rule_true (PRIMITIVE_RULE_same_cat_sym e R H d1 d2).
  Proof.
    start_proving_primitive st ct ht; auto.
    symmetry; apply st0; simpl; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_data_eq_sym {eo : EventOrdering} e R H d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_DATA_EQ d1 d2 @ e]
      (⟬ R ⟭ H ⊢ KE_DATA_EQ d2 d1 @ e).

  Lemma PRIMITIVE_RULE_data_eq_sym_true :
    forall {eo : EventOrdering} e R H d1 d2,
      rule_true (PRIMITIVE_RULE_data_eq_sym e R H d1 d2).
  Proof.
    start_proving_primitive st ct ht; auto.
    symmetry; apply st0; simpl; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_same_cat_change_event {eo : EventOrdering} e1 e2 R H d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_SAME_CAT d1 d2 @ e2]
      (⟬ R ⟭ H ⊢ KE_SAME_CAT d1 d2 @ e1).

  Lemma PRIMITIVE_RULE_same_cat_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H d1 d2,
      rule_true (PRIMITIVE_RULE_same_cat_change_event e1 e2 R H d1 d2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_has_payload_change_event {eo : EventOrdering} e1 e2 R H d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_HAS_PAYLOAD d1 d2 @ e2]
      (⟬ R ⟭ H ⊢ KE_HAS_PAYLOAD d1 d2 @ e1).

  Lemma PRIMITIVE_RULE_has_payload_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H d1 d2,
      rule_true (PRIMITIVE_RULE_has_payload_change_event e1 e2 R H d1 d2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
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
  Definition PRIMITIVE_RULE_same_cat_trans {eo : EventOrdering} e R H d1 d2 d3 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_SAME_CAT d1 d2 @ e,
       ⟬ R ⟭ H ⊢ KE_SAME_CAT d2 d3 @ e]
      (⟬ R ⟭ H ⊢ KE_SAME_CAT d1 d3 @ e).

  Lemma PRIMITIVE_RULE_same_cat_trans_true :
    forall d2 {eo : EventOrdering} e R H d1 d3,
      rule_true (PRIMITIVE_RULE_same_cat_trans e R H d1 d2 d3).
  Proof.
    start_proving_primitive st ct ht; auto.
    rewrite st0; auto.
    apply st1; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_data_eq_trans {eo : EventOrdering} e R H d1 d2 d3 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_DATA_EQ d1 d2 @ e,
       ⟬ R ⟭ H ⊢ KE_DATA_EQ d2 d3 @ e]
      (⟬ R ⟭ H ⊢ KE_DATA_EQ d1 d3 @ e).

  Lemma PRIMITIVE_RULE_data_eq_trans_true :
    forall d2 {eo : EventOrdering} e R H d1 d3,
      rule_true (PRIMITIVE_RULE_data_eq_trans e R H d1 d2 d3).
  Proof.
    start_proving_primitive st ct ht; auto.
    rewrite st0; auto.
    apply st1; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_has_payload_implies_eq {eo : EventOrdering} e R H d d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_HAS_PAYLOAD d d1 @ e,
       ⟬ R ⟭ H ⊢ KE_HAS_PAYLOAD d d2 @ e]
      (⟬ R ⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma PRIMITIVE_RULE_has_payload_implies_eq_true :
    forall d {eo : EventOrdering} e R H d1 d2,
      rule_true (PRIMITIVE_RULE_has_payload_implies_eq e R H d d1 d2).
  Proof.
    start_proving_primitive st ct ht.
    rewrite <- st0; auto.
    rewrite <- st1; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_same_cat_preserves_has_cat {eo : EventOrdering} e R H d1 d2 c :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_SAME_CAT d1 d2 @ e,
       ⟬ R ⟭ H ⊢ KE_HAS_CAT d1 c @ e]
      (⟬ R ⟭ H ⊢ KE_HAS_CAT d2 c @ e).

  Lemma PRIMITIVE_RULE_same_cat_preserves_has_cat_true :
    forall d1 {eo : EventOrdering} e R H d2 c,
      rule_true (PRIMITIVE_RULE_same_cat_preserves_has_cat e R H d1 d2 c).
  Proof.
    start_proving_primitive st ct ht.
    rewrite <- st0; auto.
    apply st1; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_has_cat_change_event {eo : EventOrdering} e1 e2 R H d c :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_HAS_CAT d c @ e2]
      (⟬ R ⟭ H ⊢ KE_HAS_CAT d c @ e1).

  Lemma PRIMITIVE_RULE_has_cat_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H d c,
      rule_true (PRIMITIVE_RULE_has_cat_change_event e1 e2 R H d c).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_ex_vouchers {eo : EventOrdering} e R H d :=
    MkRule0
      []
      (⟬ R ⟭ H ⊢ KE_EX_VOUCHERS (fun v => KE_VOUCHED d v) @ e).

  Lemma PRIMITIVE_RULE_ex_vouchers_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (PRIMITIVE_RULE_ex_vouchers e R H d).
  Proof.
    start_proving_primitive st ct ht; eauto.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_at_change_localle_rev x {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_AT a @ e2]
      (⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_AT a @ e1).

  Lemma PRIMITIVE_RULE_at_change_localle_rev_true :
    forall x {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_at_change_localle_rev x e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; clear st0; auto;[].
    simpl in *; exrepnd.
    unfold seq_event in *; simpl in *; eauto 3 with kn.
    allrw interp_owns.
    pose proof (ct (x ⋈ e1 ■ e2)) as ct; allrw in_app_iff; simpl in *.
    autodimp ct hyp; repnd.
    symmetry; rewrite <- ht; symmetry; eauto 3 with eo.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_split_local_before_as_right_before_localle u v {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule1
      (fun e =>
         [⟬Q ++ (u ⋈ e1 ⋄ e) :: (v ⋈ e ■ e2) :: R⟭ H ⊢ a])
      (⟬Q ++ (u ⋈ e1 □ e2) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_split_local_before_as_right_before_localle_true :
    forall u v {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_split_local_before_as_right_before_localle u v e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e1 □ e2)) as h; simpl in *.
    allrw in_app_iff; allsimpl; autodimp h hyp; repnd; GC.
    pose proof (local_implies_local_or_pred _ _ h0) as q.

    repndors; exrepnd.

    { inst_hyp e2 st.
      apply st1; simpl; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl; dands; tcsp;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)); eauto 3 with eo. }

    { assert (ex_node_e e) as exe.
      { eapply local_pred_preserves_ex_node_e; eauto; apply ex_node_e_EventN. }
      inst_hyp (MkEventN e exe) st.
      apply st1; simpl; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl; dands; tcsp;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)); eauto 3 with eo. }
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_split_local_before_as_localle_right_before u v {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule1
      (fun e =>
         [⟬Q ++ (u ⋈ e1 ■ e) :: (v ⋈ e ⋄ e2) :: R⟭ H ⊢ a])
      (⟬Q ++ (u ⋈ e1 □ e2) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_split_local_before_as_localle_right_before_true :
    forall u v {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_split_local_before_as_localle_right_before u v e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e1 □ e2)) as h; simpl in *.
    allrw in_app_iff; allsimpl; autodimp h hyp; repnd; GC.
    pose proof (local_implies_pred_or_local _ _ h0) as q.

    repndors; exrepnd.

    { inst_hyp e1 st.
      apply st1; simpl; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl; dands; tcsp;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)); eauto 3 with eo. }

    { assert (ex_node_e e) as exe.
      { eapply local_pred_preserves_ex_node_e_forward; eauto; apply ex_node_e_EventN. }
      inst_hyp (MkEventN e exe) st.
      apply st1; simpl; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl; dands; tcsp;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)); eauto 3 with eo. }
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_happened_after_intro u {eo : EventOrdering} e e' R Q H a (t : PosDTime) :=
    MkRule0
      [⟬R ++ (u ⋈ e ¦▷t¦ e') :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (u ⋈ e ¦▷t¦ e') :: Q⟭ H ⊢ KE_HAPPENED_AFTER a (Some t) @ e).

  Lemma PRIMITIVE_RULE_happened_after_intro_true :
    forall u {eo : EventOrdering} e e' R Q H a t,
      rule_true (PRIMITIVE_RULE_happened_after_intro u e e' R Q H a t).
  Proof.
    start_proving_primitive st ct ht.
    exists e'.
    unfold seq_event; simpl.
    pose proof (ct (u ⋈ e ¦▷ t ¦ e')) as ct'; simpl in ct'.
    autodimp ct' hyp; try rewrite in_app_iff; simpl; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_happened_after_none_intro u {eo : EventOrdering} e e' R Q H a :=
    MkRule0
      [⟬R ++ (u ⋈ e ▷ e') :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (u ⋈ e ▷ e') :: Q⟭ H ⊢ KE_HAPPENED_AFTER a None @ e).

  Lemma PRIMITIVE_RULE_happened_after_none_intro_true :
    forall u {eo : EventOrdering} e e' R Q H a,
      rule_true (PRIMITIVE_RULE_happened_after_none_intro u e e' R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    exists e'.
    unfold seq_event; simpl.
    pose proof (ct (u ⋈ e ▷ e')) as ct'; simpl in ct'.
    autodimp ct' hyp; try rewrite in_app_iff; simpl; tcsp.
  Qed.

End CalculusSMtime.

Ltac LOCKelims h n :=
  first [LOCKelim h; LOCKelims h n
        |let n' := constr:(S n) in
         let h' := constr:(String.append h (nat2string n')) in
         LOCKelim h h';
         LOCKelims h n'
        |idtac].
