Require Export CalculusSM2.
Require Export CalculusSM3.
Require Export CalculusSM_derived2.
Require Export ComponentAxiom.
Require Export ComponentSM8.


Section CalculusSM_derived4.

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


  Lemma mk_opTrust :
    forall {t a},
      In (kc_trust2data t) (kc_auth2data a)
      -> opTrust a.
  Proof.
    introv i.
    exists (Some t); simpl.
    apply kc_auth2trust_correct.
    exists (kc_trust2data t); dands; auto.
    apply kc_data2trust_correct.
  Defined.

  Definition KE_NODE_DISS (d : kc_data) : KExpression :=
    KE_AND KE_NODE (KE_DISS d).

  (* This is a LoCK representation of our HyLoE communication axiom *)
  Definition ASSUMPTION_authenticated_messages_were_sent_or_byz :=
    KE_ALL_TRUST
      (fun t =>
         KE_IMPLIES
           (KE_TLEARNS t)
           (KE_OR
              (KE_EX_DATA
                 (fun d =>
                    (KE_HAPPENED_BEFORE
                       (KE_ANDS
                          [KE_NODE_DISS d,
                           KE_IN t d,
                           KE_LOCAL_CORRECT_TRACE_BEFORE]))))
              (KE_HAPPENED_BEFORE (KE_TDISS_OWN t)))).


  (* ==================================================== *)
  (* === These 3 axioms relate HyLoE and LoCK abstraction *)
  Definition AXIOM_data_in_auth_implies_from_node :=
    forall {d a n n'},
      In d (kc_auth2data a)
      -> data_auth n a = Some n'
      -> exists k,
          name2node n' = Some k.

  (*Definition AXIOM_data_in_auth_implies_from_node :=
    forall {a d n m},
      In d (kc_auth2data a)
      -> data_auth n a = Some m
      -> exists k, name2node m = Some k /\ kc_data2owner d = Some k.*)

  Definition AXIOM_data_in_auth_implies_protocol :=
    forall {a d m},
      In d (kc_auth2data a)
      -> In a (get_contained_authenticated_data m)
      -> is_protocol_message m = true.

  Definition AXIOM_in_auth2data_implies_in_msg2data :=
    forall {d a m},
      In d (kc_auth2data a)
      -> In a (get_contained_authenticated_data m)
      -> In d (kc_msg2data m).
  (* ==================================================== *)


  Lemma dmsg_is_in_out_implies_trust_data_is_in_out :
    forall d a m dst delay {eo : EventOrdering} {e : Event} {s} (o : event2out s e),
      AXIOM_in_auth2data_implies_in_msg2data
      -> In d (kc_auth2data a)
      -> In a (get_contained_authenticated_data m)
      -> dmsg_is_in_out (MkDMsg m dst delay) o
      -> data_is_in_out d o.
  Proof.
    introv ax i j k.
    unfold dmsg_is_in_out in *.
    unfold data_is_in_out in *.
    unfold event2out in *; remember (trigger e) as trig; destruct trig; simpl in *; tcsp.
    apply in_flat_map; eexists; dands; eauto; simpl.
  Qed.
  Hint Resolve dmsg_is_in_out_implies_trust_data_is_in_out : kc.

  Lemma implies_trust2data_is_in_out :
    forall t (i : ITrusted) {eo : EventOrdering} {e : Event} {s} (o : event2out s e)
           (p : is_trusted_event e i) (x : iot_output (iot_fun (it_name i))),
      trusted_is_in_out p x o
      -> ct_out2trust (it_name i) x = Some t
      -> data_is_in_out (kc_trust2data t) o.
  Proof.
    introv h q.
    unfold trusted_is_in_out in h; subst.
    unfold is_trusted_event in p.
    unfold data_is_in_out.
    revert o q.
    unfold event2out in *; simpl in *; rewrite p; simpl; introv h.
    unfold kc_out2trust; rewrite h; simpl; tcsp.
  Qed.
  Hint Resolve implies_trust2data_is_in_out : kc.

  Lemma ASSUMPTION_authenticated_messages_were_sent_or_byz_true :
    forall (eo : EventOrdering),
      AXIOM_data_in_auth_implies_from_node
      -> AXIOM_data_in_auth_implies_protocol
      -> AXIOM_in_auth2data_implies_in_msg2data
      -> AXIOM_authenticated_messages_were_sent_or_byz eo kc_sys
      -> assume_eo eo ASSUMPTION_authenticated_messages_were_sent_or_byz.
  Proof.
    introv a2n a2p a2m sendbyz lrn; simpl in *.
    unfold learns_data in lrn; exrepnd.
    pose proof (sendbyz e a (mk_opTrust lrn3) lrn2 lrn1) as sendbyz; simpl in *.
    exrepnd; repndors; exrepnd; subst; simpl in *; ginv;[|].

    { pose proof (a2n _ _ _ _ lrn3 sendbyz4) as exe1; exrepnd.
      assert (ex_node_e e') as exe' by (exists k; auto).
      autodimp sendbyz5 hyp; try (complete (eapply a2p; eauto)).
      left.
      exists (kc_trust2data c) (MkEventN e' exe'); simpl; dands; auto;
        try apply kc_data2trust_correct;[| |].

      { apply name2node_cond in exe0; eauto. }

      { unfold disseminate_data; simpl.
        apply in_M_output_sys_on_event_implies_in_byz in sendbyz5; exrepnd.
        exists o; dands; auto.
        eapply dmsg_is_in_out_implies_trust_data_is_in_out; eauto. }

      { apply M_output_sys_on_event_implies_has_correct_trace_before in sendbyz5.
        applydup name2node_cond in exe0 as cond.
        exists k; dands; auto.
        introv lte eql.
        assert (loc e'0 = loc e') as eqloc by congruence.
        pose proof (sendbyz5 e') as cor; repeat (autodimp cor hyp); eauto 2 with eo.
        apply cor; eauto 3 with eo. }
    }

    { inversion sendbyz3; subst.
      right.
      assert (ex_node_e e') as exe'.
      { unfold ex_node_e; allrw; rewrite node2name_cond; eauto. }

      exists (MkEventN e' exe'); simpl; dands; auto.

      { unfold disseminate_data, kc_out2trust; simpl.
        rewrite sendbyz4.
        exists o; dands; auto.
        eapply implies_trust2data_is_in_out; eauto. }

      { eexists; dands; eauto; simpl.
        unfold data_is_owned_by; simpl.
        rewrite kc_same_trust2owner; auto.
        unfold kc_trust2owner; allrw; auto. } }
  Qed.


  Definition ASSUMPTION_disseminate_trusted_if_own :=
    KE_ALL_DATA
      (fun d =>
         KE_ALL_TRUST
           (fun t =>
              KE_IMPLIES
                (KE_NODE_DISS d)
                (KE_IMPLIES
                   (KE_IN t d)
                   (KE_IMPLIES
                      (KE_TOWNS t)
                      (KE_TDISS_OWN t))))).

  Definition ASSUMPTION_learns_trusted_if_own :=
    KE_ALL_DATA
      (fun d =>
         KE_ALL_TRUST
           (fun t =>
              KE_IMPLIES
                (KE_NODE_DISS d)
                (KE_IMPLIES
                   (KE_IN t d)
                   (KE_IMPLIES
                      (KE_NOT (KE_TOWNS t))
                      (KE_TLEARNED t))))).


  (************************************************************************************************)
  Definition DERIVED_RULE_implies_all_trusted_learns_if_gen {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_authenticated_messages_were_sent_or_byz @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_trusted_if_own              @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_learns_trusted_if_own                   @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_has_owner_dec                           @ e'])
      (⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e).

  Lemma DERIVED_RULE_implies_all_trusted_learns_if_gen_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_implies_all_trusted_learns_if_gen e R H).
  Proof.
    start_proving_derived st.

    LOCKapply PRIMITIVE_RULE_induction_true.
    LOCKintro "ind".
    clear e; rename e0 into e.

    LOCKapply PRIMITIVE_RULE_all_trust_intro_true.
    LOCKintro "lrn".

    LOCKcut "ass1" (ASSUMPTION_authenticated_messages_were_sent_or_byz @ e).
    { inst_hyp e st'; repeat LOCKclear. }

    LOCKelim "ass1" t; try LOCKauto.
    LOCKelim "ass1"; try (unfold KE_TLEARNS in *; LOCKauto).
    LOCKelim "ass1"; try (unfold KE_TDISS_OWN in *; LOCKauto).
    LOCKelim "ass1".
    LOCKapply@ "ass1" (PRIMITIVE_RULE_unhappened_before_hyp_true "u").
    LOCKelim "ass1" "diss".
    LOCKelim "ass1" "in".
    LOCKelim "ass1" "cor".

    LOCKcut "dec" (KE_TOWNS_DEC t @ e0).
    { LOCKapply DERIVED_RULE_towns_dec_true.
      { inst_hyp e1 st'; repeat LOCKclear.
        LOCKclear "u". }
      LOCKelim "diss" "x"; try LOCKauto. }

    LOCKelim "dec".
    { LOCKcut "ass2" (ASSUMPTION_disseminate_trusted_if_own @ e0).
      { inst_hyp e0 st'; repeat LOCKclear; LOCKclear "u". }
      LOCKelim "ass2" d.
      LOCKelim "ass2" t.
      repeat (LOCKelim "ass2"; try (unfold KE_TOWNS in *; LOCKauto)).

      LOCKapply@ "u" PRIMITIVE_RULE_unhappened_before_if_causal_true; try (unfold KE_TDISS_OWN in *; LOCKauto). }

    LOCKcut "ass2" (ASSUMPTION_learns_trusted_if_own @ e0).
    { inst_hyp e0 st'; repeat LOCKclear; LOCKclear "u". }
    LOCKelim "ass2" d.
    LOCKelim "ass2" t.
    LOCKelim "ass2"; try LOCKauto.
    LOCKelim "ass2"; try LOCKauto.
    LOCKelim "ass2"; try (unfold KE_TOWNS in *; LOCKauto).

    LOCKapply@ "ass2" (DERIVED_RULE_unlocal_before_eq_hyp_true "v").
    LOCKapply@ "u" "ind" PRIMITIVE_RULE_forall_before_elim_trans_true.
    LOCKapply@ "v" "ind" DERIVED_RULE_forall_before_eq_elim_local_eq_true.
    LOCKelim "ind" t.
    LOCKelim "ind"; try (unfold KE_TLEARNS in *; LOCKauto).
    LOCKapply@ "u" PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq_true.
    LOCKapply@ "v" DERIVED_RULE_happened_before_if_local_eq_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knows_implies_learned_or_gen_implies_gen2 {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_FORALL_BEFORE_EQ (ASSUMPTION_learns_if_gen d) @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_knows_implies_learned_or_gen d @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_knows_implies_gen d @ e).

  Lemma DERIVED_RULE_knows_implies_learned_or_gen_implies_gen2_true :
    forall (eo : EventOrdering) e R H d,
      rule_true (DERIVED_RULE_knows_implies_learned_or_gen_implies_gen2 e R H d).
  Proof.
    start_proving_derived st.
    inst_hyp e st'.

    LOCKcut "a" (ASSUMPTION_knows_implies_learned_or_gen d @ e).
    LOCKintro "kn".
    LOCKelim "a"; try LOCKauto.
    LOCKelim "a"; try LOCKauto.

    { LOCKapply@ "a" (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "a").
      inst_hyp e0 st.
      LOCKcut "b" (KE_FORALL_BEFORE_EQ (ASSUMPTION_learns_if_gen d) @ e).
      { repeat LOCKclear; LOCKclear "u". }
      LOCKapply@ "u" "b" DERIVED_RULE_forall_before_eq_elim_local_eq_true.
      LOCKelim "b"; try LOCKauto.
      LOCKapply@ "u" DERIVED_RULE_happened_before_eq_if_local_eq_true.
      LOCKapply DERIVED_RULE_happened_before_implies_happened_before_eq_true; try LOCKauto. }

    LOCKapply@ "a" (DERIVED_RULE_unlocal_before_eq_hyp_true "u").
    LOCKapply@ "u" PRIMITIVE_RULE_localle_if_causalle_true.
    LOCKapply@ "u" DERIVED_RULE_unhappened_before_eq_if_causalle_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_KLD_implies_gen2 {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_FORALL_BEFORE_EQ (ASSUMPTION_learns_if_gen d) @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_knew_or_learns_or_gen d @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_knows_implies_gen d @ e).

  Lemma DERIVED_RULE_KLD_implies_gen2_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_KLD_implies_gen2 e R H d).
  Proof.
    start_proving_derived st.
    LOCKapply DERIVED_RULE_knows_implies_learned_or_gen_implies_gen2_true.
    { inst_hyp e st. }
    LOCKapply DERIVED_RULE_KLD_implies_or_true.
    inst_hyp e1 st.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_forall_before_eq_intro u {eo : EventOrdering} e R H t :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ▶ e) :: R⟭ H ⊢ t @ e'])
      (⟬R⟭ H ⊢ KE_FORALL_BEFORE_EQ t @ e).

  Lemma DERIVED_RULE_forall_before_eq_intro_true :
    forall u {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_forall_before_eq_intro u e R H t).
  Proof.
    start_proving_derived st.
    LOCKintro.
    { LOCKapply (PRIMITIVE_RULE_forall_before_intro_true u).
      LOCKapply@ u PRIMITIVE_RULE_causal_if_causalle_true.
      inst_hyp e0 hyp. }
    inst_hyp e hyp.
    LOCKapply (DERIVED_RULE_add_happenedle_refl_true u e).
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_forall_before_eq_elim u x {eo : EventOrdering} e e' R Q H J t a :=
    MkRule0
      [⟬R ++ (u ⋈ e' ▶ e) :: Q⟭ H • (x › t @ e') ⊕ J ⊢ a]
      (⟬R ++ (u ⋈ e' ▶ e) :: Q⟭ H • (x › KE_FORALL_BEFORE_EQ t @ e) ⊕ J ⊢ a).

  Lemma DERIVED_RULE_forall_before_eq_elim_true :
    forall u x {eo : EventOrdering} e e' R Q H J t a,
      rule_true (DERIVED_RULE_forall_before_eq_elim u x e e' R Q H J t a).
  Proof.
    start_proving_derived st.
    LOCKelim x "y".
    LOCKapply@ u PRIMITIVE_RULE_split_happened_before_eq2_true.

    { LOCKapply@ u PRIMITIVE_RULE_causal_eq_sym_true.
      LOCKapply@ x u PRIMITIVE_RULE_subst_causal_eq_hyp_true.
      LOCKclear "y".
      LOCKapply@ u PRIMITIVE_RULE_causal_eq_sym_true.
      LOCKapply@ u PRIMITIVE_RULE_beforele_if_eq_true. }

    LOCKapply@ "y" u PRIMITIVE_RULE_forall_before_elim_true.

    LOCKclear x.
    LOCKapply@ "y" (PRIMITIVE_RULE_rename_hyp_true "y" x).
    LOCKapply@ u PRIMITIVE_RULE_causal_if_causalle_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_swap_forall_before_eq_all_trust x {eo : EventOrdering} e f R H J a :=
    MkRule0
      [⟬R⟭ H • (x › KE_ALL_TRUST (fun t => KE_FORALL_BEFORE_EQ (f t)) @ e) ⊕ J ⊢ a]
      (⟬R⟭ H • (x › KE_FORALL_BEFORE_EQ (KE_ALL_TRUST f) @ e) ⊕ J ⊢ a).

  Lemma DERIVED_RULE_swap_forall_before_eq_all_trust_true :
    forall x {eo : EventOrdering} e f R H J a,
      rule_true (DERIVED_RULE_swap_forall_before_eq_all_trust x e f R H J a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" x (KE_ALL_TRUST (fun t => KE_FORALL_BEFORE_EQ (f t)) @ e).
    { LOCKintro.
      LOCKapply (DERIVED_RULE_forall_before_eq_intro_true "u").
      LOCKapply@ "u" DERIVED_RULE_forall_before_eq_elim_true.
      LOCKelim x t; try LOCKauto. }
    LOCKclear x.
    LOCKapply@ "x" (PRIMITIVE_RULE_rename_hyp_true "x" x).
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_forall_before_eq_trans u {eo : EventOrdering} e e' R Q H t :=
    MkRule0
      [⟬R ++ (u ⋈ e' ▷ e) :: Q⟭ H ⊢ KE_FORALL_BEFORE t @ e]
      (⟬R ++ (u ⋈ e' ▷ e) :: Q⟭ H ⊢ KE_FORALL_BEFORE_EQ t @ e').

  Lemma DERIVED_RULE_forall_before_eq_trans_true :
    forall u {eo : EventOrdering} e e' R Q H t,
      rule_true (DERIVED_RULE_forall_before_eq_trans u e e' R Q H t).
  Proof.
    start_proving_derived st.
    LOCKcut "all" (KE_FORALL_BEFORE t @ e).
    LOCKapply@ u "all" PRIMITIVE_RULE_forall_before_elim_trans_true.
    LOCKapply (DERIVED_RULE_forall_before_eq_intro_true "u").
    LOCKapply@ "u" "all" DERIVED_RULE_forall_before_eq_elim_true; try LOCKauto.
  Qed.


  Definition ASSUMPTION_diss_correct_implies_knows :=
    KE_ALL_DATA
      (fun d =>
         KE_IMPLIES
           (KE_NODE_DISS d)
           (KE_IMPLIES
              KE_LOCAL_CORRECT_TRACE_BEFORE
              (KE_KNOWS d))).

  Definition ASSUMPTION_in_knows_implies_trusted_knows :=
    KE_ALL_DATA
      (fun d =>
         KE_ALL_TRUST
           (fun t =>
              KE_IMPLIES
                (KE_KNOWS d)
                (KE_IMPLIES
                   (KE_IN t d)
                   (KE_TKNOWS t)))).


  (************************************************************************************************)
  Definition DERIVED_RULE_KIK_and_DIS_implies_knows d {eo : EventOrdering} e t R H :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_diss_correct_implies_knows              @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_in_knows_implies_trusted_knows          @ e',
          ⟬R⟭ H ⊢ KE_NODE_DISS d                @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_CORRECT_TRACE_BEFORE @ e,
          ⟬R⟭ H ⊢ KE_IN t d                     @ e])
      (⟬R⟭ H ⊢ KE_TKNOWS t @ e).

  Lemma DERIVED_RULE_KIK_and_DIS_implies_knows_true :
    forall d {eo : EventOrdering} e t R H,
      rule_true (DERIVED_RULE_KIK_and_DIS_implies_knows d e t R H).
  Proof.
    start_proving_derived st.

    inst_hyp e st'; repeat LOCKclear.

    LOCKcut "ass" (ASSUMPTION_in_knows_implies_trusted_knows @ e).
    LOCKelim "ass" d.
    LOCKelim "ass" t.
    repeat (LOCKelim "ass"; try LOCKauto).
    LOCKcut "ass" (ASSUMPTION_diss_correct_implies_knows @ e).
    LOCKelim "ass" d.
    repeat (LOCKelim "ass"; try LOCKauto).
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_implies_all_trusted_learns_if_gen2 {eo : EventOrdering} e R H :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_authenticated_messages_were_sent_or_byz @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_diss_correct_implies_knows              @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_in_knows_implies_trusted_knows          @ e',
          ⟬R⟭ H ⊢ KE_ALL_DATA ASSUMPTION_knew_or_learns_or_gen       @ e'])
      (⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e).

  Lemma DERIVED_RULE_implies_all_trusted_learns_if_gen2_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_implies_all_trusted_learns_if_gen2 e R H).
  Proof.
    start_proving_derived st.

    LOCKapply PRIMITIVE_RULE_induction_true.
    LOCKintro "ind".
    clear e; rename e0 into e.

    LOCKintro.
    LOCKintro "lrn".

    LOCKcut "ass1" (ASSUMPTION_authenticated_messages_were_sent_or_byz @ e).
    { inst_hyp e st'; repeat LOCKclear. }

    LOCKapply@ "ass1" (PRIMITIVE_RULE_all_trust_elim_true "ass1" t); try LOCKauto.
    LOCKelim "ass1"; try (unfold KE_TLEARNS in *; LOCKauto).
    LOCKelim "ass1"; try (unfold KE_TDISS_OWN in *; LOCKauto).
    LOCKelim "ass1".
    LOCKapply@ "ass1" (PRIMITIVE_RULE_unhappened_before_hyp_true "u").
    LOCKelim "ass1" "diss".
    LOCKelim "ass1" "in".
    LOCKelim "ass1" "cor".

    LOCKcut "tk" (KE_TKNOWS t @ e0).
    { LOCKapply (DERIVED_RULE_KIK_and_DIS_implies_knows_true d); try LOCKauto;
        inst_hyp e1 st'; repeat LOCKclear; LOCKclear "u". }

    LOCKcut "ass3" (ASSUMPTION_knows_implies_gen (kc_trust2data t) @ e0).
    { LOCKapply DERIVED_RULE_KLD_implies_gen2_true.
      { LOCKapply@ "u" "ind" PRIMITIVE_RULE_forall_before_elim_trans_true.
        LOCKapply@ "ind" DERIVED_RULE_swap_forall_before_eq_all_trust_true.
        LOCKelim "ind" t.
        unfold ASSUMPTION_learns_if_gen; try LOCKauto. }
      inst_hyp e1 st'; repeat LOCKclear; LOCKclear "u".
      LOCKcut "ass" (KE_ALL_DATA ASSUMPTION_knew_or_learns_or_gen @ e1).
      LOCKelim "ass" (kc_trust2data t); try LOCKauto. }

    LOCKelim "ass3"; try (unfold KE_TKNOWS in *; LOCKauto).
    LOCKapply@ "u" DERIVED_RULE_unhappened_before_if_causal_trans_true; try LOCKauto.
  Qed.

End CalculusSM_derived4.
