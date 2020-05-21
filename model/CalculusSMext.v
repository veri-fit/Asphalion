Require Export CalculusSM.
Require Export CalculusSM_tacs.


Section CalculusSMext.

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


  (* These are the axioms of S5 (R1 is just an instance of the corresponding axiom) *)

  (* K(A) -> A *)
  Lemma A1 :
    forall {eo : EventOrdering} (e : Event) (a : KExpression),
      interpret e (KE_IMPLIES (KE_EXT_KNOW a) a).
  Proof.
    introv h; simpl in *.
    apply h; apply kc_same_state_refl.
  Qed.

  (* K(A) -> K(A->B) -> K(B) *)
  Lemma A2 :
    forall {eo : EventOrdering} (e : Event) (a b : KExpression),
      interpret e (KE_IMPLIES
                     (KE_EXT_KNOW a)
                     (KE_IMPLIES
                        (KE_EXT_KNOW (KE_IMPLIES a b))
                        (KE_EXT_KNOW b))).
  Proof.
    introv h q same; simpl in *; tcsp.
  Qed.

  (* K(A) -> K(K(A)) *)
  Lemma A3 :
    forall {eo : EventOrdering} (e : Event) (a : KExpression),
      interpret e (KE_IMPLIES
                     (KE_EXT_KNOW a)
                     (KE_EXT_KNOW (KE_EXT_KNOW a))).
  Proof.
    introv h same1 same2.
    apply h.
    apply (kc_same_state_trans _ _ eo' e'); auto.
  Qed.

  (* ~K(A) -> K(~K(A)) *)
  Lemma A4 :
    forall {eo : EventOrdering} (e : Event) (a : KExpression),
      interpret e (KE_IMPLIES
                     (KE_NOT (KE_EXT_KNOW a))
                     (KE_EXT_KNOW (KE_NOT (KE_EXT_KNOW a)))).
  Proof.
    introv h same1 q.
    rewrite interp_KE_NOT in h.
    apply interp_KE_FALSE.
    simpl in *.
    destruct h.
    introv same.
    apply q.
    apply (kc_same_state_trans _ _ eo e); auto.
    apply kc_same_state_sym; auto.
  Qed.

  (* k(d) -> K(k(d)) *)
  Lemma R1_know :
    forall {eo : EventOrdering} (e : Event) (d : kc_data),
      interpret e (KE_IMPLIES
                     (KE_KNOWS d)
                     (KE_EXT_KNOW (KE_KNOWS d))).
  Proof.
    introv h same; simpl in *.
    eapply same_state_preserves_knows_after in same; eauto.
  Qed.

End CalculusSMext.
