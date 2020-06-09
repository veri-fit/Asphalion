Require Export CalculusSM.


Section CalculusSMdec.

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


  Lemma interpret_dec :
    forall (exp : KExpression) (eo : EventOrdering) (e : Event),
      decidable (interpret e exp).
  Proof.
    induction exp; introv; simpl.

    { destruct (IHexp1 _ e) as [d1|d1]; try (complete (right; intro xx; tcsp)).
      destruct (IHexp2 _ e) as [d2|d2]; try (complete (right; intro xx; tcsp)).
      left; tcsp. }

    { destruct (IHexp1 _ e) as [d1|d1]; try (complete (left; tcsp)).
      destruct (IHexp2 _ e) as [d2|d2]; try (complete (left; tcsp)).
      right; intro xx; tcsp. }

    { destruct (IHexp2 _ e) as [d1|d1]; try (complete (left; tcsp)).
      destruct (IHexp1 _ e) as [d2|d2]; try (complete (left; tcsp)).
      right; intro xx; tcsp. }

    { (* existential and universal will be decidable if the domains are finite and decidable *)

  Qed.



End CalculusSMdec.
