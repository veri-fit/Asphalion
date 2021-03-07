Require Export CalculusSMtime.


Section CalculusSMtime3.

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


  Definition KE_DISS_FIRST (d : kc_data) :=
    KE_AND
      (KE_DISS d)
      (KE_LOCAL_FORALL_BEFORE
         (KE_IMPLIES
            (KE_DISS d)
            KE_FALSE)).

  Definition KE_DISS_FOR (u T : PosDTime) (d : kc_data) := KE_TRUE.

  Definition IntersectingDelivery (f : nat) (T : PosDTime) :=
    KE_ALL_TIME
      (fun t =>
         KE_ALL_DATA
           (fun deliver =>
              KE_IMPLIESn
                [KE_CORRECT,
                 KE_IS_TIME t,
                 KE_HAS_CAT deliver "deliver",
                 KE_DISS_FIRST deliver]
                (KE_EX_NODES
                   (fun (v : nodes (S f)) =>
                      (KE_EX_TIME
                         (fun u =>
                            KE_AND
                              (KE_LE_TIME u (pdt_plus t T)%dtime)
                              (KE_ALL_NODE
                                 (fun n =>
                                    KE_IMPLIESn
                                      [KE_CORRECT,
                                       KE_NODE_IN n v]
                                      (KE_AT_TIME
                                         u
                                         (KE_ANDS
                                            [KE_AT n,
                                             KE_DISS_FOR u T deliver])))))))))).

End CalculusSMtime3.
