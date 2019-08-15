Require Export Quorum.
Require Export ComponentSM.


Section ComponentAxiom.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pm  : @Msg }.
  Context { pda : @DataAuth pd pn }.
  Context { cad : ContainedAuthData }.
  Context { gms : MsgStatus }.
  Context { dtc : @DTimeContext }.
  Context { qc  : @Quorum_context pn}.
  Context { iot : @IOTrusted }.

  Context { base_fun_io       : baseFunIO }.
  Context { base_state_fun    : baseStateFun }.
  Context { trusted_state_fun : trustedStateFun }.


  Class ComponentTrust :=
    MkComponentTrust
      {
        (* Type of trusted information *)
        ct_trust       : Type;

        ct_auth2trust  : AuthenticatedData -> list ct_trust;

        ct_out2trust   : iot_output -> option ct_trust;

        ct_trust2owner : ct_trust -> node_type;
      }.

  Context { ctp : ComponentTrust }.


  Class ComponentAuth :=
    MkComponentAuth
      {
        ca_create : forall {eo : EventOrdering} (e : Event) (a : data), Tokens;
        ca_verify : forall {eo : EventOrdering} (e : Event) (a : AuthenticatedData), bool;
      }.

  Context { cap : ComponentAuth }.

  Definition trust_in_auth (a : AuthenticatedData) (opt : option ct_trust) :=
    match opt with
    | Some t => In t (ct_auth2trust a)
    | None => True
    end.

  Record opTrust (a : AuthenticatedData) :=
    MkOpTrust
      {
        opt_T :> option ct_trust;
        opt_C : trust_in_auth a opt_T;
      }.
  Global Arguments opt_T [a] _.
  Global Arguments opt_C [a] _.

  Definition AXIOM_authenticated_messages_were_sent_or_byz {F}
             (eo : EventOrdering)
             (sys : M_USystem F) :=
    forall (e : Event)
           (a : AuthenticatedData)
           (opt : opTrust a),
      In a (bind_op_list get_contained_authenticated_data (trigger_op e))
      (* if we didn't verify the message then it could come from a Byzantine
         node that is impersonating someone else, without the logic knowing it *)
      -> ca_verify e a = true
      -> exists e',
          e' ≺ e (* event e was triggered by an earlier send event e' *)

          (* e' generated the authentication code *)
          (* TODO: the message was authenticated using a subset of the keys! *)
          /\ am_auth a = ca_create e (am_data a)

          /\
          (
            (
              isCorrect e'
              /\
              exists m dst delay,

                In a (get_contained_authenticated_data m)

                /\
                (* e' sent the message to some node "dst"
                   following the protocol as described by [sys]
                   (only if the message is a 'protocol' message though),
                   which eventually got to e *)
                (is_protocol_message m = true
                 -> In (MkDMsg m dst delay) (M_output_sys_on_event sys e'))

                /\
                (* e' is the node mentioned in the authenticated message *)
                data_auth (loc e) (am_data a) = Some (loc e')
            )

            \/

            (
              isByz e'
              /\
              exists t n,
                opt_T opt = Some t
                /\ ct_out2trust (M_byz_output_sys_on_event_to_byz sys e') = Some t
                /\ loc e' = node2name n
                /\ ct_trust2owner t = n
            )

            \/

            (* e' is not the node mentioned in the authenticated message
               because he got the keys of some other e''
             *)
            (
              (* e' is byzantine because it's using the keys of e'' (see below) *)
              isByz e'
              /\
              opt_T opt = None
              /\
              exists e'',
                e'' ≼ e'
                /\
                (* e'' is byzantine because it lost it keys *)
                isByz e''
                /\
                (* the sender mentioned in m is actually e'' and not e' but e' sent the message impersonating e''...what a nerve! *)
                data_auth (loc e) (am_data a) = Some (loc e'')
                /\
                (* e' got the key for (loc e) from e'' *)
                got_key_for (loc e) (keys e'') (keys e')
            )
          ).

End ComponentAxiom.
