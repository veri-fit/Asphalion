Require Export DTimeN.
Require Export PISTISheader.
Require Export ComponentSM.
Require Export ComponentSM2.
Require Export toString.
Require Export List.


Section PISTIS.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : DTimeContext }.

  Context { pistis_context : PISTIS_context }.
  Context { m_initial_keys : PISTIS_initial_keys }.


  (* ===============================================================
     State
     =============================================================== *)

  Record MAIN_state :=
    Build_State
      {

        local_keys : local_key_map;

        signatures : Rep ->  option (Value * Signs);

      }.

  Definition initial_state (r : Rep) : MAIN_state :=
    Build_State
      (pistis_initial_keys (PISTIS_replica r))
      (fun _ => None).

  Definition initialize_echo (s : MAIN_state) (r : Rep) (v : Value) (l : Signs) : MAIN_state :=
    Build_State
      (local_keys s)
      (fun r' => if rep_deq r r' then Some (v,l) else signatures s r').


  (* ===============================================================
     Parameters
     =============================================================== *)

  Global Instance PISTIS_I_baseFunIO : baseFunIO :=
    MkBaseFunIO (fun (nm : CompName) => CIOdef).

  Global Instance PISTIS_I_baseStateFun : baseStateFun :=
    MkBaseStateFun (fun (nm : CompName) =>
                      if CompNameKindDeq (comp_name_kind nm) msg_comp_name_kind
                      then MAIN_state
                      else unit).

  Global Instance PISTIS_I_IOTrustedFun : IOTrustedFun := MkIOTrustedFun (fun _ => MkIOTrusted unit unit tt).
  Global Instance PISTIS_I_trustedStateFun : trustedStateFun := MkTrustedStateFun (fun _ => MAIN_state).


  (* ===============================================================
     Messages
     =============================================================== *)

  Inductive PISTIS_bare_msg : Set :=
  | PISTIS_bare_echo    (e : Bare_Echo)
  | PISTIS_bare_deliver (e : Echo)
  | PISTIS_bare_hb      (h : Bare_HB).

  Inductive PISTIS_msg :=
  | PISTIS_echo    (e : Echo)
  | PISTIS_deliver (d : Deliver)
  | PISTIS_hb      (h : HB).

  Global Instance PISTIS_I_Msg : Msg := MkMsg PISTIS_msg.


  (* ===============================================================
     Crypto
     =============================================================== *)

  Global Instance PISTIS_I_Data : Data := MkData PISTIS_bare_msg.

  Global Instance PISTIS_I_Key : Key := MkKey PISTIS_sending_key PISTIS_receiving_key.

  Class PISTISauth :=
    MkPISTISauth
      {
        PISTIScreate : data -> sending_keys -> Tokens;
        PISTISverify : data -> name -> receiving_key -> Token -> bool
      }.
  Context { pistis_auth : PISTISauth }.

  Global Instance PISTIS_I_AuthFun : AuthFun :=
    MkAuthFun
      PISTIScreate
      PISTISverify.

  Class PISTISinitial_keys :=
    MkPISTISinitial_keys {
        initial_keys : key_map;
      }.

  Context { pistis_initial_keys : PISTISinitial_keys }.


  (* ===============================================================
     Handlers
     =============================================================== *)

  Definition MAINname := msg_comp_name 0.

  Definition on_echo {A} (m : PISTIS_msg) (d : unit -> Proc A) (f : Echo -> Proc A) : Proc A :=
    match m with
    | PISTIS_echo m => f m
    | _ => d tt
    end.

  Notation "a >>oe>>=( d ) f" := (on_echo a d f) (at level 80, right associativity).

  Definition mk_auth
             (r : Rep)
             (s : SeqNum)
             (v : Value)
             (keys : local_key_map) : Tokens :=
    let b := bare_echo r s v in
    authenticate (PISTIS_bare_echo b) keys.

  Definition handle_echo (slf : Rep) (n : SeqNum) : UProc MAINname MAIN_state :=
    fun state m =>
      m >>oe>>=(fun _ => [R](state,[])) fun m =>
      let keys  := local_keys state in
      let rep   := echo_r m in
      let seq   := echo_s m in
      let val   := echo_v m in
      let signs := echo_a m in
      if SeqNumDeq seq n then

        match signatures state rep with
        | None =>

          let sign := MkSign slf (mk_auth rep seq val keys) in
          let signs' := sign :: signs in
          let state' := initialize_echo state rep val signs' in

          (* execute proof-of-connectivity in piggyback mode *)

          if le_dec (length signs') (2 * F) then

            (* execute t-diffuse(rep,seq,val,T,echo) *)
            [R](state',[])

          else (* execute deliver-msg(rep,seq,val,signs') *)
            [R](state',[])
        | Some (v,l) => [R](state,[])
        end

      else [R](state,[]).

  Definition handle_deliver (slf : Rep) (n : SeqNum) : UProc MAINname MAIN_state :=
    fun state m =>
      [R] (state, []).

  Definition handle_hb (slf : Rep) (n : SeqNum) : UProc MAINname MAIN_state :=
    fun state m =>
      [R] (state, []).

  Definition MAIN_update (slf : Rep) (n : SeqNum) : M_Update 1 MAINname _ :=
    fun (s : MAIN_state) m =>
      interp_s_proc
        (match m with
         | PISTIS_echo    _ => handle_echo    slf n s m
         | PISTIS_deliver _ => handle_deliver slf n s m
         | PISTIS_hb      _ => handle_hb      slf n s m
         end).

  Definition MAIN_comp (r : Rep) (s : SeqNum) : n_proc 2 MAINname :=
    build_m_sm (MAIN_update r s) (initial_state r).

End PISTIS.
