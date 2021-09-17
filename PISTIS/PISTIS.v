Require Export DTimeN.
Require Export ComponentSM.
Require Export ComponentSM2.
Require Export ComponentAxiom.
Require Export PISTISheader.
Require Export toString.
Require Export List.


Section PISTIS.

  Local Open Scope eo.
  Local Open Scope proc.

  Global Instance dtime_nat : DTimeContext := DTimeContextN.

  Context { pistis_context : PISTIS_context }.
  Context { m_initial_keys : PISTIS_initial_keys }.


  (* ===============================================================
     State
     =============================================================== *)

  Class PistisParams1 :=
    MkPistisParams1
      {
        (* payload *)
        payload          : Set;
        payload_dec      : Deq payload;
        default_payload  : payload;

        (* we assume a BCAST component *)
        BCAST_state      : Set;
        BCAST_init_state : Rep -> BCAST_state;

        (* further parameters *)
        num_send_repeats : nat;      (* number of times a messages must be sent repeatedly *)
        max_delay        : PosDTime; (* maximum transmission delay *)
        min_replies      : nat;      (* minimum number of replies to receive to stay active *)
      }.
  Context { pistis_params1 : PistisParams1 }.

  Definition payloads := list payload.

  Record InputEntry :=
    MkInputEntry {
        ientry_payload : payload;
        ientry_nodes   : list Rep;
      }.

  Definition InputEntries := list InputEntry.

  Record MAIN_state :=
    Build_State
      {

        local_keys : local_key_map;
        inputs     : InputEntries;

      }.

  Definition MAIN_init_state (r : Rep) : MAIN_state :=
    Build_State
      (pistis_initial_keys (PISTIS_replica r))
      [].

(*  Definition initialize_echo (s : MAIN_state) (r : Rep) (v : Value) (l : Signs) : MAIN_state :=
    Build_State
      (local_keys s)
      (fun r' => if rep_deq r r' then Some (v,l) else signatures s r').*)



  (* ===============================================================
     Messages
     =============================================================== *)

  Record Alert : Set:=
    alert
      {
        alert_p :> payload;
      }.

  Record Push : Set:=
    push
      {
        push_p :> payload;
        push_a : Sign;
      }.

  Inductive PISTIS_bare_msg : Set :=
  | PISTIS_bare_payload (e : payload) (i : Rep)
  | PISTIS_bare_alert   (a : Alert).

  Inductive PISTIS_msg :=
  | PISTIS_push  (p : Push)
  | PISTIS_alert (a : Alert).

  Global Instance PISTIS_I_Msg : Msg :=
    MkMsg
      PISTIS_msg
      (PISTIS_alert (alert default_payload)).

  Definition PISTISmsg2status (m : PISTIS_msg) : msg_status :=
    match m with
    | PISTIS_push  _ => MSG_STATUS_PROTOCOL
    | PISTIS_alert _ => MSG_STATUS_INTERNAL
    end.

  Global Instance PISTIS_I_MsgStatus : MsgStatus := MkMsgStatus PISTISmsg2status.


  (* ===============================================================
     Trusted
     =============================================================== *)

  Global Instance PISTIS_I_IOTrustedFun : IOTrustedFun := MkIOTrustedFun (fun _ => MkIOTrusted unit unit tt).
  Global Instance PISTIS_I_trustedStateFun : trustedStateFun := MkTrustedStateFun (fun _ => unit).


  (* ===============================================================
     Components
     =============================================================== *)

  Inductive BCAST_input_interface :=
  | push_in (p : Push).

  Inductive BCAST_output_interface :=
  | push_out (ps : payloads).

  Definition CIObcast : ComponentIO :=
    MkComponentIO BCAST_input_interface BCAST_output_interface (push_out []).

  Definition BCASTname : CompName := MkCN "BCAST" 0 false.

  Definition MAINname := msg_comp_name 0.


  (* ===============================================================
     Parameters
     =============================================================== *)

  Global Instance PISTIS_I_baseFunIO : baseFunIO :=
    MkBaseFunIO (fun (nm : CompName) =>
                   if CompNameKindDeq (comp_name_kind nm) "BCAST" then CIObcast
                   else CIOdef).

  Global Instance PISTIS_I_baseStateFun : baseStateFun :=
    MkBaseStateFun (fun (nm : CompName) =>
                      if CompNameKindDeq (comp_name_kind nm) "BCAST" then BCAST_state
                      else if CompNameKindDeq (comp_name_kind nm) msg_comp_name_kind
                           then MAIN_state
                           else unit).


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
     No trusted components
     =============================================================== *)

  Definition pistis_trust : Type := unit.
  Definition pistis_auth2trust : AuthenticatedData -> list pistis_trust := fun _ => [].
  Lemma pistis_out2trust :
    forall (cn : PreCompName), iot_output (iot_fun cn) -> option pistis_trust.
  Proof.
    introv i; simpl in *; exact (Some i).
  Qed.
  Definition pistis_trust2owner : pistis_trust -> option node_type := fun _ => None.

  Global Instance PISTIS_I_ComponentTrust : ComponentTrust :=
    MkComponentTrust
      pistis_trust
      pistis_auth2trust
      pistis_out2trust
      pistis_trust2owner.


  (* ===============================================================
     Data Auth
     =============================================================== *)

  Definition PISTIS_data_auth (n : name) (d : data) : option name :=
    match d with
    | PISTIS_bare_payload p r => Some (PISTIS_replica r)
    | PISTIS_bare_alert a  => Some n
    end.

  Global Instance PISTIS_I_DataAuth : DataAuth := MkDataAuth PISTIS_data_auth.

  Definition push2auth_data (p : Push) : AuthenticatedData :=
    MkAuthData (PISTIS_bare_payload (push_p p) (sign_name (push_a p))) (sign_token (push_a p)).

  Definition PISTIS_get_contained_auth_data (m : msg) : list AuthenticatedData :=
    match m with
    | PISTIS_push  p => [push2auth_data p]
    | PISTIS_alert a => []
    end.

  Global Instance PISTIS_I_ContainedAuthData : ContainedAuthData :=
    MkContainedAuthData PISTIS_get_contained_auth_data.


  (* ===============================================================
     Handlers
     =============================================================== *)

  Class PistisParams2 :=
    MkPistisParams2
      {
        BCAST_proc : Rep -> UProc BCASTname BCAST_state;
      }.
  Context { pistis_params2 : PistisParams2 }.


  Definition on_push {S A} (m : PISTIS_msg) (d : unit -> HProc S A) (f : Push -> HProc S A) : HProc S A :=
    match m with
    | PISTIS_push m => f m
    | _ => d tt
    end.

  Notation "a >>op>>=( d ) f" := (on_push a d f) (at level 80, right associativity).

  Definition on_alert {S A} (m : PISTIS_msg) (d : unit -> HProc S A) (f : Alert -> HProc S A) : HProc S A :=
    match m with
    | PISTIS_alert m => f m
    | _ => d tt
    end.

  Notation "a >>oa>>=( d ) f" := (on_alert a d f) (at level 80, right associativity).

  Definition on_push_out {A} (f : payloads -> A) (d : unit -> A) (out : BCAST_output_interface) : A :=
    match out with
    | push_out p => f p
    end.

  Definition call_push {S A} (t : PosDTime) (p : Push) (d : unit -> HProc S A) (f : payloads -> HProc S A) :=
    BCASTname {C} (push_in p) @ t {>>=} on_push_out f d.

  Notation "a >>p>>=( t , d ) f" := (call_push t a d f) (at level 80, right associativity).

  Definition add_sender (s : Sign) (l : list Rep) : list Rep :=
    if in_dec rep_deq (sign_name s) l
    then l
    else sign_name s :: l.

  Fixpoint add_senders (signs : Signs) (l : list Rep) : list Rep :=
    match signs with
    | [] => l
    | s :: ss => add_senders ss (add_sender s l)
    end.

  (* We only update the list of inputs in [e] with [i] if the entry is for the
     same payload as [i]'s and [i]'s sender is not already in [e]
   *)
  Definition updateIn (p : Push) (e : InputEntry) : InputEntry :=
    match e with
    | MkInputEntry pl ins =>
      if payload_dec (push_p p) pl
      then MkInputEntry pl (add_sender (push_a p) ins)
      else MkInputEntry pl ins
    end.

  Definition updateIns (p : Push) (l : InputEntries) : InputEntries :=
    map (updateIn p) l.

  Definition updateInsOuts (p : Push) (plds : payloads) (l : InputEntries) : InputEntries :=
    updateIns p l ++ map (fun pl => MkInputEntry pl []) plds.

  (* true if [p] occurs in [l] *)
  Fixpoint payloadInIns (l : InputEntries) (p : payload) : bool :=
    match l with
      [] => false
    | e :: es => if payload_dec p (ientry_payload e) then true else payloadInIns es p
    end.

  Definition thinIns (l : InputEntries) (plds : payloads) : payloads :=
    filter (fun p => negb (payloadInIns l p)) plds.

(*  Definition mk_auth
             (r : Rep)
             (s : SeqNum)
             (v : Value)
             (keys : local_key_map) : Tokens :=
    let b := bare_echo r s v in
    authenticate (PISTIS_bare_echo b) keys.*)

  Definition other_replicas (r : Rep) : list Rep := remove_elt rep_deq r reps.

  Definition other_names (r : Rep) : list name := map PISTIS_replica (other_replicas r).

  Definition broadcast2others (slf : Rep) F : DirectedMsg :=
    F (other_names slf).

  Definition broadcast2all F : DirectedMsgs := map F (map PISTIS_replica reps).

  Definition mk_push (t : PosDTime) (p : Push) (n : list name) : DirectedMsg :=
    MkDMsg (PISTIS_push p) n t.

  Definition auth_for_push (slf : Rep) (keys : local_key_map) (p : payload) : Tokens :=
    authenticate (PISTIS_bare_payload p slf) keys.

  Definition mk_auth_push (slf : Rep) (keys : local_key_map) (p : payload) : Push :=
    push p (MkSign slf (auth_for_push slf keys p)).

  Definition auth_data2push (a : AuthenticatedData) : option Push :=
    match a with
    | MkAuthData (PISTIS_bare_payload p r) toks => Some (push p (MkSign r toks))
    | MkAuthData (PISTIS_bare_alert a) toks => None
    end.

  Definition verify_auth_push (slf : Rep) (keys : local_key_map) (p : Push) : bool :=
    verify_authenticated_data
      (PISTIS_replica slf)
      (push2auth_data p)
      keys.

  Fixpoint scheduleOutput k (slf : Rep) (t : PosDTime) (p : Push) : list DirectedMsg :=
    match k with
    | 0 => []
    | S k =>
      broadcast2others slf (mk_push t p)
      :: scheduleOutput k slf (pdt_plus t max_delay) p
    end.

  Definition alert_delay (t : PosDTime) : PosDTime :=
    pdt_plus t (pdt_mult (nat2pdt num_send_repeats) max_delay).

  Definition mk_alert (t : PosDTime) (slf : Rep) (p : payload) : DirectedMsg :=
    MkDMsg
      (PISTIS_alert (alert p))
      [PISTIS_replica slf]
      (alert_delay t).

  Definition handle_push (slf : Rep) : UHProc MAINname MAIN_state :=
    fun state t m =>
      m >>op>>=(fun _ => {R} state {->} []) fun (m : Push) =>
      let keys    := local_keys state in
      let ins     := inputs state in
      let payload := push_p m in
      let signs   := push_a m in
      if negb (verify_auth_push slf keys m) then {R} state {->} [] else

      m >>p>>=(t , fun _ => {R} state {->} []) fun plds =>

      (* we remove the payloads that we have seen before *)
      let plds' := thinIns ins plds in

      (* we have to store the input in the state *)
      let ins' := updateInsOuts m plds' ins in

      (* we now create the outputs to send out *)
      let pushes := map (mk_auth_push slf keys) plds' in
      let outs := flat_map (scheduleOutput num_send_repeats slf t) pushes in
      (* these are self messages acting as timers *)
      let alrts := map (mk_alert t slf) plds' in

      (* we compute the new state *)
      let state' := Build_State keys ins' in

      {R} state' {->} (alrts ++ outs).

  Fixpoint find_ie (p : payload) (l : InputEntries) : bool :=
    match l with
    | [] => false
    | e :: es =>
      if payload_dec p (ientry_payload e)
      then min_replies <=? length (ientry_nodes e)
      else find_ie p es
    end.

  (* on receipt of an alert, we check whether the corresponding payload
     has received enough replies
     - if yes, then we stay active
     - if not, we become passive (halt here)
   *)
  Definition handle_alert (slf : Rep) : UHProc MAINname MAIN_state :=
    fun state t m =>
      m >>oa>>=(fun _ => {R} state {->} []) fun a =>
      let ins := inputs state in
      if find_ie a ins
      then {R} state {->} []
      else {H} [].

  Definition MAIN_proc (slf : Rep) : UHProc MAINname MAIN_state :=
    fun (s : MAIN_state) t m =>
      match m with
      | PISTIS_push  _ => handle_push  slf s t m
      | PISTIS_alert _ => handle_alert slf s t m
      end.

  Definition MAIN_update (slf : Rep) : M_Update 1 MAINname _ :=
    hproc2upd (MAIN_proc slf).

  Definition MAIN_comp_st (r : Rep) (s : MAIN_state) : n_proc 2 MAINname :=
    build_m_sm (MAIN_update r) s.

  Definition MAIN_comp (r : Rep) : n_proc 2 MAINname :=
    MAIN_comp_st r (MAIN_init_state r).


  Definition BCAST_update (slf : Rep) : M_Update 0 BCASTname _ :=
    proc2upd (BCAST_proc slf).

  Definition BCAST_comp_st (r : Rep) (s : BCAST_state) : n_proc 1 BCASTname :=
    build_m_sm (BCAST_update r) s.

  Definition BCAST_comp (r : Rep) : n_proc 1 BCASTname :=
    BCAST_comp_st r (BCAST_init_state r).


  Notation ls20 := (LocalSystem 2 0).

  Definition PISTISls_st (n : Rep) sm sb : ls20 :=
    [MkPProc _ (MAIN_comp_st n sm), incr_n_nproc (MkPProc _ (BCAST_comp_st n sb))].

  Definition PISTISls (n : Rep) : ls20 :=
    [MkPProc _ (MAIN_comp n), incr_n_nproc (MkPProc _ (BCAST_comp n))].

  Definition PISTISfls :=
    MkFunLevelSpace
      (fun n =>
         match n with
         | PISTIS_replica _ => 2
         | _ => 0
         end)
      (fun n =>
         match n with
         | PISTIS_replica _ => 0
         | _ => 0
         end).

  Definition PISTISsys : M_USystem PISTISfls (*name -> M_StateMachine 2 msg_comp_name*) :=
    fun name =>
      match name with
      | PISTIS_replica n => PISTISls n
      | _ => empty_ls _ _
      end.


  (* ===============================================================
     Auth Comp
     =============================================================== *)

  Definition pistis_create (eo : EventOrdering) (e : Event) (a : data) : Tokens :=
    match a with
    | PISTIS_bare_payload p r =>
      match M_state_sys_before_event PISTISsys e MAINname with
      | Some s => auth_for_push r (local_keys s) p
      | None => []
      end
    | PISTIS_bare_alert a => []
    end.

  Definition pistis_verify (eo : EventOrdering) (e : Event) (a : AuthenticatedData) : bool :=
    match loc e, M_state_sys_before_event PISTISsys e MAINname, auth_data2push a with
    | PISTIS_replica n, Some s, Some p => verify_auth_push n (local_keys s) p
    | _,_,_ => false
    end.

  Global Instance PISTIS_I_ComponentAuth : ComponentAuth :=
    MkComponentAuth
      pistis_create
      pistis_verify.


  (* ===============================================================
     Properties
     =============================================================== *)

  (* We assume that all self-messages are received at the delay
     - The delay of 'alert' messages it the time they are received,
       as opposed to other messages, where the delay is the time they are sent
   *)
  Definition alerts_on_time (eo : EventOrdering) :=
    forall (e : Event) (t : PosDTime) (n : Rep) (p : payload),
      In (mk_alert t n p) (M_output_sys_on_event PISTISsys e)
      -> exists (e' : Event),
        e ⊏ e'
        /\ time e' = alert_delay t
        /\ trigger_op e' = Some (PISTIS_alert (alert p)).

  Definition run_to_similar {L S} {eo : EventOrdering} (e : Event) (ls : LocalSystem L S) :=
    exists ls',
      M_run_ls_on_event ls e = Some ls'
      /\ similar_subs ls ls'.

  (* a node is considered active if it is always correct
     and executes to similar systems, i.e., does not halt *)
  Definition is_active (n : Rep) (eo : EventOrdering) :=
    forall (e : Event),
      loc e = PISTIS_replica n
      -> isCorrect e /\ run_to_similar e (PISTISls n).

  Definition bounded_event {eo : EventOrdering} (e : Event) (t1 t2 : PosDTime) :=
    pdt_le t1 (time e) /\ pdt_le (time e) t2.

  Lemma highest_component_PISTISls :
    forall n, highest_component MAINname (PISTISls n).
  Proof.
    introv; exists (MkPProc _ (MAIN_comp n)); simpl; dands; auto.
  Qed.
  Hint Resolve highest_component_PISTISls : pistis.

  Lemma wf_procs_PISTISls :
    forall n, wf_procs (PISTISls n).
  Proof.
    introv; unfold wf_procs; simpl; auto.
  Qed.
  Hint Resolve wf_procs_PISTISls : pistis.

  Lemma is_hproc_n_proc_MAIN_comp :
    forall n, is_hproc_n_proc (MAIN_comp n).
  Proof.
    introv.
    unfold is_hproc_n_proc.
    exists (MAIN_proc n); tcsp.
  Qed.
  Hint Resolve is_hproc_n_proc_MAIN_comp : pistis.

  Lemma is_proc_n_proc_incr_BCAST_comp :
    forall n, is_proc_n_proc (incr_n_proc (BCAST_comp n)).
  Proof.
    introv.
    unfold is_proc_n_proc; simpl.
    exists (BCAST_proc n); tcsp.
  Qed.
  Hint Resolve is_proc_n_proc_incr_BCAST_comp : pistis.

  Lemma is_proc_n_proc_BCAST_comp_st :
    forall n s, is_proc_n_proc (BCAST_comp_st n s).
  Proof.
    introv.
    unfold is_proc_n_proc; simpl.
    exists (BCAST_proc n); tcsp.
  Qed.
  Hint Resolve is_proc_n_proc_BCAST_comp_st : pistis.

  Lemma almsot_procs_PISTISls :
    forall n, almost_procs (PISTISls n) (msg_comp_name 0).
  Proof.
    introv i; simpl in *; repndors; subst; simpl in *; tcsp; eauto 3 with pistis.
  Qed.
  Hint Resolve almsot_procs_PISTISls : pistis.


  (* MOVE to ComponentSM2 *)
  Lemma similar_subs_preserves_highest_component :
    forall {cn} {n} (l k : n_procs n),
      similar_subs l k
      -> highest_component cn l
      -> highest_component cn k.
  Proof.
    introv sim hc; unfold highest_component in *; exrepnd.
    eapply in_similar_subs_implies in hc1; eauto; exrepnd.
    exists q; dands; simpl; auto.
    { apply similar_procs_implies_same_name in hc3; try congruence. }
    { destruct p as [x p], q as [y q]; subst; simpl in *.
      inversion hc3 as [? ? ? ? xxx]; subst; simpl in *; GC.
      match goal with
      | [ H : context[p] |- _ ] => rename H into h1
      end.
      match goal with
      | [ H : context[q] |- _ ] => rename H into h2
      end.
      apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
      apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
      apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
      apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
      apply similar_sms_implies_eq_sm2levels in xxx; try congruence. }
  Qed.
  Hint Resolve similar_subs_preserves_highest_component : comp.


  (* MOVE to ComponentSM2 *)
  Lemma M_run_ls_on_op_inputs_nil :
    forall {cn} {n} l (ls : n_procs n),
      M_run_ls_on_op_inputs [] cn l = Some ls
      -> ls = [].
  Proof.
    induction l; introv h; simpl in *; ginv; auto.
    destruct a; simpl in *; ginv.
  Qed.

  (* MOVE to ComponentSM2 *)
  Lemma almost_M_run_ls_on_op_inputs_preserves_subs :
    forall cn l {n} (ls1 ls2 : n_procs n),
      highest_component cn ls1
      -> wf_procs ls1
      -> almost_procs ls1 cn
      -> M_run_ls_on_op_inputs ls1 cn l = Some ls2
      -> (wf_procs ls2
          /\ almost_procs ls2 cn
          /\ similar_subs ls1 ls2
          (*/\ run_subs_leaves ls1 ls2*)) \/ ls2 = [].
  Proof.
    induction l; introv hc wf aps run; simpl in *; ginv; tcsp.
    { left; dands; eauto 2 with comp. }
    apply map_option_Some in run; exrepnd; subst; simpl in *; rev_Some.

    unfold M_run_ls_on_input_ls in run0.
    remember (M_run_ls_on_input ls1 cn a1 a0) as run; symmetry in Heqrun; repnd; simpl in *.
    pose proof (almost_M_run_ls_on_input_preserves_subs cn a1 a0 ls1 run1 run) as z.
    repeat (autodimp z hyp); repndors; subst; repnd; tcsp.
    { apply IHl in run0; auto; repndors; repnd; eauto 3 with comp.
      left; dands; eauto 3 with comp. }
    { apply M_run_ls_on_op_inputs_nil in run0; auto. }
  Qed.

  (* MOVE to ComponentSM2 *)
  Lemma almost_M_run_ls_before_Event_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      highest_component (msg_comp_name S) ls1
      -> wf_procs ls1
      -> almost_procs ls1 (msg_comp_name S)
      -> M_run_ls_before_event ls1 e = Some ls2
      -> (wf_procs ls2
          /\ almost_procs ls2 (msg_comp_name S)
          /\ similar_subs ls1 ls2
          (*/\ run_subs_leaves ls1 ls2*)) \/ ls2 = [].
  Proof.
    introv hc wf aps run.
    apply almost_M_run_ls_on_op_inputs_preserves_subs in run; auto.
  Qed.

  (* MOVE to ComponentSM2 *)
  Lemma M_run_ls_on_input_nil :
    forall cn n t (i : cio_I (fio cn)),
      M_run_ls_on_input ([] : n_procs n) cn t i = ([], None).
  Proof.
    introv; unfold M_run_ls_on_input; simpl; tcsp.
  Qed.


  (* MOVE to ComponentSM2 *)
  (* if [ls] is made out of [Proc]s except for its main component, which is a [HProc],
     then if [ls] outputs something, it means that it was still similar to its initial
     form when it handled the event
   *)
  Lemma almost_proc_out_implies_similar_subs :
    forall {L S} {eo : EventOrdering} (e : Event) (ls ls' : LocalSystem L S) o,
      highest_component (msg_comp_name S) ls
      -> almost_procs ls (msg_comp_name S)
      -> wf_procs ls
      -> M_run_ls_before_event ls e = Some ls'
      -> In o (M_output_ls_on_this_one_event ls' e)
      -> similar_subs ls ls'.
  Proof.
    introv hc sim wf run i.
    unfold M_run_ls_before_event in run.
    remember (map time_trigger_op History( e)) as l; clear Heql.
    apply in_olist2list in i; exrepnd.
    remember (time_trigger_op e) as trig; clear Heqtrig.
    destruct trig; repnd; simpl in *; ginv;[].

    unfold M_run_ls_on_input_out in i1.

    revert dependent ls.
    induction l; introv hc sim wf i; simpl in *; ginv; auto.

    { inversion i; subst; eauto 3 with comp. }

    destruct a; repnd; simpl in *; ginv;[].
    unfold M_run_ls_on_input_ls in i; simpl in *.
    remember (M_run_ls_on_input ls (msg_comp_name S) p2 p1) as run; symmetry in Heqrun.
    repnd; simpl in *.

    pose proof (almost_M_run_ls_on_input_preserves_subs
                  (msg_comp_name S)
                  p2 p1 ls run0 run) as w.
    repeat (autodimp w hyp);[].

    repndors; repnd.

    { eapply similar_subs_trans;[eauto|].
      apply almost_M_run_ls_on_op_inputs_preserves_subs in i; eauto 3 with comp;[].
      repndors; subst; tcsp.
      rewrite M_run_ls_on_input_nil in i1; simpl in *; ginv. }

    subst; simpl in *.
    apply M_run_ls_on_op_inputs_nil in i; subst.
    rewrite M_run_ls_on_input_nil in i1; simpl in *; ginv.
  Qed.

  Lemma similar_subs_PISTISls_implies :
    forall n ls,
      similar_subs (PISTISls n) ls
      -> exists sm sb, ls = PISTISls_st n sm sb.
  Proof.
    introv sim.
    inversion sim as [|? ? ? ? simp1 sims1]; subst; simpl in *; clear sim.
    inversion sims1 as [|? ? ? ? simp2 sims2]; subst; simpl in *; clear sims1.
    inversion sims2; subst; clear sims2.

    destruct p0 as [n0 p0].
    destruct p2 as [n2 p2].

    applydup @similar_procs_implies_same_name in simp1; simpl in *; subst.
    applydup @similar_procs_implies_same_name in simp2; simpl in *; subst.
    apply @similar_procs_implies_same_proc in simp1.
    apply @similar_procs_implies_same_proc in simp2.
    simpl in *.

    destruct p2; tcsp.
    destruct p0; tcsp.
    destruct b; simpl in *; tcsp.

    destruct a as [upd1 st1].
    destruct a0 as [upd2 st2].
    simpl in *.
    unfold similar_sms_at in *; simpl in *; subst.
    exists st1 st2; auto.
  Qed.

  Lemma on_comp_PISTISls_st :
    forall r sm sb {A} (F : n_proc 2 (msg_comp_name 0) -> A) (m : A),
      on_comp (PISTISls_st r sm sb) F m
      = F (MAIN_comp_st r sm).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite on_comp_PISTISls_st : pistis.

  (* MOVE *)
  Definition lower_out_break {n} {A} {B}
             (l : n_procs (S n))
             (F : n_procs (S n) -> A -> B) : n_procs n -> A -> B :=
    fun k a => F (update_subs_decr l k) a.

  Lemma M_break_M_run_sm_on_input_MAIN_comp_st :
    forall {O} r sm t i subs (F : n_procs 2 -> hoption MAIN_state * DirectedMsgs -> O),
      M_break (M_run_sm_on_input (MAIN_comp_st r sm) t i) subs F
      = match i with
        | PISTIS_push  _ => M_break (interp_hproc (handle_push  r sm t i)) (decr_n_procs subs) (lower_out_break subs F)
        | PISTIS_alert _ => M_break (interp_hproc (handle_alert r sm t i)) (decr_n_procs subs) (lower_out_break subs F)
        end.
  Proof.
    introv.
    unfold M_run_sm_on_input.
    destruct i; introv; simpl; auto;
      try (complete (unfold M_on_decr, M_break, MAIN_update, MAIN_proc, MAIN_proc, hproc2upd;
                     simpl; repeat dest_cases w; ginv)).
  Qed.
  Hint Rewrite @M_break_M_run_sm_on_input_MAIN_comp_st : pistis.

  Ltac unfold_handler :=
    match goal with
    | [ H : context[handle_push]  |- _ ] => unfold handle_push  in H
    | [ H : context[handle_alert] |- _ ] => unfold handle_alert in H
    end.

  Lemma decr_n_procs_PISTISls_st :
    forall n sm sb,
      decr_n_procs (PISTISls_st n sm sb) = [MkPProc _ (BCAST_comp_st n sb)].
  Proof.
    tcsp.
  Qed.
  Hint Rewrite decr_n_procs_PISTISls_st : pistis.

  Lemma similar_subs_nil_left :
    forall {n} m (l : n_procs n), similar_subs l ([] : n_procs m) -> l = [].
  Proof.
    introv sim; inversion sim; auto.
  Qed.

  Lemma fst_app_n_proc_at_build_mp_sm :
    forall {n} {cn} (upd : M_Update n cn (sf cn)) s t i l,
      fst (app_n_proc_at (build_mp_sm upd s) t i l)
      = fst (upd s t i l).
  Proof.
    introv.
    unfold app_n_proc_at, build_mp_sm, bind_pair, bind; simpl.
    split_pairs; simpl; auto.
  Qed.
  Hint Rewrite @fst_app_n_proc_at_build_mp_sm : comp.

  Lemma snd_snd_app_n_proc_at_build_mp_sm :
    forall {n} {cn} (upd : M_Update n cn (sf cn)) s t i l,
      snd (snd (app_n_proc_at (build_mp_sm upd s) t i l))
      = snd (snd (upd s t i l)).
  Proof.
    introv.
    unfold app_n_proc_at, build_mp_sm, bind_pair, bind; simpl.
    split_pairs; simpl; auto.
  Qed.
  Hint Rewrite @snd_snd_app_n_proc_at_build_mp_sm : comp.

  Lemma fst_snd_app_n_proc_at_build_mp_sm :
    forall {n} {cn} (upd : M_Update n cn (sf cn)) s t i l,
      fst (snd (app_n_proc_at (build_mp_sm upd s) t i l))
      = hoption_map (build_mp_sm upd) (fst (snd (upd s t i l))).
  Proof.
    introv.
    unfold app_n_proc_at, build_mp_sm, bind_pair, bind; simpl.
    split_pairs; simpl; auto.
  Qed.
  Hint Rewrite @fst_snd_app_n_proc_at_build_mp_sm : comp.

  Lemma proc2upd_implies_hsome :
    forall {S} {n} {cn} (p : UProc cn S) s t i (subs : n_procs n) subs' sop o,
      proc2upd p s t i subs = (subs', (sop, o))
      -> exists s', sop = hsome s'.
  Proof.
    introv h; unfold proc2upd, interp_s_proc in *; simpl in *.
    unfold bind in *; simpl in *.
    split_pairs; simpl in *; ginv; eauto.
  Qed.

  Lemma M_break_call_proc_BCASTname :
    forall {O} t i n sb (F : n_procs 1 -> BCAST_output_interface -> O),
      M_break
        (call_proc BCASTname t i)
        [MkPProc _ (BCAST_comp_st n sb)]
        F
      = M_break
          (BCAST_update n sb t i)
          []
          (fun subs out =>
             F (bind_hop [MkPProc _ (BCAST_comp_st n sb)]
                         (fun s => [MkPProc _ (BCAST_comp_st n s)])
                         (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.

    unfold M_break, call_proc; simpl.
    unfold BCAST_update; simpl.
    unfold lift_M_1; simpl; simpl.
    unfold M_on_decr, bind_pair, bind; simpl; autorewrite with comp.
    split_pairs; simpl.
    unfold update_subs_decr, update_subs; simpl.

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input
                  (BCAST_comp_st n sb) t (push_in p) []) as w.
    repeat (autodimp w hyp); eauto 3 with comp pistis;[].
    unfold M_break, M_run_sm_on_input, M_on_sm, M_on_decr in w; simpl in *.
    split_pairs; repnd; simpl in *.
    unfold update_subs_decr, update_subs in *; simpl in *; autorewrite with comp in *.
    apply similar_subs_sym in w0; apply similar_subs_nil_left in w0.
    unfold BCAST_update in w0; simpl in *.
    f_equal.

    remember (proc2upd (BCAST_proc n) sb t (push_in p) []) as z.
    repnd; simpl in *; rewrite w0; simpl.
    symmetry in Heqz.
    pose proof (proc2upd_implies_hsome (BCAST_proc n) sb t (push_in p) ([] : n_procs 0)) as q.
    apply q in Heqz; exrepnd; subst; simpl in *; auto.
  Qed.
  Hint Rewrite @M_break_call_proc_BCASTname : pistis.

  Lemma M_break_BCAST_update :
    forall {O} t i n sb (F : n_procs 0 -> (hoption BCAST_state ## cio_O (fio BCASTname)) -> O),
      M_break
        (BCAST_update n sb t i)
        ([] : n_procs 0)
        F = F [] (snd (BCAST_update n sb t i [])).
  Proof.
    introv.
    unfold M_break; simpl; split_pairs; simpl.

    unfold BCAST_update; simpl.

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input
                  (BCAST_comp_st n sb) t i []) as w.
    repeat (autodimp w hyp); eauto 3 with comp pistis;[].
    unfold M_break, M_run_sm_on_input, M_on_sm, M_on_decr in w; simpl in *.
    split_pairs; repnd; simpl in *.
    unfold update_subs_decr, update_subs in *; simpl in *; autorewrite with comp in *.
    apply similar_subs_sym in w0; apply similar_subs_nil_left in w0.
    unfold BCAST_update in w0; simpl in *.

    remember (fst (proc2upd (BCAST_proc n) sb t i ([] : n_procs 0))) as q.
    simpl in *; rewrite <- Heqq in w0.
    destruct q; simpl in *; ginv.
  Qed.
  Hint Rewrite @M_break_call_proc_BCASTname : pistis.

  Lemma eq_PosDTime :
    forall d1 d2,
      pos_dt_t d1 = pos_dt_t d2 -> d1 = d2.
  Proof.
    introv i; destruct d1 as [t1 c1], d2 as [t2 c2]; simpl in *; subst.
    f_equal.
    apply UIP_dec; apply bool_dec.
  Qed.

  Lemma pdt_mult_0_left :
    forall t, pdt_mult (nat2pdt 0) t = nat2pdt 0.
  Proof.
    introv; apply eq_PosDTime; simpl; auto.
  Qed.
  Hint Rewrite pdt_mult_0_left : pistis.

  Lemma pdt_plus_0_right :
    forall t, pdt_plus t (nat2pdt 0) = t.
  Proof.
    introv; apply eq_PosDTime; simpl.
    unfold N_dt_nat_inj, N_dt_add; simpl.
    rewrite Nat.add_0_r; auto.
  Qed.
  Hint Rewrite pdt_plus_0_right : pistis.

  Lemma pdt_mult_S_left :
    forall j t, pdt_mult (nat2pdt (S j)) t = pdt_plus t (pdt_mult (nat2pdt j) t).
  Proof.
    introv; apply eq_PosDTime; simpl; auto.
  Qed.
  Hint Rewrite pdt_mult_S_left : pistis.

  Lemma pdt_plus_assoc :
    forall a b c, pdt_plus (pdt_plus a b) c = pdt_plus a (pdt_plus b c).
  Proof.
    introv; apply eq_PosDTime; simpl.
    unfold N_dt_add; simpl.
    rewrite Nat.add_assoc; auto.
  Qed.

  Lemma in_scheduleOutput :
    forall d k n t p,
      In d (scheduleOutput k n t p)
      -> exists j,
        j < k
        /\ d = broadcast2others n (mk_push (pdt_plus t (pdt_mult (nat2pdt j) max_delay)) p).
  Proof.
    induction k; introv i; simpl in *; tcsp.
    repndors; subst; tcsp.

    { exists 0; autorewrite with pistis; dands; auto; try omega. }

    apply IHk in i; exrepnd; subst; clear IHk.
    exists (S j); dands; auto; try omega; autorewrite with pistis.
    rewrite pdt_plus_assoc; auto.
  Qed.

  (* the [t] of the alert might be before *)
  Lemma alert_if_push :
    forall n {eo : EventOrdering} (e : Event) t p l,
      loc e = PISTIS_replica n
      -> In (mk_push t p l) (M_output_sys_on_event PISTISsys e)
      -> exists (j : nat) (s : MAIN_state),
          j < num_send_repeats
          /\ t = pdt_plus (time e) (pdt_mult (nat2pdt j) max_delay)
          /\ In (mk_alert (time e) n p) (M_output_sys_on_event PISTISsys e)
          /\ M_state_sys_before_event PISTISsys e MAINname = Some s
          /\ payloadInIns (inputs s) p = false.
  Proof.
    introv eqloc i.
    apply M_output_ls_on_event_as_run in i; exrepnd.
    unfold M_output_sys_on_event in *.
    rewrite M_output_ls_on_event_as_run_before, i1.

    unfold M_output_ls_on_this_one_event in *.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input_out, time_trigger_op, trigger_op in *; simpl in *.
    remember (trigger e) as trig; symmetry in Heqtrig.
    destruct trig; simpl in *; tcsp;[].
    revert dependent ls'.
    rewrite eqloc; introv run i; simpl in *.
    applydup almost_M_run_ls_before_Event_preserves_subs in run; simpl; eauto 3 with comp pistis;[].
    repndors; repnd; subst; simpl in *; tcsp;[].

    applydup @similar_subs_PISTISls_implies in run0; exrepnd; subst.
    allrw @in_olist2list; exrepnd.
    rewrite i1; simpl.

    unfold M_run_ls_on_input in i1; simpl in *.
    autorewrite with comp pistis in *; simpl in *.

    destruct d; simpl in *;
      repeat (autorewrite with comp pistis in *; simpl in *; try dest_cases w);
      try (complete (apply Some_inj in i1; subst; simpl in *; tcsp));[].

    rewrite M_break_BCAST_update in i1; simpl in *.
    remember (snd (snd (BCAST_update n sb (time e) (push_in p0) []))) as out.
    simpl in *; rewrite <- Heqout in i1; symmetry in Heqout.
    destruct out; simpl in *.
    apply Some_inj in i1; subst.
    allrw in_app_iff.
    repndors.

    { apply in_map_iff in i0; exrepnd; ginv. }

    apply in_flat_map in i0; exrepnd.
    apply in_map_iff in i0; exrepnd; subst; simpl in *.
    apply in_scheduleOutput in i1; exrepnd.
    unfold broadcast2others in i0; ginv; simpl in *.

    unfold M_state_sys_before_event, M_state_ls_before_event.
    rewrite eqloc; simpl; rewrite run; simpl.
    unfold state_of_component; simpl.

    exists j sm; dands; auto.

    { apply in_app_iff; left.
      apply in_map_iff; eexists; dands; eauto. }

    { apply filter_In in i2; repnd.
      apply negb_true_iff in i2; auto. }
  Qed.

  (* MOVE *)
  Lemma M_run_ls_on_this_one_event_nil :
    forall {L} {S} {eo : EventOrdering} e (ls : LocalSystem L S),
      M_run_ls_on_this_one_event [] e = Some ls
      -> ls = [].
  Proof.
    introv h; apply option_map_Some in h; exrepnd; subst; auto.
  Qed.

  Lemma find_ie_true_implies :
    forall p l,
      find_ie p l = true
      -> exists e,
        In e l
        /\ p = ientry_payload e
        /\ min_replies <= length (ientry_nodes e).
  Proof.
    induction l; introv h; simpl in *; ginv; dest_cases w; subst.
    { apply Nat.leb_le in h; eauto. }
    apply IHl in h; exrepnd; eauto.
  Qed.

  Lemma PISTISls_as_PISTIS_ls_st :
    forall n, PISTISls n = PISTISls_st n (MAIN_init_state n) (BCAST_init_state n).
  Proof.
    introv; auto.
  Qed.

  Lemma eq_PITISls_st :
    forall n sm1 sm2 sb1 sb2,
      PISTISls_st n sm1 sb1  = PISTISls_st n sm2 sb2
      -> sm1 = sm2 /\ sb1 = sb2.
  Proof.
    introv h.
    apply eq_cons in h; repnd.
    apply eq_cons in h; repnd; GC.
    simpl in *.
    apply decomp_p_nproc in h0.
    apply decomp_p_nproc in h1.
    inversion h0 as [xx]; subst.
    inversion h1 as [yy]; subst; auto.
  Qed.

  Lemma no_repeats_add_sender :
    forall s l,
      no_repeats l
      -> no_repeats (add_sender s l).
  Proof.
    introv norep.
    unfold add_sender; dest_cases w.
  Qed.
  Hint Resolve no_repeats_add_sender : pistis.

  Lemma no_repeats_ientry_nodes_updateIn :
    forall p x,
      no_repeats (ientry_nodes x)
      -> no_repeats (ientry_nodes (updateIn p x)).
  Proof.
    introv h; destruct x; simpl in *; dest_cases w; simpl; subst; eauto 3 with pistis.
  Qed.
  Hint Resolve no_repeats_ientry_nodes_updateIn : pistis.

  Lemma in_ientry_nodes_updateIn_implies :
    forall r p e,
      In r (ientry_nodes (updateIn p e))
      -> (r = sign_name (push_a p) /\ push_p p = ientry_payload e)
         \/ In r (ientry_nodes e).
  Proof.
    introv i.
    destruct e as [pl ins]; simpl in *; dest_cases w; simpl in *; subst.
    unfold add_sender in i; dest_cases w; tcsp.
  Qed.

  Lemma ientry_payload_updateIn :
    forall p x, ientry_payload (updateIn p x) = ientry_payload x.
  Proof.
    introv; unfold updateIn; destruct x; simpl; dest_cases w.
  Qed.
  Hint Rewrite ientry_payload_updateIn : pistis.

  Lemma push_eta :
    forall p, push (push_p p) (push_a p) = p.
  Proof.
    destruct p; simpl; auto.
  Qed.
  Hint Rewrite push_eta : pistis.

  Lemma verify_auth_push_implies_pistis_verify :
    forall {eo : EventOrdering} e n sm sb p,
      loc e = PISTIS_replica n
      -> M_run_ls_before_event (PISTISls n) e = Some (PISTISls_st n sm sb)
      -> verify_auth_push n (local_keys sm) p = true
      -> pistis_verify eo e (push2auth_data p) = true.
  Proof.
    introv eqloc run ver.
    unfold pistis_verify, M_state_sys_before_event, PISTISsys, M_state_ls_before_event.
    simpl; allrw; simpl; auto.
  Qed.
  Hint Resolve verify_auth_push_implies_pistis_verify : pistis.

  Lemma inIns_implies_payloadInIns :
    forall e l,
      In e l
      -> payloadInIns l (ientry_payload e) = true.
  Proof.
    induction l; introv i; simpl in *; tcsp.
    repndors; subst; tcsp; dest_cases w.
  Qed.

  Lemma all_inputs_from :
    forall {eo : EventOrdering} e (n : Rep) sm sb entry,
      loc e = PISTIS_replica n
      -> In entry (inputs sm)
      -> M_run_ls_before_event (PISTISls n) e = Some (PISTISls_st n sm sb)
      -> no_repeats (ientry_nodes entry)
         /\ forall r,
          In r (ientry_nodes entry)
          -> exists (e' : Event) (sign : Sign) (s : MAIN_state),
            e' ⊏ e
            /\ trigger_op e' = Some (PISTIS_push (push (ientry_payload entry) sign))
            /\ pistis_verify eo e' (push2auth_data (push (ientry_payload entry) sign)) = true
            /\ sign_name sign = r
            /\ M_state_sys_before_event PISTISsys e' MAINname = Some s
            /\ payloadInIns (inputs s) (ientry_payload entry) = true.
  Proof.
    intros eo e; induction e as [e ind] using predHappenedBeforeInd_type.
    introv eqloc i run.
    rewrite M_run_ls_before_event_unroll in run.
    dest_cases w; ginv.

    { apply Some_inj in run.
      apply eq_PITISls_st in run; repnd; subst; simpl in *; tcsp. }

    apply map_option_Some in run; exrepnd.
    symmetry in run0.
    applydup almost_M_run_ls_before_Event_preserves_subs in run1; eauto 3 with pistis;[].
    repndors; repnd; subst; simpl in *;
      [|apply M_run_ls_on_this_one_event_nil in run0; ginv];[].

    apply similar_subs_PISTISls_implies in run2; exrepnd; subst.
    apply option_map_Some in run0; exrepnd; simpl in *; symmetry in run2.

    unfold M_run_ls_on_input_ls in run2.
    remember (M_run_ls_on_input (PISTISls_st n sm0 sb0) (msg_comp_name 0) (time (local_pred e)) a) as z.
    symmetry in Heqz; repnd; simpl in *; subst.

    unfold M_run_ls_on_input in Heqz; simpl in *.
    repeat (autorewrite with comp pistis in *; simpl in *; try dest_cases w; simpl in * ).

    { unfold lower_out_break in Heqz; simpl in *.
      apply pair_inj in Heqz; repnd; subst.
      apply eq_cons in Heqz0; repnd; simpl in *.
      apply eq_cons in Heqz0; repnd; simpl in *; GC.
      apply decomp_p_nproc in Heqz1; simpl in *.
      apply decomp_p_nproc in Heqz2; simpl in *.
      inversion Heqz1 as [xx]; subst.
      inversion Heqz2 as [yy]; subst.
      dup run1 as runBef.
      eapply ind in run1; eauto; eauto 3 with eo; autorewrite with eo; auto;[].
      repnd.
      dands; eauto 3 with pistis.
      introv j.
      apply run1 in j; exrepnd; exists e' sign s; dands; auto; eauto 3 with eo. }

    { rewrite M_break_BCAST_update in Heqz; simpl in *.
      remember (BCAST_update n sb0 (time (local_pred e)) (push_in p) []) as out.
      repnd; simpl in *; symmetry in Heqout.
      destruct out; simpl in *; autorewrite with comp pistis in Heqz.
      unfold lower_out_break in Heqz; simpl in *.
      apply pair_inj in Heqz; repnd; subst; simpl in *.
      apply eq_cons in Heqz0; repnd; simpl in *.
      clear Heqz0.
      apply decomp_p_nproc in Heqz1; simpl in *.
      inversion Heqz1 as [xx]; subst.
      simpl in *.
      apply in_app_iff in i; repndors.

      { apply in_map_iff in i; exrepnd; subst.
        dup run1 as runBef.
        eapply ind in run1; eauto; eauto 3 with eo; autorewrite with eo; auto;[].
        repnd.
        dands; eauto 3 with pistis.

        introv i.
        apply in_ientry_nodes_updateIn_implies in i; repndors; repnd; subst.

        { unfold updateIn; destruct x as [pl ins]; simpl in *; subst; dest_cases w; simpl in *; GC.
          exists (local_pred e) (push_a p) sm0.
          dands; auto; eauto 3 with eo.
          { destruct p as [p a]; simpl in *; auto. }

          { symmetry in Heqw1; apply negb_false_iff in Heqw1.
            autorewrite with pistis.
            eapply verify_auth_push_implies_pistis_verify; eauto.
            autorewrite with eo; auto. }

          { unfold M_state_sys_before_event; autorewrite with eo; allrw; simpl.
            unfold M_state_ls_before_event; simpl; allrw; simpl; tcsp. }

          { apply inIns_implies_payloadInIns in i0; simpl in i0; auto. } }

        apply run1 in i; exrepnd; exists e' sign s; dands; auto; eauto 3 with eo;
          subst; autorewrite with pistis; auto. }

      apply in_map_iff in i; exrepnd; subst; simpl in *.
      dands; auto; introv xx; tcsp. }

    subst; simpl in *.
    symmetry in Heqw1.
    unfold lower_out_break in Heqz; simpl in *.
    apply pair_inj in Heqz; repnd; subst.
    apply eq_cons in Heqz0; repnd; simpl in *.
    apply eq_cons in Heqz0; repnd; simpl in *; GC.
    apply decomp_p_nproc in Heqz1; simpl in *.
    apply decomp_p_nproc in Heqz2; simpl in *.
    inversion Heqz1 as [xx]; subst.
    inversion Heqz2 as [yy]; subst.
    eapply ind in run1; eauto; eauto 3 with eo; autorewrite with eo; auto;[].
    repnd.
    dands; eauto 3 with pistis.

    introv j.
    apply run1 in j; exrepnd; exists e' sign s; dands; auto; eauto 3 with eo.
  Qed.

  Lemma in_PISTIS_get_contained_auth_data :
    forall a m,
      In a (PISTIS_get_contained_auth_data m)
      -> exists p, m = PISTIS_push p /\ a = push2auth_data p.
  Proof.
    introv i.
    destruct m; simpl in *; repndors; tcsp; subst; eauto.
  Qed.

  Lemma push2auth_data_inj :
    forall p1 p2,
      push2auth_data p1 = push2auth_data p2
      -> p1 = p2.
  Proof.
    introv h; destruct p1 as [p1 s1], p2 as [p2 s2]; simpl in *.
    destruct s1 as [n1 t1], s2 as [n2 t2]; simpl in *.
    unfold push2auth_data in *; simpl in *.
    inversion h; subst; auto.
  Qed.

  Lemma payloadInIns_updateInsOuts_false_implies :
    forall p plds l q,
      payloadInIns (updateInsOuts p plds l) q = false
      -> payloadInIns l q = false.
  Proof.
    induction l; introv i; simpl in *; auto.
    autorewrite with pistis in *; dest_cases w.
  Qed.

  Lemma payloadInIns_mon1 :
    forall {eo : EventOrdering} e e' s s' p n,
      e' ⊂ e
      -> loc e = PISTIS_replica n
      -> M_state_sys_before_event PISTISsys e MAINname = Some s
      -> payloadInIns (inputs s) p = false
      -> M_state_sys_before_event PISTISsys e' MAINname = Some s'
      -> payloadInIns (inputs s') p = false.
  Proof.
    introv lee eqloc st1 i1 st2.
    unfold M_state_sys_before_event in st1; simpl in *.
    rewrite eqloc in st1; simpl in *.
    apply map_option_Some in st1; exrepnd; symmetry in st0.
    rewrite M_run_ls_before_event_unroll in st1.
    dest_cases w; ginv.

    { apply pred_implies_not_first in lee; tcsp. }

    apply map_option_Some in st1; exrepnd.
    symmetry in st3.
    applydup almost_M_run_ls_before_Event_preserves_subs in st1; simpl; eauto 3 with comp pistis;[].
    repndors; repnd; subst; simpl in *; tcsp.

    { applydup @similar_subs_PISTISls_implies in st4; exrepnd; subst.
      apply option_map_Some in st3; exrepnd; subst; simpl in *.

      unfold M_run_ls_on_input_ls in st0.
      remember (M_run_ls_on_input (PISTISls_st n sm sb) (msg_comp_name 0) (time (local_pred e)) a0) as z.
      symmetry in Heqz; repnd; simpl in *; subst.
      unfold M_state_sys_before_event in st2.
      applydup pred_implies_loc in lee as eql; rewrite eql, eqloc in st2; simpl in *.
      apply map_option_Some in st2; exrepnd.
      applydup pred_implies_local_pred in lee; subst.
      rewrite st1 in st2; apply Some_inj in st2; subst; simpl in *.
      unfold state_of_component in st7; simpl in *; ginv.

      unfold M_run_ls_on_input in Heqz; simpl in *.
      repeat (autorewrite with comp pistis in *; simpl in *; try dest_cases w; simpl in * ).

      { unfold lower_out_break in Heqz; simpl in *.
        apply pair_inj in Heqz; repnd; subst.
        unfold state_of_component in st0; simpl in *; ginv. }

      { rewrite M_break_BCAST_update in Heqz; simpl in *.
        remember (BCAST_update n sb (time (local_pred e)) (push_in p0) []) as out.
        repnd; simpl in *; symmetry in Heqout.
        destruct out; simpl in *; autorewrite with comp pistis in Heqz.
        unfold lower_out_break in Heqz; simpl in *.
        apply pair_inj in Heqz; repnd; subst; simpl in *.

        unfold state_of_component in st0; simpl in *; ginv; simpl in *.
        apply payloadInIns_updateInsOuts_false_implies in i1; auto. }

      { unfold lower_out_break in Heqz; simpl in *.
        apply pair_inj in Heqz; repnd; subst.
        unfold state_of_component in st0; simpl in *; ginv. }

      { unfold lower_out_break in Heqz; simpl in *.
        apply pair_inj in Heqz; repnd; subst.
        unfold state_of_component in st0; simpl in *; ginv. } }

    apply M_run_ls_on_this_one_event_nil in st3; ginv; subst.
    unfold state_of_component in *; simpl in *; ginv.
  Qed.

  Lemma payloadInIns_mon2 :
    forall {eo : EventOrdering} e e' s s' p n,
      e' ⊏ e
      -> loc e = PISTIS_replica n
      -> M_state_sys_before_event PISTISsys e MAINname = Some s
      -> payloadInIns (inputs s) p = false
      -> M_state_sys_before_event PISTISsys e' MAINname = Some s'
      -> payloadInIns (inputs s') p = false.
  Proof.
    intros eo e; induction e as [e ind] using predHappenedBeforeInd_type.
    introv lee eqloc st1 i1 st2.
    dup st1 as stBef.
    unfold M_state_sys_before_event in st1; simpl in *.
    rewrite eqloc in st1; simpl in *.
    apply map_option_Some in st1; exrepnd; symmetry in st0.
    rewrite M_run_ls_before_event_unroll in st1.
    dest_cases w; ginv.

    { apply local_causal_implies_not_first in lee; tcsp. }

    apply map_option_Some in st1; exrepnd.
    symmetry in st3.
    applydup almost_M_run_ls_before_Event_preserves_subs in st1; simpl; eauto 3 with comp pistis;[].
    repndors; repnd; subst; simpl in *; tcsp.

    { applydup @similar_subs_PISTISls_implies in st4; exrepnd; subst.
      pose proof (payloadInIns_mon1 e (local_pred e) s sm p n) as q.
      repeat (autodimp q hyp); eauto 3 with eo.
      { unfold M_state_sys_before_event; autorewrite with eo; allrw; simpl.
        unfold M_state_ls_before_event; allrw; simpl; auto. }

      apply localHappenedBefore_implies_le_local_pred in lee.
      apply localHappenedBeforeLe_implies_or2 in lee; repndors; subst; auto.

      { unfold M_state_sys_before_event in st2; simpl in *; autorewrite with eo in *.
        rewrite eqloc in *; simpl in *.
        apply map_option_Some in st2; exrepnd; symmetry in st0.
        rewrite st2 in *; apply Some_inj in st1; subst; simpl in *.
        unfold state_of_component in *; simpl in *; ginv. }

      eapply (ind (local_pred e)); try exact lee; autorewrite with eo; eauto 3 with eo.
      unfold M_state_sys_before_event; simpl in *; autorewrite with eo in *.
      allrw; simpl.
      unfold M_state_ls_before_event; allrw; simpl; auto. }

    apply M_run_ls_on_this_one_event_nil in st3; ginv; subst.
    unfold state_of_component in *; simpl in *; ginv.
  Qed.

  Lemma payloadInIns_mon3 :
    forall {eo : EventOrdering} e e' s s' p n,
      loc e = loc e'
      -> loc e = PISTIS_replica n
      -> M_state_sys_before_event PISTISsys e MAINname = Some s
      -> payloadInIns (inputs s) p = false
      -> M_state_sys_before_event PISTISsys e' MAINname = Some s'
      -> payloadInIns (inputs s') p = true
      -> e ⊏ e'.
  Proof.
    introv eqloc eql st1 i1 st2 i2.
    pose proof (tri_if_same_loc e e' eqloc) as q; repndors; subst; auto.

    { rewrite st1 in *; ginv; rewrite i1 in *; ginv. }

    eapply (payloadInIns_mon2 e e') in st1; eauto.
    rewrite st1 in *; ginv.
  Qed.

  Lemma pushing :
    forall {eo : EventOrdering} (e : Event) (n : Rep)
           (t : PosDTime) (p : Push) (l : list name),
      alerts_on_time eo
      -> AXIOM_authenticated_messages_were_sent_or_byz eo PISTISsys
      -> loc e = PISTIS_replica n
      -> is_active n eo
      (* the push is considered sent at [t] (a delay) rather than [time e]
         [time e] is the time the first such message is sent
       *)
      -> In (mk_push t p l) (M_output_sys_on_event PISTISsys e)
      -> exists (l : list name),
          min_replies <= length l
          /\ forall q,
            In q l
            -> has_correct_trace eo q
            -> exists e',
                trigger_op e' = Some (PISTIS_push p)
                /\ bounded_event e t (alert_delay t).
  Proof.
    introv ontime sendbyz eqloc isa i.
    applydup (alert_if_push n) in i; auto; exrepnd; subst.
    applydup ontime in i3; exrepnd.

    applydup @local_implies_loc in i2.

    pose proof (isa e') as isa'; autodimp isa' hyp; try congruence; repnd;[].
    unfold run_to_similar in isa'; exrepnd.
    apply similar_subs_PISTISls_implies in isa'1; exrepnd; subst.

    rewrite M_run_ls_on_event_unroll2 in isa'2.
    apply map_option_Some in isa'2; exrepnd.
    applydup almost_M_run_ls_before_Event_preserves_subs in isa'2; eauto 3 with pistis;[].
    repndors; repnd; subst; symmetry in isa'1;
      [|apply M_run_ls_on_this_one_event_nil in isa'1; ginv].

    apply similar_subs_PISTISls_implies in isa'3; exrepnd; subst.
    unfold M_run_ls_on_this_one_event in isa'1.
    rewrite i5 in isa'1; simpl in *.
    apply Some_inj in isa'1.
    unfold M_run_ls_on_input_ls in isa'1; simpl in *.

    remember (M_run_ls_on_input (PISTISls_st n sm0 sb0) (msg_comp_name 0) (time e') (PISTIS_alert {| alert_p := p |})) as run.
    symmetry in Heqrun; repnd; simpl in *; subst.

    unfold M_run_ls_on_input in Heqrun; simpl in *.
    repeat (autorewrite with comp pistis in *; simpl in *; try dest_cases w; simpl in * ).
    unfold lower_out_break in Heqrun; simpl in *.
    apply pair_inj in Heqrun; repnd; subst.

    symmetry in Heqw.
    apply find_ie_true_implies in Heqw; exrepnd.

    dup isa'2 as bef.
    eapply all_inputs_from in bef; eauto; try congruence;[].
    repnd.

    exists (map PISTIS_replica (ientry_nodes e0)).
    autorewrite with list; dands; auto.
    introv im hc.
    apply in_map_iff in im; exrepnd; subst; simpl in *.

    pose proof (bef _ im0) as q; exrepnd; subst.
    applydup local_implies_loc in q1.
    pose proof (payloadInIns_mon3 e e'0 s s0 (ientry_payload e0) n) as z.
    repeat (autodimp z hyp); try congruence.

    pose proof (sendbyz e'0 (push2auth_data (push (ientry_payload e0) sign)) (MkOpTrust _ None I)) as sendbyz.
    simpl in *.
    repeat (autodimp sendbyz hyp); tcsp.
    { allrw; simpl; tcsp. }

    exrepnd; repndors; exrepnd; ginv;
      [|apply Some_inj in sendbyz7; symmetry in sendbyz7;
        pose proof (hc e'' sendbyz7) as hc;
        apply correct_is_not_byzantine in hc; tcsp];[].
    apply Some_inj in sendbyz4.
    apply in_PISTIS_get_contained_auth_data in sendbyz0; exrepnd; subst; simpl in *.
    apply push2auth_data_inj in sendbyz6; subst.
    autodimp sendbyz5 hyp; tcsp;[].

  Qed.

End PISTIS.
