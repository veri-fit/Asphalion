Require Export Quorum.
Require Export Process.
Require Export DTimeQ.
Require Export ComponentSM.
Require Export ComponentSM2.
Require Export CalculusSM_derived6.
Require Export CalculusSM_tacs2.
Require Export toString.
Require Export List.


(* Contains out implementation of PBFT *)
Section AbstractPaxos.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : @DTimeContext }.

  Definition round := nat.
  Definition round_deq := deq_nat.
  Definition round_lt_dec := lt_dec.
  Definition round_le_dec := le_dec.

  Class Paxos_context :=
    {
      (* types *)
      node   : Set;
      value  : Set;
      quorum : Set;

      (* round numbers are simply numbers *)

      (* functions *)
      is_proposer   : node -> round -> bool;
      forms_quorum  : list node -> bool;
      default_value : node -> value;

      (* axioms *)
      value_deq : Deq value;
      node_deq  : Deq node;

      num_nodes;
      node2nat : node -> nat_n num_nodes;
      node_bij : bijective node2nat;

      is_proposer_inj :
        forall n1 n2 r,
          is_proposer n1 r = true
          -> is_proposer n2 r = true
          -> n1 = n2;

      quorum_intersection :
        forall l1 l2,
          forms_quorum l1 = true
          -> forms_quorum l2 = true
          -> exists n, In n l1 /\ In n l2
    }.

  Context { pc : Paxos_context }.

  Global Instance Paxos_I_Node : Node := MkNode node node_deq.

  Lemma some_inj_rev :
    forall (n : node) (m : name), Some m = Some n -> n = m.
  Proof.
    introv xx; ginv; auto.
  Qed.

  Lemma inj_node : injective (fun n : node => n).
  Proof.
    introv; tcsp.
  Qed.

  Global Instance paxos_I_Quorum : Quorum_context :=
    MkQuorumContext
      node
      num_nodes
      node_deq
      node2nat
      node_bij
      (fun n => n)
      Some
      (fun n => eq_refl (Some n))
      some_inj_rev
      inj_node.

  Definition nodes : list node := nodes.

  Record start    := mk_start    { start_R :> round; }.
  Record one_a    := mk_one_a    { one_a_R :> round; }.
  Record one_b    := mk_one_b    { one_b_N : node; one_b_R : round; one_b_maxr : round; one_b_maxv : value; }.
  Record vote     := mk_vote     { vote_N : node; vote_R : round; vote_V : value; }.
  Record decision := mk_decision { decision_N : node; decision_R : round; decision_V : value; }.

  Definition MAINname := msg_comp_name 0.

  (* ******************************************* *)
  (* *** entries hold [one_b] messages and proposed values *** *)
  Record entry :=
    MkEntry
      { entry_round    : round;
        entry_one_bs   : list one_b;
        entry_votes    : list vote;
        entry_proposal : option value; }.

  Definition entries := list entry.

  Fixpoint find_entry (r : round) (l : entries) : option entry :=
    match l with
    | [] => None
    | entry :: l =>
      if round_deq r (entry_round entry)
      then Some entry
      else find_entry r l
    end.

  Definition proposed_entry (e : entry) : bool :=
    is_some (entry_proposal e).

  Definition entry2one_b_nodes (e : entry) : list node :=
    map one_b_N (entry_one_bs e).

  (* gets all the nodes that voted for [v] *)
  Definition entry2vote_nodes (v : value) (e : entry) : list node :=
    map vote_N
        (filter
           (fun x => if value_deq v (vote_V x) then true else false)
           (entry_votes e)).

  Definition entry2voters (e : entry) : list node := map vote_N (entry_votes e).

  (* We add [b] to the list if there's not already a message from the same node in the list *)
  Fixpoint add_one_b_to_list (b : one_b) (l : list one_b) : list one_b :=
    match l with
    | [] => [b]
    | b' :: l =>
      if node_deq (one_b_N b) (one_b_N b') then b' :: l
      else b' :: add_one_b_to_list b l
    end.

  Definition add_one_b_to_entry (b : one_b) (e : entry) : entry :=
    MkEntry
      (entry_round e)
      (add_one_b_to_list b (entry_one_bs e))
      (entry_votes e)
      (entry_proposal e).

  Definition upd_none {A} (o : option A) (a : A) :=
    match o with
    | Some _ => o
    | None => Some a
    end.

  Fixpoint add_vote_to_list (v : vote) (l : list vote) : list vote :=
    match l with
    | [] => [v]
    | v' :: l =>
      if node_deq (vote_N v) (vote_N v') then v' :: l
      else v' :: add_vote_to_list v l
    end.

  Definition is_vote_from_proposer (v : vote) : bool := is_proposer (vote_N v) (vote_R v).

  Definition upd_proposal (vop : option value) (v : vote) : option value :=
    if is_vote_from_proposer v
    then upd_none vop (vote_V v)
    else vop.

  Definition add_vote_to_entry (v : vote) (e : entry) : entry :=
    MkEntry
      (entry_round e)
      (entry_one_bs e)
      (add_vote_to_list v (entry_votes e))
      (upd_proposal (entry_proposal e) v).

  Definition one_b2entry (b : one_b) : entry :=
    MkEntry (one_b_R b) [b] [] None.

  Definition vote2entry (v : vote) : entry :=
    MkEntry (vote_R v) [] [v] (upd_proposal None v).

  Fixpoint add_one_b (b : one_b) (l : entries) : entry * entries :=
    match l with
    | [] => let entry := one_b2entry b in (entry, [entry])
    | entry :: entries =>
      if round_deq (one_b_R b) (entry_round entry)
      then
        let entry' := add_one_b_to_entry b entry
        in (entry', entry' :: entries)
      else
        let (entry', entries') := add_one_b b entries
        in (entry', entry :: entries')
    end.

  Fixpoint add_vote (v : vote) (l : entries) : entry * entries :=
    match l with
    | [] => let entry := vote2entry v in (entry,[entry])
    | entry :: entries =>
      if round_deq (vote_R v) (entry_round entry)
      then
        let entry' := add_vote_to_entry v entry in
        (entry', entry' :: entries)
      else
        let (entry',entries') := add_vote v entries in
        (entry', entry :: entries')
    end.

  Fixpoint find_voted_value_from_votes (n : node) (l : list vote) : option value :=
    match l with
    | [] => None
    | v :: vs =>
      if node_deq (vote_N v) n
      then Some (vote_V v)
      else find_voted_value_from_votes n vs
    end.

  Fixpoint find_latest_value_from_votes (n : node) (v : value) (low high : round) (l : entries) : round * value :=
    match l with
    | [] => (low,v)
    | entry :: entries =>
      let r := entry_round entry in
      if round_lt_dec r high then
        if round_lt_dec low r then
          (* we might as well pick the proposal in the entry *)
          match find_voted_value_from_votes n (entry_votes entry) with
          | Some v' => find_latest_value_from_votes n v' r high entries
          | None => find_latest_value_from_votes n v low high entries
          end
        else find_latest_value_from_votes n v low high entries
      else find_latest_value_from_votes n v low high entries
    end.

  Fixpoint find_voted_value_from_one_bs (v : value) (low high : round) (l : list one_b) : round * value :=
    match l with
    | [] => (low,v)
    | b :: bs =>
      let r' := one_b_maxr b in
      let v' := one_b_maxv b in
      if r' <? high
      then
        if low <? r'
        then find_voted_value_from_one_bs v' r' high bs
        else find_voted_value_from_one_bs v low high bs
      else find_voted_value_from_one_bs v low high bs
    end.

  Definition vote2my slf (v : vote) : vote := mk_vote slf (vote_R v) (vote_V v).

  Definition is_my_vote slf (v : vote) : bool := if node_deq slf (vote_N v) then true else false.


  (* ******************************************* *)
  (* *** MAIN state *** *)
  Record MAIN_state :=
    MkState {
        st_current_round : round;
        st_entries       : entries;
      }.

  Definition initial_state_at (r : round) : MAIN_state := MkState r [].

  (* 0 is not used though *)
  Definition initial_round : round := 0.

  Definition initial_state : MAIN_state := initial_state_at initial_round.

  Definition has_left_round (r : round) (s : MAIN_state) : bool := r <? st_current_round s.
  Definition valid_round (r : round) : bool := initial_round <? r.
  Definition new_round (r : round) (s : MAIN_state) : bool := st_current_round s <? r.
  Definition same_round (r1 r2 : round) : bool := if round_deq r1 r2 then true else false.

  Definition same_node (n1 n2 : node) : bool := if node_deq n1 n2 then true else false.

  Definition update_last_round (r : round) (s : MAIN_state) : MAIN_state :=
    MkState
      (if round_lt_dec r (st_current_round s) then st_current_round s else r)
      (st_entries s).

  Definition log_one_b (b : one_b) (s : MAIN_state) : entry * MAIN_state :=
    let (entry, entries) := add_one_b b (st_entries s) in
    (entry, MkState (st_current_round s) entries).

  Definition log_vote (v : vote) (s : MAIN_state) : entry * MAIN_state :=
    let (entry,entries) := add_vote v (st_entries s) in
    (entry, MkState (st_current_round s) entries).

  Definition is_new_vote slf entry := if in_dec node_deq slf (entry2voters entry) then false else true.

  Definition has_proposed (v : value) (e : entry) : bool :=
    match entry_proposal e with
    | Some v' => if value_deq v v' then true else false
    | None => false
    end.

  (* On receipt of a vote [v], a node generates a new vote if [v] is a proposal, i.e.,
      (1) [v] is from the proposer of the corresponding round
      (2) We stored the vote of the proposer
      (3) We haven't voted before
      (4) We're not the proposer *)
  Definition valid_my_vote slf v entry : bool :=
    (is_vote_from_proposer v)
      && (has_proposed (vote_V v) entry)
      && (is_new_vote slf entry)
      && (negb (same_node slf (vote_N v))).

  Definition log_my_vote slf v entry state :=
    if valid_my_vote slf v entry
    then log_vote (vote2my slf v) state
    else (entry,state).


  (* ******************************************* *)
  (* *** messages *** *)
  Inductive Paxos_msg : Set :=
  | paxos_start    (s : start)
  | paxos_one_a    (a : one_a)
  | paxos_one_b    (b : one_b)
  | paxos_vote     (v : vote)
  | paxos_decision (d : decision).

  Global Instance Paxos_I_Msg : Msg := MkMsg Paxos_msg.

  Definition send_one_a    (a : one_a)    (n : list name) : DirectedMsg := MkDMsg (paxos_one_a a)    n ('0).
  Definition send_one_b    (b : one_b)    (n : list name) : DirectedMsg := MkDMsg (paxos_one_b b)    n ('0).
  Definition send_vote     (v : vote)     (n : list name) : DirectedMsg := MkDMsg (paxos_vote v)     n ('0).
  Definition send_decision (d : decision) (n : list name) : DirectedMsg := MkDMsg (paxos_decision d) n ('0).

  Definition other_nodes (n : node) : list node := remove_elt node_deq n nodes.

  Definition broadcast2others (slf : node) F : DirectedMsg := F (other_nodes slf).
  Definition broadcast2all F : DirectedMsg := F nodes.

  Definition send_my_vote (slf : node) entry (v : vote) : DirectedMsgs :=
    if valid_my_vote slf v entry
    then [broadcast2others slf (send_vote (vote2my slf v))]
    else [].

  Definition Paxos_msg2status (m : Paxos_msg) : msg_status :=
    match m with
    | paxos_start    _ => MSG_STATUS_EXTERNAL
    | paxos_one_a    _ => MSG_STATUS_PROTOCOL
    | paxos_one_b    _ => MSG_STATUS_PROTOCOL
    | paxos_vote     _ => MSG_STATUS_PROTOCOL
    | paxos_decision _ => MSG_STATUS_PROTOCOL
    end.

  Definition Paxos_msg2sender (_ : name) (m : Paxos_msg) : option name :=
    match m with
    | paxos_start    s => None
    | paxos_one_a    a => None
    | paxos_one_b    b => Some (one_b_N b)
    | paxos_vote     v => Some (vote_N v)
    | paxos_decision d => Some (decision_N d)
    end.


  (* ******************************************* *)
  (* *** instances *** *)
  Global Instance Paxos_I_IOTrustedFun : IOTrustedFun := MkIOTrustedFun (fun _ => MkIOTrusted unit unit tt).
  Global Instance Paxos_I_trustedStateFun : trustedStateFun := MkTrustedStateFun (fun _ => MAIN_state).
  Global Instance Paxos_I_Key : Key := MkKey unit unit.
  Global Instance paxos_I_AuthTok : AuthTok := MkAuthTok unit Deq_unit.
  Global Instance Paxos_I_MsgStatus : MsgStatus := MkMsgStatus Paxos_msg2status.
  Global Instance Paxos_I_Data : Data := MkData Paxos_msg.
  Global Instance Paxos_I_baseFunIO : baseFunIO := MkBaseFunIO (fun (nm : CompName) => CIOdef).
  Global Instance Paxos_I_baseStateFun : baseStateFun :=
    MkBaseStateFun (fun (nm : CompName) =>
                      if CompNameKindDeq (comp_name_kind nm) msg_comp_name_kind
                      then MAIN_state
                      else unit).
  Definition paxos_get_contained_auth_data (m : msg) : list AuthenticatedData := [MkAuthData m [tt]].
  Global Instance Paxos_I_ContainedAuthData : ContainedAuthData := MkContainedAuthData paxos_get_contained_auth_data.
  Global Instance Paxos_I_DataAuth : DataAuth := MkDataAuth Paxos_msg2sender.


  (* ******************************************* *)
  (* *** message handling notation *** *)
  Definition on_start {A} (m : Paxos_msg) (d : unit -> Proc A) (f : start -> Proc A) : Proc A :=
    match m with paxos_start s => f s | _ => d tt end.
  Notation "a >>os>>=( d ) f" := (on_start a d f) (at level 80, right associativity).

  Definition on_one_a {A} (m : Paxos_msg) (d : unit -> Proc A) (f : one_a -> Proc A) : Proc A :=
    match m with paxos_one_a a => f a | _ => d tt end.
  Notation "a >>oa>>=( d ) f" := (on_one_a a d f) (at level 80, right associativity).

  Definition on_one_b {A} (m : Paxos_msg) (d : unit -> Proc A) (f : one_b -> Proc A) : Proc A :=
    match m with paxos_one_b b => f b | _ => d tt end.
  Notation "a >>ob>>=( d ) f" := (on_one_b a d f) (at level 80, right associativity).

  Definition on_vote {A} (m : Paxos_msg) (d : unit -> Proc A) (f : vote -> Proc A) : Proc A :=
    match m with paxos_vote v => f v | _ => d tt end.
  Notation "a >>ov>>=( d ) f" := (on_vote a d f) (at level 80, right associativity).

  (* ******************************************* *)
  (* *** handlers *** *)
  Definition handle_start (slf : node) : UProc MAINname MAIN_state :=
    fun state m =>
      m >>os>>=(fun _ => [R](state,[])) fun s =>
      if negb (is_proposer slf s) then [R](state,[]) else
      if (start_R s <=? st_current_round state) then [R](state,[]) else
      let state1 := update_last_round s state in
      [R](state1,[broadcast2others slf (send_one_a (mk_one_a s))]).

  (* 1a are sent by proposers *)
  Definition handle_one_a (slf : node) : UProc MAINname MAIN_state :=
    fun state m =>
      m >>oa>>=(fun _ => [R](state,[])) fun a =>
      if negb (new_round a state) then [R](state,[]) else
      let d := default_value slf in
      (* maxv is the value to propose *)
      let (maxr,maxv) := find_latest_value_from_votes slf d 0 a (st_entries state) in
      let b := mk_one_b slf a maxr maxv in
      let state1 := update_last_round a state in
      let (entry,state2) := log_one_b b state1 in
      [R] (state2, [broadcast2others slf (send_one_b b)]).

  (* 1b are handle by proposers *)
  Definition handle_one_b (slf : node) : UProc MAINname MAIN_state :=
    fun state m =>
      m >>ob>>=(fun _ => [R](state,[])) fun b =>
      let bround := one_b_R b in
      let cround := st_current_round state in
      if negb (same_round bround cround) then [R](state,[]) else
      if negb (is_proposer slf cround) then [R](state,[]) else
      let (entry, state1) := log_one_b b state in
      if proposed_entry entry then [R](state1,[]) else
      let q := entry2one_b_nodes entry in
      if negb (forms_quorum q) then [R](state1,[]) else
      let d := default_value slf in
      (* v is the value to propose *)
      let (maxr,maxv) := find_voted_value_from_one_bs d 0 cround (entry_one_bs entry) in
      let vote := mk_vote slf cround maxv in
      let (_,state2) := log_vote vote state1 in
      [R](state2,[broadcast2others slf (send_vote vote)]).

  Definition handle_vote (slf : node) : UProc MAINname MAIN_state :=
    fun state m =>
      m >>ov>>=(fun _ => [R](state,[])) fun v =>
      let round := vote_R v in
      let val   := vote_V v in
      if has_left_round round state then [R](state,[]) else
      let (entry1,state1) := log_vote v state in
      let (entry2,state2) := log_my_vote slf v entry1 state1 in
      let q := entry2vote_nodes val entry2 in
      if negb (forms_quorum q) then [R](state2,send_my_vote slf entry1 v) else
      let d := mk_decision slf round (vote_V v) in
      [R](state2, broadcast2others slf (send_decision d) :: send_my_vote slf entry1 v).

  Definition handle_decision (slf : node) : UProc MAINname MAIN_state :=
    fun state m => [R](state,[]).

  Definition MAIN_update (slf : node) : M_Update 0 MAINname _ :=
    fun (s : MAIN_state) m =>
      interp_s_proc
        (match m with
         | paxos_start    _ => handle_start    slf s m
         | paxos_one_a    _ => handle_one_a    slf s m
         | paxos_one_b    _ => handle_one_b    slf s m
         | paxos_vote     _ => handle_vote     slf s m
         | paxos_decision _ => handle_decision slf s m
         end).

  Notation PaxosLS := (LocalSystem 1 0).

  Definition MAIN_comp n (s : MAIN_state) : n_proc 1 MAINname := build_m_sm (MAIN_update n) s.
  Definition PaxosLocalSys n (s : MAIN_state) : PaxosLS := [MkPProc _ (MAIN_comp n s)].
  Definition PaxosfunLevelSpace := MkFunLevelSpace (fun _ => 1) (fun _ => 0).
  Definition PaxosSys : M_USystem PaxosfunLevelSpace := fun n => PaxosLocalSys n initial_state.


  (* ******************************************* *)
  (* *** well-formedness of paxos state machines *** *)
  Create HintDb paxos.
  Create HintDb paxos2.
  Hint Resolve implies_authenticated_messages_were_sent_non_byz_usys : paxos paxos2.
  Hint Rewrite @run_process_on_list_haltedProc : paxos paxos2.

  Lemma are_procs_PaxosLs : forall n s, are_procs_n_procs (PaxosLocalSys n s).
  Proof.
    introv; simpl;
      try (complete (eexists; introv; unfold proc2upd; simpl; try reflexivity));
      try (complete (introv i; simpl in *; repndors; subst; tcsp; simpl;
                     eexists; introv; unfold proc2upd;  reflexivity)).
  Qed.
  Hint Resolve are_procs_PaxosLs : paxos.

  Lemma wf_PaxosLs : forall n s, wf_procs (PaxosLocalSys n s).
  Proof.
    repeat introv; unfold wf_procs; simpl;
      dands; try (complete (introv xx; repndors; tcsp; ginv));
        repeat constructor; simpl; tcsp;
          try (complete (introv xx; repndors; tcsp; ginv)).
  Qed.
  Hint Resolve wf_PaxosLs : paxos.

  Lemma are_procs_PaxosSys : are_procs_sys PaxosSys.
  Proof.
    unfold PaxosSys; introv; simpl; eauto 3 with comp paxos.
  Qed.
  Hint Resolve are_procs_PaxosSys : paxos.

  Lemma wf_PaxosSys : wf_sys PaxosSys.
  Proof.
    unfold PaxosSys; introv; simpl; eauto 3 with comp paxos.
  Qed.
  Hint Resolve wf_PaxosSys : paxos.

  Lemma PaxosSys_preserves_subs :
    sys_preserves_subs PaxosSys.
  Proof.
    introv; eauto 3 with comp paxos.
  Qed.
  Hint Resolve PaxosSys_preserves_subs : paxos.

  Lemma sys_non_trusted_PaxosSys : sys_non_trusted PaxosSys.
  Proof.
    introv; simpl; tcsp.
  Qed.
  Hint Resolve sys_non_trusted_PaxosSys : paxos.

  Lemma similar_sms_at_paxos_replica :
    forall r s (p : n_proc 1 _),
      similar_sms p (MAIN_comp r s)
      -> exists s', p = MAIN_comp r s'.
  Proof.
    introv sim; simpl in *.
    destruct p; simpl in *; tcsp.
    unfold similar_sms_at in sim.
    destruct a as [upd st]; simpl in *; subst; simpl in *.
    exists st; auto.
  Qed.

  Lemma similar_procs_MAIN :
    forall r s p,
      similar_procs (MkPProc MAINname (MAIN_comp r s)) p
      -> exists s', p = MkPProc MAINname (MAIN_comp r s').
  Proof.
    introv sim.
    inversion sim as [? ? ? ? sims]; clear sim; subst.
    repeat sp_exI; subst.
    apply similar_sms_sym in sims.
    apply similar_sms_at_paxos_replica in sims; exrepnd; subst; eauto.
  Qed.

  Lemma similar_subs_PaxosLocalSys :
    forall r s ls,
      similar_subs (PaxosLocalSys r s) ls
      -> exists s', ls = PaxosLocalSys r s'.
  Proof.
    introv sim.
    inversion sim; subst; simpl in *.
    apply similar_procs_MAIN in simp; exrepnd; subst; simpl in *.
    inversion sims; subst.
    exists s'; dands; tcsp.
  Qed.

  Lemma similar_subs_PaxosLocalSys_implies :
    forall n s (ls : n_procs 1),
      similar_subs (PaxosLocalSys n s) ls
      -> exists s', ls = PaxosLocalSys n s'.
  Proof.
    introv sim.
    apply similar_subs_PaxosLocalSys in sim; exrepnd; subst; eauto.
  Qed.

  Lemma M_run_ls_before_event_ls_is_paxos :
    forall {eo : EventOrdering}
           (e  : Event)
           (n  : name)
           (s  : MAIN_state)
           (ls : LocalSystem 1 0),
      M_run_ls_before_event (PaxosLocalSys n s) e = Some ls
      -> exists (s' : MAIN_state), ls = PaxosLocalSys n s'.
  Proof.
    introv run.
    apply M_run_ls_before_event_preserves_subs in run; eauto 3 with comp paxos.
    repnd; simpl in *.
    apply similar_subs_PaxosLocalSys_implies in run2; auto.
  Qed.

  Lemma M_run_ls_on_event_ls_is_paxos :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : name)
           (s  : MAIN_state)
           (ls : LocalSystem 1 0),
      M_run_ls_on_event (PaxosLocalSys r s) e = Some ls
      -> exists s', ls = PaxosLocalSys r s'.
  Proof.
    introv run.
    apply M_run_ls_on_event_preserves_subs in run; eauto 3 with comp paxos.
    repnd; simpl in *.
    apply similar_subs_PaxosLocalSys_implies in run2; auto.
  Qed.

  Lemma eq_PaxosLocalSys_implies :
    forall n s1 s2,
      PaxosLocalSys n s1 = PaxosLocalSys n s2
      -> s1 = s2.
  Proof.
    introv h.
    apply eq_cons in h; repnd.
    apply decomp_p_nproc in h0.
    inversion h0; subst; auto.
  Qed.

  Definition lower_out_break {n} {A} {B}
             (l : n_procs (S n))
             (F : n_procs (S n) -> A -> B) : n_procs n -> A -> B :=
    fun k a => F (update_subs l k) a.

  Lemma M_break_M_run_sm_on_input_Paxos :
    forall {O} n s m subs (F : n_procs 1 -> option MAIN_state * DirectedMsgs -> O),
      M_break (M_run_sm_on_input (MAIN_comp n s) m) subs F
      = match m with
        | paxos_start    _ => M_break (interp_s_proc (handle_start    n s m)) (decr_n_procs subs) (lower_out_break subs F)
        | paxos_one_a    _ => M_break (interp_s_proc (handle_one_a    n s m)) (decr_n_procs subs) (lower_out_break subs F)
        | paxos_one_b    _ => M_break (interp_s_proc (handle_one_b    n s m)) (decr_n_procs subs) (lower_out_break subs F)
        | paxos_vote     _ => M_break (interp_s_proc (handle_vote     n s m)) (decr_n_procs subs) (lower_out_break subs F)
        | paxos_decision _ => M_break (interp_s_proc (handle_decision n s m)) (decr_n_procs subs) (lower_out_break subs F)
        end.
  Proof.
    introv.
    unfold M_run_sm_on_input.
    destruct m; introv; simpl; auto;
      try (complete (unfold M_on_decr, M_break, MAIN_update;
                     simpl; repeat dest_cases w; ginv)).
  Qed.
  Hint Rewrite @M_break_M_run_sm_on_input_Paxos : paxos.


  (* ******************************************* *)
  (* *** standard tactics *** *)
  Ltac paxos_simplifier_step :=
    match goal with
    | [ H : true = false |- _ ] => inversion H
    | [ H : false = true |- _ ] => inversion H

    | [ H : broadcast2others _ (send_one_a    _) = send_vote _ _ |- _ ] => complete (inversion H)
    | [ H : broadcast2others _ (send_one_b    _) = send_vote _ _ |- _ ] => complete (inversion H)
    | [ H : broadcast2others _ (send_decision _) = send_vote _ _ |- _ ] => complete (inversion H)

    | [ H : broadcast2others _ (send_one_a _) = send_decision _ _ |- _ ] => complete (inversion H)
    | [ H : broadcast2others _ (send_one_b _) = send_decision _ _ |- _ ] => complete (inversion H)
    | [ H : broadcast2others _ (send_vote  _) = send_decision _ _ |- _ ] => complete (inversion H)

    | [ H : send_one_a _ _ = send_one_b _ _ |- _ ] => complete (inversion H)
    | [ H : send_one_b _ _ = send_one_a _ _ |- _ ] => complete (inversion H)
    | [ H : send_one_a _ _ = send_vote  _ _ |- _ ] => complete (inversion H)
    | [ H : send_vote _ _  = send_one_a _ _ |- _ ] => complete (inversion H)
    | [ H : send_one_b _ _ = send_vote  _ _ |- _ ] => complete (inversion H)
    | [ H : send_vote _ _  = send_one_b _ _ |- _ ] => complete (inversion H)

    | [ H : broadcast2others _ (?F _) = ?F _ _ |- _ ] => inversion H; clear H; subst

    | [ H : n_procs 0 |- _ ] => rewrite (n_procs_0 H) in *; simpl in *; clear H
    | [ H : ret _ _ _ = (_,_) |- _ ] => unfold ret in H
    | [ H : (_,_) = (_,_) |- _ ] => apply pair_inj in H; repnd
    | [ H : Some _ = Some _ |- _ ] => apply Some_inj in H
    | [ x : _, H : ?x = _ |- _ ] => subst x
    | [ x : _, H : _ = ?x |- _ ] => subst x

    | [ H : PaxosLocalSys ?r _ = PaxosLocalSys ?r _ |- _ ] => apply eq_PaxosLocalSys_implies in H; repnd
    | [ H : PaxosLocalSys ?r _ = _ |- _ ] => apply eq_PaxosLocalSys_implies in H; repnd
    | [ H : _ = PaxosLocalSys ?r _ |- _ ] => apply eq_PaxosLocalSys_implies in H; repnd
    end.

  Ltac paxos_simp := repeat (paxos_simplifier_step; simpl in * ).

  Ltac unfold_handler :=
    match goal with
    | [ H : context[ handle_start    ] |- _ ] => unfold handle_start    in H
    | [ H : context[ handle_one_a    ] |- _ ] => unfold handle_one_a    in H
    | [ H : context[ handle_one_b    ] |- _ ] => unfold handle_one_b    in H
    | [ H : context[ handle_vote     ] |- _ ] => unfold handle_vote     in H
    | [ H : context[ handle_decision ] |- _ ] => unfold handle_decision in H
    end.

  Ltac unfold_handler_concl :=
    match goal with
    | [ |- context[ handle_start    ] ] => unfold handle_start
    | [ |- context[ handle_one_a    ] ] => unfold handle_one_a
    | [ |- context[ handle_one_b    ] ] => unfold handle_one_b
    | [ |- context[ handle_vote     ] ] => unfold handle_vote
    | [ |- context[ handle_decision ] ] => unfold handle_decision
    end.

  Ltac paxos_simplifier :=
    let stac := (fun _ => paxos_simplifier_step) in
    simplifier stac.

  Ltac paxos_dest_all name :=
    let stac := fun _ => paxos_simplifier_step in
    let ftac := fun _ => try (fold DirectedMsgs in * ) in
    dest_all
      name
      stac
      ftac.

  Ltac smash_paxos_tac tac :=
    let stac := fun _ => paxos_simplifier_step in
    let ftac := fun _ => try (fold DirectedMsgs in * ) in
    let atac := fun _ => repeat (autorewrite with paxos paxos2 comp kn eo proc in *;simpl in * ) in
    smash_byzeml_tac
      tac
      stac
      ftac
      atac.

  Ltac smash_paxos_tac_at H tac :=
    let stac := fun _ => paxos_simplifier_step in
    let ftac := fun _ => try (fold DirectedMsgs in * ) in
    let atac := fun _ => repeat (autorewrite with paxos paxos2 comp kn eo proc in H;simpl in H) in
    smash_byzeml_tac
      tac
      stac
      ftac
      atac.

  (* As opposed to the one above, this one doesn't contain paxos2 *)
  Ltac smash_paxos_tac_ tac :=
    let stac := fun _ => paxos_simplifier_step in
    let ftac := fun _ => try (fold DirectedMsgs in * ) in
    let atac := fun _ => repeat (autorewrite with paxos comp kn eo proc in *;simpl in * ) in
    smash_byzeml_tac
      tac
      stac
      ftac
      atac.

  Ltac smash_paxos1  := let tac := fun _ => (eauto 1  with paxos) in smash_paxos_tac tac.
  Ltac smash_paxos2  := let tac := fun _ => (eauto 2  with paxos) in smash_paxos_tac tac.
  Ltac smash_paxos3  := let tac := fun _ => (eauto 3  with paxos) in smash_paxos_tac tac.
  Ltac smash_paxos4  := let tac := fun _ => (eauto 4  with paxos) in smash_paxos_tac tac.
  Ltac smash_paxos5  := let tac := fun _ => (eauto 5  with paxos) in smash_paxos_tac tac.
  Ltac smash_paxos6  := let tac := fun _ => (eauto 6  with paxos) in smash_paxos_tac tac.
  Ltac smash_paxos7  := let tac := fun _ => (eauto 7  with paxos) in smash_paxos_tac tac.
  Ltac smash_paxos8  := let tac := fun _ => (eauto 8  with paxos) in smash_paxos_tac tac.
  Ltac smash_paxos9  := let tac := fun _ => (eauto 9  with paxos) in smash_paxos_tac tac.
  Ltac smash_paxos10 := let tac := fun _ => (eauto 10 with paxos) in smash_paxos_tac tac.

  Ltac smash_paxos1_at  H := let tac := fun _ => (eauto 1  with paxos) in smash_paxos_tac_at H tac.
  Ltac smash_paxos2_at  H := let tac := fun _ => (eauto 2  with paxos) in smash_paxos_tac_at H tac.
  Ltac smash_paxos3_at  H := let tac := fun _ => (eauto 3  with paxos) in smash_paxos_tac_at H tac.
  Ltac smash_paxos4_at  H := let tac := fun _ => (eauto 4  with paxos) in smash_paxos_tac_at H tac.
  Ltac smash_paxos5_at  H := let tac := fun _ => (eauto 5  with paxos) in smash_paxos_tac_at H tac.
  Ltac smash_paxos6_at  H := let tac := fun _ => (eauto 6  with paxos) in smash_paxos_tac_at H tac.
  Ltac smash_paxos7_at  H := let tac := fun _ => (eauto 7  with paxos) in smash_paxos_tac_at H tac.
  Ltac smash_paxos8_at  H := let tac := fun _ => (eauto 8  with paxos) in smash_paxos_tac_at H tac.
  Ltac smash_paxos9_at  H := let tac := fun _ => (eauto 9  with paxos) in smash_paxos_tac_at H tac.
  Ltac smash_paxos10_at H := let tac := fun _ => (eauto 10 with paxos) in smash_paxos_tac_at H tac.

  Ltac smash_paxos_1  := let tac := fun _ => (eauto 1  with paxos) in smash_paxos_tac_ tac.
  Ltac smash_paxos_2  := let tac := fun _ => (eauto 2  with paxos) in smash_paxos_tac_ tac.
  Ltac smash_paxos_3  := let tac := fun _ => (eauto 3  with paxos) in smash_paxos_tac_ tac.
  Ltac smash_paxos_4  := let tac := fun _ => (eauto 4  with paxos) in smash_paxos_tac_ tac.
  Ltac smash_paxos_5  := let tac := fun _ => (eauto 5  with paxos) in smash_paxos_tac_ tac.
  Ltac smash_paxos_6  := let tac := fun _ => (eauto 6  with paxos) in smash_paxos_tac_ tac.
  Ltac smash_paxos_7  := let tac := fun _ => (eauto 7  with paxos) in smash_paxos_tac_ tac.
  Ltac smash_paxos_8  := let tac := fun _ => (eauto 8  with paxos) in smash_paxos_tac_ tac.
  Ltac smash_paxos_9  := let tac := fun _ => (eauto 9  with paxos) in smash_paxos_tac_ tac.
  Ltac smash_paxos_10 := let tac := fun _ => (eauto 10 with paxos) in smash_paxos_tac_ tac.

  Ltac smash_paxos := smash_paxos3.

  Ltac post_paxos_dest_msg :=
    simpl in *;
    autorewrite with comp paxos paxos2 in *; simpl in *;
    repeat unfold_handler;
    repeat unfold_handler_concl;
    smash_paxos.

  Ltac pre_paxos_dest_msg c :=
    match goal with
    | [ H : Paxos_msg |- _ ] =>
      destruct H;
      [ Case_aux c "Start"
      | Case_aux c "OneA"
      | Case_aux c "OneB"
      | Case_aux c "Vote"
      | Case_aux c "Decision"
      ]
    end.

  Ltac paxos_dest_msg c :=
    progress (pre_paxos_dest_msg c);
    post_paxos_dest_msg.

  Ltac paxo_finish_eexists :=
    repeat match goal with
           | [ |- ex _ ] => eexists
           end;
    dands; eauto; eauto 3 with eo.

  Ltac rename_hyp_with oldname newname :=
    match goal with
    | [ H : context[oldname] |- _ ] => rename H into newname
    end.


  (* ******************************************* *)
  (* *** instantiation of the knowledge calculus *** *)

  Record kdata : Type := mk_data { data_n : node; data_r : round ; data_v : value }.
  Definition trust := kdata.
  Definition trust2owner (t : trust) : option node := Some (data_n t).

  Definition vote2kdata (v : vote) :=
    match v with
    | mk_vote n r v => mk_data n r v
    end.

  Definition decision2kdata (d : decision) :=
    match d with
    | mk_decision n r v => mk_data n r v
    end.

  Definition msg2data (m : Paxos_msg) : list kdata :=
    match m with
    | paxos_start s => []
    | paxos_one_a a => []
    | paxos_one_b b => []
    | paxos_vote v => [vote2kdata v]
    | paxos_decision d => [(*decision2kdata d*)]
    end.

  Definition auth2data (a : AuthenticatedData) : list kdata := msg2data (am_data a).
  Definition auth2trust (a : AuthenticatedData) : list trust := auth2data a.

  Global Instance Paxos_I_ComponentTrust : ComponentTrust :=
    MkComponentTrust trust auth2trust (fun cn out => None) trust2owner.

  Definition trust2data (t : trust) : kdata := t.
  Definition gen_for (d : kdata) (t : trust) := d = t.
  Definition data2owner (d : kdata) : option node := Some (data_n d).

  Lemma inj_no_data : injective trust2data.
  Proof.
    introv; destruct n, m; tcsp.
  Qed.

  Definition sim_data (d1 d2 : kdata) : Prop :=
    match d1, d2 with
    | mk_data n1 r1 v1, mk_data n2 r2 v2 => n1 = n2 /\ r1 = r2
    end.

  Lemma sim_data_sym : symmetric _ sim_data.
  Proof.
    introv; destruct x, y; simpl; tcsp.
  Qed.
  Hint Resolve sim_data_sym : paxos.

  Lemma sim_data_trans : transitive _ sim_data.
  Proof.
    introv; destruct x, y, z; introv a b; simpl in *; repnd; subst; tcsp.
  Qed.
  Hint Resolve sim_data_trans : paxos.

  Lemma sim_data_refl : reflexive _ sim_data.
  Proof.
    introv; destruct x; simpl in *; tcsp.
  Qed.
  Hint Resolve sim_data_refl : paxos.

  Lemma sim_data_equiv : equivalence _ sim_data.
  Proof.
    split; eauto 2 with paxos.
  Qed.
  Hint Resolve sim_data_equiv : paxos.

  Lemma collision_res :
    forall (t : trust) (d1 d2 : kdata),
      gen_for d1 t -> gen_for d2 t -> sim_data d1 d2 -> d1 = d2.
  Proof.
    introv h q; unfold gen_for in *; tcsp; subst; tcsp.
  Qed.

  Definition same_trust2owner :
    forall (t : trust), data2owner (trust2data t) = trust2owner t.
  Proof.
    tcsp.
  Qed.

  Definition data2trust (d : kdata) : list trust := [d].

  Lemma data2trust_correct : forall t, In t (data2trust (trust2data t)).
  Proof.
    introv; simpl; destruct t; tcsp.
  Qed.

  Lemma auth2trust_correct :
    forall a t, In t (auth2trust a) <-> exists d, In t (data2trust d) /\ In d (auth2data a).
  Proof.
    introv; simpl; split; intro h; exrepnd; repndors; subst; tcsp; eauto.
  Qed.

  Definition mem_comp : CompName := MAINname.
  Definition trust_comp : PreCompName := MAINname.

  Definition in_entries (d : kdata) (l : entries) : Prop :=
    exists entry,
      find_entry (data_r d) l = Some entry
      /\ entry_proposal entry = Some (data_v d).

  Definition knows (d : kdata) (m : MAIN_state) : Prop :=
    in_entries d (st_entries m).

  Lemma knows_dec : forall (d : kdata) (m : MAIN_state), decidable (knows d m).
  Proof.
    introv.
    unfold knows, in_entries.
    remember (find_entry (data_r d) (st_entries m)) as fe; symmetry in Heqfe.
    destruct fe;[|right; intro xx; exrepnd; ginv];[].
    destruct e as [r one_bs votes valueop].
    destruct valueop;[|right; intro xx; exrepnd; ginv];[].
    destruct (value_deq v (data_v d)); subst;[|right; intro xx; exrepnd; ginv];[].
    left; eexists; dands; try reflexivity.
  Qed.

  Lemma no_initial_memory :
    forall n i, on_state_of_component MAINname (PaxosSys n) (fun s => ~ knows i s).
  Proof.
    introv h; simpl in *; unfold knows, in_entries in *; exrepnd; simpl in *; ginv.
  Qed.

  Definition id := round.
  Definition id_lt (r1 r2 : id) : Prop := r1 < r2.
  Definition id_lt_trans : transitive _ id_lt := Nat.lt_trans.
  Definition id_lt_arefl  : antireflexive id_lt := Nat.lt_irrefl.
  Definition trust_has_id (t : trust) (i : id) : Prop := data_r t = i.

  Lemma trust_has_id_pres : forall t a b c, trust_has_id t a -> trust_has_id t c -> (id_lt a b \/ a = b) -> (id_lt b c \/ b = c) -> trust_has_id t b.
  Proof.
    introv h q u v.
    repndors; subst; tcsp.
    unfold trust_has_id, id_lt in *; subst; try omega.
  Qed.

  Definition sim_trust := sim_data.

  Lemma sim_trust_equiv : equivalence _ sim_trust.
  Proof.
    unfold sim_trust; eauto 3 with paxos.
  Qed.

  Lemma sim_trust_pres : forall t t' a b, trust_has_id t a -> trust_has_id t b -> sim_trust t t' -> trust_has_id t' a -> trust_has_id t' b.
  Proof.
    unfold trust_has_id; introv h q v w; subst; auto.
  Qed.

  Definition getId (s : MAIN_state) : id := st_current_round s.

  Definition ExtPrim := unit.
  Definition ext_prim_interp (eo : EventOrdering) (e : Event) (p : ExtPrim) : Prop := False.


  Global Instance Paxos_I_KnowledgeComponents : KnowledgeComponents :=
    MkKnowledgeComponents
      kdata
      trust2data
      inj_no_data
      gen_for
      sim_data
      sim_data_sym
      collision_res
      data2owner
      same_trust2owner
      auth2data
      data2trust
      data2trust_correct
      auth2trust_correct
      mem_comp
      trust_comp
      knows
      knows_dec
      PaxosfunLevelSpace
      PaxosSys
      no_initial_memory
      msg2data
      id
      id_lt
      id_lt_trans
      id_lt_arefl
      trust_has_id
      trust_has_id_pres
      sim_trust
      sim_trust_equiv
      sim_trust_pres
      getId
      ExtPrim
      ext_prim_interp.

  Definition create (eo : EventOrdering) (e : Event) (a : data) : list unit := [tt].
  Definition verify (eo : EventOrdering) (e : Event) (a : AuthenticatedData) : bool := true.

  Global Instance Paxos_I_ComponentAuth : ComponentAuth :=
    MkComponentAuth create verify.


  (* ******************************************* *)
  (* *** properties *** *)

  Lemma in_entries_cons :
    forall d a s,
      in_entries d (a :: s)
      <-> if round_deq (data_r d) (entry_round a)
          then entry_proposal a = Some (data_v d)
          else in_entries d s.
  Proof.
    introv; unfold in_entries; split; intro h; exrepnd; smash_paxos2; eauto.
  Qed.
  Hint Rewrite in_entries_cons : paxos.

  Lemma in_entries_nil : forall d, in_entries d [] <-> False.
  Proof.
    introv; unfold in_entries; split; intro h; exrepnd; smash_paxos2; eauto.
  Qed.
  Hint Rewrite in_entries_nil : paxos.

  Lemma add_one_b_preserves_in_entries :
    forall b d s e s',
      add_one_b b s = (e, s')
      -> in_entries d s
      -> in_entries d s'.
  Proof.
    induction s; introv add i; simpl in *; repeat smash_paxos2.
  Qed.
  Hint Resolve add_one_b_preserves_in_entries : paxos.

  Lemma add_vote_preserves_in_entries :
    forall b d s e s',
      add_vote b s = (e, s')
      -> in_entries d s
      -> in_entries d s'.
  Proof.
    induction s; introv add i; simpl in *; repeat smash_paxos2.
    unfold upd_proposal, upd_none; smash_paxos2.
  Qed.
  Hint Resolve add_vote_preserves_in_entries : paxos.

  Lemma log_one_b_preserves_knows :
    forall b d s e s',
      log_one_b b s = (e, s')
      -> knows d s
      -> knows d s'.
  Proof.
    introv log kn.
    destruct s as [r l]; unfold log_one_b in *; simpl in *; smash_paxos2.
    unfold knows in *; simpl in *; smash_paxos2.
  Qed.
  Hint Resolve log_one_b_preserves_knows : paxos.

  Lemma log_vote_preserves_knows :
    forall b d s e s',
      log_vote b s = (e, s')
      -> knows d s
      -> knows d s'.
  Proof.
    introv log kn.
    destruct s as [r l]; unfold log_vote in *; simpl in *; smash_paxos2.
    unfold knows in *; simpl in *; smash_paxos2.
  Qed.
  Hint Resolve log_vote_preserves_knows : paxos.

  Lemma log_my_vote_preserves_knows :
    forall n b d x s e s',
      log_my_vote n b x s = (e, s')
      -> knows d s
      -> knows d s'.
  Proof.
    introv log kn.
    destruct s as [r l]; unfold log_my_vote in *; simpl in *; smash_paxos2.
  Qed.
  Hint Resolve log_my_vote_preserves_knows : paxos.

  Lemma update_last_round_preserves_knows :
    forall d a s,
      knows d s
      -> knows d (update_last_round a s).
  Proof.
    introv kn; tcsp.
  Qed.
  Hint Resolve update_last_round_preserves_knows : paxos.

  Lemma in_entries_unique :
    forall s a b,
      in_entries a s
      -> in_entries b s
      -> sim_data a b
      -> a = b.
  Proof.
    induction s; introv kna knb sim; repeat smash_paxos2;
      destruct a0, b; simpl in *; repnd; subst; try congruence.
  Qed.
  Hint Resolve in_entries_unique : paxos.

  Lemma knows_unique :
    forall s a b,
      knows a s
      -> knows b s
      -> sim_data a b
      -> a = b.
  Proof.
    introv kna knb sim; unfold knows in *; simpl in *; smash_paxos2.
  Qed.
  Hint Resolve knows_unique : paxos.

  Lemma data_is_in_out_implies_dmsg_is_in_out :
    forall {eo : EventOrdering} (e : Event) (o : event2out 0 e) d,
      data_is_in_out d o
      -> exists m, dmsg_is_in_out m o /\ In d (msg2data (dmMsg m)).
  Proof.
    introv h.
    unfold event2out, data_is_in_out, dmsg_is_in_out in *.
    remember (trigger e) as trig.
    destruct trig; simpl in *; tcsp.
    apply in_flat_map; auto.
  Qed.

  Definition not_in_entries r (l : entries) : Prop :=
    match find_entry r l with
    | Some e => entry_proposal e = None
    | None => True
    end.

  Lemma not_in_entries_cons :
    forall r a l,
      not_in_entries r (a :: l)
      <-> if round_deq r (entry_round a)
          then entry_proposal a = None
          else not_in_entries r l.
  Proof.
    unfold not_in_entries; introv; simpl; smash_paxos2; split; intro h; tcsp.
  Qed.
  Hint Rewrite not_in_entries_cons : paxos.

  Lemma in_entries_add_vote_if_not_in :
    forall l n r v e k,
      is_proposer n r = true
      -> not_in_entries r l
      -> add_vote (mk_vote n r v) l = (e, k)
      -> in_entries (mk_data n r v) k.
  Proof.
    induction l; introv isp ni add; simpl in *; repeat smash_paxos2;
      unfold upd_proposal, upd_none, is_vote_from_proposer; smash_paxos2.
  Qed.
  Hint Resolve in_entries_add_vote_if_not_in : paxos.

  Lemma knows_log_vote_if_not_in :
    forall s n r v e s',
      is_proposer n r = true
      -> log_vote (mk_vote n r v) s = (e, s')
      -> not_in_entries r (st_entries s)
      -> knows (mk_data n r v) s'.
  Proof.
    introv isp lv nkn.
    unfold knows, log_vote in *; simpl in *; smash_paxos2.
  Qed.

  Lemma add_one_b_implies_find_entry :
    forall b s e s',
      add_one_b b s = (e, s')
      -> find_entry (one_b_R b) s' = Some e.
  Proof.
    induction s; introv h; simpl in *; repeat smash_paxos2.
  Qed.
  Hint Resolve add_one_b_implies_find_entry : paxos.

  Lemma log_one_b_implies_find_entry :
    forall b s e s',
      log_one_b b s = (e, s')
      -> find_entry (one_b_R b) (st_entries s') = Some e.
  Proof.
    introv h.
    unfold log_one_b in *; smash_paxos2.
  Qed.
  Hint Resolve log_one_b_implies_find_entry : paxos.

  Lemma is_some_false_iff :
    forall {T} (o : option T), is_some o = false <-> o = None.
  Proof.
    unfold is_some; introv; split; destruct o; intro h; subst; tcsp.
  Qed.
  Hint Rewrite @is_some_false_iff : paxos.

  Lemma find_entry_not_proposed_implies_not_in_entries :
    forall r l e,
      find_entry r l = Some e
      -> proposed_entry e = false
      -> not_in_entries r l.
  Proof.
    introv h q; unfold not_in_entries; allrw.
    unfold proposed_entry in *; smash_paxos2.
  Qed.
  Hint Resolve find_entry_not_proposed_implies_not_in_entries : paxos.

  Lemma add_vote_implies_find_entry :
    forall v s e s',
      add_vote v s = (e, s')
      -> find_entry (vote_R v) s' = Some e.
  Proof.
    induction s; introv h; simpl in *; repeat smash_paxos2.
  Qed.
  Hint Resolve add_vote_implies_find_entry : paxos.

  Lemma log_vote_implies_find_entry :
    forall v s e s',
      log_vote v s = (e, s')
      -> find_entry (vote_R v) (st_entries s') = Some e.
  Proof.
    introv h.
    unfold log_vote in *; smash_paxos2.
  Qed.
  Hint Resolve log_vote_implies_find_entry : paxos.

  Lemma data_v_vote2kdata : forall v, data_v (vote2kdata v) = vote_V v.
  Proof.
    destruct v; tcsp.
  Qed.
  Hint Rewrite data_v_vote2kdata : paxos.

  Lemma data_r_vote2kdata : forall v, data_r (vote2kdata v) = vote_R v.
  Proof.
    destruct v; tcsp.
  Qed.
  Hint Rewrite data_r_vote2kdata : paxos.

  Lemma add_vote_preserves_proposal :
    forall v s e s' e' x,
      add_vote v s = (e', s')
      -> find_entry (vote_R v) s = Some e
      -> entry_proposal e = Some x
      -> entry_proposal e' = Some x.
  Proof.
    induction s; introv h q w; simpl in *; smash_paxos2.
    allrw; unfold upd_proposal; simpl; smash_paxos2.
  Qed.

  Lemma valid_my_vote_implies_entry_proposal :
    forall n v e,
      valid_my_vote n v e = true
      -> entry_proposal e = Some (vote_V v).
  Proof.
    introv h; unfold valid_my_vote, has_proposed in *; smash_paxos2.
  Qed.
  Hint Resolve valid_my_vote_implies_entry_proposal : paxos.

  Lemma knows_log_my_vote :
    forall n v s s1 e1 e2 s2 d m,
      log_vote v s = (e1, s1)
      -> log_my_vote n v e1 s1 = (e2, s2)
      -> In d (msg2data (dmMsg m))
      -> In m (send_my_vote n e1 v)
      -> knows d s2.
  Proof.
    introv lv lmv im isv.
    unfold knows, log_my_vote, log_vote, send_my_vote, vote2my in *; simpl in *; smash_paxos2.
    applydup add_vote_implies_find_entry in Heqx1; simpl in *.
    applydup add_vote_implies_find_entry in Heqx0; simpl in *.
    exists e2; dands; smash_paxos2.
    eapply add_vote_preserves_proposal; eauto; smash_paxos2.
  Qed.

  Definition logged_vote (v : vote) (s : MAIN_state) :=
    exists r x,
      find_entry r (st_entries s) = Some x
      /\ In v (entry_votes x).

  Lemma logged_vote_initial_state :
    forall v, logged_vote v initial_state <-> False.
  Proof.
    introv; unfold logged_vote; simpl; split; intro h; exrepnd; tcsp.
  Qed.
  Hint Rewrite logged_vote_initial_state : paxos.

  Lemma logged_vote_initial_state_at :
    forall v r, logged_vote v (initial_state_at r) <-> False.
  Proof.
    introv; unfold logged_vote; simpl; split; intro h; exrepnd; tcsp.
  Qed.
  Hint Rewrite logged_vote_initial_state_at : paxos.

  Lemma update_last_round_initial_state :
    forall r,
      valid_round r = true
      -> update_last_round r initial_state = initial_state_at r.
  Proof.
    introv h; unfold update_last_round, valid_round in *; smash_paxos2.
  Qed.
  (*Hint Rewrite update_last_round_initial_state : paxos.*)

  Lemma log_one_b_initial_state_at :
    forall b r,
      log_one_b b (initial_state_at r)
      = (one_b2entry b, MkState r [one_b2entry b]).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite log_one_b_initial_state_at : paxos.

  Lemma log_one_b_initial_state :
    forall b,
      log_one_b b initial_state
      = (one_b2entry b, MkState initial_round [one_b2entry b]).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite log_one_b_initial_state : paxos.

  Lemma log_vote_initial_state :
    forall v,
      log_vote v initial_state
      = (vote2entry v, MkState initial_round [vote2entry v]).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite log_vote_initial_state : paxos.

  Lemma logged_vote_one_b2entry :
    forall v r b,
      logged_vote v (MkState r [one_b2entry b]) <-> False.
  Proof.
    introv; split; intro h; tcsp.
    unfold logged_vote in *; exrepnd; smash_paxos2.
  Qed.
  Hint Rewrite logged_vote_one_b2entry : paxos.

  Lemma find_entry_add_one_b_implies :
    forall b l e k r x,
      add_one_b b l = (e, k)
      -> find_entry r k = Some x
      -> (exists x', find_entry r l = Some x' /\ r = one_b_R b /\ x = add_one_b_to_entry b x')
         \/ (find_entry r l = Some x /\ r <> one_b_R b)
         \/ (find_entry r l = None /\ x = one_b2entry b).
  Proof.
    induction l; introv add fe; simpl in *; repeat smash_paxos2; eauto; allrw; tcsp.
  Qed.

  Lemma find_entry_add_vote_implies :
    forall v l e k r x,
      add_vote v l = (e, k)
      -> find_entry r k = Some x
      -> (exists x', find_entry r l = Some x' /\ r = vote_R v /\ x = add_vote_to_entry v x')
         \/ (find_entry r l = Some x /\ r <> vote_R v)
         \/ (find_entry r l = None /\ x = vote2entry v).
  Proof.
    induction l; introv add fe; simpl in *; repeat smash_paxos2; eauto; allrw; tcsp.
  Qed.

  Lemma logged_vote_log_one_b :
    forall b s e s' v,
      log_one_b b s = (e, s')
      -> logged_vote v s'
      -> logged_vote v s.
  Proof.
    introv log i; unfold logged_vote, log_one_b in *; exrepnd; smash_paxos2;
      eapply find_entry_add_one_b_implies in i0; eauto; repndors; exrepnd; subst; simpl in *; tcsp;
        try (complete (eexists; eexists; dands; eauto)).
  Qed.
  Hint Resolve logged_vote_log_one_b : paxos.

  Lemma in_add_vote_to_list_implies :
    forall v v' l,
      In v (add_vote_to_list v' l)
      -> v = v' \/ In v l.
  Proof.
    induction l; introv i; simpl in *; tcsp; repeat smash_paxos2.
    repndors; subst; tcsp.
  Qed.

  Lemma logged_vote_log_vote :
    forall s v v' e s',
      log_vote v' s = (e,s')
      -> logged_vote v s'
      -> (v = v' \/ logged_vote v s).
  Proof.
    introv lv i; unfold logged_vote, log_vote in *; exrepnd; smash_paxos2.
    eapply find_entry_add_vote_implies in i0; eauto; repndors; exrepnd; subst; simpl in *; tcsp;
      try (complete (eexists; eexists; dands; eauto)); try complete (right; eauto).
    apply in_add_vote_to_list_implies in i1; repndors; tcsp.
    right; eauto.
  Qed.

  Lemma logged_vote_log_my_vote :
    forall s n e0 v v' e s',
      log_my_vote n v' e0 s = (e,s')
      -> logged_vote v s'
      -> ((v = vote2my n v' /\ valid_my_vote n v' e0 = true) \/ logged_vote v s).
  Proof.
    introv lv i; unfold log_my_vote in *; smash_paxos2.
    eapply logged_vote_log_vote in i; eauto; repndors; tcsp.
  Qed.

  Lemma logged_vote_vote2entry :
    forall v r w,
      logged_vote v (MkState r [vote2entry w]) <-> v = w.
  Proof.
    introv; split; intro h; subst; tcsp;
      unfold logged_vote in *; exrepnd; smash_paxos2.
    exists (vote_R w) (vote2entry w); smash_paxos2.
  Qed.
  Hint Rewrite logged_vote_vote2entry : paxos.

  Lemma find_latest_value_from_votes_nil :
    forall n v low high,
      find_latest_value_from_votes n v low high [] = (low,v).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite find_latest_value_from_votes_nil : paxos.

  Lemma valid_round_if_gt :
    forall r r0,
      r0 < r
      -> valid_round r = true.
  Proof.
    introv h; unfold valid_round, initial_round; smash_paxos2; try omega.
  Qed.
  Hint Resolve valid_round_if_gt : paxos.

  Definition wf_entries (l : entries) :=
    no_repeats (map entry_round l)
    /\ forall x,
      In x l
      -> (forall b, In b (entry_one_bs x) -> one_b_R b = entry_round x)
         /\ (forall v, In v (entry_votes x) -> vote_R v = entry_round x).

  Definition wf_state (s : MAIN_state) := wf_entries (st_entries s).

  Lemma wf_state_initial_state : wf_state initial_state.
  Proof.
    split; simpl; tcsp.
  Qed.
  Hint Resolve wf_state_initial_state : paxos.

  Lemma update_last_round_preserves_wf_state :
    forall a s,
      wf_state s
      -> wf_state (update_last_round a s).
  Proof.
    tcsp.
  Qed.
  Hint Resolve update_last_round_preserves_wf_state : paxos.

  Lemma implies_wf_entries_cons :
    forall x l,
      wf_entries (x :: l)
      <-> ((forall b, In b (entry_one_bs x) -> one_b_R b = entry_round x)
           /\ (forall v, In v (entry_votes x) -> vote_R v = entry_round x)
           /\ wf_entries l
           /\ ~ In (entry_round x) (map entry_round l)).
  Proof.
    introv; split; intro h; repnd; dands; tcsp; try (complete (apply h; tcsp)).
    { destruct h as [norep imp]; simpl in *.
      rewrite no_repeats_cons in *; repnd.
      split; tcsp.
      introv xx; apply imp; tcsp. }
    { destruct h as [norep imp]; simpl in *.
      rewrite no_repeats_cons in *; repnd; tcsp. }
    { destruct h2 as [norep imp].
      split; simpl in *.
      { rewrite no_repeats_cons; dands; tcsp. }
      introv xx; simpl in *; repndors; subst; tcsp.
      apply imp in xx; tcsp. }
  Qed.

  Lemma in_add_one_b_to_list_implies :
    forall x b l,
      In x (add_one_b_to_list b l)
      -> x = b \/ In x l.
  Proof.
    induction l; introv h; simpl in *; tcsp; smash_paxos2; repndors; subst; tcsp.
  Qed.

  Lemma add_one_b_preserves_entry_rounds_rev :
    forall b l e k,
      add_one_b b l = (e, k)
      -> eqset (map entry_round k) (one_b_R b :: map entry_round l).
  Proof.
    induction l; introv h; simpl in *; smash_paxos2.
    { introv; split; intro h; simpl in *; repndors; subst; tcsp. }
    pose proof (IHl e x1) as IHl; autodimp IHl hyp.
    introv; split; intro h; simpl in *; repndors; subst; tcsp.
    { apply IHl in h; simpl in *; tcsp. }
    { right; apply IHl; simpl; tcsp. }
    { right; apply IHl; simpl; tcsp. }
  Qed.

  Lemma add_vote_preserves_entry_rounds_rev :
    forall v l e k,
      add_vote v l = (e, k)
      -> eqset (map entry_round k) (vote_R v :: map entry_round l).
  Proof.
    induction l; introv h; simpl in *; smash_paxos2.
    { introv; split; intro h; simpl in *; repndors; subst; tcsp. }
    pose proof (IHl e x1) as IHl; autodimp IHl hyp.
    introv; split; intro h; simpl in *; repndors; subst; tcsp.
    { apply IHl in h; simpl in *; tcsp. }
    { right; apply IHl; simpl; tcsp. }
    { right; apply IHl; simpl; tcsp. }
  Qed.

  Lemma add_one_b_preserves_wf_entries :
    forall b l e k,
      add_one_b b l = (e, k)
      -> wf_entries l
      -> wf_entries k.
  Proof.
    induction l; introv h q; simpl in *; tcsp; smash_paxos2;
      apply implies_wf_entries_cons; repnd; dands; simpl in *; tcsp;
        try (apply implies_wf_entries_cons in q; repnd; tcsp);
        try (complete (introv xx; repndors; subst; tcsp));
        try (complete (eapply IHl; eauto));
        try (complete (introv xx; apply in_add_one_b_to_list_implies in xx; repndors; subst; tcsp));
        try (complete (apply add_one_b_preserves_entry_rounds_rev in Heqx;
                       intro xx; destruct q; apply Heqx in xx; simpl in *; tcsp)).
  Qed.
  Hint Resolve add_one_b_preserves_wf_entries : paxos.

  Lemma add_vote_preserves_wf_entries :
    forall v l e k,
      add_vote v l = (e, k)
      -> wf_entries l
      -> wf_entries k.
  Proof.
    induction l; introv h q; simpl in *; tcsp; smash_paxos2;
      apply implies_wf_entries_cons; repnd; dands; simpl in *; tcsp;
        try (apply implies_wf_entries_cons in q; repnd; tcsp);
        try (complete (introv xx; repndors; subst; tcsp));
        try (complete (eapply IHl; eauto));
        try (complete (introv xx; apply in_add_vote_to_list_implies in xx; repndors; subst; tcsp));
        try (complete (apply add_vote_preserves_entry_rounds_rev in Heqx;
                       intro xx; destruct q; apply Heqx in xx; simpl in *; tcsp)).
  Qed.
  Hint Resolve add_vote_preserves_wf_entries : paxos.

  Lemma log_one_b_preserves_wf_state :
    forall b s e s',
      log_one_b b s = (e, s')
      -> wf_state s
      -> wf_state s'.
  Proof.
    introv h wf; unfold log_one_b, wf_state in *; smash_paxos2.
  Qed.
  Hint Resolve log_one_b_preserves_wf_state : paxos.

  Lemma log_vote_preserves_wf_state :
    forall b s e s',
      log_vote b s = (e, s')
      -> wf_state s
      -> wf_state s'.
  Proof.
    introv h wf; unfold log_vote, wf_state in *; smash_paxos2.
  Qed.
  Hint Resolve log_vote_preserves_wf_state : paxos.

  Lemma log_my_vote_preserves_wf_state :
    forall n b x s e s',
      log_my_vote n b x s = (e, s')
      -> wf_state s
      -> wf_state s'.
  Proof.
    introv h wf; unfold log_my_vote in *; smash_paxos2.
  Qed.
  Hint Resolve log_my_vote_preserves_wf_state : paxos.

  Lemma log_vote_implies_logged_vote :
    forall w s e s' x,
      log_vote w s = (e, s')
      -> In x (entry_votes e)
      -> logged_vote x s'.
  Proof.
    introv log i; unfold logged_vote, log_vote in *; exrepnd; smash_paxos2.
    apply add_vote_implies_find_entry in Heqx0.
    exists (vote_R w) e; allrw; tcsp.
  Qed.
  Hint Resolve log_vote_implies_logged_vote : paxos.

  Lemma wf_state_log_vote_in_entry_votes_implies :
    forall v s e s' v',
      wf_state s
      -> log_vote v s = (e, s')
      -> In v' (entry_votes e)
      -> vote_R v = vote_R v'.
  Proof.
    introv wf lv i.
    unfold log_vote, wf_state in *; smash_paxos2.
    remember (st_entries s) as l; clear Heql.
    revert dependent x1.
    induction l; introv h; simpl in *; tcsp; smash_paxos2;
      allrw implies_wf_entries_cons; repnd;
        simpl in *; repndors; subst; tcsp.
    { apply in_add_vote_to_list_implies in i; repndors; subst; tcsp.
      apply wf1 in i; try congruence. }
    { autodimp IHl hyp; pose proof (IHl x2) as IHl; autodimp IHl hyp. }
  Qed.

  Lemma in_entry2vote_nodes :
    forall n val e,
      In n (entry2vote_nodes val e)
      -> exists v,
        In v (entry_votes e)
        /\ vote_N v = n
        /\ vote_V v = val.
  Proof.
    introv i.
    apply in_map_iff in i; exrepnd.
    apply filter_In in i0; repnd; smash_paxos2; eauto.
  Qed.

  Lemma log_my_vote_implies_find_entry :
    forall n v x s e s',
      log_my_vote n v x s = (e, s')
      -> (find_entry (vote_R v) (st_entries s') = Some e
          \/ (e = x /\ s = s' /\ valid_my_vote n v x = false)).
  Proof.
    introv h.
    unfold log_my_vote in *; smash_paxos2.
    apply log_vote_implies_find_entry in h; smash_paxos2.
  Qed.

  Lemma add_vote_implies_equal_entry_round :
    forall v s e s',
      add_vote v s = (e, s')
      -> vote_R v = entry_round e.
  Proof.
    induction s; introv h; simpl in *; smash_paxos2.
  Qed.

  Lemma log_vote_implies_equal_entry_round :
    forall v s e s',
      log_vote v s = (e, s')
      -> vote_R v = entry_round e.
  Proof.
    unfold log_vote; introv h; simpl in *; smash_paxos2.
    apply add_vote_implies_equal_entry_round in Heqx; auto.
  Qed.

  Lemma log_my_vote_implies_equal_entry_round :
    forall n v e1 s1 e2 s2,
      log_my_vote n v e1 s1 = (e2, s2)
      -> vote_R v = entry_round e2 \/ e1 = e2.
  Proof.
    introv h; unfold log_my_vote in h; smash_paxos2.
    apply log_vote_implies_equal_entry_round in h; smash_paxos2.
  Qed.

  Lemma mk_vote_eta :
    forall v, mk_vote (vote_N v) (vote_R v) (vote_V v) = v.
  Proof.
    destruct v; auto.
  Qed.
  Hint Rewrite mk_vote_eta : paxos.

  Definition by_quorum (F : node -> Prop) : Prop :=
    exists q,
      forms_quorum q = true
      /\ forall m, In m q -> F m.

  Lemma forms_quorum_pos :
    forall q, forms_quorum q = true -> 0 < length q.
  Proof.
    introv h; dup h as w.
    eapply quorum_intersection in h; eauto; exrepnd.
    destruct q; simpl in *; tcsp; try omega.
  Qed.

  Lemma implies_in_add_vote_to_list :
    forall v v' l,
      In v l
      -> In v (add_vote_to_list v' l).
  Proof.
    induction l; introv i; simpl in *; tcsp; repeat smash_paxos2.
    repndors; subst; tcsp.
  Qed.

  Lemma log_vote_preserves_logged_vote :
    forall s v v' e s',
      log_vote v' s = (e,s')
      -> logged_vote v s
      -> logged_vote v s'.
  Proof.
    introv lv i; unfold logged_vote, log_vote in *; exrepnd; smash_paxos2.
    remember (st_entries s) as l; clear Heql.
    exists r.
    revert dependent e.
    revert dependent x2.
    induction l; introv h; simpl in *; tcsp; smash_paxos2.
    { eexists; dands; eauto.
      apply implies_in_add_vote_to_list; auto. }
    { exists x; dands; tcsp. }
    { eexists; dands; eauto. }
  Qed.
  Hint Resolve log_vote_preserves_logged_vote : paxos.

  Lemma log_my_vote_preserves_logged_vote :
    forall s v n v' x e s',
      log_my_vote n v' x s = (e,s')
      -> logged_vote v s
      -> logged_vote v s'.
  Proof.
    introv lv i; unfold log_my_vote in *; smash_paxos2.
  Qed.
  Hint Resolve log_my_vote_preserves_logged_vote : paxos.

  Lemma log_one_b_preserves_logged_vote :
    forall b s e s' v,
      log_one_b b s = (e, s')
      -> logged_vote v s
      -> logged_vote v s'.
  Proof.
    introv log i; unfold logged_vote, log_one_b in *; exrepnd; smash_paxos2.
    exists r.
    remember (st_entries s) as l; clear Heql.
    revert e x2 Heqx0; induction l; introv h; simpl in *; smash_paxos2;
      try (complete (eexists; dands; eauto)).
  Qed.
  Hint Resolve log_one_b_preserves_logged_vote : paxos.

  Lemma find_entry_implies_eq_entry_round :
    forall r l e,
      find_entry r l = Some e
      -> entry_round e = r.
  Proof.
    induction l; introv h; simpl in *; smash_paxos2.
  Qed.

  Lemma find_entry_implies_in :
    forall r l e,
      find_entry r l = Some e
      -> In e l.
  Proof.
    induction l; introv h; simpl in *; smash_paxos2.
  Qed.

  Lemma log_vote_preserves_in_entry_votes :
    forall v s e' s' e,
      log_vote v s = (e', s')
      -> find_entry (vote_R v) (st_entries s) = Some e
      -> In v (entry_votes e)
      -> In v (entry_votes e').
  Proof.
    introv h q i.
    unfold log_vote in *; smash_paxos2.
    remember (st_entries s) as l; clear Heql.
    revert e' x1 Heqx.
    induction l; introv h; simpl in *; smash_paxos2.
    apply implies_in_add_vote_to_list; auto.
  Qed.

  Definition logged_one_b (b : one_b) (s : MAIN_state) :=
    exists r x,
      find_entry r (st_entries s) = Some x
      /\ In b (entry_one_bs x).

  Lemma logged_one_b_initial_state :
    forall b, logged_one_b b initial_state <-> False.
  Proof.
    introv; unfold logged_one_b; simpl; split; intro h; exrepnd; tcsp.
  Qed.
  Hint Rewrite logged_one_b_initial_state : paxos.

  Lemma logged_one_b_initial_state_at :
    forall b r, logged_one_b b (initial_state_at r) <-> False.
  Proof.
    introv; unfold logged_one_b; simpl; split; intro h; exrepnd; tcsp.
  Qed.
  Hint Rewrite logged_one_b_initial_state_at : paxos.

  Lemma logged_one_b_one_b2entry :
    forall b r b',
      logged_one_b b (MkState r [one_b2entry b']) <-> b' = b.
  Proof.
    introv; split; intro h; tcsp.
    { unfold logged_one_b in *; exrepnd; smash_paxos2. }
    { subst; unfold logged_one_b; simpl.
      exists (one_b_R b); smash_paxos2; eexists; dands; eauto.
      simpl; tcsp. }
  Qed.
  Hint Rewrite logged_one_b_one_b2entry : paxos.

  Lemma logged_one_b_log_one_b :
    forall s b b' e s',
      log_one_b b' s = (e,s')
      -> logged_one_b b s'
      -> (b = b' \/ logged_one_b b s).
  Proof.
    introv lv i; unfold logged_one_b, log_one_b in *; exrepnd; smash_paxos2.
    eapply find_entry_add_one_b_implies in i0; eauto; repndors; exrepnd; subst; simpl in *; tcsp;
      try (complete (eexists; eexists; dands; eauto)); try complete (right; eauto).
    apply in_add_one_b_to_list_implies in i1; repndors; tcsp.
    right; eauto.
  Qed.

  Lemma logged_one_b_update_last_round :
    forall b r s,
      logged_one_b b (update_last_round r s) = logged_one_b b s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite logged_one_b_update_last_round : paxos.

  Lemma logged_one_b_log_vote :
    forall s b v e s',
      log_vote v s = (e,s')
      -> logged_one_b b s'
      -> logged_one_b b s.
  Proof.
    introv lv i; unfold logged_one_b, log_vote in *; exrepnd; smash_paxos2.
    eapply find_entry_add_vote_implies in i0; eauto; repndors; exrepnd; subst; simpl in *; tcsp;
      try (complete (eexists; eexists; dands; eauto)); try complete (right; eauto).
  Qed.

  Lemma logged_one_b_log_my_vote :
    forall s n e b v e' s',
      log_my_vote n v e s = (e',s')
      -> logged_one_b b s'
      -> logged_one_b b s.
  Proof.
    introv lv i; unfold log_my_vote in *; smash_paxos2.
    eapply logged_one_b_log_vote in i; eauto; repndors; tcsp.
  Qed.

  Lemma logged_one_b_vote2entry :
    forall b r v,
      logged_one_b b (MkState r [vote2entry v]) <-> False.
  Proof.
    introv; split; intro h; tcsp.
    unfold logged_one_b in *; exrepnd; smash_paxos2.
  Qed.
  Hint Rewrite logged_one_b_vote2entry : paxos.

  Lemma log_vote_preserves_logged_one_b :
    forall s b v e s',
      log_vote v s = (e,s')
      -> logged_one_b b s
      -> logged_one_b b s'.
  Proof.
    introv lv i; unfold logged_one_b, log_vote in *; exrepnd; smash_paxos2.
    remember (st_entries s) as l; clear Heql.
    exists r.
    revert dependent e.
    revert dependent x2.
    induction l; introv h; simpl in *; tcsp; smash_paxos2;
      try (complete (eexists; dands; eauto)).
  Qed.

  Lemma log_my_vote_preserves_logged_one_b :
    forall s n e b v e' s',
      log_my_vote n v e s = (e',s')
      -> logged_one_b b s
      -> logged_one_b b s'.
  Proof.
    introv lv i; unfold log_my_vote in *; smash_paxos2.
    eapply log_vote_preserves_logged_one_b; eauto.
  Qed.

  Lemma add_one_b_implies_equal_entry_round :
    forall b s e s',
      add_one_b b s = (e, s')
      -> one_b_R b = entry_round e.
  Proof.
    induction s; introv h; simpl in *; smash_paxos2.
  Qed.

  Lemma log_one_b_implies_equal_entry_round :
    forall b s e s',
      log_one_b b s = (e, s')
      -> one_b_R b = entry_round e.
  Proof.
    unfold log_one_b; introv h; simpl in *; smash_paxos2.
    apply add_one_b_implies_equal_entry_round in Heqx; auto.
  Qed.

  Lemma valid_my_vote_implies_not_proposer :
    forall n v e,
      valid_my_vote n v e = true
      -> is_proposer n (vote_R v) = false.
  Proof.
    introv h.
    unfold valid_my_vote, is_vote_from_proposer, same_node in h; smash_paxos2.
    remember (is_proposer n (vote_R v)) as b; symmetry in Heqb; destruct b; auto.
    eapply is_proposer_inj in h; try exact Heqb; tcsp.
  Qed.

  Definition is_vote {eo : EventOrdering} (e : Event) :=
    exists (v : vote), trigger_op e = Some (paxos_vote v).

  Definition is_one_a {eo : EventOrdering} (e : Event) :=
    exists (a : one_a), trigger_op e = Some (paxos_one_a a).

  Definition is_one_b {eo : EventOrdering} (e : Event) :=
    exists (b : one_b), trigger_op e = Some (paxos_one_b b).

  Definition logged_similar_vote (v : vote) (s : MAIN_state) :=
    exists v',
      logged_vote v' s /\ vote_N v = vote_N v' /\ vote_R v = vote_R v'.

  Lemma in_add_vote_to_list :
    forall v vs,
      ~ In (vote_N v) (map vote_N vs)
      -> In v (add_vote_to_list v vs).
  Proof.
    induction vs; introv ni; simpl in *; smash_paxos2; apply not_or in ni; repnd; tcsp.
  Qed.

  Lemma find_entry_implies_in_entry_rounds :
    forall r l e,
      find_entry r l = Some e
      -> In r (map entry_round l).
  Proof.
    introv find.
    applydup find_entry_implies_in in find.
    applydup find_entry_implies_eq_entry_round in find; subst.
    apply in_map_iff; eexists; eauto.
  Qed.

  Lemma log_vote_implies_logged :
    forall v s1 e s2,
      wf_state s1
      -> log_vote v s1 = (e, s2)
      -> logged_vote v s2 \/ logged_similar_vote v s1.
  Proof.
    introv wf h.
    unfold log_vote in *; smash_paxos2.
    unfold logged_similar_vote, logged_vote; simpl.
    unfold wf_state in *.
    remember (st_entries s1) as l; clear Heql.
    revert e x1 Heqx wf.
    induction l; introv h wf; simpl in *; smash_paxos2.

    { unfold find_entry; simpl.
      left.
      exists (vote_R v); smash_paxos2; eexists; dands; eauto; simpl; tcsp. }

    { destruct a as [r bs vs prp]; simpl in *; subst.
      rewrite implies_wf_entries_cons in *; simpl in *; repnd.
      unfold add_vote_to_entry; simpl.
      destruct (in_dec node_deq (vote_N v) (map vote_N vs)) as [d|d].

      { right.
        apply in_map_iff in d; exrepnd.
        applydup wf1 in d0.
        exists x; dands; tcsp.
        exists (vote_R x); smash_paxos2.
        eexists; dands; eauto. }

      { left.
        exists (vote_R v); smash_paxos2.
        eexists; dands; eauto; simpl.
        apply in_add_vote_to_list; auto. } }

    { rewrite implies_wf_entries_cons in *; simpl in *; repnd.
      pose proof (IHl e x2) as IHl; repeat (autodimp IHl hyp).
      repndors; exrepnd.

      { applydup add_vote_preserves_entry_rounds_rev in Heqx as eqs.
        applydup find_entry_implies_eq_entry_round in IHl0 as eqr; subst.
        applydup find_entry_implies_in_entry_rounds in IHl0 as j.
        left.
        exists (entry_round x); smash_paxos2.
        { destruct wf; apply eqs in j; simpl in *; repndors; tcsp; try congruence. }
        eexists; dands; eauto. }

      { right.
        exists v'; dands; auto.
        exists r x; smash_paxos2.
        apply find_entry_implies_in_entry_rounds in IHl3; tcsp. } }
  Qed.

  Lemma logged_vote_implies_logged_similar_votes :
    forall v s, logged_vote v s -> logged_similar_vote v s.
  Proof.
    introv h; exists v; dands; tcsp.
  Qed.
  Hint Resolve logged_vote_implies_logged_similar_votes : paxos.

  Lemma log_vote_preserves_logged_similar_vote :
    forall v s1 e s2 v',
      log_vote v s1 = (e, s2)
      -> logged_similar_vote v' s1
      -> logged_similar_vote v' s2.
  Proof.
    introv log h.
    unfold logged_similar_vote in *; exrepnd.
    exists v'0; dands; tcsp.
    eapply log_vote_preserves_logged_vote; eauto.
  Qed.
  Hint Resolve log_vote_preserves_logged_similar_vote : paxos.

  Lemma find_voted_value_from_votes_some_implies :
    forall n vs val,
      find_voted_value_from_votes n vs = Some val
      -> exists v,
        In v vs
        /\ vote_N v = n
        /\ vote_V v = val.
  Proof.
    induction vs; introv find; simpl in *; smash_paxos2; eauto.
    { apply IHvs in find; exrepnd; eauto. }
  Qed.

  Lemma find_voted_value_from_votes_none_implies :
    forall n vs,
      find_voted_value_from_votes n vs = None
      -> forall v, In v vs -> vote_N v <> n.
  Proof.
    induction vs; introv find; simpl in *; smash_paxos2; eauto.
    introv xx; repndors; subst; tcsp.
    apply IHvs; auto.
  Qed.

  Lemma find_latest_value_from_votes_implies :
    forall l n v low high r v',
      wf_entries l
      -> find_latest_value_from_votes n v low high l = (r, v')
      ->
      (r = low
       /\ v' = v
       /\ forall e x,
           In e l
           -> low < entry_round e < high
           -> In x (entry_votes e)
           -> vote_N x <> n)
      \/ (exists e,
             find_entry r l = Some e
             /\ low < r < high
             /\ In (mk_vote n r v') (entry_votes e)
             /\ forall r' e' w,
                 low < r' < high
                 -> find_entry r' l = Some e'
                 -> In (mk_vote n r' w) (entry_votes e')
                 -> r' <= r).
  Proof.
    induction l; introv wf find; simpl in *; smash_paxos2; tcsp; try omega;
      try (complete (allrw implies_wf_entries_cons; repnd;
                     apply IHl in find; repndors; exrepnd; subst; tcsp; try omega;
                     try (complete (left; dands; tcsp; introv xx; repndors; subst; tcsp; try (complete (apply find; auto));
                                    introv w z; eapply find_voted_value_from_votes_none_implies in Heqx; eauto));
                     right; exists e; dands; tcsp; GC; try omega;
                     introv h q z; smash_paxos2; try omega;
                     try (complete (eapply find_voted_value_from_votes_none_implies in Heqx; eauto; simpl in *; tcsp));
                     destruct (le_dec r' r); tcsp;
                     applydup find_entry_implies_in in q;
                     applydup wf2 in q0; repnd;
                     applydup q1 in z; simpl in *; subst;
                     apply find0 in z; smash_paxos2; try omega)).

    { allrw implies_wf_entries_cons; repnd.
      apply IHl in find; repndors; exrepnd; subst; tcsp; try omega.
      right; exists a; dands; tcsp; GC.
      { apply find_voted_value_from_votes_some_implies in Heqx; exrepnd; subst.
        applydup wf1 in Heqx1.
        rewrite <- Heqx0; autorewrite with paxos; auto. }
      { introv h q z; smash_paxos2; try omega.
        apply find_entry_implies_in in q.
        destruct (le_dec r' (entry_round a)); tcsp.
        applydup wf2 in q; repnd.
        applydup q0 in z; simpl in *; subst.
        apply find in z; smash_paxos2; try omega. } }

    { allrw implies_wf_entries_cons; repnd.
      apply IHl in find; repndors; exrepnd; subst; tcsp; try omega.
      destruct wf.
      apply find_entry_implies_in_entry_rounds in find1; auto. }
  Qed.

  Lemma find_voted_value_from_one_bs_prop1 :
    forall bs v low high,
      find_voted_value_from_one_bs v low high bs = (low,v)
      \/ exists b,
        In b bs
        /\ find_voted_value_from_one_bs v low high bs = (one_b_maxr b, one_b_maxv b)
        /\ low < one_b_maxr b < high.
  Proof.
    induction bs; introv; simpl in *; tcsp; smash_paxos2;
      try (complete (pose proof (IHbs v low high) as IHbs; repndors; tcsp;
                     try (complete (right; exists a; dands; tcsp));
                     try (complete (exrepnd; right; exists b; dands; tcsp; try omega)))).
    pose proof (IHbs (one_b_maxv a) (one_b_maxr a) high) as IHbs; repndors; tcsp;
      try (complete (right; exists a; dands; tcsp));
      try (complete (exrepnd; right; exists b; dands; tcsp; try omega)).
  Qed.

  Lemma find_voted_value_from_one_bs_prop2 :
    forall n r mr mv bs v low high,
      In (mk_one_b n r mr mv) bs
      -> low < mr < high
      -> exists b,
          In b bs
          /\ find_voted_value_from_one_bs v low high bs = (one_b_maxr b, one_b_maxv b)
          /\ mr <= one_b_maxr b < high.
  Proof.
    induction bs; introv i cond; simpl in *; tcsp.
    repndors; subst; simpl in *; smash_paxos2; GC; try omega;
      try (complete (destruct (lt_dec (one_b_maxr a) mr); try omega;
                     pose proof (IHbs v low high) as q;
                     repeat (autodimp q hyp); exrepnd;
                     exists b; dands; tcsp)).

    { pose proof (find_voted_value_from_one_bs_prop1 bs mv mr high) as q.
      repndors; exrepnd.
      { eexists; dands; eauto. }
      { exists b; dands; tcsp; try omega. } }

    { destruct (lt_dec (one_b_maxr a) mr); try omega.

      { pose proof (IHbs (one_b_maxv a) (one_b_maxr a) high) as q.
        repeat (autodimp q hyp); exrepnd.
        exists b; dands; tcsp. }

      pose proof (find_voted_value_from_one_bs_prop1 bs (one_b_maxv a) (one_b_maxr a) high) as q.
      repndors; exrepnd.
      { exists a; dands; tcsp; try omega. }
      { exists b; dands; tcsp; try omega. } }
  Qed.


  (* === === *)


  Lemma send_vote_from_location_step :
    forall (eo : EventOrdering) (e : Event) n r v l m s,
      In (send_vote (mk_vote n r v) l) (M_output_ls_on_this_one_event (PaxosLocalSys m s) e)
      -> n = m.
  Proof.
    introv i.
    apply in_M_output_ls_on_this_one_event_implies in i.
    exrepnd; simpl in *; ginv; simpl in *.
    paxos_dest_msg m0; try (unfold send_my_vote in *; repndors; smash_paxos2).
  Qed.

  Lemma send_vote_from_location :
    forall (eo : EventOrdering) (e : Event) n r v l,
      In (send_vote (mk_vote n r v) l) (M_output_sys_on_event PaxosSys e)
      -> n = loc e.
  Proof.
    introv out.
    unfold M_output_sys_on_event in *; simpl in *.
    allrw @M_output_ls_on_event_as_run; exrepnd; simpl in *.
    applydup M_run_ls_before_event_ls_is_paxos in out1.
    exrepnd; subst; simpl in *; ginv; simpl in *.
    apply send_vote_from_location_step in out0; auto.
  Qed.

  Lemma paxos_preserves_knows_step :
    forall {eo : EventOrdering} (e : Event) d, preserves_knows_step e d.
  Proof.
    introv cor run eqst kn; simpl in *; unfold PaxosSys in *; simpl in *.
    apply M_run_ls_before_event_ls_is_paxos in run; exrepnd; subst.
    unfold state_of_component in eqst; simpl in *; ginv.
    unfold M_run_ls_on_this_one_event.
    unfold isCorrect in *.
    remember (trigger_op e) as trig; destruct trig; tcsp;[]; GC; rev_Some; simpl in *.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input, on_comp; simpl.
    paxos_dest_msg m;
      try (complete (eexists; eexists; dands; try reflexivity; simpl; smash_paxos3)).
  Qed.
  Hint Resolve paxos_preserves_knows_step : paxos.

  Lemma ASSUMPTION_knowledge_preserved_true :
    forall {eo : EventOrdering} (e : Event), interpret e ASSUMPTION_knowledge_preserved_step.
  Proof.
    introv h; simpl in *.
    remember (direct_pred e) as dp; symmetry in Heqdp; destruct dp; tcsp.
    eapply knows_after_preserved_step; smash_paxos2.
  Qed.
  Hint Resolve ASSUMPTION_knowledge_preserved_true : paxos.

  Lemma ASSUMPTION_knows_unique_true :
    forall {eo : EventOrdering} (e : Event), interpret e ASSUMPTION_knows_unique.
  Proof.
    introv h; simpl in *; repnd; unfold knows_after in *; exrepnd.
    eapply state_after_eq_state_after_implies_eq_mem in h0; try exact h1; subst; simpl in *.
    f_equal; smash_paxos2.
  Qed.
  Hint Resolve ASSUMPTION_knows_unique_true : paxos.

  Lemma ASSUMPTION_disseminate_new_true :
    forall {eo : EventOrdering} (e : Event), interpret e ASSUMPTION_disseminate_new.
  Proof.
    introv h; simpl in *; exrepnd; subst.
    unfold disseminate_data, knows_after in *; exrepnd; simpl in *.
    apply data_is_in_out_implies_dmsg_is_in_out in h1; exrepnd.
    eapply M_byz_output_sys_on_event_implies_M_output_sys_on_event in h0; eauto; smash_paxos2.

    unfold M_output_sys_on_event in *; simpl in *.
    apply M_output_ls_on_event_as_run in h0; exrepnd.
    unfold state_after, M_state_sys_on_event, M_state_ls_on_event; simpl.
    rewrite M_run_ls_on_event_unroll2; allrw; simpl.
    apply M_run_ls_before_event_ls_is_paxos in h0; exrepnd; subst; simpl in *.

    apply in_M_output_ls_on_this_one_event_implies in h3; exrepnd; simpl in *; ginv.
    unfold M_run_ls_on_this_one_event; simpl; allrw; simpl.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input, on_comp, state_of_component in *; simpl in *.
    paxos_dest_msg m0; eexists; dands; repndors; smash_paxos2;
        try (complete (eexists; dands; try reflexivity));
        try (complete (eapply knows_log_my_vote; eauto; smash_paxos3));
        try (complete (eapply knows_log_vote_if_not_in; eauto; smash_paxos3));
        try (complete (unfold same_round in *; smash_paxos3; eapply knows_log_vote_if_not_in; eauto; allrw <-; smash_paxos3)).
  Qed.
  Hint Resolve ASSUMPTION_disseminate_new_true : paxos.

  Lemma unique_votes :
    forall (eo : EventOrdering) (e1 e2 : Event) n r v1 v2 l1 l2,
      In (send_vote (mk_vote n r v1) l1) (M_output_sys_on_event PaxosSys e1)
      -> In (send_vote (mk_vote n r v2) l2) (M_output_sys_on_event PaxosSys e2)
      -> v1 = v2.
  Proof.
    introv outa outb.
    applydup send_vote_from_location in outa.
    applydup send_vote_from_location in outb.
    simpl in *.

    assert (ex_node_e e1) as ex1 by (unfold ex_node_e; allrw; simpl; eauto).
    assert (ex_node_e e2) as ex2 by (unfold ex_node_e; allrw; simpl; eauto).

    Opaque ASSUMPTION_knowledge_preserved_step ASSUMPTION_disseminate_new ASSUMPTION_knows_unique.
    let tac := (fun _ => eauto 3 with paxos) in
    let smash := (fun _ => smash_paxos2) in
    use_rule (DERIVED_RULE_disseminate_once_true
                n (MkEventN e1 ex1) (MkEventN e1 ex1) (MkEventN e2 ex2)
                [] [] (mk_data n r v1) (mk_data n r v2))
             tac smash;
      try (complete (introv xx; eapply in_M_output_sys_on_event_implies_disseminate; eauto; simpl; tcsp)).
  Qed.

  (* This could be derived from our knowledge theory *)
  Lemma received_votes :
    forall {eo : EventOrdering} (e : Event) n s v,
      M_run_ls_on_event (PaxosLocalSys n initial_state) e = Some (PaxosLocalSys n s)
      -> logged_vote v s
      -> exists (e' : Event),
          e' ⊑ e
          /\ ((trigger_op e' = Some (paxos_vote v)(* /\ vote_N v <> n*))
              \/ (In (send_vote v (other_nodes n)) (M_output_ls_on_event (PaxosSys n) e') /\ vote_N v = n)).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd_type.
    introv run i.
    rewrite M_run_ls_on_event_unroll2 in run.
    apply map_option_Some in run; exrepnd; rev_Some.
    apply map_option_Some in run0; exrepnd; ginv.
    applydup M_run_ls_before_event_ls_is_paxos in run1; exrepnd; subst; smash_paxos2.

    unfold M_run_ls_on_input_ls, M_run_ls_on_input, on_comp in run2; simpl in *.
    paxos_dest_msg a0;
      rewrite M_run_ls_before_event_unroll_on in run1;
      destruct (dec_isFirst e); repeat smash_paxos2;
        repeat (rewrite update_last_round_initial_state in *; auto; smash_paxos2;first[ idtac;[] | fail]);
        try (complete (eapply ind in run1; eauto; eauto 3 with eo; exrepnd; exists e'; dands; eauto 3 with eo));
        try (eapply logged_vote_log_my_vote in i; eauto;[]; repndors; subst; smash_paxos2; try omega);
        try (eapply logged_vote_log_vote in i; eauto;[]; repndors; subst; smash_paxos2; try omega);
        try (eapply logged_vote_log_one_b in i; eauto;[]);
        try (complete (eapply ind in run1; eauto 3 with eo; exrepnd; eexists; dands; eauto; eauto 3 with eo));
        try (complete (exists e; dands; eauto 3 with eo;
                       right; unfold M_output_ls_on_event; simpl; rewrite M_run_ls_before_event_unroll_on;
                       destruct (dec_isFirst e); tcsp; simpl;
                       unfold PaxosSys, M_output_ls_on_this_one_event, M_run_ls_on_input_out, M_run_ls_on_input, on_comp;
                       repeat (allrw; simpl; try (unfold send_my_vote); smash_paxos2; tcsp))).
  Qed.

  Lemma send_vote_implies :
    forall {eo : EventOrdering} (e : Event) v dst delay,
      (MkDMsg (paxos_vote v) dst delay) ∈ PaxosSys ⇝ e
      -> dst = other_nodes (loc e) /\ delay = '0.
  Proof.
    introv send.
    unfold M_output_sys_on_event in *; simpl in *.
    allrw @M_output_ls_on_event_as_run; exrepnd; simpl in *.
    apply in_M_output_ls_on_this_one_event_implies in send0; exrepnd; simpl in *.
    applydup M_run_ls_before_event_ls_is_paxos in send1; exrepnd; subst; simpl in *; ginv; simpl in *.
    paxos_dest_msg m;
      try (complete (unfold lower_out_break, PaxosLocalSys, send_my_vote in *;
                     simpl in *; repndors; smash_paxos2; inversion send0; tcsp)).
  Qed.

  Lemma send_one_b_implies :
    forall {eo : EventOrdering} (e : Event) b dst delay,
      (MkDMsg (paxos_one_b b) dst delay) ∈ PaxosSys ⇝ e
      -> dst = other_nodes (loc e) /\ delay = '0.
  Proof.
    introv send.
    unfold M_output_sys_on_event in *; simpl in *.
    allrw @M_output_ls_on_event_as_run; exrepnd; simpl in *.
    apply in_M_output_ls_on_this_one_event_implies in send0; exrepnd; simpl in *.
    applydup M_run_ls_before_event_ls_is_paxos in send1; exrepnd; subst; simpl in *; ginv; simpl in *.
    paxos_dest_msg Case;
      try (complete (unfold lower_out_break, PaxosLocalSys, send_my_vote in *;
                     simpl in *; repndors; smash_paxos2; inversion send0; tcsp)).
  Qed.

  Lemma sent_vote :
    forall {eo : EventOrdering} (e : Event) L e' v,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes L
      -> e' ⊑ e
      -> In e L
      -> trigger_op e' = Some (paxos_vote v)
      -> exists e'',
          e'' ≺ e'
          /\ In (send_vote v (other_nodes (loc e''))) (M_output_sys_on_event PaxosSys e'')
          /\ vote_N v = loc e''.
  Proof.
    introv sendbyz cor lee i trig.
    pose proof (sendbyz e' (MkAuthData (paxos_vote v) [tt]) (MkOpTrust _ None I)) as senda.
    simpl in senda.
    repeat (autodimp senda hyp); try (complete (allrw; simpl; tcsp));[].
    exrepnd; repndors; exrepnd; ginv.

    { repndors; tcsp; ginv; simpl in *.
      autodimp senda5 hyp; ginv.
      inversion senda4 as [eqloca]; clear senda4.
      applydup send_vote_implies in senda5; repnd; subst; eauto. }

    { assert (e'' ≼ e') as lte' by eauto 3 with eo.
      pose proof (cor (loc e'') e'' e) as cor; simpl in cor.
      pose proof (nodes_prop (loc e'')) as prp; tcsp.
      repeat (autodimp cor hyp); tcsp; eauto 3 with eo.
      apply correct_is_not_byzantine in senda6; tcsp; eauto 3 with eo. }
  Qed.

  Lemma wf_state_before :
    forall {eo : EventOrdering} (e : Event) n s,
      M_run_ls_before_event (PaxosSys n) e = Some (PaxosLocalSys n s)
      -> wf_state s.
  Proof.
    intros eo e; induction e as [e ind] using predHappenedBeforeInd_type; introv eqst.
    rewrite M_run_ls_before_event_unroll in eqst.
    destruct (dec_isFirst e) as [d|d]; smash_paxos2.
    apply map_option_Some in eqst; exrepnd; rev_Some.
    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo.
    unfold PaxosSys in *; simpl in *.
    applydup M_run_ls_before_event_ls_is_paxos in eqst1; exrepnd; subst.
    apply ind in eqst1; clear ind.
    apply map_option_Some in eqst0; exrepnd; smash_paxos2.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input, on_comp in eqst2; simpl in *.
    paxos_dest_msg Case.
  Qed.

  Lemma decisions_from_quorums_of_votes :
    forall (eo : EventOrdering) (e : Event) r v n l,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> In (send_decision (mk_decision n r v) l) (M_output_sys_on_event PaxosSys e)
      -> by_quorum (fun m =>
                      exists e',
                        e' ≼ e
                        /\ loc e' = m
                        /\ In (send_vote (mk_vote m r v) (other_nodes m)) (M_output_sys_on_event PaxosSys e')).
  Proof.
    introv sendbyz cor outa.
    unfold M_output_sys_on_event in outa; simpl in *.
    allrw @M_output_ls_on_event_as_run; exrepnd; simpl in *.

    pose proof (M_run_ls_on_event_unroll2 (PaxosSys (loc e)) e) as runOn; simpl in *.
    rewrite outa1 in runOn; simpl in *.
    apply in_M_output_ls_on_this_one_event_implies in outa0.
    exrepnd; simpl in *.

    unfold M_run_ls_on_this_one_event in runOn.
    rewrite outa2 in *; simpl in *.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input, on_comp in *.
    rewrite outa3 in *; simpl in *.

    applydup M_run_ls_before_event_ls_is_paxos in outa1.
    exrepnd; subst; simpl in *; ginv; simpl in *.

    paxos_dest_msg Case;
      try (repndors; unfold lower_out_break, PaxosLocalSys, send_my_vote in *;
           simpl in *; repndors; smash_paxos2; try (complete (inversion outa0; tcsp))).

    { Case "Vote".
      applydup wf_state_before in outa1 as wf.
      eexists; dands; eauto;[].
      introv i; apply in_entry2vote_nodes in i; exrepnd; subst.

      assert (vote_R v = vote_R v0) as eqr.
      { applydup log_vote_preserves_wf_state in Heqx0; auto.
        unfold log_my_vote in *; smash_paxos2.
        { eapply wf_state_log_vote_in_entry_votes_implies in Heqx1; eauto. }
        { eapply wf_state_log_vote_in_entry_votes_implies in Heqx0; eauto. } }

      rewrite <- i0, <- eqr; autorewrite with paxos.

      assert (logged_vote v x3) as logv.
      { apply log_my_vote_implies_find_entry in Heqx1; repndors; repnd; subst; smash_paxos2.
        eexists; eexists; dands; eauto. }
      eapply received_votes in logv;[|exact runOn]; exrepnd.
      repndors; repnd.

      { eapply (sent_vote e [e]) in logv0; simpl; tcsp.
        exrepnd.
        exists e''; dands; eauto 4 with eo; auto; try congruence. }

      applydup localLe_implies_loc in logv1.
      exists e'; dands; eauto 3 with eo; try congruence.
      unfold M_output_sys_on_event; auto; try congruence. }
  Qed.

  Lemma received_votes_before :
    forall {eo : EventOrdering} (e : Event) n s v,
      M_run_ls_before_event (PaxosLocalSys n initial_state) e = Some (PaxosLocalSys n s)
      -> logged_vote v s
      -> exists (e' : Event),
          e' ⊏ e
          /\ ((trigger_op e' = Some (paxos_vote v)(* /\ vote_N v <> n*))
              \/ (In (send_vote v (other_nodes n)) (M_output_ls_on_event (PaxosSys n) e') /\ vote_N v = n)).
  Proof.
    introv run log.
    rewrite M_run_ls_before_event_unroll_on in run.
    destruct (dec_isFirst e) as [d|d]; repeat smash_paxos2.
    eapply received_votes in run; eauto.
    exrepnd.
    exists e'; dands; eauto 3 with eo.
  Qed.

  Lemma logged_votes_were_sent :
    forall {eo : EventOrdering} (e : Event) s v,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> M_run_ls_before_event (PaxosLocalSys (loc e) initial_state) e = Some (PaxosLocalSys (loc e) s)
      -> logged_vote v s
      -> exists (e' : Event),
          e' ≺ e
          /\ In (send_vote v (other_nodes (loc e'))) (M_output_ls_on_event (PaxosSys (loc e')) e')
          /\ vote_N v = loc e'.
  Proof.
    introv send cor run log.
    eapply received_votes_before in log; eauto.
    exrepnd; repndors; repnd.

    { pose proof (sent_vote e [e] e' v) as q; simpl in q.
      repeat (autodimp q hyp); eauto 3 with eo; exrepnd.
      exists e''; dands; eauto 3 with eo. }

    { applydup local_implies_loc in log1.
      exists e'; dands; eauto 3 with eo; try congruence. }
  Qed.

  Lemma vote_after_proposal :
    forall (eo : EventOrdering) (e : Event) n r v l,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> In (send_vote (mk_vote n r v) l) (M_output_sys_on_event PaxosSys e)
      -> exists e',
          e' ≼ e
          /\ is_proposer (loc e') r = true
          /\ In (send_vote (mk_vote (loc e') r v) (other_nodes (loc e'))) (M_output_sys_on_event PaxosSys e').
  Proof.
    intros eo e; induction e as [e ind] using HappenedBeforeInd_type.
    introv sendbyz cor outa.
    unfold M_output_sys_on_event in outa; simpl in *.
    allrw @M_output_ls_on_event_as_run; exrepnd; simpl in *.

    pose proof (M_run_ls_on_event_unroll2 (PaxosSys (loc e)) e) as runOn; simpl in *.
    rewrite outa1 in runOn; simpl in *.
    apply in_M_output_ls_on_this_one_event_implies in outa0.
    exrepnd; simpl in *.

    unfold M_run_ls_on_this_one_event in runOn.
    rewrite outa2 in *; simpl in *.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input, on_comp in *.
    rewrite outa3 in *; simpl in *.

    applydup M_run_ls_before_event_ls_is_paxos in outa1.
    exrepnd; subst; simpl in *; ginv; simpl in *.

    paxos_dest_msg Case.

    { Case "OneB".
      exists e; dands; eauto 3 with eo.

      unfold M_output_sys_on_event; simpl in *.
      allrw @M_output_ls_on_event_as_run; allrw; eexists; dands; eauto.
      unfold M_output_ls_on_this_one_event; allrw; simpl.
      unfold M_run_ls_on_input_out, M_run_ls_on_input, on_comp; simpl.
      repeat smash_paxos2. }

    { Case "Vote".
      unfold lower_out_break in outa0; simpl in *.
      unfold send_my_vote in outa0; smash_paxos2.

      pose proof (sent_vote e [e] e v0) as q; simpl in q.
      repeat (autodimp q hyp); eauto 3 with eo.
      exrepnd.
      exists e''.
      dands; eauto 3 with eo.
      { unfold valid_my_vote, is_vote_from_proposer in *; smash_paxos2. }
      { rewrite <- q0; autorewrite with paxos; rewrite q0; tcsp. } }

    { Case "Vote".
      repndors; smash_paxos2.
      unfold send_my_vote in outa0; smash_paxos2.

      pose proof (sent_vote e [e] e v0) as q; simpl in q.
      repeat (autodimp q hyp); eauto 3 with eo.
      exrepnd.
      exists e''.
      dands; eauto 3 with eo.
      { unfold valid_my_vote, is_vote_from_proposer in *; smash_paxos2. }
      { rewrite <- q0; autorewrite with paxos; rewrite q0; tcsp. } }
  Qed.

  Lemma received_one_bs :
    forall {eo : EventOrdering} (e : Event) n s b,
      M_run_ls_on_event (PaxosLocalSys n initial_state) e = Some (PaxosLocalSys n s)
      -> logged_one_b b s
      -> exists (e' : Event),
          e' ⊑ e
          /\ ((trigger_op e' = Some (paxos_one_b b)(* /\ vote_N v <> n*))
              \/ (In (send_one_b b (other_nodes n)) (M_output_ls_on_event (PaxosSys n) e') /\ one_b_N b = n)).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd_type.
    introv run i.
    rewrite M_run_ls_on_event_unroll2 in run.
    apply map_option_Some in run; exrepnd; rev_Some.
    apply map_option_Some in run0; exrepnd; ginv.
    applydup M_run_ls_before_event_ls_is_paxos in run1; exrepnd; subst; smash_paxos2.

    unfold M_run_ls_on_input_ls, M_run_ls_on_input, on_comp in run2; simpl in *.
    paxos_dest_msg Case;
      rewrite M_run_ls_before_event_unroll_on in run1;
      destruct (dec_isFirst e); repeat smash_paxos2;
        repeat (rewrite update_last_round_initial_state in *; auto; smash_paxos2;first[ idtac;[] | fail]);
        try (eapply logged_one_b_log_my_vote in i; eauto;[]; repndors; subst; smash_paxos2; try omega);
        try (eapply logged_one_b_log_vote in i; eauto;[]; repndors; subst; smash_paxos2; try omega);
        try (eapply logged_one_b_log_one_b in i; eauto;[]; repndors; subst; smash_paxos2; try omega);
        try (complete (eapply ind in run1; eauto; eauto 3 with eo; exrepnd; exists e'; dands; eauto 3 with eo));
        try (complete (exists e; dands; eauto 3 with eo;
                       right; unfold M_output_ls_on_event; simpl; rewrite M_run_ls_before_event_unroll_on;
                       destruct (dec_isFirst e); tcsp; simpl;
                       unfold PaxosSys, M_output_ls_on_this_one_event, M_run_ls_on_input_out, M_run_ls_on_input, on_comp;
                       repeat (allrw; simpl; try (unfold send_my_vote); smash_paxos2; tcsp))).
  Qed.

  Lemma sent_one_b :
    forall {eo : EventOrdering} (e : Event) L e' b,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes L
      -> e' ⊑ e
      -> In e L
      -> trigger_op e' = Some (paxos_one_b b)
      -> exists e'',
          e'' ≺ e'
          /\ In (send_one_b b (other_nodes (loc e''))) (M_output_sys_on_event PaxosSys e'')
          /\ one_b_N b = loc e''.
  Proof.
    introv sendbyz cor lee i trig.
    pose proof (sendbyz e' (MkAuthData (paxos_one_b b) [tt]) (MkOpTrust _ None I)) as senda.
    simpl in senda.
    repeat (autodimp senda hyp); try (complete (allrw; simpl; tcsp));[].
    exrepnd; repndors; exrepnd; ginv.

    { repndors; tcsp; ginv; simpl in *.
      autodimp senda5 hyp; ginv.
      inversion senda4 as [eqloca]; clear senda4.
      applydup send_one_b_implies in senda5; repnd; subst; eauto. }

    { assert (e'' ≼ e') as lte' by eauto 3 with eo.
      pose proof (cor (loc e'') e'' e) as cor; simpl in cor.
      pose proof (nodes_prop (loc e'')) as prp; tcsp.
      repeat (autodimp cor hyp); tcsp; eauto 3 with eo.
      apply correct_is_not_byzantine in senda6; tcsp; eauto 3 with eo. }
  Qed.

  Lemma logged_one_bs_were_sent_on :
    forall {eo : EventOrdering} (e : Event) s b,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> M_run_ls_on_event (PaxosLocalSys (loc e) initial_state) e = Some (PaxosLocalSys (loc e) s)
      -> logged_one_b b s
      -> exists (e' : Event),
          e' ≼ e
          /\ In (send_one_b b (other_nodes (loc e'))) (M_output_ls_on_event (PaxosSys (loc e')) e')
          /\ one_b_N b = loc e'.
  Proof.
    introv send cor run log.
    eapply received_one_bs in log; eauto.
    exrepnd; repndors; repnd.

    { pose proof (sent_one_b e [e] e' b) as q; simpl in q.
      repeat (autodimp q hyp); eauto 3 with eo; exrepnd.
      exists e''; dands; eauto 4 with eo. }

    { applydup localLe_implies_loc in log1.
      exists e'; dands; eauto 3 with eo; try congruence. }
  Qed.

  Lemma send_vote_implies_current_round :
    forall {eo : EventOrdering} (e : Event) v l,
      send_vote v l ∈ PaxosSys ⇝ e
      -> exists s1 s2,
        M_run_ls_before_event (PaxosLocalSys (loc e) initial_state) e = Some (PaxosLocalSys (loc e) s1)
        /\ M_run_ls_on_event (PaxosLocalSys (loc e) initial_state) e = Some (PaxosLocalSys (loc e) s2)
        /\ (is_one_b e \/ is_vote e)
        /\ st_current_round s1 <= vote_R v
        /\ logged_similar_vote v s2.
  Proof.
    introv send.
    unfold M_output_sys_on_event in send; simpl in *.
    allrw @M_output_ls_on_event_as_run; exrepnd; simpl in *.
    apply in_M_output_ls_on_this_one_event_implies in send0; exrepnd; simpl in *.
    applydup M_run_ls_before_event_ls_is_paxos in send1.
    exrepnd; subst; simpl in *; ginv; simpl in *.
    applydup wf_state_before in send1 as wf.
    unfold PaxosSys in *; allrw.
    rewrite M_run_ls_on_event_unroll2; allrw; simpl.
    unfold M_run_ls_on_this_one_event, M_run_ls_on_input_ls, M_run_ls_on_input, on_comp; simpl; allrw; simpl.
    clear send1.

    paxos_dest_msg Case; eexists; eexists; dands; try reflexivity; smash_paxos2;
      try (complete (unfold is_one_b, is_vote; allrw; eauto));
      try (complete (applydup log_vote_implies_logged in Heqx5; repndors; smash_paxos2));
      try (complete (repndors; smash_paxos2;
                     unfold lower_out_break, send_my_vote in *; simpl in *; smash_paxos2;
                     unfold has_left_round, log_my_vote in *; smash_paxos2;
                     applydup log_vote_implies_logged in Heqx1; repndors; smash_paxos2)).
  Qed.

  Lemma logged_votes_were_sent_on :
    forall {eo : EventOrdering} (e : Event) s v,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> M_run_ls_on_event (PaxosLocalSys (loc e) initial_state) e = Some (PaxosLocalSys (loc e) s)
      -> logged_vote v s
      -> exists (e' : Event),
          e' ≼ e
          /\ In (send_vote v (other_nodes (loc e'))) (M_output_ls_on_event (PaxosSys (loc e')) e')
          /\ vote_N v = loc e'.
  Proof.
    introv send cor run log.
    eapply received_votes in log; eauto.
    exrepnd; repndors; repnd.

    { pose proof (sent_vote e [e] e' v) as q; simpl in q.
      repeat (autodimp q hyp); eauto 3 with eo; exrepnd.
      exists e''; dands; eauto 4 with eo. }

    { applydup localLe_implies_loc in log1.
      exists e'; dands; eauto 3 with eo; try congruence. }
  Qed.

  Lemma unique_votes2 :
    forall (eo : EventOrdering) (e1 e2 : Event) v1 v2 l1 l2,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e1,e2]
      -> In (send_vote v1 l1) (M_output_sys_on_event PaxosSys e1)
      -> In (send_vote v2 l2) (M_output_sys_on_event PaxosSys e2)
      -> vote_R v1 = vote_R v2
      -> vote_V v1 = vote_V v2.
  Proof.
    introv send cor outa outb eqr.
    destruct v1 as [n1 r1 v1].
    destruct v2 as [n2 r2 v2].
    simpl in *; subst.
    apply vote_after_proposal in outa; eauto 3 with eo.
    apply vote_after_proposal in outb; eauto 3 with eo.
    exrepnd.

    assert (loc e'0 = loc e') as eqloc.
    { eapply is_proposer_inj in outa2; try exact outb2; auto. }
    rewrite eqloc in *.
    eapply unique_votes in outa0; try exact outb0; auto.
  Qed.

  Lemma send_vote_implies_current_round2 :
    forall {eo : EventOrdering} (e : Event) v l,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> send_vote v l ∈ PaxosSys ⇝ e
      -> exists s1 s2,
        M_run_ls_before_event (PaxosLocalSys (loc e) initial_state) e = Some (PaxosLocalSys (loc e) s1)
        /\ M_run_ls_on_event (PaxosLocalSys (loc e) initial_state) e = Some (PaxosLocalSys (loc e) s2)
        /\ (is_one_b e \/ is_vote e)
        /\ st_current_round s1 <= vote_R v
        /\ logged_vote v s2.
  Proof.
    introv ax cor send.
    applydup send_vote_implies_current_round in send; exrepnd.
    exists s1 s2; dands; auto.
    unfold logged_similar_vote in *; exrepnd.
    dup send0 as log.
    eapply logged_votes_were_sent_on in log; eauto; exrepnd.
    eapply unique_votes2 in send; try exact log2; smash_paxos2; eauto 3 with eo;[].
    assert (v' = v) by (destruct v, v'; simpl in *; subst; tcsp); subst; auto.
  Qed.

  Lemma send_one_b_implies_current_round :
    forall {eo : EventOrdering} (e : Event) b l,
      send_one_b b l ∈ PaxosSys ⇝ e
      -> exists s1 s2,
        M_run_ls_before_event (PaxosLocalSys (loc e) initial_state) e = Some (PaxosLocalSys (loc e) s1)
        /\ M_run_ls_on_event (PaxosLocalSys (loc e) initial_state) e = Some (PaxosLocalSys (loc e) s2)
        /\ is_one_a e
        /\ st_current_round s1 < st_current_round s2
        /\ st_current_round s2 = one_b_R b
        /\ (one_b_maxr b,one_b_maxv b) = find_latest_value_from_votes (loc e) (default_value (loc e)) 0 (st_current_round s2) (st_entries s1).
  Proof.
    introv send.
    unfold M_output_sys_on_event in send; simpl in *.
    allrw @M_output_ls_on_event_as_run; exrepnd; simpl in *.
    apply in_M_output_ls_on_this_one_event_implies in send0; exrepnd; simpl in *.
    applydup M_run_ls_before_event_ls_is_paxos in send1.
    exrepnd; subst; simpl in *; ginv; simpl in *.
    unfold PaxosSys in *; allrw.
    rewrite M_run_ls_on_event_unroll2; allrw; simpl.
    unfold M_run_ls_on_this_one_event, M_run_ls_on_input_ls, M_run_ls_on_input, on_comp; simpl; allrw; simpl.
    clear send1.

    paxos_dest_msg Case;
      repndors; smash_paxos2;
        try (complete (unfold lower_out_break, send_my_vote in *; simpl in *; repeat smash_paxos2; inversion send0));
        eexists; eexists; dands; try reflexivity; try (complete (unfold is_one_a; allrw; eauto));
          try (complete (unfold new_round in *; smash_paxos2;
                         apply implies_eq_snd in Heqx1; simpl in *; subst;
                         unfold log_one_b; smash_paxos2; try omega)).
  Qed.

  Lemma proposal_from_one_bs :
    forall (eo : EventOrdering) (e : Event) v l,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> In (send_vote v l) (M_output_sys_on_event PaxosSys e)
      -> vote_N v = loc e
      -> is_proposer (loc e) (vote_R v) = true
      -> exists bs,
          forms_quorum (map one_b_N bs) = true
          /\ vote_V v = snd (find_voted_value_from_one_bs (default_value (loc e)) 0 (vote_R v) bs)
          /\ forall b,
            In b bs
            -> exists e',
              e' ≺ e
              /\ one_b_R b = vote_R v
              /\ one_b_N b = loc e'
              /\ In (send_one_b b (other_nodes (loc e'))) (M_output_sys_on_event PaxosSys e').
  Proof.
    intros eo e; induction e as [e ind] using HappenedBeforeInd_type.
    introv sendbyz cor outa eqv isp.
    unfold M_output_sys_on_event in outa; simpl in *.
    allrw @M_output_ls_on_event_as_run; exrepnd; simpl in *.

    pose proof (M_run_ls_on_event_unroll2 (PaxosSys (loc e)) e) as runOn; simpl in *.
    rewrite outa1 in runOn; simpl in *.
    apply in_M_output_ls_on_this_one_event_implies in outa0.
    exrepnd; simpl in *.

    unfold M_run_ls_on_this_one_event in runOn.
    rewrite outa2 in *; simpl in *.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input, on_comp in *.
    rewrite outa3 in *; simpl in *.

    applydup M_run_ls_before_event_ls_is_paxos in outa1.
    exrepnd; subst; simpl in *; ginv; simpl in *.

    paxos_dest_msg Case.

    { Case "OneB".
      exists (entry_one_bs x0); dands; tcsp; try (complete (allrw; simpl; auto)).
      introv i.

      assert (logged_one_b b0 x5) as log.
      { eapply log_vote_preserves_logged_one_b; eauto.
        eexists; eexists; dands; eauto; smash_paxos2. }

      eapply logged_one_bs_were_sent_on in log; eauto; tcsp.
      exrepnd.

      assert (e' ≺ e) as lte.
      { destruct log1 as [w|w]; tcsp; subst;[].
        apply send_one_b_implies_current_round in log2 as z; exrepnd.
        unfold is_one_a in *; exrepnd.
        rewrite z6 in *; ginv. }

      exists e'; dands; auto; try congruence.
      unfold same_round in *; smash_paxos2.
      applydup log_one_b_implies_equal_entry_round in Heqx1.
      assert (In x0 (st_entries x1)) as j.
      { apply log_one_b_implies_find_entry in Heqx1; apply find_entry_implies_in in Heqx1; auto. }
      assert (wf_state s') as wfs by (eapply wf_state_before; eauto).
      eapply log_one_b_preserves_wf_state in wfs; eauto.
      apply wfs in j; repnd.
      apply j0 in i; try congruence. }

    { Case "Vote".
      unfold lower_out_break in outa0; simpl in *.
      unfold send_my_vote in outa0; smash_paxos2.
      rename_hyp_with valid_my_vote valid.
      apply valid_my_vote_implies_not_proposer in valid; smash_paxos2. }

    { Case "Vote".
      repndors; smash_paxos2.
      unfold lower_out_break in outa0; simpl in *.
      unfold send_my_vote in outa0; smash_paxos2.
      rename_hyp_with valid_my_vote valid.
      apply valid_my_vote_implies_not_proposer in valid; smash_paxos2. }
  Qed.

  Lemma round_increases_step :
    forall {eo : EventOrdering} (e : Event) n s1 s2,
      M_run_ls_on_this_one_event (PaxosLocalSys n s1) e = Some (PaxosLocalSys n s2)
      -> st_current_round s1 <= st_current_round s2.
  Proof.
    introv run.
    apply option_map_Some in run; exrepnd.
    unfold M_run_ls_on_this_one_event, M_run_ls_on_input_ls, M_run_ls_on_input, on_comp in *; simpl in *.
    paxos_dest_msg Case; try omega;
      try (rename_hyp_with log_one_b logb; apply implies_eq_snd in logb; simpl in *; subst; unfold log_one_b in *; smash_paxos2; try omega);
      try (rename_hyp_with log_my_vote logm; apply implies_eq_snd in logm; simpl in *; subst; unfold log_my_vote in *; smash_paxos2; try omega);
      try (rename_hyp_with log_vote logv; apply implies_eq_snd in logv; simpl in *; subst; unfold log_vote in *; smash_paxos2; try omega).
  Qed.

  Lemma round_increases_on :
    forall {eo : EventOrdering} (e1 e2 : Event) s1 s2,
      e1 ⊑ e2
      -> M_run_ls_on_event (PaxosLocalSys (loc e1) initial_state) e1 = Some (PaxosLocalSys (loc e1) s1)
      -> M_run_ls_on_event (PaxosLocalSys (loc e2) initial_state) e2 = Some (PaxosLocalSys (loc e2) s2)
      -> st_current_round s1 <= st_current_round s2.
  Proof.
    intros eo e1 e2; induction e2 as [e2 ind] using predHappenedBeforeInd_type; introv lee runa runb.
    apply decomp_local_le in lee; repndors; repnd; subst.

    { rewrite runa in runb; smash_paxos2. }

    pose proof (ind (local_pred e2)) as ind; autodimp ind hyp.
    pose proof (ind s1) as ind.
    rewrite M_run_ls_on_event_unroll in runb.
    destruct (dec_isFirst e2) as [d|d]; smash_paxos2.
    apply map_option_Some in runb; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_paxos in runb1; exrepnd; subst.
    rewrite <- M_run_ls_before_event_as_M_run_ls_on_event_pred in ind; eauto 3 with eo.
    rewrite runb1 in ind.
    pose proof (ind s') as ind.
    repeat (autodimp ind hyp).
    eapply le_trans;eauto.
    apply round_increases_step in runb0; auto.
  Qed.

  Lemma round_increases_on_before :
    forall {eo : EventOrdering} (e1 e2 : Event) s1 s2,
      e1 ⊏ e2
      -> M_run_ls_on_event (PaxosLocalSys (loc e1) initial_state) e1 = Some (PaxosLocalSys (loc e1) s1)
      -> M_run_ls_before_event (PaxosLocalSys (loc e2) initial_state) e2 = Some (PaxosLocalSys (loc e2) s2)
      -> st_current_round s1 <= st_current_round s2.
  Proof.
    introv lte runa runb.
    apply local_implies_pred_or_local in lte; repndors; exrepnd.

    { rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred in runb; eauto 3 with eo.
      apply pred_implies_local_pred in lte; subst; autorewrite with eo in *.
      rewrite runa in runb; smash_paxos2. }

    rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred in runb; eauto 3 with eo.
    assert (loc e2 = loc (local_pred e2)) as eqloc by (autorewrite with eo; auto).
    rewrite eqloc in runb.
    eapply round_increases_on in runb; try exact runa; auto 2 with eo.
    apply pred_implies_local_pred in lte1; subst; eauto 2 with eo.
  Qed.

  Lemma preserves_logged_vote_step :
    forall {eo : EventOrdering} (e : Event) n s1 s2 v,
      M_run_ls_on_this_one_event (PaxosLocalSys n s1) e = Some (PaxosLocalSys n s2)
      -> logged_vote v s1
      -> logged_vote v s2.
  Proof.
    introv run log.
    apply option_map_Some in run; exrepnd.
    unfold M_run_ls_on_this_one_event, M_run_ls_on_input_ls, M_run_ls_on_input, on_comp in *; simpl in *.
    paxos_dest_msg Case.
  Qed.

  Lemma preserves_logged_vote_on_before :
    forall {eo : EventOrdering} (e1 e2 : Event) s1 s2 v,
      e1 ⊏ e2
      -> M_run_ls_on_event (PaxosLocalSys (loc e1) initial_state) e1 = Some (PaxosLocalSys (loc e1) s1)
      -> M_run_ls_before_event (PaxosLocalSys (loc e2) initial_state) e2 = Some (PaxosLocalSys (loc e2) s2)
      -> logged_vote v s1
      -> logged_vote v s2.
  Proof.
    intros eo e1 e2; induction e2 as [e2 ind] using predHappenedBeforeInd_type; introv lte runa runb log.
    apply local_implies_pred_or_local in lte; exrepnd; repndors; exrepnd.

    { rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred in runb; eauto 3 with eo.
      apply pred_implies_local_pred in lte; subst; autorewrite with eo in *.
      rewrite runa in runb; smash_paxos2. }

    pose proof (ind e) as ind; autodimp ind hyp.
    rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred in runb; eauto 3 with eo.
    assert (loc e2 = loc (local_pred e2)) as eqloc by (autorewrite with eo; auto).
    rewrite eqloc in runb.
    apply pred_implies_local_pred in lte1; subst.

    rewrite M_run_ls_on_event_unroll2 in runb; apply map_option_Some in runb; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_paxos in runb1; exrepnd; subst.
    pose proof (ind s1 s' v) as ind; repeat (autodimp ind hyp).
    eapply preserves_logged_vote_step; eauto.
  Qed.

  Lemma sent_one_b_pos :
    forall {eo : EventOrdering} (e : Event) n r maxr maxv l,
      In (send_one_b (mk_one_b n r maxr maxv) l) (M_output_sys_on_event PaxosSys e)
      -> 0 < r.
  Proof.
    introv send.
    apply send_one_b_implies_current_round in send; exrepnd; simpl in *; omega.
  Qed.

  Lemma sent_vote_pos :
    forall {eo : EventOrdering} (e : Event) n r v l,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> In (send_vote (mk_vote n r v) l) (M_output_sys_on_event PaxosSys e)
      -> 0 < r.
  Proof.
    introv ax cor send.
    apply vote_after_proposal in send; auto; exrepnd.
    apply proposal_from_one_bs in send0; auto; eauto 3 with eo; exrepnd; simpl in *.
    pose proof (forms_quorum_pos (map one_b_N bs)) as h; autodimp h hyp.
    destruct bs; simpl in *; tcsp.
    pose proof (send3 o) as send3; autodimp send3 hyp; exrepnd; tcsp; subst.
    destruct o; simpl in *.
    apply sent_one_b_pos in send5; auto.
  Qed.

  Lemma sent_decision_pos :
    forall {eo : EventOrdering} (e : Event) n r v l,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> In (send_decision (mk_decision n r v) l) (M_output_sys_on_event PaxosSys e)
      -> 0 < r.
  Proof.
    introv ax cor send.
    apply decisions_from_quorums_of_votes in send; auto.
    unfold by_quorum in send; exrepnd.
    pose proof (forms_quorum_pos q) as h; autodimp h hyp.
    destruct q; simpl in *; tcsp.
    pose proof (send0 n0) as send0; autodimp send0 hyp; exrepnd; tcsp.
    apply sent_vote_pos in send2; eauto 3 with eo.
  Qed.

  Lemma send_one_b_implies_send_vote :
    forall {eo : EventOrdering} (e : Event) b l,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e]
      -> 0 < one_b_maxr b
      -> send_one_b b l ∈ PaxosSys ⇝ e
      -> exists e',
        e' ≺ e
        /\ send_vote (mk_vote (loc e') (one_b_maxr b) (one_b_maxv b)) (other_nodes (loc e')) ∈ PaxosSys ⇝ e'.
  Proof.
    introv ax cor ltr send.
    apply send_one_b_implies_current_round in send; exrepnd.
    symmetry in send1.
    applydup wf_state_before in send0 as wf.
    apply find_latest_value_from_votes_implies in send1; tcsp;[].
    repndors; exrepnd; try omega.

    assert (logged_vote (mk_vote (loc e) (one_b_maxr b) (one_b_maxv b)) s1) as log.
    { exists (one_b_maxr b) e0; dands; tcsp. }
    eapply logged_votes_were_sent in log; eauto;[].
    exrepnd; simpl in *.
    rewrite log0 in log2.
    exists e'; dands; tcsp.
  Qed.

  Lemma vote_after_decision :
    forall (eo : EventOrdering) (e1 e2 : Event) n1 n2 r1 r2 v1 v2 l1 l2,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e1, e2]
      -> In (send_decision (mk_decision n1 r1 v1) l1) (M_output_sys_on_event PaxosSys e1)
      -> In (send_vote (mk_vote n2 r2 v2) l2) (M_output_sys_on_event PaxosSys e2)
      -> r1 <= r2
      -> v1 = v2.
  Proof.
    intros eo e1 e2; induction e2 as [e2 ind] using HappenedBeforeInd_type.
    introv sendbyz cor outa outb ltr.

    applydup sent_decision_pos in outa as posa; eauto 3 with eo;[].
    dup outa as senddec.
    apply decisions_from_quorums_of_votes in outa; eauto 2 with eo;[].

    apply le_lt_or_eq in ltr; repndors;
      [|subst; unfold by_quorum in outa; exrepnd;
        pose proof (forms_quorum_pos q) as h; autodimp h hyp;
        destruct q; simpl in *; tcsp;
        pose proof (outa0 n) as outa0; autodimp outa0 hyp; exrepnd;
        eapply unique_votes2 in outb; try exact outa2; simpl in *; tcsp; eauto 3 with eo];[].

    apply vote_after_proposal in outb; eauto 3 with eo;[]; exrepnd.
    apply proposal_from_one_bs in outb0; eauto 3 with eo;[]; exrepnd.
    simpl in *.
    unfold by_quorum in outa; exrepnd.

    pose proof (quorum_intersection q (map one_b_N bs)) as quor.
    repeat (autodimp quor hyp); exrepnd.
    apply in_map_iff in quor0; exrepnd; subst.
    apply outa0 in quor1 as quora.
    apply outb3 in quor2 as quorb.
    hide_hyp outa0; hide_hyp outb3.
    exrepnd.
    destruct x as [n r maxr maxv]; simpl in *; subst.

    applydup send_vote_implies_current_round2 in quora0 as runa; exrepnd; simpl in *; eauto 3 with eo;[].
    applydup send_one_b_implies_current_round in quorb0 as runb; exrepnd; simpl in *;[].

    pose proof (tri_if_same_loc e'1 e'0) as tri; autodimp tri hyp.
    destruct tri as [tri|[tri|tri] ];
      [|subst; unfold is_one_a, is_one_b, is_vote in *; exrepnd;
        rewrite runb5 in *; repndors; exrepnd; ginv
       |eapply round_increases_on_before in runb2; try exact runa0; auto; try omega];[].

    assert (logged_vote (mk_vote (loc e'1) r1 v1) s0) as log.
    { eapply preserves_logged_vote_on_before; eauto. }

    symmetry in runb1.
    dup runb1 as fv.

    applydup wf_state_before in runb0 as wf.
    apply find_latest_value_from_votes_implies in fv; tcsp;[].
    destruct fv as [fv|fv]; repnd.
    { unfold logged_vote in log; exrepnd.
      apply find_entry_implies_in in log0.
      apply fv in log1; simpl in *; tcsp.
      apply wf in log0; repnd.
      apply log0 in log1; simpl in *; subst; split; tcsp. }

    exrepnd.
    assert (r1 <= maxr) as ler.
    { unfold logged_vote in log; exrepnd.
      rewrite <- quorb3 in fv0.
      eapply fv0 in log1; auto; try omega.
      applydup find_entry_implies_eq_entry_round in log0; subst.
      applydup find_entry_implies_in in log0.
      apply wf in log2; simpl in *; subst; auto; repnd.
      apply log2 in log1; simpl in *; subst; auto. }

    dup quor2 as fbs.
    apply (find_voted_value_from_one_bs_prop2 _ _ _ _ _ (default_value (loc e')) 0 r2) in fbs; exrepnd; try omega;[].
    rewrite fbs2; simpl.

    show_hyp outb3.
    apply outb3 in fbs1; exrepnd.
    destruct b as [n r maxr' maxv']; simpl in *.
    apply send_one_b_implies_send_vote in fbs4; simpl; tcsp; try omega; eauto 4 with eo;[].
    exrepnd; simpl in *.

    pose proof (ind e'3) as ind.
    autodimp ind hyp; eauto 3 with eo;[].
    pose proof (ind n1 (loc e'3) r1 maxr' v1 maxv' l1 (other_nodes (loc e'3))) as ind.
    repeat (autodimp ind hyp); eauto 5 with eo; try omega.
  Qed.

  (* This could be derived from our knowledge theory *)
  Lemma safety_le :
    forall (eo : EventOrdering) (e1 e2 : Event) n1 n2 r1 r2 v1 v2 l1 l2,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e1, e2]
      -> r1 <= r2
      -> In (send_decision (mk_decision n1 r1 v1) l1) (M_output_sys_on_event PaxosSys e1)
      -> In (send_decision (mk_decision n2 r2 v2) l2) (M_output_sys_on_event PaxosSys e2)
      -> v1 = v2.
  Proof.
    introv sendbyz cor ler outa outb.
    apply decisions_from_quorums_of_votes in outb; eauto 2 with eo;[].
    unfold by_quorum in *; exrepnd.
    pose proof (forms_quorum_pos q) as h; autodimp h hyp.
    destruct q; simpl in *; tcsp.
    pose proof (outb0 n) as outb0; autodimp outb0 hyp; exrepnd.
    eapply vote_after_decision in outa; try exact outb2; eauto 3 with eo.
  Qed.

  Lemma safety :
    forall (eo : EventOrdering) (e1 e2 : Event) n1 n2 r1 r2 v1 v2 l1 l2,
      AXIOM_authenticated_messages_were_sent_or_byz eo PaxosSys
      -> have_correct_traces_before nodes [e1, e2]
      -> In (send_decision (mk_decision n1 r1 v1) l1) (M_output_sys_on_event PaxosSys e1)
      -> In (send_decision (mk_decision n2 r2 v2) l2) (M_output_sys_on_event PaxosSys e2)
      -> v1 = v2.
  Proof.
    introv sendbyz cor outa outb.
    destruct (lt_dec r1 r2) as [d|d].
    { eapply safety_le in outb; try exact outa; auto; try omega. }
    { eapply safety_le in outa; try exact outb; auto; try omega; eauto 3 with eo. }
  Qed.

End AbstractPaxos.
