Require Export Process.
(* easier to deal with monads? *)
Require Export FunctionalExtensionality.
Require Export tactics2.
Require Export Ref.

Require Export String.
Require Export Peano.
Require Export List.


Section ComponentSM.

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
  Context { qc  : @Quorum_context pn }.
  Context { iot : @IOTrustedFun }.


  Definition CompNameLevel := nat.
  Definition CompNameState := nat.
  Definition CompNameTrust := bool.

  Definition CompNameKindDeq  : Deq CompNameKind  := String.string_dec.
  Definition CompNameSpaceDeq : Deq CompNameSpace := deq_nat.
  Definition CompNameStateDeq : Deq CompNameSpace := deq_nat.
  Definition CompNameTrustDeq : Deq CompNameTrust := bool_dec.

  (* TODO:use [TrustTag] instead of [bool] *)
  Inductive TrustTag :=
  | tt_TRUSTED
  | tt_UNTRUSTED.

  Record CompName :=
    MkCompName
      {
        comp_name_pre   :> PreCompName;
        comp_name_trust : CompNameTrust (* TrustTag *);
      }.

  Definition MkCN
             (k : CompNameKind)
             (s : CompNameSpace)
             (t : CompNameTrust)
    : CompName :=
    MkCompName (MkPreCompName k s) t.

  Lemma CompNameDeq : Deq CompName.
  Proof.
    introv; unfold deceq; destruct x as [[n1 s1] b1], y as [[n2 s2] b2].
    destruct (CompNameKindDeq n1 n2);
      destruct (CompNameSpaceDeq s1 s2);
      destruct (CompNameTrustDeq b1 b2);
      prove_dec.
  Defined.

  (* component *)
  Record p_nproc (p : CompName -> Type) :=
    MkPProc
      {
        pp_name : CompName;
        pp_proc : p pp_name;
      }.
  Global Arguments MkPProc [p] _ _.
  Global Arguments pp_name [p] _.
  Global Arguments pp_proc [p] _.
  (* list of components *)
  Definition p_procs (p : CompName -> Type) := list (p_nproc p).

  Lemma decomp_p_nproc :
    forall {p : CompName -> Type} {cn : CompName} {p1 p2 : p cn},
      MkPProc cn p1 = MkPProc cn p2 -> p1 = p2.
  Proof.
    introv h.
    inversion h as [xx].
    apply inj_pair2_eq_dec in xx; auto.
    apply CompNameDeq.
  Qed.

  (* monad of the component *)
  Definition M_p (p : CompName -> Type) (PO : Type) :=
    p_procs p -> (p_procs p * PO)%type.

  (* option type with different halting conditions *)
  Inductive hoption (S : Type) :=
  | hsome (s : S)
  | halt_local
  | halt_global.
  Global Arguments hsome [S] _.
  Global Arguments halt_local [S].
  Global Arguments halt_global [S].

  Definition hoption_map {A B} (f : A -> B) (st : hoption A) : hoption B :=
    match st with
    | hsome s => hsome (f s)
    | halt_local => halt_local
    | halt_global => halt_global
    end.

  Definition map_hoption {T U} (f : T -> hoption U) (o : hoption T) : hoption U :=
    match o with
    | hsome s => f s
    | halt_local => halt_local
    | halt_global => halt_global
    end.

  Definition bind_hop {A B} (b : B) (F : A -> B) (i : hoption A) : B :=
    match i with
    | hsome a => F a
    | halt_local => b
    | halt_global => b
    end.

  (* monad update function of the component that can halt *)
  Definition MP_Update (p : CompName -> Type) (I O S : Type) :=
    S -> PosDTime -> I -> M_p p (hoption S * O).

  (* component interface;
     we need cio_I ans cio_O because USIG does not take messages as input and
     it does not return Directed messages as output *)
  Record ComponentIO :=
    MkComponentIO
      {
        cio_I : Type;
        cio_O : Type;
        cio_default_O : cio_O;
      }.

  (* component that works with DirectedMsgs *)
  Definition CIOmsg : ComponentIO :=
    MkComponentIO msg DirectedMsgs [].

  Definition CIOtrusted (cn : PreCompName) : ComponentIO :=
    MkComponentIO
      (iot_input (iot_fun cn))
      (iot_output (iot_fun cn))
      (iot_def_output (iot_fun cn)).

  (* A default CIO *)
  Definition CIOdef : ComponentIO :=
    MkComponentIO unit unit tt.

  (* A [nat] CIO *)
  Definition CIOnat : ComponentIO :=
    MkComponentIO nat nat 0.

  (* A [bool] CIO *)
  Definition CIObool : ComponentIO :=
    MkComponentIO bool bool true.

  (* interface of the single component *)
  Class baseFunIO :=
    MkBaseFunIO
      {
        bfio : CompName -> ComponentIO;
      }.

  Context { base_fun_io : baseFunIO }.

  Class baseStateFun :=
    MkBaseStateFun
      {
        bsf : CompName -> Type;
      }.

  Context { base_state_fun : baseStateFun }.

  Class trustedStateFun :=
    MkTrustedStateFun
      {
        tsf : PreCompName -> Type;
      }.

  Context { trusted_state_fun : trustedStateFun }.

  (* interface of the single component;
     all components with same name have same input/output behavior  *)
  Class funIO :=
    MkFunIO
      {
        fio : CompName -> ComponentIO;
      }.

  Class stateFun :=
    MkStateFun
      {
        sf : CompName -> Type;
      }.

  (* unit state *)

  (* "MSG" components must have a msg interface *)
  Definition msg_comp_name_kind  : CompNameKind  := "MSG".
  Definition msg_comp_name_state : CompNameState := 0.
  Definition msg_comp_name_trust : CompNameTrust := false.
  Definition msg_comp_name space : CompName :=
    MkCN
      msg_comp_name_kind
      space
      msg_comp_name_trust.

  (* "UNIT",0 components must have a unit interface and a [unit] state *)
  Definition unit_comp_name_kind  : CompNameKind  := "UNIT".
  Definition unit_comp_name_space : CompNameSpace := 1.
  Definition unit_comp_name_trust : CompNameTrust := false.
  Definition unit_comp_name_state : CompNameState := 0.
  Definition unit_comp_name : CompName :=
    MkCN
      unit_comp_name_kind
      unit_comp_name_space
      unit_comp_name_trust.

  (* "NAT",0 components must have a unit interface and a [nat] state *)
  Definition nat_comp_name_kind  : CompNameKind  := "NAT".
  Definition nat_comp_name_space : CompNameSpace := 0.
  Definition nat_comp_name_state : CompNameState := 0.
  Definition nat_comp_name_trust : CompNameTrust := false.
  Definition nat_comp_name : CompName :=
    MkCN
      nat_comp_name_kind
      nat_comp_name_space
      nat_comp_name_trust.

  (* "BOOL",0 components must have a unit interface and a [bool] state *)
  Definition bool_comp_name_kind  : CompNameKind := "BOOL".
  Definition bool_comp_name_space : CompNameSpace := 0.
  Definition bool_comp_name_state : CompNameState := 0.
  Definition bool_comp_name_trust : CompNameTrust := false.
  Definition bool_comp_name : CompName :=
    MkCN
      bool_comp_name_kind
      bool_comp_name_space
      bool_comp_name_trust.

  (* "MSG",1 components must have a msg interface and a unit state *)
  Definition munit_comp_name : CompName := msg_comp_name 1.

  Definition key_comp_name_kind  : CompNameKind := "KEY".

  (* We override here some IO interfaces:
       - "MSG"   components must have the [CIOmsg] IO interface
       - "UNIT"  components must have the [CIOdef] IO interface
       - "NAT"   components must have the [CIOnat] IO interface
       - "BOOL"  components must have the [CIObool] IO interface
       - trusted components must have the [CIOtrusted] IO interface
   *)
  Definition funIOd_msg_nm (nm : CompName) :=
    if comp_name_trust nm then CIOtrusted nm
    else if CompNameKindDeq (comp_name_kind nm) msg_comp_name_kind then CIOmsg
         else if CompNameKindDeq (comp_name_kind nm) unit_comp_name_kind then CIOdef
              else if CompNameKindDeq (comp_name_kind nm) nat_comp_name_kind then CIOnat
                   else if CompNameKindDeq (comp_name_kind nm) bool_comp_name_kind then CIObool
                        else bfio nm.

  (* We constrain here that components with named [msg_comp_name] have to be
     message components, i.e., taking in messages and returning directed messages *)
  Global Instance funIOd_msg : funIO :=
    MkFunIO funIOd_msg_nm.

  (* We override here some types of states:
       - "UNIT"  components must have a state of type [unit]
       - "NAT"   components must have a state of type [nat]
       - "BOOL"  components must have a state of type [nat]
       - "KEY"   components must have a state of type [local_key_map]
       - trusted components must have a state of type [tsf]
   *)
  Definition statefund_nm (nm : CompName) : Type :=
    if comp_name_trust nm then tsf nm
    else if CompNameSpaceDeq (comp_name_space nm) unit_comp_name_space then unit
         else if CompNameKindDeq (comp_name_kind nm) nat_comp_name_kind then nat
              else if CompNameKindDeq (comp_name_kind nm) bool_comp_name_kind then bool
                   else if CompNameKindDeq (comp_name_kind nm) key_comp_name_kind then local_key_map
                        else bsf nm.

  Global Instance stateFund : stateFun :=
    MkStateFun statefund_nm.


  (* ====== Lookup table ====== *)
  (* This is used to register state machines when not using the monad
     The Boolean is redundant, it says whether [cn] is trusted, which is already part of [cn] *)
  Definition lookup_table : ref (list {cn : CompName & {b : bool & PosDTime -> cio_I (fio cn) -> (unit * cio_O (fio cn))}}) :=
    ref_cons [].

  Definition update_lookup
             (level   : nat)
             (name    : CompName)
             (sm      : PosDTime -> cio_I (fio name) -> (unit * cio_O (fio name))) :=
    update_ref
      lookup_table
      ((existT _ name (existT _ (comp_name_trust name) sm)) :: get_ref lookup_table).
  (* ====== ======= *)


  (* state machine as monad -- one level state machine*)
  Record MP_StateMachine (p : CompName -> Type) (cn : CompName) : Type :=
    MkMPSM
      {
        sm_update :> MP_Update p (cio_I (fio cn)) (cio_O (fio cn)) (sf cn);
        sm_state  : sf cn;
      }.
  Global Arguments MkMPSM    [p] [cn] _ _.
  Global Arguments sm_update [p] [cn] _ _ _ _.
  Global Arguments sm_state  [p] [cn] _.

  Definition NFalse (cn : CompName) : Type := False.

  Inductive sm_or (A B : Type) : Type :=
  | sm_or_at (a : A)
  | sm_or_sm (b : B).
  Global Arguments sm_or_at [A] [B] _.
  Global Arguments sm_or_sm [A] [B] _.

  Notation "A \+/ B" := (sm_or A B) (at level 70).

  (* Cumulative hierarchy of state machines *)
  Fixpoint M_StateMachine (n : nat) (cn : CompName) : Type :=
    match n with
    | 0 => False (*MP_StateMachine NFalse cn*)
    | S n => MP_StateMachine (M_StateMachine n) cn \+/ M_StateMachine n cn
    end.

  (* list of state machines; each state machine can have several levels *)
  Definition n_proc := M_StateMachine.
  Definition n_nproc (n : nat) := p_nproc (n_proc n).
  Definition n_procs (n : nat) := list (n_nproc n).

  (* a state machine exactly at level [S n] *)
  Definition n_proc_at (n : nat) (cn : CompName) := MP_StateMachine (n_proc n) cn.

  (* monad of the list of state machines; each state machine can have several levels *)
  Definition M_n (n : nat) (PO : Type) := n_procs n -> (n_procs n * PO)%type.

  (* monad update function that can halt *)
  Definition M_Update (n : nat) (nm : CompName) (S : Type) :=
    S -> PosDTime -> cio_I (fio nm) -> M_n n (hoption S * cio_O (fio nm)).

  (* return state and output ? *)
  Definition ret {A} (n : nat) (a : A) : M_n n A := fun s => (s, a).

  (* discards all processes *)
  Definition halt {A} (n : nat) (a : A) : M_n n A := fun s => ([], a).

  (* enables combining multiple state machine monads *)
  Definition bind {A B} {n:nat} (m : M_n n A) (f : A -> M_n n B) : M_n n B :=
    fun s =>
      let (s1,a) := m s in
      let (s2,b) := f a s1 in
      (s2,b).

  Notation "a >>= f" := (bind a f) (at level 80).

  Definition bind_pair {A B C} {n:nat} (m : M_n n (A * B)) (f : A -> B -> M_n n C) : M_n n C :=
    m >>= fun p => let (a,b) := p in f a b.

  Notation "a >>>= f" := (bind_pair a f) (at level 80).

  Lemma bind_bind :
    forall {n} {A B C} (m : M_n n A) (f : A -> M_n n B) (g : B -> M_n n C),
      ((m >>= f) >>= g)
      = (m >>= (fun a => ((f a) >>= g))).
  Proof.
    introv; apply functional_extensionality; introv; simpl.
    unfold bind; simpl.
    destruct (m x).
    destruct (f a n0).
    destruct (g b n1); auto.
  Qed.

  (* in a list of monad processes, find the one that has a Component Name nm *)
  Fixpoint find_name {n:nat} (nm : CompName) (l : n_procs n) : option (n_proc n nm) :=
    match l with
    | [] => None
    | MkPProc m pr :: rest =>
      match CompNameDeq m nm with
      | left q => Some (eq_rect _ _ pr _ q)
      | right _ => find_name nm rest
      end
    end.

  Definition at2sm
             {n  : nat}
             {cn : CompName}
             (p  : n_proc_at n cn) : n_proc (S n) cn :=
    sm_or_at p.

  Definition MP_defSM
             (cn : CompName)
             (n  : nat)
             (d  : sf cn) : n_proc_at n cn :=
    MkMPSM
      (fun t s i p => (p, (halt_local, cio_default_O (fio cn))))
      d.

  Definition M_defSM
             (nm : CompName)
             (n  : nat)
             (d  : sf nm) : n_proc 1 nm :=
    at2sm
      (MkMPSM
         (fun t s i p => (p, (halt_local, cio_default_O (fio nm))))
         d).

  (* incr of one level state machine monad *)
  Definition incr_n_proc {n} {nm} (p : n_proc n nm) : n_proc (S n) nm := sm_or_sm p.

  (* incr of state machine monad -each state machine can have multiple levels *)
  Definition incr_n_nproc {n} (p : n_nproc n) : n_nproc (S n) :=
    match p with
    | MkPProc m q =>
      MkPProc m (incr_n_proc q)
    end.

  (* incr list of state machine monads -- each state machine can have multiple levels *)
  Definition incr_n_procs {n} (ps : n_procs n) : n_procs (S n) :=
    map incr_n_nproc ps.

(*  (* halted monad of the state machine -- each state machine that can have several levels*)
  Fixpoint M_haltedSM_n {S}
           (n  : nat)
           (nm : CompName)
           (d  : S) : n_proc n nm :=
    match n with
    | 0 => M_haltedSM nm d
    | S m => incr_n_proc (M_haltedSM_n m nm d)
    end.*)

  Definition decr_n_proc {n} {nm} : n_proc n nm -> option (n_proc (Init.Nat.pred n) nm) :=
    match n with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | sm_or_at _ => None
               | sm_or_sm q => Some q
               end
    end.

  Definition decr_n_nproc {n} (np : n_nproc n) : option (n_nproc (Init.Nat.pred n)) :=
    match np with
    | MkPProc m p =>
      match decr_n_proc p with
      | Some q => Some (MkPProc m q)
      | None => None
      end
    end.

  Definition decr_n_procs {n} (ps : n_procs n) : n_procs (Init.Nat.pred n) :=
    mapOption decr_n_nproc ps.

  Definition incr_pred_n_proc {n} {nm} : n_proc (pred n) nm -> n_proc n nm :=
    match n with
    | 0 => fun p => match p with end
    | S m => fun p => sm_or_sm p
    end.

  Definition incr_pred_n_nproc {n} (p : n_nproc (pred n)) : n_nproc n :=
    match p with
    | MkPProc m q =>
      MkPProc m (incr_pred_n_proc q)
    end.

  Definition incr_pred_n_procs {n} (ps : n_procs (pred n)) : n_procs n :=
    map incr_pred_n_nproc ps.

  Definition update_state {n} {cn} (sm : n_proc_at n cn) (s : sf cn) : n_proc_at n cn :=
    MkMPSM
      (sm_update sm)
      s.

  (* lift from state to state machine; here x is sub-component with state and output*)
  Definition app_n_proc_at {n} {nm}
             (sm : n_proc_at n nm)
             (t  : PosDTime)
             (i  : cio_I (fio nm))
    : M_n n (hoption (n_proc_at n nm) * cio_O (fio nm)) :=
    (sm_update sm (sm_state sm) t i)
      >>>=
      fun ops o => ret _ (hoption_map (update_state sm) ops, o).

  Definition lift_M_O {m} {nm} {O}
             (x : M_n m (n_proc_at m nm * O))
    : M_n m (n_proc (S m) nm * O) :=
    x >>>= fun q o => ret _ (at2sm q, o).

(*  Definition lift_M {m} {nm} (x : M_p (n_proc m) (n_proc_at m nm))
    : M_n m (n_proc (S m) nm) :=
    x >>= fun q => ret _ (at2sm q).*)

  (* Part of the monad *)
  Definition M_on_pred {n} {O} (m : M_n (pred n) O) : M_n n O :=
    fun (ps : n_procs n) =>
      let (ps', o') := m (decr_n_procs ps)
      in (incr_pred_n_procs ps', o').

  Definition lift_M_O2 {n} {nm} {O} (m : M_n (pred n) (n_proc n nm * O))
    : M_n n (n_proc (S n) nm * O) :=
    M_on_pred m >>>= fun sm o => ret _ (incr_n_proc sm,o).

  Definition lift_M2 {n} {nm} (m : M_n (pred n) (n_proc n nm))
    : M_n n (n_proc (S n) nm) :=
    M_on_pred m >>= fun sm => ret _ (incr_n_proc sm).

(*  (* replace subprocess *)
  Fixpoint replace_sub {n} {nm}
           (ps : n_procs n)
           (p  : n_proc n nm) : n_procs n :=
    match ps with
    | [] => []
    | MkPProc m q :: rest =>
      if CompNameDeq nm m then MkPProc nm p :: rest
      else MkPProc m q :: replace_sub rest p
    end.

  (* replace subprocesses in a list: copy from [l] into [ps] *)
  Fixpoint replace_subs {n} (ps : n_procs n) (l : n_procs n) : n_procs n :=
    match l with
    | [] => ps
    | p :: rest =>
      match p with
      | MkPProc nm q => replace_subs (replace_sub ps q) rest
      end
    end.*)

  Fixpoint remove_name {n}
           (ps : n_procs n)
           (cn : CompName) : n_procs n :=
    match ps with
    | [] => []
    | p :: rest =>
      if CompNameDeq cn (pp_name p) then rest
      else p :: remove_name rest cn
    end.

  (* removes subprocesses in a list: removes [l] from [ps] *)
  Fixpoint remove_names {n} (ps : n_procs n) (l : list CompName) : n_procs n :=
    match l with
    | [] => ps
    | cn :: rest => remove_names (remove_name ps cn) rest
    end.

  Definition get_names {n} (l : n_procs n) : list CompName :=
    map (fun p => pp_name p) l.

  Definition remove_subs {n m} (ps : n_procs n) (l : n_procs m) : n_procs n :=
    remove_names ps (get_names l).

  (* NOTE: The order is going to be preserved if the components
     are ordered in decreasing order of level *)
  Definition update_subs {n} (ps : n_procs (S n)) (l : list CompName) (ps' : n_procs n) : n_procs (S n) :=
(*    remove_subs ps ps' ++ incr_n_procs ps'.*)
    remove_names ps l ++ incr_n_procs ps'.

  Definition update_subs_decr {n} (ps : n_procs (S n)) (ps' : n_procs n) : n_procs (S n) :=
    update_subs ps (get_names (decr_n_procs ps)) ps'.

  (* Part of the monad *)
  Definition M_on_decr {n} {O} (m : M_n n O) : M_n (S n) O :=
    fun (ps : n_procs (S n)) =>
      let (ps', o') := m (decr_n_procs ps)
      in (update_subs_decr ps ps', o').

  Fixpoint sm2level {n} {nm} : n_proc n nm -> nat :=
    match n return n_proc n nm -> nat with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | sm_or_at q => m
               | sm_or_sm q => sm2level q
               end
    end.

  Fixpoint M_on_sm {n} {cn} {A} :
    forall (sm : n_proc n cn) (f : n_proc_at (sm2level sm) cn -> M_n (sm2level sm) A), M_n n A :=
    match n with
    | 0 => fun sm f => match sm with end
    | S n =>
      fun sm =>
        match sm with
        | sm_or_at p => fun f => M_on_decr (f p)
        | sm_or_sm q => fun f => M_on_decr (M_on_sm q f)
        end
    end.

(*  Definition lift_sm_O {m} {nm} {O}
             (x : M_n m (n_proc_at m nm * O))
    : M_n m (n_proc m nm * O) :=
    x >>>= fun q o => ret _ (at2sm q, o).*)

  Definition lift_M_1 {m} {nm} {O}
             (x : M_n m (hoption (n_proc_at m nm) * O))
    : M_n (S m) (hoption (n_proc (S m) nm) * O) :=
    M_on_decr x >>>= fun q o => ret _ (hoption_map at2sm q, o).

  Definition lift_M_2 {n} {nm} {O} (m : M_n n (hoption (n_proc n nm) * O))
    : M_n (S n) (hoption (n_proc (S n) nm) * O) :=
    M_on_decr m >>>= fun sm o => ret _ (hoption_map incr_n_proc sm,o).

  Fixpoint app_m_proc {n} {nm}
    : n_proc n nm
      -> PosDTime
      -> cio_I (fio nm)
      -> M_n n (hoption (n_proc n nm) * cio_O (fio nm)) :=
    match n return n_proc n nm -> PosDTime -> cio_I (fio nm) -> M_n n (hoption (n_proc n nm) * cio_O (fio nm)) with
    | 0 =>
      fun pr t i => match pr with end
    | S m =>
      fun pr t i =>
        match pr with
        | sm_or_at sm => lift_M_1 (app_n_proc_at sm t i)
        | sm_or_sm pr' => lift_M_2 (app_m_proc pr' t i)
        end
    end.

  Fixpoint replace_name {n:nat} {nm : CompName} (pr : n_proc n nm) (l : n_procs n) : n_procs n :=
    match l with
    | [] => []
    | MkPProc m q :: rest =>
      if CompNameDeq m nm then MkPProc nm pr :: rest
      else MkPProc m q :: replace_name pr rest
    end.

  Definition replace_name_op {n:nat} {cn : CompName} (o : hoption (n_proc n cn)) (l : n_procs n) : n_procs n :=
    match o with
    | hsome p => replace_name p l
    | halt_local => remove_name l cn
    | halt_global => []
    end.

  Definition call_proc {n:nat} (nm : CompName) (t : PosDTime) (i : cio_I (fio nm)) : M_n n (cio_O (fio nm)) :=
    fun (l : n_procs n) =>
      match find_name nm l with
      | Some pr =>
        match app_m_proc pr t i l with
        | (l',(pr',o)) => (replace_name_op pr' l',o)
        end
      | None => (l,cio_default_O (fio nm))
      end.

  (* We had to break the abstraction because Coq didn't like [build_m_process]. *)
  Definition build_mp_sm {n}
             {nm  : CompName}
             (upd : M_Update n nm (sf nm))
             (s   : sf nm) : n_proc_at n nm :=
    MkMPSM upd s.

  Definition build_m_sm {n}
             {nm  : CompName}
             (upd : M_Update n nm (sf nm))
             (s   : sf nm) : n_proc (S n) nm :=
    at2sm (build_mp_sm upd s).

  (*Fixpoint run_n_proc {n} {nm} (p : n_proc n nm) (l : list (cio_I (fio nm)))
    : M_n n (list (cio_O (fio nm)) * n_proc n nm) :=
    match l with
    | [] => ret _ ([], p)
    | i :: rest =>
      (app_m_proc p i)
        >>>= fun p' o =>
               (run_n_proc p' rest)
                 >>>= fun outs p'' => ret _ (o :: outs, p'')
    end.*)

(*  (* extracts the type of states by going down a state machine until an MP machine *)
  Fixpoint sm2S {n} {nm} : n_proc n nm -> Type :=
    match n return n_proc n nm -> Type with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | inl q => sm_S q
               | inr q => sm2S q
               end
    end.*)

  Fixpoint sm2state {n} {nm} : forall (sm : n_proc n nm), sf nm :=
    match n return forall (sm : n_proc n nm), sf nm with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | sm_or_at q => sm_state q
               | sm_or_sm q => sm2state q
               end
    end.

  (*Inductive LSstatus :=
  | ls_is_ok
  | ls_is_byz.*)

  (* the [space] is the space of the main component, which should be of kind "MAIN" *)
  Definition LocalSystem
             (L : CompNameLevel)
             (S : CompNameSpace) := n_procs L.

  Definition defaultLocalSystem : LocalSystem 0 1 := [].

(*  Definition upd_ls_main {L} {S} (ls : LocalSystem L S) (m : n_proc_at _ _) : LocalSystem L S :=
    MkLocalSystem
      m
      (ls_subs ls)
      (ls_status ls).

  Definition upd_ls_main_state {L} {S} (ls : LocalSystem L S) (s : sf _) : LocalSystem L S :=
    MkLocalSystem
      (update_state (ls_main ls) s)
      (ls_subs ls)
      (ls_status ls).

  Definition upd_ls_subs {L} {S} (ls : LocalSystem L S) (ss : n_procs _) : LocalSystem L S :=
    MkLocalSystem
      (ls_main ls)
      ss
      (ls_status ls).*)

  Definition is_trusted {n} (comp : n_nproc n) : bool :=
    comp_name_trust (pp_name comp).

  Fixpoint remove_non_trusted {n} (l : n_procs n) : n_procs n :=
    match l with
    | [] => []
    | comp :: rest =>
      if is_trusted comp then comp :: remove_non_trusted rest
      else remove_non_trusted rest
    end.

(*  Definition upd_ls_byz {L} {S} (ls : LocalSystem L S) : LocalSystem L S :=
    MkLocalSystem
      (ls_main ls) (* the main component becomes useless now *)
      (remove_non_trusted (ls_subs ls))
      ls_is_byz.*)

(*  Definition upd_ls_main_state_and_subs
             {L} {S}
             (ls : LocalSystem L S)
             (s  : sf _)
             (ss : n_procs _) : LocalSystem _ _ :=
    MkLocalSystem
      (update_state (ls_main ls) s)
      ss
      (ls_status ls).*)

(*  Definition if_ls_is_ok_opt {L S} (ls : LocalSystem L S) {A} (a : option A) : option A :=
    match ls_status ls with
    | ls_is_ok => a
    | ls_is_byz => None
    end.*)

(*  Record message_local_system_constraint (s : LocalSystem) :=
    MkMessageLocalSystemConstratin
      {
        mlsc_I : cio_I (fio (projT1 (ls_main s))) = msg;
        mlsc_O : cio_O (fio (projT1 (ls_main s))) = DirectedMsgs;
      }.*)

  (*Definition run_local_system (s : LocalSystem) (l : list (cio_I (fio msg_comp_name))) :=
    run_n_proc (ls_main s) l (ls_subs s).*)

  (*Definition M_NStateMachine (nm : CompName) (n : nat) := name -> n_proc n nm.*)

  Record funLevelSpace :=
    MkFunLevelSpace
      {
        fls_level : name -> CompNameLevel;
        fls_space : name -> CompNameSpace;
      }.

  Definition M_USystem (F : funLevelSpace) :=
    forall (n : name), LocalSystem (fls_level F n) (fls_space F n).

(*  Definition message_system_constraint (sys : M_USystem) :=
    forall nm, message_local_system_constraint (sys nm).*)

  (* This is a system with a constraint that the main component takes in messages
     and outputs directed messages *)
(*  Record M_MUSystem :=
    MkMMUSystem
      {
        msys_sys  :> M_USystem;
        msys_cond : message_system_constraint msys_sys;
      }.*)

  Definition M_on_some
             {n A B}
             (f : A -> M_n n (hoption B))
             (xop : hoption A) : M_n n (hoption B) :=
    match xop with
    | hsome a => f a
    | halt_local => ret _ halt_local
    | halt_global => ret _ halt_global
    end.

  Notation "a >>o>> f" := (M_on_some f a) (at level 80).

  Definition bind_some {A B} {n:nat}
             (m : M_n n (hoption A))
             (f : A -> M_n n (hoption B)) : M_n n (hoption B) :=
    m >>= fun x => x >>o>> f.

  Notation "a >>o= f" := (bind_some a f) (at level 80).

  Definition M_op_update {S} {n} {nm}
             (upd : M_Update n nm S)
             (s   : S)
             (o   : hoption (PosDTime * cio_I (fio nm)))
    : M_n n (hoption (hoption S * cio_O (fio nm))) :=
    o >>o>> (fun i => (upd s (fst i) (snd i)) >>= fun so => ret _ (hsome so)).

  Definition M_op_state {S} {n} {nm}
             (upd : M_Update n nm S)
             (s   : S)
             (o   : hoption (PosDTime * cio_I (fio nm)))
    : M_n n (hoption S) :=
    o >>o>> (fun i => (upd s (fst i) (snd i)) >>= fun so => ret _ (fst so)).

  (* never used
  Definition M_op_op_update {S} {n} {nm}
             (upd : M_Update n nm S)
             (s   : S)
             (o   : option (cio_I (fio nm)))
    : option (M_n n (option S * cio_O (fio nm))) :=
    match o with
    | Some i => Some (upd s i)
    | None => None
    end.

  Definition M_op_sm_update {n} {nm}
             (sm  : n_proc n nm)
             (iop : option (cio_I (fio nm)))
    : M_n (pred n) (option (n_proc n nm * cio_O (fio nm))) :=
    match iop with
    | Some i => match app_m_proc sm i with
                | Some x => x >>= fun x => ret _ (Some x)
                | None => ret _ None
                end
    | None => ret _ None
    end. *)

  (* Note: the monad is taking care of calling the lower levels *)
  (* TODO: We currently return None either if the input is unavailable or
       if the machine stops.  We should distinguish the 2. *)
(*  Fixpoint M_run_update_on_list {S} {n} {nm}
           (s   : S)
           (upd : M_Update n nm S)
           (l   : oplist (cio_I (fio nm))) : M_n n (option S) :=
    match l with
    | [] => ret _ (Some s)
    | aop :: l =>
      aop >>o>>
          fun a =>
            (upd s a) >>= fun so =>
                            (fst so) >>o>>
                                     fun s' => M_run_update_on_list s' upd l
    end.*)

(*  Definition sm2update {n} {cn} : forall (sm : n_proc n cn), MP_Update (n_proc (sm2level sm)) (cio_I (fio cn)) (cio_O (fio cn)) (sm2S sm).
  Proof.
    induction n; introv; simpl in *.

    - destruct sm.

    - destruct sm; simpl in *.

      + exact (sm_update m).

      + apply IHn.
  Qed.*)

  Fixpoint sm2update {n} {cn}
    : forall (sm : n_proc n cn), M_Update (sm2level sm) cn (sf cn) :=
    match n with
    | 0 => fun sm => match sm with end
    | S m => fun sm =>
               match sm with
               | sm_or_at q => sm_update q
               | sm_or_sm q => sm2update q
               end
    end.

(*  Definition M_run_sm_on_inputs {n} {nm}
             (sm : n_proc n nm)
             (l  : oplist (cio_I (fio nm))) : M_n n (option (sf nm)) :=
    M_on_sm
      sm
      (fun p => M_run_update_on_list (sm_state p) (sm_update p) l).*)

  Definition M_run_sm_on_input {n} {nm}
             (sm : n_proc n nm)
             (t  : PosDTime)
             (i  : cio_I (fio nm)) : M_n n (hoption (sf nm) * cio_O (fio nm)) :=
    M_on_sm
      sm
      (fun p => (sm_update p (sm_state p) t i)).

  Definition M_fst {n} {A} {B} (m : M_n n (A * B)) : M_n n A :=
    m >>= fun so => ret _ (fst so).

  Definition M_snd {n} {A} {B} (m : M_n n (A * B)) : M_n n B :=
    m >>= fun so => ret _ (snd so).

(*  Fixpoint M_run_sm_on_list_p {n} {nm}
           (sm : n_proc n nm)
           (l  : oplist (cio_I (fio nm))) : M_n (pred n) (option (n_proc n nm)) :=
    match l with
    | [] => ret _ (Some sm)
    | aop :: l =>
      aop >>o>> fun a =>
                  (app_m_proc sm a)
                    >>o>> fun f => f >>= fun so => M_run_sm_on_list_p (fst so) l
    end.*)

  (* never used
  Definition lift_M3 {n} {O} (m : M_n (pred n) O)
    : M_n (pred (S n)) O :=
    fun (ps : n_procs n) =>
      match m (decr_n_procs ps) with
      | (ps',o) => (incr_pred_n_procs ps', o)
      end.

  Fixpoint app_m_proc_state {n} {nm}
    : forall (sm : n_proc n nm),
      cio_I (fio nm)
      -> option (M_n (pred n) (option (sm2S sm) * cio_O (fio nm))) :=
    match n return forall (sm : n_proc n nm), cio_I (fio nm) -> option (M_n (pred n) (option (sm2S sm) * cio_O (fio nm))) with
    | 0 =>
      fun pr i =>
        (*Some (lift_M (sm_s_to_sm pr (sm_update pr (sm_state pr) i)))*)
        None
    | S m =>
      fun pr =>
        match pr with
        | inl sm => fun i => Some (sm_update sm (sm_state sm) i)
        | inr pr' => fun i => option_map lift_M3 (app_m_proc_state pr' i)
        end
    end.
   *)

  (*Fixpoint M_run_sm_on_list_state {n} {nm}
           (sm : n_proc n nm)
           (l  : oplist (cio_I (fio nm))) : M_n (pred n) (option (sm2S sm)) :=
    match l with
    | [] => ret _ (Some (sm2state sm))
    | Some a :: l =>
      match app_m_proc_state sm a with
      | Some f => f >>= fun so => let (sm',_) := so in M_run_sm_on_list_state sm' l
      | None => ret _ None
      end
    | None :: _ => ret _ None
    end.*)


  Definition op_state_out (S : Type) := option (option S * DirectedMsgs).

(*  Definition M_run_update_on_event {S} {n} {k}
             (s    : S)
             (upd  : M_Update n (main_comp_name k) S)
             {eo   : EventOrdering}
             (e    : Event) : M_n n (op_state_out S) :=
    (M_run_update_on_list s upd (map trigger_op (@localPreds pn pk pm _ _ eo e)))
      >>o= fun s => M_op_update upd s (trigger_op e).*)

(*  Definition M_run_sm_on_event {n} {k}
             (sm : n_proc n (main_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n n (op_state_out (sf (main_comp_name k))) :=
    M_on_sm sm (fun p => M_run_update_on_event (sm_state p) (sm_update p) e).*)

  (*Definition M_run_sm_on_event {n} {k}
             (sm : n_proc n (main_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (op_state_out (sf (main_comp_name k))) :=
    M_run_update_on_event (sm2state sm) (sm2update sm) e.*)

(*  Definition M_state_sm_on_event {n} {k}
             (sm : n_proc n (main_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n n (option (sf (main_comp_name k))) :=
  (M_run_sm_on_event sm e)
    >>o= fun p => ret _ (fst p).*)

(*  Definition M_state_sm_before_event {n} {k}
             (sm : n_proc n (main_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n n (option (sf (main_comp_name k))) :=
    M_run_sm_on_inputs sm (map trigger_op (@localPreds pn pk pm _ _ eo e)).*)



  (******************************************)
  (* *** state of local system on event *** *)
  (******************************************)

  Fixpoint update_state_m {n} {cn} :
    forall (sm : n_proc n cn)
           (s  : sf cn), n_proc n cn :=
    match n with
    | 0 => fun sm s => match sm with end
    | S m =>
      fun sm s =>
        match sm with
        | sm_or_at p => sm_or_at (update_state p s)
        | sm_or_sm q => sm_or_sm (update_state_m q s)
        end
    end.

  Lemma n_procs_to_level_update_state_sm
        {lvl} {cn}
        {p : n_proc lvl cn}
        (s : sf cn)
        (l : n_procs (sm2level p)) : n_procs (sm2level (update_state_m p s)).
  Proof.
    induction lvl; simpl in *; auto; destruct p; auto.
  Defined.

  Definition M_break {n} {S} {O}
             (sm   : M_n n S)
             (subs : n_procs n)
             (F    : n_procs n -> S -> O) : O :=
    let (subs', out) := sm subs in F subs' out.

  (* by default main components are not trusted *)

  (* m : missing *)
  Definition on_comp {n}
             (l : n_procs n)
             {cn} {A}
             (f : n_proc n cn -> A) (m : A) :  A :=
    match find_name cn l with
    | Some comp => f comp
    | None => m
    end.

  (* m <= n *)
  Fixpoint select_n_proc {n} {cn} m {struct n} : n_proc n cn -> option (n_proc m cn) :=
    match deq_nat n m with
    | left q => fun p => Some (eq_rect _ (fun n => n_proc n cn) p _ q)
    | right q =>
      match n with
      | 0 => fun p => match p with end
      | S k =>
        fun p =>
          match p with
          | sm_or_at q => None
          | sm_or_sm q => select_n_proc m q
          end
      end
    end.

  Definition select_n_nproc {n} m (p : n_nproc n) : option (n_nproc m) :=
    match p with
    | MkPProc cn p => option_map (MkPProc cn) (select_n_proc m p)
    end.

  Definition select_n_procs {n} m (ps : n_procs n) : n_procs m :=
    mapOption (select_n_nproc m) ps.

  Fixpoint lift_n_proc {n} {cn} j : n_proc n cn -> n_proc (j + n) cn :=
    match j with
    | 0 => fun p => p
    | S k => fun p => incr_n_proc (lift_n_proc k p)
    end.

  Definition lift_n_nproc {n} j (p : n_nproc n) : n_nproc (j + n) :=
    match p with
    | MkPProc cn p => MkPProc cn (lift_n_proc j p)
    end.

  Definition lift_n_procs {n} j (l : n_procs n) : n_procs (j + n) :=
    map (lift_n_nproc j) l.

  Lemma select_n_proc_trivial :
    forall {n} {cn} (p : n_proc n cn),
      select_n_proc n p = Some p.
  Proof.
    introv.
    destruct n; simpl; auto;[].
    destruct (deq_nat n n); simpl; tcsp.
    pose proof (UIP_refl_nat _ e) as q; subst; simpl; auto.
  Qed.
  Hint Rewrite @select_n_proc_trivial : comp.

  Lemma select_n_procs_trivial :
    forall {n} (subs : n_procs n),
      select_n_procs n subs = subs.
  Proof.
    introv; unfold select_n_procs.
    induction subs; simpl; auto.
    rewrite IHsubs.
    destruct a; simpl in *.
    autorewrite with comp; simpl; auto.
  Qed.
  Hint Rewrite @select_n_procs_trivial : comp.

  Lemma lift_n_procs_0 :
    forall {n} (subs : n_procs n),
      lift_n_procs 0 subs = subs.
  Proof.
    introv; unfold lift_n_procs.
    induction subs; simpl in *; tcsp.
    rewrite IHsubs.
    destruct a; simpl; auto.
  Qed.
  Hint Rewrite @lift_n_procs_0 : comp.

  Lemma mapOption_fun_Some :
    forall {A} (l : list A),
      mapOption (fun p => Some p) l = l.
  Proof.
    induction l; simpl; auto.
    rewrite IHl; auto.
  Qed.
  Hint Rewrite @mapOption_fun_Some : list.

  Lemma mapOption_fun_None :
    forall {A B} (l : list A),
      mapOption (fun _ => @None B) l = [].
  Proof.
    induction l; simpl; auto.
  Qed.
  Hint Rewrite @mapOption_fun_None : list.

  Lemma select_n_proc_lt :
    forall cn n m (p : n_proc n cn),
      n < m
      -> select_n_proc m p = None.
  Proof.
    induction n; introv ltm; simpl in *; tcsp.
    destruct p as [p|p]; simpl in *.

    { destruct m; try omega.
      destruct (deq_nat n m); subst; try omega; auto. }

    destruct m; try omega.
    destruct (deq_nat n m); subst; try omega; auto.
    apply IHn; auto; try omega.
  Qed.

  Lemma select_n_proc_S_sm_implies :
    forall cn n m (p : n_proc n cn) (q : n_proc m cn),
      select_n_proc (S m) p = Some (sm_or_sm q)
      -> select_n_proc m p = Some q.
  Proof.
    induction n; introv sel; simpl in *; tcsp.
    fold M_StateMachine in *.
    fold n_proc in *.
    destruct m; simpl.

    { destruct (deq_nat n 0); subst; simpl in *; tcsp. }

    destruct (deq_nat n (S m)); subst.

    { simpl in sel; inversion sel; subst.
      destruct (deq_nat (S m) m); try omega.
      simpl.
      destruct (deq_nat m m); try omega.
      pose proof (UIP_refl_nat _ e) as w; subst; simpl; auto. }

    destruct p; ginv.
    destruct (deq_nat n m); subst; tcsp;[|].

    { rewrite select_n_proc_lt in sel; ginv; try omega. }

    apply IHn in sel; auto.
  Qed.

  Lemma select_n_proc_select_n_proc_le :
    forall cn k n m (p : n_proc k cn) q r,
      n <= m
      -> select_n_proc m p = Some q
      -> select_n_proc n q = Some r
      -> select_n_proc n p = Some r.
  Proof.
    induction k; introv le sela selb; simpl in *; tcsp;[].
    destruct m; simpl in *; tcsp;[].
    destruct n; simpl in *; tcsp;[].
    destruct (deq_nat k m); subst; ginv;[].
    destruct p as [p|p]; ginv;[].
    destruct (deq_nat m n); subst; ginv; try omega;[|].

    { destruct (deq_nat k n); subst; try omega; auto. }

    destruct q as [q|q]; ginv;[].
    destruct (deq_nat k n); subst; try omega; auto.

    { simpl in *.
      apply select_n_proc_S_sm_implies in sela.
      pose proof (IHk (S n) m p q r) as IHk.
      repeat (autodimp IHk hyp); try omega;[].
      destruct r.
      { rewrite select_n_proc_lt in IHk; ginv; try omega. }
      apply select_n_proc_S_sm_implies in IHk.
      rewrite select_n_proc_trivial in IHk.
      inversion IHk; auto. }

    { apply select_n_proc_S_sm_implies in sela.
      pose proof (IHk (S n) m p q r) as IHk.
      repeat (autodimp IHk hyp); try omega. }
  Qed.

  Lemma select_n_proc_some_at_implies :
    forall cn k n m (p : n_proc k cn) (q : n_proc_at m cn),
      n <= m
      -> select_n_proc (S m) p = Some (sm_or_at q)
      -> select_n_proc n p = None.
  Proof.
    induction k; introv lem sel; simpl in *; tcsp;[].
    destruct (deq_nat k m); subst.

    { simpl in *; inversion sel; subst; simpl in *; clear sel.
      destruct n; auto.
      destruct (deq_nat m n); subst; auto; try omega. }

    destruct p; ginv.
    destruct n.

    { eapply IHk; eauto. }

    destruct (deq_nat k n); subst; try omega; simpl; auto.

    { rewrite select_n_proc_lt in sel; try omega; ginv. }

    pose proof (IHk (S n) m b q) as IHk.
    repeat (autodimp IHk hyp).
  Qed.

  Lemma select_n_proc_select_n_proc_le2 :
    forall cn k n m (p : n_proc k cn) q,
      n <= m
      -> select_n_proc m p = Some q
      -> select_n_proc n q = None
      -> select_n_proc n p = None.
  Proof.
    induction k; introv le sela selb; simpl in *; tcsp;[].
    destruct m; simpl in *; tcsp;[].
    destruct n; simpl in *; tcsp;[|].

    { destruct (deq_nat k m); subst; ginv;[].
      destruct p; ginv;[].
      destruct q; ginv.
      { clear IHk.
        destruct k; simpl in *; tcsp.
        destruct (deq_nat k m); subst; try omega; ginv; auto.
        destruct b; ginv.
        pose proof (select_n_proc_some_at_implies cn k 0 m b a) as w.
        repeat (autodimp w hyp); try omega. }
      apply select_n_proc_S_sm_implies in sela.
      pose proof (IHk 0 m b b0) as IHk.
      repeat (autodimp IHk hyp); try omega. }

    destruct (deq_nat k m); subst; try omega; ginv;[].
    destruct (deq_nat m n); subst; try omega; ginv;[].
    destruct (deq_nat k n); subst; try omega; ginv.

    { simpl.
      destruct p; ginv.
      rewrite select_n_proc_lt in sela; try omega; ginv. }

    destruct p; ginv;[].
    destruct q; ginv.

    { pose proof (select_n_proc_some_at_implies cn k (S n) m b a) as w.
      repeat (autodimp w hyp); try omega. }

    pose proof (IHk (S n) (S m) b (sm_or_sm b0)) as IHk.
    repeat (autodimp IHk hyp).
    simpl.
    destruct (deq_nat m n); try omega; auto.
  Qed.

  Lemma select_n_proc_none_implies :
    forall cn k n m (p : n_proc k cn),
      m <= k
      -> n <= m
      -> select_n_proc m p = None
      -> select_n_proc n p = None.
  Proof.
    induction k; introv lek lem sel; simpl in *; tcsp;[].
    destruct m; simpl in *; tcsp.

    { destruct n; auto; try omega. }

    destruct n; simpl in *; tcsp;[|].

    { destruct (deq_nat k m); subst; ginv;[].
      destruct p; ginv; auto;[].
      pose proof (IHk 0 (S m) b) as IHk.
      repeat (autodimp IHk hyp); try omega. }

    destruct (deq_nat k m); subst; try omega; ginv;[].
    destruct (deq_nat k n); subst; try omega; ginv.

    { simpl.
      destruct p; ginv; auto.
      pose proof (IHk (S n) (S m) b) as IHk; repeat (autodimp IHk hyp); try omega. }
  Qed.

  Lemma select_n_procs_select_n_procs_le :
    forall n m k (subs : n_procs k),
      m <= k
      -> n <= m
      -> select_n_procs n (select_n_procs m subs)
         = select_n_procs n subs.
  Proof.
    unfold select_n_procs.
    induction subs; introv ltk lem; simpl in *; auto.
    repeat (autodimp IHsubs hyp).
    destruct a as [cn p]; simpl.
    remember (select_n_proc m p) as w; symmetry in Heqw; destruct w; simpl.

    { remember (select_n_proc n n0) as z; symmetry in Heqz; destruct z; simpl.

      { pose proof (select_n_proc_select_n_proc_le cn k n m p n0 n1) as q.
        repeat (autodimp q hyp);[].
        rewrite q; simpl.
        rewrite IHsubs; auto. }

      rewrite IHsubs.
      pose proof (select_n_proc_select_n_proc_le2 cn k n m p n0) as q.
      repeat (autodimp q hyp).
      rewrite q; simpl; auto. }

    rewrite IHsubs; clear IHsubs.

    remember (select_n_proc n p) as z; symmetry in Heqz; destruct z; simpl; auto;[].
    pose proof (select_n_proc_none_implies cn k n m p) as q.
    repeat (autodimp q hyp); try omega.
    rewrite q in Heqz; ginv.
  Qed.

  Lemma select_n_nproc_succ :
    forall {cn} {k} (p : n_proc (S k) cn),
      select_n_proc k p
      = match p with
        | sm_or_at q => None
        | sm_or_sm q => Some q
        end.
  Proof.
    introv.
    unfold select_n_proc.
    destruct (deq_nat (S k) k); try omega.
    destruct p; auto.
    destruct k.
    { simpl; auto. }
    destruct (deq_nat (S k) (S k)); auto; try omega.
    pose proof (UIP_refl_nat _ e) as w; subst; simpl; auto.
  Qed.

  Lemma decr_n_procs_as_select_n_procs :
    forall {k} (subs : n_procs (S k)),
      decr_n_procs subs = select_n_procs k subs.
  Proof.
    introv; simpl.
    unfold decr_n_procs, select_n_procs.
    induction subs; simpl; auto.
    destruct a as [cn p].
    unfold select_n_nproc at 1.
    rewrite select_n_nproc_succ.
    simpl.
    destruct p; simpl in *; auto.
    unfold n_procs in *; rewrite IHsubs; auto.
  Qed.

  Definition M_run_ls_on_input
             {n}
             (ls : n_procs n)
             cn
             (t  : PosDTime)
             (i  : cio_I (fio cn)) : n_procs n * option (cio_O (fio cn)) :=
    on_comp
      ls
      (fun main =>
         M_break
           (M_run_sm_on_input main t i)
           ls
           (fun subs out =>
              (match fst out with
               | hsome s => replace_name (update_state_m main s) subs
               | halt_local => remove_name subs cn
               | halt_global => []
               end,
               Some (snd out))))
      (* We simply return the local system if we cannot find the component *)
      (ls, None).

  Definition to_snd_default
             {A} {cn}
             (x : A * option (cio_O (fio cn))) : A * cio_O (fio cn) :=
    match x with
    | (a, Some o) => (a,o)
    | (a, None) => (a,cio_default_O _)
    end.

  Lemma UIP_refl_CompName :
    forall (n : CompName) (x : n = n), x = eq_refl.
  Proof.
    introv; apply UIPReflDeq; auto.
    apply CompNameDeq.
  Qed.

  Lemma UIP_refl_CompNameKind :
    forall (k : CompNameKind) (x : k = k), x = eq_refl.
  Proof.
    introv; apply UIPReflDeq; auto.
    apply CompNameKindDeq.
  Qed.

  Lemma UIP_refl_CompNameSpace :
    forall (s : CompNameSpace) (x : s = s), x = eq_refl.
  Proof.
    introv; apply UIPReflDeq; auto.
    apply CompNameSpaceDeq.
  Qed.

  Lemma UIP_refl_CompNameState :
    forall (s : CompNameState) (x : s = s), x = eq_refl.
  Proof.
    introv; apply UIPReflDeq; auto.
    apply CompNameStateDeq.
  Qed.

  Lemma implies_find_name_decr_n_procs :
    forall {cn} {n} (l : n_procs (S n)) (b : n_proc n cn),
      find_name cn l = Some (sm_or_sm b)
      -> find_name cn (decr_n_procs l) = Some b.
  Proof.
    induction l; introv h; simpl in *; tcsp.
    destruct a as [cn' p']; simpl in *; dest_cases w; subst; simpl in *; ginv.

    { inversion h; subst; simpl in *; clear h; dest_cases w.
      rewrite (UIP_refl_CompName _ w); simpl; auto. }

    {apply IHl in h; clear IHl; unfold decr_n_procs in *; simpl in *.
     destruct p'; simpl in *; tcsp; dest_cases w. }
  Qed.

  Definition nested2state
             {A} {n} {cn} {B}
             (x : A * (hoption (n_proc n cn) * B)) : A * (hoption (sf cn) * B) :=
    match x with
    | (a, (pop, b)) => (a,(hoption_map sm2state pop,b))
    end.

  Lemma app_m_proc_as_M_on_sm :
    forall {n} {cn} (p : n_proc n cn) t i (l : n_procs n),
      nested2state (app_m_proc p t i l)
      = M_on_sm p (fun a => sm_update a (sm_state a) t i) l.
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct p; simpl in *; tcsp.

    { unfold lift_M_1, app_n_proc_at, bind_pair, bind, M_on_decr; simpl.
      remember (sm_update a (sm_state a) t i (decr_n_procs l)) as u; symmetry in Hequ; repnd; simpl in *.
      destruct u1; simpl in *; tcsp. }

    unfold lift_M_2, bind_pair, bind, M_on_decr; simpl.
    pose proof (IHn cn b t i (decr_n_procs l)) as IHn.
    rewrite <- IHn; clear IHn.
    remember (app_m_proc b t i (decr_n_procs l)) as u; symmetry in Hequ; repnd; simpl in *.
    f_equal.
    f_equal.
    destruct u1; simpl; tcsp.
  Qed.

  Lemma hoption_map_correct :
    forall {A B} (f : A -> B) (o : hoption A) (b : B),
      hoption_map f o = hsome b
      <-> (exists a, o = hsome a /\ b = f a).
  Proof.
    introv; destruct o; split; introv h; simpl in *; exrepnd; ginv; auto.
    eexists; dands; eauto.
  Qed.

  Lemma update_state_if_app_m_proc :
    forall {n} {cn} (p : n_proc n cn) t i l k q o,
      app_m_proc p t i l = (k, (hsome q, o))
      -> update_state_m p (sm2state q) = q.
  Proof.
    induction n; introv h; simpl in *; tcsp.
    destruct p; simpl in *; tcsp.

    { unfold lift_M_1, bind_pair, bind, M_on_decr in h.
      remember (app_n_proc_at a t i (decr_n_procs l)) as u; symmetry in Hequ; repnd; simpl in *.
      inversion h; subst; simpl in *; clear h.
      rename_hyp_with @at2sm h.
      apply hoption_map_correct in h; exrepnd; subst; simpl in *.
      unfold app_n_proc_at, bind_pair, bind in Hequ.
      remember (sm_update a (sm_state a) t i (decr_n_procs l)) as z; symmetry in Heqz.
      repnd; simpl in *; ginv.
      inversion Hequ; subst; simpl in *; tcsp; clear Hequ.
      rename_hyp_with @update_state h.
      apply hoption_map_correct in h; exrepnd; subst; simpl in *; tcsp. }

    unfold lift_M_2, bind_pair, bind, M_on_decr in h.
    remember (app_m_proc b t i (decr_n_procs l)) as u; symmetry in Hequ; repnd; simpl in *.
    inversion h; subst; simpl in *; clear h.
    rename_hyp_with @hoption_map h.
    apply hoption_map_correct in h; exrepnd; subst; simpl in *.
    apply IHn in Hequ; rewrite Hequ; auto.
  Qed.

  (* TODO: I defined a separate [M_run_ls_on_input] to reason about local system, but
     it's essentially the same as [call_proc]:
   *)
  Lemma M_run_ls_on_input_as_call_proc :
    forall {n}
           (ls : n_procs n)
           cn
           (t  : PosDTime)
           (i  : cio_I (fio cn)),
      to_snd_default (M_run_ls_on_input ls cn t i)
      = call_proc cn t i ls.
  Proof.
    introv.
    unfold M_run_ls_on_input, call_proc, M_run_sm_on_input, LocalSystem, M_break, on_comp in *; simpl in *.
    dest_cases w; rev_Some.
    pose proof (app_m_proc_as_M_on_sm w t i ls) as q.
    simpl in *; rewrite <- q; clear q.
    remember (app_m_proc w t i ls) as u; symmetry in Hequ; repnd; simpl in *.
    f_equal.
    destruct u1; simpl in *; tcsp.
    f_equal.
    apply update_state_if_app_m_proc in Hequ; auto.
  Qed.

  Definition on_some
             {A B}
             (xop : option A)
             (f : A -> option B) : option B :=
    map_option f xop.

  Definition M_run_ls_on_input_ls
             {n}
             (ls : n_procs n)
             cn
             (t  : PosDTime)
             (i  : cio_I (fio cn)) : n_procs n :=
    fst (M_run_ls_on_input ls cn t i).

  Definition M_run_ls_on_input_out
             {n}
             (ls : n_procs n)
             cn
             (t  : PosDTime)
             (i  : cio_I (fio cn)) : option (cio_O (fio cn)) :=
    snd (M_run_ls_on_input ls cn t i).

  Fixpoint M_run_ls_on_op_inputs
           {n}
           (ls : n_procs n)
           cn
           (l  : oplist (PosDTime * cio_I (fio cn))) : option (n_procs n) :=
    match l with
    | [] => Some ls
    | mop :: l =>
      on_some
        mop
        (fun m =>
           let ls' := M_run_ls_on_input_ls ls cn (fst m) (snd m) in
           M_run_ls_on_op_inputs ls' cn l)
    end.

  Fixpoint M_run_ls_on_inputs
           {n}
           (ls : n_procs n)
           cn
           (l  : list (PosDTime * cio_I (fio cn))) : n_procs n :=
    match l with
    | [] => ls
    | m :: l =>
      let ls' := M_run_ls_on_input_ls ls cn (fst m) (snd m) in
      M_run_ls_on_inputs ls' cn l
    end.

  Definition M_run_ls_before_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (LocalSystem L S) :=
    M_run_ls_on_op_inputs
      ls
      (msg_comp_name S)
      (map time_trigger_op (@localPreds pn pk pm _ _ eo e)).

  Definition M_run_ls_on_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (LocalSystem L S) :=
    on_some
      (M_run_ls_before_event ls e)
      (fun ls' =>
         option_map
           (M_run_ls_on_input_ls ls' (msg_comp_name S) (time e))
           (trigger_op e)).


  (*Lemma break_M_run_ls_before_event :
    forall (ls  : LocalSystem)
           {eo  : EventOrdering}
           (e   : Event)
           (ls' : LocalSystem),
      M_run_ls_before_event ls e = Some ls'
      -> exists s,
        M_state_sm_before_event (n_proc_at2nproc (ls_main ls)) e (ls_subs ls)
        = (ls_subs ls', Some (sm_state (ls_main ls'))).*)


  Definition state_of_component
             {L}
             (cn : CompName)
             (ls : n_procs L) : option (sf cn) :=
    option_map sm2state (find_name cn ls).

  Definition on_state_of_component
             {L}
             (cn : CompName)
             (ls : n_procs L)
             (F  : sf cn -> Prop) : Prop :=
    match state_of_component cn ls with
    | Some s => F s
    | None => True
    end.

  Definition cn2space (cn : CompName) : CompNameSpace :=
    comp_name_space cn.

  Definition sm2ls {n} {cn} (p : n_proc n cn) : LocalSystem n (cn2space cn) :=
    [MkPProc cn p].

  Definition M_comp_ls_on_op_inputs {n}
             (ls : n_procs n)
             cn
             (l : oplist (PosDTime * cio_I (fio cn))) : option (n_proc n cn) :=
    on_some
      (M_run_ls_on_op_inputs ls cn l)
      (find_name cn).

  Definition M_comp_ls_on_inputs {n}
             (ls : n_procs n)
             cn
             (l : list (PosDTime * cio_I (fio cn))) : option (n_proc n cn) :=
    find_name cn (M_run_ls_on_inputs ls cn l).

  Definition M_state_ls_on_op_inputs {n}
             (ls : n_procs n)
             cn
             (l : oplist (PosDTime * cio_I (fio cn))) : option (sf cn) :=
    on_some
      (M_run_ls_on_op_inputs ls cn l)
      (state_of_component cn).

  Definition M_state_ls_on_inputs {n}
             (ls : n_procs n)
             cn
             (l : list (PosDTime * cio_I (fio cn))) : option (sf cn) :=
    state_of_component cn (M_run_ls_on_inputs ls cn l).

  Lemma M_state_ls_on_op_inputs_as_comp :
    forall {n}
           (ls : n_procs n)
           cn
           (l : oplist (PosDTime * cio_I (fio cn))),
      M_state_ls_on_op_inputs ls cn l
      = option_map
          sm2state
          (M_comp_ls_on_op_inputs ls cn l).
  Proof.
    introv; unfold M_state_ls_on_op_inputs, M_comp_ls_on_op_inputs.
    remember (M_run_ls_on_op_inputs ls cn l) as x; destruct x; simpl; auto.
  Qed.

  Lemma M_state_ls_on_inputs_as_comp :
    forall {n}
           (ls : n_procs n)
           cn
           (l : list (PosDTime * cio_I (fio cn))),
      M_state_ls_on_inputs ls cn l
      = option_map
          sm2state
          (M_comp_ls_on_inputs ls cn l).
  Proof.
    introv; unfold M_state_ls_on_inputs, M_comp_ls_on_inputs.
    remember (M_run_ls_on_inputs ls cn l) as x; destruct x; simpl; auto.
  Qed.

  Definition M_state_ls_on_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event)
             (cn : CompName) : option (sf cn) :=
    map_option
      (state_of_component cn)
      (M_run_ls_on_event ls e).

  Definition M_state_ls_before_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event)
             (cn : CompName) : option (sf cn) :=
    map_option
      (state_of_component cn)
      (M_run_ls_before_event ls e).

  Definition M_state_sys_on_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event)
             (cn  : CompName) : option (sf cn) :=
    M_state_ls_on_event (sys (loc e)) e cn.

  Definition M_state_sys_before_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event)
             (cn  : CompName) : option (sf cn) :=
    M_state_ls_before_event (sys (loc e)) e cn.

(*  Definition M_run_local_system_on_event
             (ls : LocalSystem)
             {eo : EventOrdering}
             (e  : Event) : option LocalSystem :=
    match ls with
    | MkLocalSystem lvl space main subs =>
      match trigger e with
      | Some i =>
        let (subs',out) := sm_update main (sm_state main) i subs in
        let (sop,o) := out in
        match sop with
        | Some s => Some (MkLocalSystem lvl space (update_state main s) subs')
        | None => None
        end
      | None => None
      end
    end.*)

  Definition M_run_ls_on_this_one_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (LocalSystem L S) :=
    option_map
      (M_run_ls_on_input_ls ls (msg_comp_name S) (time e))
      (trigger_op e).

  Lemma crazy_bind_option1 :
    forall {n A O} (F : A -> M_n n (hoption A ## O)),
      (fun a : hoption A =>
         (a >>o>>
            (fun s : A => (F s) >>= (fun so : hoption A ## O => ret _ (hsome so))))
           >>o= fun p : hoption A ## O => ret _ (fst p))
      = fun (a : hoption A) =>
          a >>o>> fun s => F s >>= fun x => ret _ (fst x).
  Proof.
    introv.
    apply functional_extensionality; introv; simpl.
    apply functional_extensionality; introv; simpl.
    unfold bind_some, bind, M_on_some; simpl.
    destruct x; simpl; auto.
    destruct (F s x0); simpl; auto.
  Qed.
  Hint Rewrite @crazy_bind_option1 : comp.

  Definition bind_ret :
    forall {n} {A B} (a : A) (f : A-> M_n n B),
      ((ret n a) >>= f) = f a.
  Proof.
    introv.
    apply functional_extensionality; introv; simpl.
    unfold bind; simpl.
    destruct (f a x); auto.
  Qed.
  Hint Rewrite @bind_ret : comp.

  Definition bind_ret_fun :
    forall {n} {A B X} (F : X -> A) (f : A-> M_n n B),
      (fun x => (ret n (F x)) >>= f) = (fun x => f (F x)).
  Proof.
    introv.
    apply functional_extensionality; introv; simpl; autorewrite with comp; auto.
  Qed.
  Hint Rewrite @bind_ret_fun : comp.

  Lemma M_on_some_some :
    forall {n A B} a (f : A -> M_n n (hoption B)),
      ((hsome a) >>o>> f) = f a.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @M_on_some_some : comp.

  Lemma M_on_some_some_fun :
    forall {n A B X} (x : X) (F : X -> A) (f : A -> M_n n (hoption B)),
      (fun x => (hsome (F x)) >>o>> f) = (fun x => f (F x)).
  Proof.
    tcsp.
  Qed.
  (*Hint Rewrite @M_on_some_some_fun : comp.*)

  Lemma eq_M_break :
    forall {n} {S} {O}
           (sm   : M_n n S)
           (subs : n_procs n)
           (F G  : n_procs n -> S -> O),
      (forall subs' s, F subs' s = G subs' s)
      -> M_break sm subs F = M_break sm subs G.
  Proof.
    introv imp.
    f_equal.
    apply functional_extensionality; introv.
    apply functional_extensionality; introv; auto.
  Qed.

  Lemma M_break_bind :
    forall {n A B O}
           (a    : M_n n A)
           (G    : A -> M_n n B)
           (subs : n_procs n)
           (F    : n_procs n -> B -> O),
      M_break
        (a >>= G)
        subs
        F
      = M_break
          a
          subs
          (fun subs' x =>
             M_break
               (G x)
               subs'
               F).
  Proof.
    introv.
    unfold M_break, bind; simpl.
    destruct (a subs); auto.
    destruct (G a0 n0); auto.
  Qed.
  Hint Rewrite @M_break_bind : comp.

  Lemma M_break_bind_pair :
    forall {n A B C O}
           (a    : M_n n (A * B))
           (G    : A -> B -> M_n n C)
           (subs : n_procs n)
           (F    : n_procs n -> C -> O),
      M_break
        (a >>>= G)
        subs
        F
      = M_break
          a
          subs
          (fun subs' x =>
             M_break
               (G (fst x) (snd x))
               subs'
               F).
  Proof.
    introv.
    unfold bind_pair.
    rewrite M_break_bind; auto.
    apply eq_M_break; introv; repnd; subst; auto.
  Qed.
  Hint Rewrite @M_break_bind_pair : comp.

  Lemma M_break_bind_ret :
    forall {n A B O}
           (a    : M_n n A)
           (G    : A -> B)
           (subs : n_procs n)
           (F    : n_procs n -> B -> O),
      M_break
        (a >>= fun p => ret _ (G p))
        subs
        F
      = M_break
          a
          subs
          (fun subs' x => F subs' (G x)).
  Proof.
    introv.
    unfold M_break, bind; simpl.
    destruct (a subs); auto.
  Qed.
  Hint Rewrite @M_break_bind_ret : comp.

  Lemma crazy_bind_option2 :
    forall {n nm A} a (upd : M_Update n nm A) (o : hoption (PosDTime * cio_I (fio nm))),
      ((a >>o= fun s : A => M_op_update upd s o)
         >>o= fun p : hoption A ## cio_O (fio nm) => ret n (fst p))
      = (a >>o= fun s => M_op_state upd s o).
  Proof.
    introv; apply functional_extensionality; introv; simpl.
    unfold M_op_update, M_op_state, bind_some, bind, M_on_some, ret; simpl.
    destruct (a x); simpl.
    destruct h; auto.
    destruct o; auto; repnd; simpl in *.
    destruct (upd s s1 s0 n0); auto.
  Qed.
  Hint Rewrite @crazy_bind_option2 : comp.

  Lemma map_option_M_break :
    forall {n} {S} {O} {X}
           (sm   : M_n n S)
           (subs : n_procs n)
           (F    : n_procs n -> S -> option O)
           (G    : O -> option X),
      map_option G (M_break sm subs F)
      = M_break sm subs (fun subs' s => map_option G (F subs' s)).
  Proof.
    introv.
    unfold map_option, M_break.
    destruct (sm subs).
    destruct (F n0 s); auto.
  Qed.

  Lemma map_option_swap :
    forall {A B C} (a : option A) (b : option B) (F : A -> B -> option C),
      map_option
        (fun a =>
           map_option
             (fun b => F a b)
             b)
        a
      = map_option
          (fun b =>
             map_option
               (fun a => F a b)
               a)
          b.
  Proof.
    introv; unfold map_option.
    destruct a, b; simpl; auto.
  Qed.

  Lemma M_break_M_on_some_option_map :
    forall {A n S O}
           (a    : hoption A)
           (sm   : A -> M_n n (hoption S))
           (subs : n_procs n)
           (F    : n_procs n -> hoption S -> hoption O),
      (forall subs', F subs' halt_local = halt_local)
      -> (forall subs', F subs' halt_global = halt_global)
      -> M_break
           (a >>o>> sm)
           subs
           F
         = map_hoption
             (fun a => M_break (sm a) subs F)
             a.
  Proof.
    introv impl impg.
    unfold hoption_map, map_hoption, M_break, M_on_some, ret.
    destruct a; auto.
  Qed.

  Lemma M_break_ret :
    forall {n A O}
           (a    : A)
           (subs : n_procs n)
           (F    : n_procs n -> A -> O),
      M_break
        (ret _ a)
        subs
        F
      = F subs a.
  Proof.
    auto.
  Qed.
  Hint Rewrite @M_break_ret : comp.

  Definition bind_some_ret_some :
    forall {n} {A B} (a : A) (f : A -> M_n n (hoption B)),
      ((ret n (hsome a)) >>o= f) = f a.
  Proof.
    introv.
    apply functional_extensionality; introv; simpl.
    unfold bind_some, bind; simpl.
    destruct (f a x); auto.
  Qed.
  Hint Rewrite @bind_some_ret_some : comp.

  Definition bind_some_ret_some_fun :
    forall {n} {T A B} (f : A -> M_n n (hoption B)) (F : T -> A),
      (fun a => ((ret n (hsome (F a))) >>o= f)) = fun x => f (F x).
  Proof.
    introv.
    apply functional_extensionality; introv; simpl; autorewrite with comp; auto.
  Qed.
  Hint Rewrite @bind_some_ret_some_fun : comp.

  Lemma bind_bind_some :
    forall {n} {A B C} (m : M_n n A) (f : A -> M_n n (hoption B)) (g : B -> M_n n (hoption C)),
      ((m >>= f) >>o= g)
      = (m >>= (fun a => ((f a) >>o= g))).
  Proof.
    introv; apply functional_extensionality; introv; simpl.
    unfold bind_some, bind, M_on_some; simpl.
    destruct (m x).
    destruct (f a n0).
    destruct h; simpl; auto.
    destruct (g s n1); auto.
  Qed.

  Lemma M_break_bind_some :
    forall {n A B O}
           (a    : M_n n (hoption A))
           (G    : A -> M_n n (hoption B))
           (subs : n_procs n)
           (F    : n_procs n -> hoption B -> hoption O),
      (forall subs, F subs halt_local = halt_local)
      -> (forall subs, F subs halt_global = halt_global)
      -> M_break
           (a >>o= G)
           subs
           F
         = M_break
             a
             subs
             (fun subs' (aop : hoption A) =>
                map_hoption
                  (fun (a : A) => M_break (G a) subs' F)
                  aop).
  Proof.
    introv impl impg.
    unfold M_break, bind_some, bind, M_on_some; simpl.
    destruct (a subs); auto.
    destruct h; simpl; auto.
    destruct (G s n0); auto.
  Qed.

  Lemma M_break_bind_some_ret :
    forall {n A B O}
           (a    : M_n n (hoption A))
           (G    : A -> hoption B)
           (subs : n_procs n)
           (F    : n_procs n -> hoption B -> hoption O),
      (forall subs, F subs halt_local = halt_local)
      -> (forall subs, F subs halt_global = halt_global)
      -> M_break
           (a >>o= fun p => ret _ (G p))
           subs
           F
         = M_break
             a
             subs
             (fun subs' aop => map_hoption (fun a => F subs' (G a)) aop).
  Proof.
    introv impl impg.
    rewrite M_break_bind_some; auto.
  Qed.

  Ltac auto_rw_bind :=
    repeat (repeat (first [rewrite bind_bind
                          |rewrite bind_bind_some
                          ]
                   );
            repeat (first [rewrite M_break_bind_ret;[|simpl;tcsp];[]
                          |rewrite M_break_bind_some_ret;[|simpl;tcsp];[]
                          ]
                   );
            autorewrite with comp;
            simpl;
            auto).

  Definition bind_some_ret_some_fun2 :
    forall {n} {T A B} (f : T -> A -> M_n n (hoption B)) (F : T -> A),
      (fun a => ((ret n (hsome (F a))) >>o= f a)) = fun x => (f x) (F x).
  Proof.
    introv.
    apply functional_extensionality; introv; simpl; autorewrite with comp; auto.
  Qed.
  Hint Rewrite @bind_some_ret_some_fun2 : comp.

  Lemma M_on_sm_bind_ret_const :
    forall {n cn A B}
           (sm : n_proc n cn)
           (f  : n_proc_at (sm2level sm) cn -> M_n (sm2level sm) A)
           (g  :  A -> B),
      M_on_sm sm (fun x => (f x) >>= (fun y => ret _ (g y)))
      = ((M_on_sm sm f) >>= fun y => ret _ (g y)).
  Proof.
    induction n; introv; simpl; tcsp; destruct sm; simpl; auto.

    { unfold M_on_decr, bind; simpl.
      apply functional_extensionality; introv; simpl.
      destruct (f a (decr_n_procs x)); auto. }

    rewrite IHn.
    unfold M_on_decr, bind; simpl.
    apply functional_extensionality; introv; simpl.
    destruct (M_on_sm b f (decr_n_procs x)); auto.
  Qed.
  Hint Rewrite @M_on_sm_bind_ret_const : comp.

(*  Lemma M_break_map_option_M_on_sm_ret_None :
    forall {n cn A B}
           (sm : n_proc n cn)
           subs
           (f : n_procs n -> A -> option B),
      M_break (M_on_sm sm (fun x => ret _ None)) subs (fun subs' x => map_option (f subs') x)
      = None.
  Proof.
    induction n; introv; simpl; tcsp; destruct sm; simpl; auto.
    unfold M_break, M_on_decr in *; simpl in *.
    pose proof (IHn _ _ _ b (decr_n_procs subs) (fun ps a => f (incr_n_procs ps) a)) as IHn.
    dest_cases w; auto.
    destruct w1; simpl in *; auto.
  Qed.
  Hint Rewrite @M_break_map_option_M_on_sm_ret_None : comp.*)

  Lemma M_run_ls_on_event_unroll :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_run_ls_on_event ls e
      = if dec_isFirst e
        then M_run_ls_on_this_one_event ls e
        else
          map_option
            (fun ls => M_run_ls_on_this_one_event ls e)
            (M_run_ls_before_event ls e).
  Proof.
    introv.
    unfold M_run_ls_on_event; simpl.
    destruct (dec_isFirst e); simpl.
    { unfold M_run_ls_before_event.
      rewrite isFirst_implies_localPreds_eq; simpl; auto. }
    remember (M_run_ls_before_event ls e) as x; destruct x; simpl; auto.
  Qed.

  Lemma M_on_some_ret_some :
    forall {n A} (a : hoption A),
      (a >>o>> fun a => ret n (hsome a))
      = ret _ a.
  Proof.
    destruct a; simpl; auto.
  Qed.
  Hint Rewrite @M_on_some_ret_some : comp.

  Lemma M_on_some_ret_some_fun :
    forall {n A B} (F : B -> hoption A),
      (fun x => F x >>o>> fun a => ret n (hsome a))
      = fun x => ret _ (F x).
  Proof.
    introv; apply functional_extensionality; introv; autorewrite with comp; auto.
  Qed.
  Hint Rewrite @M_on_some_ret_some_fun : comp.

  Lemma eq_bind :
    forall {A B} {n:nat} (m : M_n n A) (f g : A -> M_n n B),
      (forall a, f a = g a)
      -> (m >>= f) = (m >>= g).
  Proof.
    introv imp; apply functional_extensionality; introv; unfold bind; simpl; auto.
    destruct (m x); auto.
    rewrite imp; auto.
  Qed.

  Lemma eq_M_on_some :
    forall {A B} {n:nat} (m : hoption A) (f g : A -> M_n n (hoption B)),
      (forall a, f a = g a)
      -> (m >>o>> f) = (m >>o>> g).
  Proof.
    introv imp; apply functional_extensionality; introv; unfold M_on_some; simpl; auto.
    destruct m; auto.
    rewrite imp; auto.
  Qed.

  Lemma M_on_some_bind_M_on_some :
    forall {n A B C}
           (xop : hoption A)
           (f : A -> M_n n (hoption B))
           (g : B -> M_n n (hoption C)),
      ((xop >>o>> f) >>= fun x => x >>o>> g)
      = (xop >>o>> fun a => f a >>= fun y => y >>o>> g).
  Proof.
    introv.
    apply functional_extensionality; introv; simpl.
    destruct xop; simpl; auto.
  Qed.

  Lemma M_break_M_op_state :
    forall {n} {nm} {S} {O}
           (upd  : M_Update n nm S)
           (s    : S)
           (i    : hoption (PosDTime * cio_I (fio nm)))
           (subs : n_procs n)
           (F    : n_procs n -> _ -> hoption O),
      (forall subs', F subs' halt_local = halt_local)
      -> (forall subs', F subs' halt_global = halt_global)
      -> M_break
           (M_op_state upd s i)
           subs
           F
         = map_hoption
             (fun i => M_break (upd s (fst i) (snd i)) subs (fun subs' s => F subs' (fst s)))
             i.
  Proof.
    introv impl impg.
    unfold M_break; destruct i; repnd; simpl; auto.
    unfold bind; simpl.
    destruct (upd s s1 s0 subs); auto.
  Qed.

  Lemma bind_some_bind_M_on_some :
    forall {n} {A B C}
           (m : M_n n (hoption A))
           (f : A -> M_n n (hoption B))
           (g : B -> M_n n (hoption C)),
      ((m >>o= f) >>= (fun b => b >>o>> g))
      = (m >>o= fun a => (f a) >>= fun b => b >>o>> g).
  Proof.
    introv; apply functional_extensionality; introv; simpl.
    unfold bind_some, bind, M_on_some; simpl.
    destruct (m x).
    destruct h; simpl; auto.
    destruct (f s n0).
    destruct h; simpl; auto.
    destruct (g s0 n1); auto.
  Qed.

  Lemma bind_some_bind_some :
    forall {n A B C}
           (a : M_n n (hoption A))
           (f : A -> M_n n (hoption B))
           (g : B -> M_n n (hoption C)),
      ((a >>o= f) >>o= g)
      = (a >>o= (fun a => (f a) >>o= g)).
  Proof.
    introv; unfold bind_some.
    rewrite bind_bind.
    apply eq_bind; introv.
    rewrite M_on_some_bind_M_on_some; auto.
  Qed.

  Lemma M_on_some_bind_some :
    forall {n A B C}
           (a : hoption A)
           (f : A -> M_n n (hoption B))
           (g : B -> M_n n (hoption C)),
      ((a >>o>> f) >>o= g)
      = (a >>o>> (fun a => (f a) >>o= g)).
  Proof.
    introv; unfold M_on_some, bind_some.
    destruct a; simpl; auto.
  Qed.

  Lemma eq_bind_some :
    forall {A B} {n:nat} (m : M_n n (hoption A)) (f g : A -> M_n n (hoption B)),
      (forall a, f a = g a)
      -> (m >>o= f) = (m >>o= g).
  Proof.
    introv imp; apply functional_extensionality; introv.
    unfold bind_some, bind, M_on_some; simpl; auto.
    destruct (m x); auto.
    destruct h; simpl; auto.
    rewrite imp; auto.
  Qed.

(*  Lemma M_run_update_on_list_snoc :
    forall {S} {n} {nm}
           (upd : M_Update n nm S)
           (l : oplist (cio_I (fio nm)))
           (s : S)
           (x : option (cio_I (fio nm))),
      M_run_update_on_list s upd (snoc l x)
      = ((M_run_update_on_list s upd l)
           >>o= fun s => M_op_state upd s x).
  Proof.
    induction l; introv; simpl; auto.

    {
      destruct x; simpl; auto.
      autorewrite with comp; auto.
    }

    destruct a; auto;[]; autorewrite with comp.
    auto_rw_bind.
    apply eq_bind; introv.
    rewrite M_on_some_bind_some.
    apply eq_M_on_some; introv; auto.
  Qed.*)

  Lemma M_run_ls_on_op_inputs_snoc :
    forall {L S}
           (ls : LocalSystem L S)
           {cn}
           (i  : option (PosDTime * cio_I (fio cn)))
           (l  : oplist (PosDTime * cio_I (fio cn))),
      M_run_ls_on_op_inputs ls cn (snoc l i)
      = on_some
          (M_run_ls_on_op_inputs ls cn l)
          (fun ls' => option_map (fun x => M_run_ls_on_input_ls ls' cn (fst x) (snd x)) i).
  Proof.
    introv; revert ls; induction l; introv; simpl; auto.
    unfold on_some.
    rewrite map_option_map_option.
    destruct a; simpl in *; auto.
    rewrite IHl; auto.
  Qed.

  Lemma M_run_ls_on_inputs_snoc :
    forall {L S}
           (ls : LocalSystem L S)
           {cn}
           (t  : PosDTime)
           (i  : cio_I (fio cn))
           (l  : list (PosDTime * cio_I (fio cn))),
      M_run_ls_on_inputs ls cn (snoc l (t,i))
      = let ls' := M_run_ls_on_inputs ls cn l
        in M_run_ls_on_input_ls ls' cn t i.
  Proof.
    introv; revert ls; induction l; introv; simpl; auto.
  Qed.

  Lemma option_map_time_trigger_op :
    forall {S B} {eo : EventOrdering} (e : Event)
           (F : (PosDTime * cio_I (fio (msg_comp_name S))) -> B),
      option_map F (time_trigger_op e)
      = option_map (fun i => F (time e, i)) (trigger_op e).
  Proof.
    introv.
    unfold time_trigger_op, trigger_op; auto.
    destruct (trigger e); simpl; auto.
  Qed.

  Lemma M_run_ls_before_event_unroll :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_run_ls_before_event ls e
      = if dec_isFirst e
        then Some ls
        else map_option
               (fun ls => M_run_ls_on_this_one_event ls (local_pred e))
               (M_run_ls_before_event ls (local_pred e)).
  Proof.
    introv.
    unfold M_run_ls_before_event.
    destruct (dec_isFirst e) as [d|d].

    { rewrite isFirst_implies_localPreds_eq; simpl; auto. }

    rewrite (localPreds_unroll e) at 1; auto; simpl.
    rewrite map_snoc; simpl.
    rewrite M_run_ls_on_op_inputs_snoc.

    unfold on_some, map_option; dest_cases w.
    rewrite option_map_time_trigger_op; auto.
  Qed.

  Lemma M_run_ls_before_event_as_M_run_ls_on_event_pred :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      ~ isFirst e
      -> M_run_ls_before_event ls e = M_run_ls_on_event ls (local_pred e).
  Proof.
    introv ni.
    rewrite M_run_ls_on_event_unroll.
    rewrite M_run_ls_before_event_unroll.

    destruct (dec_isFirst e) as [d1|d1]; tcsp;[].
    destruct (dec_isFirst (local_pred e)) as [d2|d2]; tcsp;[].

    rewrite M_run_ls_before_event_unroll.
    destruct (dec_isFirst (local_pred e)); tcsp; GC.
  Qed.

  Lemma M_run_ls_before_event_unroll_on :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_run_ls_before_event ls e
      = if dec_isFirst e
        then Some ls
        else M_run_ls_on_event ls (local_pred e).
  Proof.
    introv.
    destruct (dec_isFirst e) as [d|d];
      [|apply M_run_ls_before_event_as_M_run_ls_on_event_pred;auto].
    rewrite M_run_ls_before_event_unroll.
    destruct (dec_isFirst e); tcsp.
  Qed.

  Lemma M_state_sys_before_event_as_M_state_sys_on_event_pred :
    forall {F}
           (sys : M_USystem F)
           {eo  : EventOrdering}
           (e   : Event)
           (cn  : CompName),
      ~ isFirst e
      -> M_state_sys_before_event sys e cn = M_state_sys_on_event sys (local_pred e) cn.
  Proof.
    introv nfst.
    unfold M_state_sys_on_event.
    unfold M_state_sys_before_event.
    autorewrite with eo.
    unfold M_state_ls_on_event.
    unfold M_state_ls_before_event.
    rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred; auto.
  Qed.

  Lemma M_state_sys_before_event_if_on_event_direct_pred :
    forall {cn  : CompName}
           {eo : EventOrdering}
           (e1 e2 : Event)
           {F}
           (sys : M_USystem F)
           (s   : sf cn),
      e1 ⊂ e2
      -> M_state_sys_on_event sys e1 cn = Some s
      -> M_state_sys_before_event sys e2 cn = Some s.
  Proof.
    introv lte eqst.
    applydup pred_implies_local_pred in lte; subst.
    rewrite M_state_sys_before_event_as_M_state_sys_on_event_pred; eauto 2 with eo.
  Qed.
  Hint Resolve M_state_sys_before_event_if_on_event_direct_pred : proc.

  Lemma M_state_sys_before_event_unfold :
    forall {F}
           (sys : M_USystem F)
           {eo  : EventOrdering}
           (e   : Event)
           (cn  : CompName),
      M_state_sys_before_event sys e cn
      = map_option
          (state_of_component cn)
          (M_run_ls_before_event (sys (loc e)) e).
  Proof.
    tcsp.
  Qed.

  Lemma M_state_sys_on_event_unfold :
    forall {F}
           (sys : M_USystem F)
           {eo  : EventOrdering}
           (e   : Event)
           (cn  : CompName),
      M_state_sys_on_event sys e cn
      = map_option
          (state_of_component cn)
          (M_run_ls_on_event (sys (loc e)) e).
  Proof.
    tcsp.
  Qed.

  Lemma M_run_ls_before_event_is_first :
    forall {L S} {eo : EventOrdering} (e : Event) (ls : LocalSystem L S),
      isFirst e
      -> M_run_ls_before_event ls e = Some ls.
  Proof.
    introv isf.
    unfold M_run_ls_before_event;simpl.
    rewrite isFirst_implies_localPreds_eq; auto; simpl.
  Qed.

  Lemma M_state_sys_on_event_unfold_before :
    forall {F}
           (sys : M_USystem F)
           {eo  : EventOrdering}
           (e   : Event)
           (cn  : CompName),
      M_state_sys_on_event sys e cn
      = map_option
          (fun ls => map_option
                       (state_of_component cn)
                       (M_run_ls_on_this_one_event ls e))
          (M_run_ls_before_event (sys (loc e)) e).
  Proof.
    introv.
    unfold M_state_sys_on_event.
    unfold M_state_ls_on_event.
    rewrite M_run_ls_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; tcsp.

    { rewrite M_run_ls_before_event_is_first; auto. }

    unfold map_option.
    remember (M_run_ls_before_event (sys (loc e)) e) as xx; destruct xx; auto.
  Qed.


(*  Lemma state_sm_on_event_unroll2 :
    forall (sys : M_USystem)
           {eo  : EventOrdering}
           (e   : Event)
           (cn  : CompName),
      M_state_sys_on_event sys e cn
      = map_option
          (fun s => op_state sm s (trigger e) (time e))
          (M_state_sys_before_event sys e cn).
  Proof.
    introv.
    rewrite <- ite_first_state_sm_on_event_as_before.
    unfold ite_first.
    rewrite state_sm_on_event_unroll.
    destruct (dec_isFirst e); simpl; auto.
  Qed.*)

  (* *** END *** *)
  (******************************************)



  Definition remove_proc
             (cn : CompName)
             {n} {A}
             (x : M_n n A) : M_n n A :=
    fun ps => x (remove_name ps cn).

  Definition spawn_proc
             {n}
             (p : n_nproc n)
             {A}
             (x : M_n n A) : M_n n A :=
    fun ps => x (p :: ps).

  Definition spawn_proc_once
             {n}
             (p : n_nproc n)
             {A}
             (x : M_n n A) : M_n n A :=
    fun ps => x (match find_name (pp_name p) ps with
                 | Some _ => ps
                 | None => p :: ps
                 end).



  (******************************************)
  (* ====== A ====== *)
  Definition Aname : CompName := MkCN "NAT" 2 false.
  Definition A_update : M_Update 0 Aname _ :=
    fun (s : nat) (t : PosDTime) (i : nat) =>
        (ret _ (hsome (s + i), s + i)).
  Definition A : n_proc 1 _ := build_m_sm A_update 0.

  (* ====== B ====== *)
  Definition Bname : CompName := MkCN "NAT" 3 false.
  Definition B_update : M_Update 1 Bname _ :=
    fun s t i =>
      spawn_proc_once
        (MkPProc _ A)
        (*remove_proc Aname*)
        ((call_proc Aname t i)
           >>= fun out =>
                 ret _ (hsome (s + out + 1), s + out + 1)).
  Definition B : n_proc _ _ := build_m_sm B_update 0.

  (* ====== C ====== *)
  Definition Cname : CompName := MkCN "NAT" 4 false.
  Definition C_update : M_Update 2 Cname _ :=
    fun s t i =>
      (call_proc Bname t i)
        >>= fun out1 =>
              (call_proc Bname t i)
                >>= fun out2 =>
                      ret _ (hsome (s + out1 + out2 + 2), s + out1 + out2 + 2).
  Definition C : n_proc _ _ := build_m_sm C_update 0.

  (* ====== Main ====== *)
  Definition Mname : CompName := MkCN "NAT" 5 false.
  Definition M_update : M_Update 3 Mname nat :=
    fun s t i =>
      (call_proc Cname t i)
        >>= (fun out => ret _ (hsome s, out)).
  Definition M : n_proc _ _ := build_m_sm M_update 0.


  (* ====== Local System ====== *)

  Definition ex_ls : LocalSystem 4 5 :=
    [
      (*MkPProc _ (incr_n_proc (incr_n_proc (incr_n_proc A))),*)
      MkPProc _ (incr_n_proc (incr_n_proc B)),
      MkPProc _ (incr_n_proc C),
      MkPProc _ M
    ].


  Definition ex_test1 := M_run_ls_on_input_out ex_ls Mname pdt0 17.
  Eval compute in (ex_test1 = Some 73).

  Definition ex_test2 := let ls := M_run_ls_on_input_ls ex_ls Mname pdt0 17 in
                         M_run_ls_on_input_out ls Mname pdt0 17.
  Eval compute in (ex_test2 = Some 354).
  (******************************************)




  (***************************)

(*  Definition M_output_sm_on_event {n} {k}
             (sm : n_proc n (main_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (option DirectedMsgs) :=
    (M_run_sm_on_event sm e)
      >>o= fun x => ret _ (Some (snd x)).*)

(*  Definition system2level
             {eo : EventOrdering}
             (e  : Event) : nat := fls_level (loc e).*)

(*  Definition system2space
             {eo : EventOrdering}
             (e  : Event) : nat := fls_space (loc e).*)

  Definition system2local
             {eo  : EventOrdering}
             (e   : Event)
             {F}
             (sys : M_USystem F)
    : LocalSystem (fls_level F (loc e)) (fls_space F (loc e)) :=
    sys (loc e).

(*  Fixpoint app_m_proc_to_subs {n} {nm}
    : n_proc n nm -> M_n (pred n) (n_proc n nm) :=
    match n return n_proc n nm -> M_n (pred n) (n_proc n nm) with
    | 0 => fun pr ps => (ps, pr)
    | S m =>
      fun pr =>
        match pr with
        | inl sm => fun ps => lift_M sm ps
        | inr pr' => fun ps => (ps,pr) (*lift_M2 (app_m_proc_to_subs pr')*)
        end
    end.*)

(*  Definition system2main_local
             {eo  : EventOrdering}
             (e   : Event)
             (sys : M_USystem) (*: n_proc (S (system2level e sys)) msg_comp_name*) :=
    let local := sys (loc e) in
    ls_main local (ls_subs local).*)




(*
  Definition system2main_local
             {eo  : EventOrdering}
             (e   : Event)
             (sys : M_USystem) : n_proc (S (system2level e sys)) (msg_comp_name (system2space e sys)) :=
    ls_main (sys (loc e)).

  Definition MM_run_system_on_event_sm
             (sys : M_USystem)
             {eo  : EventOrdering}
             (e   : Event)
    : M_n (sm2level (system2main_local e sys))
          (option (option (sf (msg_comp_name (system2space e sys))) * DirectedMsgs)) :=
    M_run_sm_on_event (system2main_local e sys) e.

  Definition M_run_system_on_event_sm
             (sys : M_USystem)
             {eo  : EventOrdering}
             (e   : Event)
    : n_procs (sm2level (system2main_local e sys))
      * (option (option (sf (msg_comp_name (system2space e sys))) * DirectedMsgs)) :=
    MM_run_system_on_event_sm sys e (ls_subs (sys (loc e))).

  Definition MM_output_system_on_event
             (sys : M_USystem)
             {eo  : EventOrdering}
             (e   : Event) : M_n (sm2level (system2main_local e sys)) (option DirectedMsgs) :=
    (MM_run_system_on_event_sm sys e)
      >>= fun x =>
            match x with
            | Some (sm',msgs) => ret _ (Some msgs)
            | None => ret _ None
            end.

  Definition M_output_system_on_event
             (sys : M_USystem)
             {eo  : EventOrdering}
             (e   : Event) : option DirectedMsgs :=
    snd (MM_output_system_on_event sys e (ls_subs (sys (loc e)))).

  (* apply history with last event *)
  Definition MM_output_system_on_event_ldata
             (sys : M_USystem)
             {eo  : EventOrdering}
             (e   : Event) : M_n (sm2level (system2main_local e sys)) DirectedMsgs :=
    (MM_output_system_on_event sys e)
      >>= fun x =>
            match x with
            | Some msgs => ret _ msgs
            | None => ret _ []
            end.

  Definition M_output_system_on_event_ldata
             (sys : M_USystem)
             {eo  : EventOrdering}
             (e   : Event) : DirectedMsgs :=
    snd (MM_output_system_on_event_ldata sys e (ls_subs (sys (loc e)))).

  Definition M_state_system_on_event
             (sys : M_USystem)
             {eo  : EventOrdering}
             (e   : Event)
    : n_procs (sm2level (system2main_local e sys))
      * option (sf (msg_comp_name (system2space e sys))) :=
    M_state_sm_on_event (system2main_local e sys) e (ls_subs (sys (loc e))).

  Definition M_state_system_on_event_main
             (sys : M_USystem)
             {eo  : EventOrdering}
             (e   : Event)
    : option (sf (msg_comp_name (system2space e sys))) :=
    snd (M_state_system_on_event sys e).
*)



  (* ============== Constraint on types of states ============== *)

(*  Definition StateConstraint := CompName -> option Type.

  Fixpoint sm_satisfies_type_constraint (T : Type) {n : nat} {nm : CompName} : n_proc n nm -> Prop :=
    match n with
    | 0 => fun sm => True
    | S n =>
      fun sm =>
        match sm with
        | inl x => sm_S x = T
        | inr x => sm_satisfies_type_constraint T x
        end
    end.

  Definition nsm_satisfies_type_constraint (C : StateConstraint) {n : nat} (nsm : {cn : CompName & n_proc n cn}) : Prop :=
    let (name, sm) := nsm in
    match C name with
    | Some T => sm_satisfies_type_constraint T sm
    | None => True
    end.

  Definition local_system_satisfies_type_constraint (C : StateConstraint) (sys : LocalSystem) :=
    forall sm, In sm (ls_subs sys) -> nsm_satisfies_type_constraint C sm.

  Definition system_satisfies_type_constraint (C : StateConstraint) (sys : M_USystem) :=
    forall n, local_system_satisfies_type_constraint C (sys n).


  Definition is_key_name (name : CompName) : bool :=
    if CompNameKindDeq (comp_name_kind name) key_comp_name_kind
    then true
    else false.

  (*Definition key_state_constraint : StateConstraint :=
    fun n => if is_key_name n then Some local_key_map else None.*)

  Definition sm_key_constraint {n : nat} {nm : CompName} : n_proc n nm -> Prop :=
    sm_satisfies_type_constraint local_key_map.

  Definition nsm_key_constraint {n : nat} (nsm : {cn : CompName & n_proc n cn}) : Prop :=
    let (name, sm) := nsm in
    if CompNameKindDeq (comp_name_kind name) key_comp_name_kind
    then sm_key_constraint sm
    else True.

  Definition local_system_key_constraint (sys : LocalSystem) :=
    forall sm, In sm (ls_subs sys) -> nsm_key_constraint sm.

  Definition system_key_constraint (sys : M_USystem) :=
    forall n, local_system_key_constraint (sys n).*)

  (* ==============  ==============  ============== *)



  Definition find_state_machine_with_name {n}
             (L  : n_procs n)
             (cn : CompName) : option (sf cn) :=
    state_of_component cn L.

(*  Definition M_state_system_on_event_sub
           (sys : M_USystem)
           {eo  : EventOrdering}
           (e   : Event)
           (cn  : CompName) : option (sf cn) :=
    find_state_machine_with_name (fst (M_state_system_on_event sys e)) cn.*)

  Definition pbind {A} {n:nat} (m : M_n n A) (f : A -> M_n n Prop) : Prop :=
    forall s,
      let (s1,a) := m s in
      let (s2,b) := f a s1 in
      b.
  Notation "a >p>= f" := (pbind a f) (at level 80).

  (*Open Scope eo.*)

  (*Definition AXIOM_M_authenticated_messages_were_sent_or_byz
             (sys : M_USystem)
             (F : forall (eo : EventOrdering) (e : Event), M_n (sm2level (system2main_local e sys)) DirectedMsgs) :=
    forall {eo : EventOrdering} e (a : AuthenticatedData),
      In a (bind_op_list get_contained_authenticated_data (trigger e))
      (* if we didn't verify the message then it could come from a Byzantine
         node that is impersonating someone else, without the logic knowing it *)
      -> verify_authenticated_data (loc e) a (keys e) = true
      -> exists e',
        e' ≺ e (* event e was triggered by an earlier send event e' *)

        (* e' generated the authentication code *)
        (* QUESTION: Should we say instead that the message was authenticated
           using a subset of the keys? *)
        /\ am_auth a = authenticate (am_data a) (keys e')

        /\
        (
          (
            exists m dst delay,

              In a (get_contained_authenticated_data m)

              /\
              (* e' sent the message to some node "dst"
                 following the protocol as described by F
                 (only if the message is the message is internal though),
                 which eventually got to e *)
              (is_protocol_message m = true
               -> ((F eo e') >p>= (fun msgs => ret _ (In (MkDMsg m dst delay) msgs))))

              /\
              (* e' is the node mentioned in the authenticated message *)
              data_auth (loc e) (am_data a) = Some (loc e')
          )

          \/

          (* e' is not the node mentioned in the authenticated message
             because he got the keys of some other e''
           *)
          (
            exists e'',
              e'' ≼ e'
              /\
              (* e' is byzantine because it's using the keys of e'' *)
              isByz e'
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
        ).*)

(*  Definition AXIOM_M_correct_keys {n}
             (sm : name -> n_proc n msg_comp_name)
             (K  : forall (i : name), sm2S (sm i) -> local_key_map)
             (eo : EventOrdering) : Prop :=
    forall (e : Event) (i : name) st,
      has_correct_trace_before e i
      -> M_state_sm_before_event (sm i) e = st
      -> st >p>= (fun sop => match sop with
                             | Some s => ret _ (keys e = K i s)
                             | None => ret _ True
                             end).*)


  Definition sub_sending_key (sk1 sk2 : DSKey) : Prop :=
    subset (dsk_dst sk1) (dsk_dst sk2) /\ dsk_key sk1 = dsk_key sk2.

  Definition sub_sending_keys (l1 l2 : list DSKey) : Prop :=
    forall sk1,
      In sk1 l1
      ->
      exists sk2,
        In sk2 l2
        /\ sub_sending_key sk1 sk2.

  Definition sub_receiving_key (rk1 rk2 : DRKey) : Prop :=
    subset (drk_dst rk1) (drk_dst rk2) /\ drk_key rk1 = drk_key rk2.

  Definition sub_receiving_keys (l1 l2 : list DRKey) : Prop :=
    forall rk1,
      In rk1 l1
      ->
      exists rk2,
        In rk2 l2
        /\ sub_receiving_key rk1 rk2.

  Definition sub_local_key_map (k1 k2 : local_key_map) : Prop :=
    sub_sending_keys (lkm_sending_keys k1) (lkm_sending_keys k2)
    /\ sub_receiving_keys (lkm_receiving_keys k1) (lkm_receiving_keys k2).

  Lemma sub_local_key_map_preserves_in_lookup_receiving_keys :
    forall ks1 ks2 x n,
      sub_local_key_map ks1 ks2
      -> In x (lookup_receiving_keys ks1 n)
      -> In x (lookup_receiving_keys ks2 n).
  Proof.
    introv sub i.
    unfold lookup_receiving_keys in *; allrw in_map_iff; exrepnd; subst.
    unfold lookup_drkeys in *.
    allrw @filter_In; repnd; dest_cases x; GC.
    apply sub in i1; exrepnd.
    unfold sub_receiving_key in *; repnd.
    exists rk2; dands; auto.
    apply filter_In; dands; auto; dest_cases y.
  Qed.
  Hint Resolve sub_local_key_map_preserves_in_lookup_receiving_keys : eo.

  Lemma verify_authenticated_data_if_sub_keys :
    forall (ks1 ks2 : local_key_map) n a,
      sub_local_key_map ks1 ks2
      -> verify_authenticated_data n a ks1 = true
      -> verify_authenticated_data n a ks2 = true.
  Proof.
    introv sub verif.
    unfold verify_authenticated_data in *.
    remember (data_auth n a) as da; symmetry in Heqda; destruct da; ginv.
    unfold verify_authenticated_data_keys in *.
    allrw existsb_exists; exrepnd.
    exists x; dands; auto; eauto 3 with eo.
  Qed.
  Hint Resolve verify_authenticated_data_if_sub_keys : eo.

  Lemma local_happened_before_implies_history_app :
    forall {eo : EventOrdering} (e1 e2 : Event),
      e1 ⊑ e2
      -> exists l, History(e2) = History(e1) ++ l.
  Proof.
    intros eo e1.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv lte.
    apply localHappenedBeforeLe_implies_or2 in lte; repndors; subst.

    { exists ([] : list Event); autorewrite with list; auto. }

    apply local_implies_pred_or_local in lte; repndors; exrepnd.

    { applydup pred_implies_not_first in lte.
      rewrite (localPreds_unroll e2); auto.
      exists [local_pred e2].
      rewrite snoc_as_app; f_equal; f_equal.
      unfold local_pred; rewrite lte; auto. }

    pose proof (ind e) as ind; repeat (autodimp ind hyp); eauto 3 with eo; exrepnd.
    applydup pred_implies_not_first in lte1.
    rewrite (localPreds_unroll e2); auto.
    unfold local_pred; rewrite lte1.
    rewrite ind0.
    exists (snoc l e).
    rewrite app_snoc; auto.
  Qed.

(*  Lemma M_run_update_on_list_app :
    forall {S} {n} {nm}
           (upd : M_Update n nm S)
           (l k : oplist (cio_I (fio nm)))
           (s : S),
      M_run_update_on_list s upd (l ++ k)
      = ((M_run_update_on_list s upd l)
           >>o= fun s => M_run_update_on_list s upd k).
  Proof.
    induction l; introv; simpl; auto; autorewrite with comp in *; auto;[].
    rewrite M_on_some_bind_some.
    apply eq_M_on_some; introv.
    rewrite bind_bind_some.
    apply eq_bind; introv.
    rewrite M_on_some_bind_some.
    apply eq_M_on_some; introv; auto.
  Qed.*)

  Lemma local_happened_before_implies_history_app2 :
    forall {eo : EventOrdering} (e1 e2 : Event),
      e1 ⊏ e2
      -> exists l, History(e2) = History(e1) ++ e1 :: l.
  Proof.
    intros eo e1.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv lte.

    apply local_implies_pred_or_local in lte; repndors; exrepnd.

    { applydup pred_implies_not_first in lte.
      rewrite (localPreds_unroll e2); auto.
      exists ([] : list Event).
      unfold local_pred.
      rewrite lte.
      rewrite snoc_as_app; auto. }

    pose proof (ind e) as ind; repeat (autodimp ind hyp); eauto 3 with eo; exrepnd.
    applydup pred_implies_not_first in lte1.
    rewrite (localPreds_unroll e2); auto.
    unfold local_pred; rewrite lte1.
    rewrite ind0.
    exists (snoc l e).
    rewrite <- snoc_cons.
    rewrite app_snoc; auto.
  Qed.

(*  Lemma M_on_some_bind_M_on_some_fun :
    forall {n A B C}
           (f : A -> M_n n (option B))
           (g : B -> M_n n (option C)),
      (fun xop => (xop >>o>> f) >>= fun x => x >>o>> g)
      = (fun xop => xop >>o>> fun a => f a >>= fun y => y >>o>> g).
  Proof.
    introv; apply functional_extensionality; introv; simpl.
    apply M_on_some_bind_M_on_some.
  Qed.*)

(*  Lemma M_run_update_on_list_snoc_fun :
    forall {S} {n} {nm}
           (upd : M_Update n nm S)
           (l : oplist (cio_I (fio nm)))
           (x : option (cio_I (fio nm))),
      (fun s => M_run_update_on_list s upd (snoc l x))
      = (fun s => (M_run_update_on_list s upd l)
                    >>o= fun s => M_op_state upd s x).
  Proof.
    introv; apply functional_extensionality; introv.
    apply M_run_update_on_list_snoc.
  Qed.*)

  Definition similar_sms_at {cn} {k} (p1 p2 : n_proc_at k cn) : Prop :=
    sm_update p1 = sm_update p2.

  Lemma similar_sms_at_refl :
    forall cn k (p : n_proc_at k cn),
      similar_sms_at p p.
  Proof.
    introv; split; auto.
  Qed.
  Hint Resolve similar_sms_at_refl : comp.

  Lemma similar_sms_at_sym :
    forall cn k (p1 p2 : n_proc_at k cn),
      similar_sms_at p1 p2
      -> similar_sms_at p2 p1.
  Proof.
    introv h; unfold similar_sms_at in *; tcsp.
  Qed.
  Hint Resolve similar_sms_at_sym : comp.

  Lemma similar_sms_at_trans :
    forall cn k (p1 p2 p3 : n_proc_at k cn),
      similar_sms_at p1 p2
      -> similar_sms_at p2 p3
      -> similar_sms_at p1 p3.
  Proof.
    introv h q; unfold similar_sms_at in *; repnd; dands; try congruence.
  Qed.
  Hint Resolve similar_sms_at_trans : comp.

  Fixpoint similar_sms {cn} {k} : n_proc k cn -> n_proc k cn -> Prop :=
    match k with
    | 0 => fun sm1 sm2 => False
    | S n =>
      fun sm1 sm2 =>
        match sm1, sm2 with
        | sm_or_at p1, sm_or_at p2 => similar_sms_at p1 p2
        | sm_or_sm p1, sm_or_sm p2 => similar_sms p1 p2
        | _, _ => False
        end
    end.

  Inductive similar_procs : forall {n m}, n_nproc n -> n_nproc m -> Prop :=
  | sim_procs :
      forall {k cn} (p1 : n_proc k cn) (p2 : n_proc k cn),
        similar_sms p1 p2
        -> similar_procs (MkPProc cn p1) (MkPProc cn p2).
  Hint Constructors similar_procs.

  Inductive similar_subs {n m} : n_procs n -> n_procs m -> Prop :=
  | sim_subs_nil : similar_subs [] []
  | sim_subs_cons :
      forall (p1   : n_nproc n)
             (p2   : n_nproc m)
             (ps1  : n_procs n)
             (ps2  : n_procs m)
             (simp : similar_procs p1 p2)
             (sims : similar_subs ps1 ps2),
        similar_subs (p1 :: ps1) (p2 :: ps2).
  Hint Constructors similar_subs.

  Lemma similar_procs_implies_same_level :
    forall {n m} (p1 : n_nproc n) (p2 : n_nproc m),
      similar_procs p1 p2 -> n = m.
  Proof.
    introv sim.
    inversion sim; auto.
  Qed.

  Lemma similar_procs_implies_same_name :
    forall {n m} (p1 : n_nproc n) (p2 : n_nproc m),
      similar_procs p1 p2 -> pp_name p1 = pp_name p2.
  Proof.
    introv sim.
    inversion sim; auto; subst; simpl in *.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; simpl in *; auto.
  Qed.

  Lemma similar_procs_implies_same_proc :
    forall {n} cn (p1 : n_proc n cn) (p2 : n_proc n cn),
      similar_procs (MkPProc cn p1) (MkPProc cn p2) -> similar_sms p1 p2.
  Proof.
    introv sim.
    inversion sim; auto; subst; simpl in *.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; simpl in *; auto.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; simpl in *; auto.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; simpl in *; auto.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; simpl in *; auto.
  Qed.

  Lemma similar_subs_implies_same_level :
    forall {n m} (subs1 : n_procs n) (subs2 : n_procs m),
      0 < length subs1
      -> similar_subs subs1 subs2
      -> n = m.
  Proof.
    introv len sim.
    destruct subs1; simpl in *; ginv; try omega;[].
    inversion sim; subst; clear sim.
    apply similar_procs_implies_same_level in simp; auto.
  Qed.

  Lemma similar_sms_refl :
    forall {n cn} (sm : n_proc n cn), similar_sms sm sm.
  Proof.
    induction n; introv; destruct sm; eauto; constructor; auto.
  Qed.
  Hint Resolve similar_sms_refl : comp.

  Lemma similar_procs_refl :
    forall {n} (p : n_nproc n), similar_procs p p.
  Proof.
    destruct p; constructor; eauto 3 with comp.
  Qed.
  Hint Resolve similar_procs_refl : comp.

  Lemma similar_subs_refl :
    forall {n} (subs : n_procs n), similar_subs subs subs.
  Proof.
    induction subs; eauto;[].
    constructor; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_refl : comp.

  Lemma similar_sms_sym :
    forall {n} {cn} (sm1 sm2 : n_proc n cn),
      similar_sms sm1 sm2
      -> similar_sms sm2 sm1.
  Proof.
    induction n; introv h; auto; simpl in *.
    destruct sm1, sm2; tcsp; eauto 3 with comp.
  Qed.
  Hint Resolve similar_sms_sym : comp.

  Lemma similar_procs_sym :
    forall {n} {m} (p1 : n_nproc n) (p2 : n_nproc m),
      similar_procs p1 p2
      -> similar_procs p2 p1.
  Proof.
    introv h; induction h; auto.
    constructor; eauto 3 with comp.
  Qed.
  Hint Resolve similar_procs_sym : comp.

  Lemma similar_subs_sym :
    forall {n} {m} (subs1 : n_procs n) (subs2 : n_procs m),
      similar_subs subs1 subs2
      -> similar_subs subs2 subs1.
  Proof.
    introv h; induction h; auto.
    constructor; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_sym : comp.

  Lemma similar_sms_trans :
    forall {n} {cn} (sm1 sm2 sm3 : n_proc n cn),
      similar_sms sm1 sm2
      -> similar_sms sm2 sm3
      -> similar_sms sm1 sm3.
  Proof.
    induction n; introv h q; simpl in *; tcsp.
    destruct sm1, sm2, sm3; simpl in *; repnd; tcsp; eauto;[].
    destruct a0, a1; simpl in *; subst; dands; auto; eauto 3 with comp.
  Qed.
  Hint Resolve similar_sms_trans : comp.

  Lemma similar_procs_trans :
    forall {n} {m} {k} (p1 : n_nproc n) (p2 : n_nproc m) (p3 : n_nproc k),
      similar_procs p1 p2
      -> similar_procs p2 p3
      -> similar_procs p1 p3.
  Proof.
    introv h q.
    destruct h as [? ? ? ? h].
    destruct p3 as [n3 p3].
    inversion q; subst; GC.
    constructor.
    eapply similar_sms_trans;[eauto|].
    clear dependent p1.
    clear dependent p4.
    clear dependent p5.
    inversion q; subst.

    match goal with
    | [ H : context[p2] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p3] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1.
    apply Eqdep.EqdepTheory.inj_pair2 in h1.
    apply Eqdep.EqdepTheory.inj_pair2 in h2.
    apply Eqdep.EqdepTheory.inj_pair2 in h2.
    subst; auto.
  Qed.
  Hint Resolve similar_procs_trans : comp.

  Lemma similar_subs_trans :
    forall {n} {m} {k} (subs1 : n_procs n) (subs2 : n_procs m) (subs3 : n_procs k),
      similar_subs subs1 subs2
      -> similar_subs subs2 subs3
      -> similar_subs subs1 subs3.
  Proof.
    introv h; revert k subs3; induction h; introv q; auto;
      inversion q; subst; auto.
    constructor; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_trans : comp.

  Lemma M_break_preserves_similar_subs :
    forall {n} {S} {Lv} {Sp}
           (sm   : M_n n S)
           (subs : n_procs n)
           (F    : n_procs n -> S -> option (LocalSystem _ _))
           (ls   : LocalSystem Lv Sp),
      (forall subs1 subs2 out,
          sm subs1 = (subs2, out)
          -> similar_subs subs subs1
          -> similar_subs subs1 subs2)
      -> (forall subs' out ls,
             F subs' out = Some ls
             -> similar_subs subs subs'
             -> similar_subs subs' ls)
      -> M_break sm subs F = Some ls
      -> similar_subs subs ls.
  Proof.
    introv impsm impF h.
    unfold M_break in h.
    remember (sm subs) as k; repnd; symmetry in Heqk.
    apply impsm in Heqk; eauto 3 with comp.
  Qed.

(*  Lemma M_run_update_on_list_preserves_subs :
    forall {n : nat} {nm : CompName} {S : Type} {Lv Sp}
           (l  : oplist (cio_I (fio nm)))
           (s  : S)
           (sm : M_Update n nm S)
           subs F
           (ls : LocalSystem Lv Sp),
      (forall s i subs1 subs2 out, sm s i subs1 = (subs2, out) -> similar_subs subs subs1 -> similar_subs subs1 subs2)
      -> (forall subs' out ls, F subs' out = Some ls -> similar_subs subs subs' -> similar_subs subs' (ls_subs ls))
      -> (forall subs, F subs None = None)
      -> M_break (M_run_update_on_list s sm l) subs F = Some ls
      -> similar_subs subs ls.
  Proof.
    induction l; introv impsm impF fnone h; simpl in *; autorewrite with comp in *; simpl in *; ginv;
      simpl in *; eauto 3 with comp;[].

    rewrite M_break_M_on_some_option_map in h; simpl; auto;[].
    apply map_option_Some in h; exrepnd; subst; simpl in *.
    symmetry in h0.

    rewrite M_break_bind in h0.
    erewrite eq_M_break in h0;
      [|introv;rewrite @M_break_M_on_some_option_map;[reflexivity|];simpl;auto].

    eapply M_break_preserves_similar_subs;[| |eauto];[|]; simpl.

    { introv h; eapply impsm; eauto. }

    introv h sim.
    apply map_option_Some in h; exrepnd; simpl in *; subst.
    symmetry in h1.

    apply IHl in h1; auto.

    { introv h q; eapply impsm; eauto; eauto 3 with comp. }

    { introv h q; eapply impF; eauto; eauto 3 with comp. }
  Qed.*)

  Lemma similar_subs_preserves_find_name :
    forall {n} cn (subs1 subs2 : n_procs n) s,
      similar_subs subs1 subs2
      -> find_name cn subs1 = Some s
      -> exists s', find_name cn subs2 = Some s' /\ similar_sms s s'.
  Proof.
    induction subs1; introv sim h; simpl in *; ginv;[].
    inversion sim; subst; clear sim.
    inversion simp; clear simp; auto; subst; simpl in *.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; simpl in *; auto.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; simpl in *; auto.
    dest_cases w; subst; simpl in *; ginv; eauto.
  Qed.

  Lemma state_of_component_if_similar :
    forall {n} cn (subs1 subs2 : n_procs n) s,
      similar_subs subs1 subs2
      -> state_of_component cn subs1 = Some s
      -> exists s', state_of_component cn subs2 = Some s'.
  Proof.
    introv sim h.
    unfold state_of_component in *.
    apply option_map_Some in h; exrepnd; subst.
    eapply similar_subs_preserves_find_name in h1;[|eauto].
    exrepnd; rewrite h1; simpl; eauto.
  Qed.
  Hint Resolve state_of_component_if_similar : comp.

  (* TODO: why is that just for the main component? *)
  Definition ls_preserves_subs {n} (ls : n_procs n) :=
    forall (cn : CompName) (t : PosDTime) (i : cio_I (fio cn)) (ls0 : n_procs n),
      similar_subs ls ls0
      -> similar_subs ls0 (M_run_ls_on_input_ls ls0 cn t i).

  Definition sys_preserves_subs {F} (sys : M_USystem F) :=
    forall cn, ls_preserves_subs (sys cn).

  Lemma M_run_ls_on_input_preserves_ls_preserves_subs :
    forall {n} (ls : n_procs n) cn t i,
      ls_preserves_subs ls
      -> ls_preserves_subs (M_run_ls_on_input_ls ls cn t i).
  Proof.
    introv pres sim.
    apply pres; eauto 3 with comp.
  Qed.

  Lemma M_run_ls_on_inputs_preserves_ls_preserves_subs :
    forall {n} cn l (ls1 ls2 : n_procs n),
      M_run_ls_on_op_inputs ls1 cn l = Some ls2
      -> ls_preserves_subs ls1
      -> ls_preserves_subs ls2.
  Proof.
    induction l; introv run1 pres sim; simpl in *; tcsp; ginv; eauto 3 with comp.
    apply map_option_Some in run1; exrepnd; subst; rev_Some.
    apply IHl in run0; eauto 3 with comp.
    eapply M_run_ls_on_input_preserves_ls_preserves_subs; eauto.
  Qed.

  Lemma ls_preserves_subs_implies_M_run_update_on_list :
    forall {n} cn L (ls : n_procs n) ls',
      ls_preserves_subs ls
      -> M_run_ls_on_op_inputs ls cn L = Some ls'
      -> similar_subs ls ls'.
  Proof.
    induction L; introv pres q; simpl in *; autorewrite with comp;
      tcsp; ginv; eauto 3 with comp.
    apply map_option_Some in q; exrepnd; subst; simpl in *; rev_Some.
    apply IHL in q0; eauto 4 with comp.
    eapply M_run_ls_on_input_preserves_ls_preserves_subs; eauto.
  Qed.
  Hint Resolve ls_preserves_subs_implies_M_run_update_on_list : comp.

(*  Lemma ls_preserves_subs_implies_M_run_update_on_list2 :
    forall {Lv Sp} (ls : LocalSystem Lv Sp) L s,
      ls_preserves_subs ls
      -> M_break
           (M_run_update_on_list
              s
              (sm_update (ls_main ls))
              L)
           (ls_subs ls)
         (fun subs2 _ => similar_subs (ls_subs ls) subs2).
  Proof.
    introv pres.
    pose proof (ls_preserves_subs_implies_M_run_update_on_list ls L s (ls_subs ls) pres) as q.
    unfold M_break in *; dest_cases w; apply q; eauto 3 with comp.
  Qed.
  Hint Resolve ls_preserves_subs_implies_M_run_update_on_list2 : comp.*)

  Lemma M_run_ls_on_op_inputs_app :
    forall {n}
           (ls : n_procs n)
           {cn}
           (l k : oplist (PosDTime * cio_I (fio cn))),
      M_run_ls_on_op_inputs ls cn (l ++ k)
      = on_some
          (M_run_ls_on_op_inputs ls cn l)
          (fun ls' => M_run_ls_on_op_inputs ls' cn k).
  Proof.
    introv; revert ls k; induction l; introv; simpl; auto.
    unfold on_some.
    rewrite map_option_map_option.
    destruct a; simpl; auto.
    unfold option_compose2; simpl.
    rewrite IHl; auto.
  Qed.

  Lemma M_run_ls_on_inputs_app :
    forall {n}
           (ls : n_procs n)
           {cn}
           (l k : list (PosDTime * cio_I (fio cn))),
      M_run_ls_on_inputs ls cn (l ++ k)
      = let ls' := M_run_ls_on_inputs ls cn l in
        M_run_ls_on_inputs ls' cn k.
  Proof.
    introv; revert ls k; induction l; introv; simpl; auto.
  Qed.

  Lemma time_trigger_op_some_implies_time :
    forall {eo : EventOrdering} (e : Event) t i,
      time_trigger_op e = Some (t, i)
      -> time e = t.
  Proof.
    introv h; unfold time_trigger_op, trigger_op in h.
    destruct (trigger e); simpl in *; ginv; auto.
  Qed.

  Lemma time_trigger_op_some_implies_time_trigger_op :
    forall {eo : EventOrdering} (e : Event) t i,
      time_trigger_op e = Some (t, i)
      -> trigger_op e = Some i.
  Proof.
    introv h; unfold time_trigger_op, trigger_op in *.
    destruct (trigger e); simpl in *; ginv; auto.
  Qed.

  Lemma M_state_sys_on_event_some_between :
    forall {eo : EventOrdering} (e1 e2 : Event) {F} (sys : M_USystem F) cn (s : sf cn),
      sys_preserves_subs sys
      -> e1 ⊑ e2
      -> M_state_sys_on_event sys e2 cn = Some s
      -> exists s', M_state_sys_on_event sys e1 cn = Some s'.
  Proof.
    introv pres lte eqs.
    apply localHappenedBeforeLe_implies_or2 in lte; repndors; subst.
    { eexists; eauto. }

    unfold M_state_sys_on_event in *; simpl in *.

    assert (loc e1 = loc e2) as eqloc by eauto 3 with eo.
    rewrite <- eqloc in eqs.

    pose proof (pres (loc e1)) as pres.
    remember (sys (loc e1)) as ls; clear Heqls.
    clear sys.

    unfold M_state_ls_on_event in *; simpl in *.
    unfold M_run_ls_on_event in *; simpl in *.
    unfold M_run_ls_before_event in *; simpl in *.

    apply map_option_Some in eqs; exrepnd; rev_Some.
    apply map_option_Some in eqs1; exrepnd; rev_Some.
    apply map_option_Some in eqs2; exrepnd; rev_Some; ginv.

    pose proof (local_happened_before_implies_history_app2 _ _ lte) as q; exrepnd.

    assert (History(e1) ++ e1 :: l = snoc (History(e1)) e1 ++ l) as eqx.
    { simpl.
      rewrite snoc_as_app.
      rewrite <- app_assoc; simpl; auto. }
    rewrite eqx in q0; clear eqx.
    rewrite q0 in eqs1; clear q0.

    rewrite map_app in eqs1.
    rewrite map_snoc in eqs1.
    rewrite M_run_ls_on_op_inputs_app in eqs1.
    rewrite M_run_ls_on_op_inputs_snoc in eqs1.
    apply map_option_Some in eqs1; exrepnd; rev_Some.
    apply map_option_Some in eqs1; exrepnd; rev_Some.
    apply map_option_Some in eqs4; exrepnd; rev_Some; ginv.

    allrw; simpl in *.

    applydup @M_run_ls_on_inputs_preserves_ls_preserves_subs in eqs1 as pres1; auto;[].
    pose proof (M_run_ls_on_input_preserves_ls_preserves_subs
                  a2
                  (msg_comp_name (fls_space F (loc e1)))
                  (time e1)
                  a3) as pres2;
      autodimp pres2 hyp.
    assert (a4 = time e1) as eqt1 by (apply time_trigger_op_some_implies_time in eqs4; auto); subst.
    applydup @M_run_ls_on_inputs_preserves_ls_preserves_subs in eqs3 as pres3; auto;[].

    applydup @ls_preserves_subs_implies_M_run_update_on_list in eqs3 as sim1; auto;[].
    pose proof (pres3 (msg_comp_name (fls_space F(loc e1))) (time e2) a1 a0) as sim2; autodimp sim2 hyp; eauto 3 with comp.

    eapply similar_subs_trans in sim2;[|exact sim1].
    apply similar_subs_sym in sim2.
    eapply state_of_component_if_similar in eqs0; try exact sim2; auto.
    erewrite time_trigger_op_some_implies_time_trigger_op; eauto; simpl; auto.
  Qed.

  Definition M_output_ls_on_this_one_event
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event) : DirectedMsgs :=
    olist2list
      (on_some
         (time_trigger_op e)
         (fun x => M_run_ls_on_input_out ls (msg_comp_name Sp) (fst x) (snd x))).

  Definition M_output_ls_on_event
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event) : DirectedMsgs :=
    olist2list
      (option_map
         (fun ls' => M_output_ls_on_this_one_event ls' e)
         (M_run_ls_before_event ls e)).

  Definition M_output_sys_on_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : DirectedMsgs :=
    M_output_ls_on_event (sys (loc e)) e.

  (* REDO WITHOUT UNFOLDING MONAD *)
  Lemma M_output_ls_on_event_as_run_before :
    forall {Lv Sp}
           (ls : LocalSystem Lv Sp)
           {eo : EventOrdering}
           (e  : Event),
      M_output_ls_on_event ls e
      = match M_run_ls_before_event ls e with
        | Some ls' => M_output_ls_on_this_one_event ls' e
        | None => []
        end.
  Proof.
    introv.
    unfold M_output_ls_on_event.
    remember (M_run_ls_before_event ls e) as run; destruct run; simpl; auto.
  Qed.

  Lemma M_output_ls_on_event_as_run :
    forall {Lv Sp}
           (ls : LocalSystem Lv Sp)
           {eo : EventOrdering}
           (e  : Event)
           (m  : DirectedMsg),
      In m (M_output_ls_on_event ls e)
      <->
      exists (ls' : LocalSystem _ _),
        M_run_ls_before_event ls e = Some ls'
        /\ In m (M_output_ls_on_this_one_event ls' e).
  Proof.
    introv.
    rewrite M_output_ls_on_event_as_run_before.
    remember (M_run_ls_before_event ls e) as w; symmetry in Heqw.
    destruct w; simpl; split; intro h; exrepnd; tcsp; ginv;[].
    eexists; dands; eauto.
  Qed.

  Lemma M_output_ls_on_event_implies_run :
    forall {Lv Sp}
           (ls : LocalSystem Lv Sp)
           {eo : EventOrdering}
           (e  : Event)
           (m  : DirectedMsg),
      In m (M_output_ls_on_event ls e)
      ->
      exists (ls' : LocalSystem _ _),
        M_run_ls_before_event ls e = Some ls'
        /\ In m (M_output_ls_on_this_one_event ls' e).
  Proof.
    introv h.
    apply M_output_ls_on_event_as_run; auto.
  Qed.


  (* XXXXXXXXXXXXXXXXXX *)

  (*
  (* FIX THE NEXT 4 DEFINITIONS! *)

  (* we have to rewrite [AXIOM_authenticated_messages_were_sent_or_byz]
     so that not all keys are used to authenticated the data at [e'] *)
  Definition included_keys_proc
             {n} {nm} : n_proc n nm -> local_key_map -> Prop :
      match nm with
      | MkCompName "KEY" _ =>
        fun sm ks => sm2state sm
      | _ => fun sm ks => True
      end.


  Definition included_keys_nproc
             {n}
             (p  : n_nproc n)
             (ks : local_key_map) : Prop :
      let (nm,sm) := p in
      included_keys_proc sm ks

  Fixpoint included_keys
           {n}
           (l  : n_procs n)
           (ks : local_key_map) : Prop :=
    match l with
    | [] => True
    | p :: ps => included_keys_nproc p ks /\ included_keys ps ks
    end.

  (* get all keys from the KEY components *)
  Definition AXIOM_M_correct_keys_local_sys
             (sys : LocalSystem)
             {eo  : EventOrdering}
             (e   : Event) : Prop :=
    forall st,
      M_state_sm_before_event (ls_main sys) e = st
      -> st >p>= (fun sop => match sop with
                             | Some s => ret _ (keys e = K s)
                             | None => ret _ True
                             end).

  Definition AXIOM_M_correct_keys_sys
             (sys : M_USystem)
             {eo  : EventOrdering}
             (K   : system_key_constraint sys) : Prop :=
    forall e (i : name) e',
      has_correct_trace_before e i
      -> e' ≼ e
      -> loc e' = i
      -> AXIOM_M_correct_keys_local_sys (sys i) e' (K i).
*)


(*  Definition AXIOM_M_authenticated_messages_were_sent_or_byz_usys
             (eo : EventOrdering) (s : M_USystem) :=
    fun p =>
      @AXIOM_authenticated_messages_were_sent_or_byz
        pd
        pn
        pk
        pat
        paf
        pm
        dtc
        eo
        pda
        cad
        gms
        (fun eo e => snd (M_output_system_on_event_ldata s e p)).*)

  (* ============== Computations on Byzantine events ============== *)

  Fixpoint sm2at {n} {cn}
    : forall (sm : n_proc n cn), n_proc_at (sm2level sm) cn :=
    match n with
    | 0 => fun sm => match sm with end
    | S m => fun sm =>
               match sm with
               | sm_or_at q => q
               | sm_or_sm q => sm2at q
               end
    end.

  Record trustedSM :=
    MktrustedSM
      {
        tsm_level : nat;
        tsm_kind  : CompNameKind;
        tsm_space : CompNameSpace;
        tsm_sm    : n_proc_at tsm_level (MkCN tsm_kind tsm_space true);
      }.

  Definition tsm2pcn (tsm : trustedSM) : PreCompName :=
    MkPreCompName (tsm_kind tsm) (tsm_space tsm).
  Coercion tsm2pcn : trustedSM >-> PreCompName.

  Definition state_of_trusted (tsm : trustedSM) : tsf tsm :=
    sm_state (tsm_sm tsm).

  Definition updateTrustedSM (tsm : trustedSM) : tsf tsm -> trustedSM :=
    match tsm with
    | MktrustedSM l k s sm => fun new => MktrustedSM l k s (update_state sm new)
    end.

(*  Definition haltTrustedSM (tsm : trustedSM) : trustedSM :=
    match tsm with
    | MktrustedSM l k s sm => MktrustedSM l k s (halt_machine sm)
    end.*)

  Fixpoint find_trusted {n:nat} (l : n_procs n) : n_procs n :=
    match l with
    | [] => []
    | comp :: rest =>
      if is_trusted comp then comp :: find_trusted rest
      else find_trusted rest
    end.

  Definition find_trusted_sub {L S} (ls : LocalSystem L S) : n_procs L :=
    find_trusted ls.

  (* We run the trusted with no subcomponents *)
(*  Definition run_trustedSM_on_trigger_info {D}
             (tsm : trustedSM)
             (ti  : trigger_info D) : trustedSM * iot_output (iot_fun tsm) :=
    match ti with
    | trigger_info_data d => (tsm, iot_def_output)
    | trigger_info_arbitrary => (tsm, iot_def_output)
    | trigger_info_trusted i =>
      match sm_update (tsm_sm tsm) (state_of_trusted tsm) i [] with
      | (_, (Some s, out)) => (updateTrustedSM tsm s, out)
      | (_, (None, out)) => (haltTrustedSM tsm, out)
      end
    end.*)

(*  Fixpoint run_trustedSM_on_trigger_info_list {D}
           (tsm : trustedSM)
           (l   : list (trigger_info D)) : trustedSM :=
    match l with
    | [] => tsm
    | ti :: l =>
      run_trustedSM_on_trigger_info_list
        (fst (run_trustedSM_on_trigger_info tsm ti))
        l
    end.*)

(*  Definition M_find_trusted {n} : M_n n (option trustedSM) :=
    fun subs => ([], find_trusted subs).*)

(*  Definition run_trusted_on_trigger_info_list {n} {D}
             (l : list (trigger_info D)) : M_n n (option trustedSM) :=
    M_find_trusted
      >>o= fun tsm => ret _ (Some (run_trustedSM_on_trigger_info_list tsm l)).*)

(*  Definition M_trusted (T : Type) := T [+] trustedSM.
  Definition M_trusted_with_out (T : Type) := (option T * DirectedMsgs) [+] (trustedSM * iot_output).
  Definition M_trusted_out (T : Type) := T [+] iot_output.
  Definition M_trusted_msgs := M_trusted_out DirectedMsgs.

  Definition on_M_trusted {T} {A}
             (x : M_trusted T)
             (F : T -> A)
             (G : trustedSM -> A) : A :=
    match x with
    | inl t => F t
    | inr tsm => G tsm
    end.

  Definition on_M_trusted_out {T} {A}
             (x : M_trusted_out T)
             (F : T -> A)
             (G : iot_output -> A) : A :=
    match x with
    | inl t => F t
    | inr tsm => G tsm
    end.

  Definition on_M_trusted_with_out {T} {A}
             (x : M_trusted_with_out T)
             (F : (option T * DirectedMsgs) -> A)
             (G : (trustedSM * iot_output) -> A) : A :=
    match x with
    | inl t => F t
    | inr tsm => G tsm
    end.

  (* non-trusted *)
  Definition M_nt {T : Type} (t : T) : M_trusted T := inl t.
  (* trusted *)
  Definition M_t {T : Type} (tsm : trustedSM) : M_trusted T := inr tsm.

  (* non-trusted with output *)
  Definition M_nt_w_o {T : Type} (t : option T * DirectedMsgs) : M_trusted_with_out T := inl t.
  (* trusted with ouput *)
  Definition M_t_w_o {T : Type} (x : trustedSM * iot_output) : M_trusted_with_out T := inr x.

  (* non-trusted output *)
  Definition M_nt_o {T : Type} (t : T) : M_trusted_out T := inl t.
  (* trusted ouput *)
  Definition M_t_o {T : Type} (x : iot_output) : M_trusted_out T := inr x.

  Definition to_op_M_trusted {T} (mt : M_trusted_with_out T) : option (M_trusted T) :=
    on_M_trusted_with_out
      mt
      (fun x => option_map M_nt (fst x))
      (fun x => Some (M_t (fst x))).

  Definition to_M_trusted_out {T} (mt : M_trusted_with_out T) : M_trusted_msgs :=
    on_M_trusted_with_out
      mt
      (fun x => M_nt_o (snd x))
      (fun x => M_t_o (snd x)).

  Definition M_run_trusted_on_trigger_info_list {n} {S} {D}
             (l : list (trigger_info D)) : M_n n (option (M_trusted S)) :=
    (run_trusted_on_trigger_info_list l)
      >>o= fun tsm => ret _ (Some (M_t tsm)).*)

(*  (* As opposed to [M_run_update_on_list] below, this one starts running the (first)
     trusted component as soon as we encounter an abnormal event, discarding the
     other subcomponents (meaning that a trusted component cannot use other components
     with this simple implementation).  Once we start running the trusted component,
     the normal events are considered as arbitrary/byzantine events. *)
  Fixpoint M_byz_run_update_on_list {S} {n} {cn}
           (s   : S)
           (upd : M_Update n cn S)
           (l   : list (trigger_info (cio_I (fio cn)))) : M_n n (option (M_trusted S)) :=
    match l with
    | [] => ret _ (Some (M_nt s))
    | ti :: k =>
      if_trigger_info_data
        ti
        (fun m =>
           (upd s m)
             >>= fun so =>
                   (fst so)
                     >>o>> fun s' => M_byz_run_update_on_list s' upd k)
        (M_run_trusted_on_trigger_info_list l)
    end.

  Definition M_op2M_trusted_with_out {n} {T}
             (p : M_n n (op_state_out T))
    : M_n n (option (M_trusted_with_out T)) :=
    p >>o= fun t => ret _ (Some (M_nt_w_o t)).

  Definition M_byz_run_update_on_event {S} {n} {k}
             (s   : S)
             (upd : M_Update n (msg_comp_name k) S)
             {eo  : EventOrdering}
             (e   : Event) : M_n n (option (M_trusted_with_out S)) :=
    (M_byz_run_update_on_list s upd (map trigger (@localPreds pn pk pm _ _ eo e)))
      >>o= fun mt =>
             on_M_trusted
               mt
               (fun s =>
                  if_trigger_info_data
                    (trigger e)
                    (fun m => (upd s m) >>= fun so => ret _ (Some (M_nt_w_o so)))
                    (M_find_trusted >>o= fun tsm => ret _ (Some (M_t_w_o (run_trustedSM_on_trigger_info tsm (trigger e))))))
               (fun tsm => ret _ (Some (M_t_w_o (run_trustedSM_on_trigger_info tsm (trigger e))))).

  Definition M_byz_run_sm_on_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event)
    : M_n (sm2level sm) (option (M_trusted_with_out (sf (msg_comp_name k)))) :=
    M_byz_run_update_on_event (sm2state sm) (sm2update sm) e.

  Definition M_byz_output_sm_on_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event)
    : M_n (sm2level sm) (option M_trusted_msgs) :=
    (M_byz_run_sm_on_event sm e)
      >>o= fun mt => ret _ (Some (to_M_trusted_out mt)).

  Definition on_Some_t_o {T} (op : option T) (f : T -> M_trusted_msgs):=
    match op with
    | Some t => f t
    | None => M_nt_o []
    end.*)

  (*Definition to_opt_snd
             {A B}
             (x : A * B)
    : A * option B :=
    let (a,b) := x in (a, Some b).*)

(*  Definition M_byz_run_ls_on_input
             {lvl Sp}
             (ls : LocalSystem lvl Sp)
             cn
             (i  : cio_I (fio cn)) : option (LocalSystem lvl cn) * option (cio_O (fio cn)) :=
    match ls_status ls with
    | ls_is_ok  => to_opt_snd (M_run_ls_on_input ls i)
    | ls_is_byz => (Some (upd_ls_byz ls), None)
    end.*)

  Definition pre2trusted (p : PreCompName) : CompName :=
    MkCompName p true.

  Definition trigger_info2out {A} cn (i : trigger_info A) : Type :=
    match i with
    | trigger_info_data _ => cio_O (fio cn)
    | trigger_info_arbitrary => False
    | trigger_info_trusted j => iot_output (iot_fun (it_name j))
    end.

  Definition event2out space {eo : EventOrdering} (e : Event) : Type :=
    trigger_info2out (msg_comp_name space) (trigger e).

  Inductive M_byz_output {A} cn (i : trigger_info A) :=
  | m_byz_output_msg   (m : cio_O (fio cn))
  | m_byz_output_event (j : trigger_info2out cn i)
  | m_byz_output_no.

  Definition event2M_byz_output space {eo : EventOrdering} (e : Event) :=
    M_byz_output (msg_comp_name space) (trigger e).

(*  Definition event2out_to_byz {Sp} {eo : EventOrdering} {e}
             (x : event2out Sp e) : event2M_byz_output Sp e.
  Proof.
    unfold event2out, event2M_byz_output in *.
    destruct (trigger e).
    { exact (m_byz_output_msg _ _ x). }
    { destruct x. }
    { exact (m_byz_output_event _ _ x). }
  Defined.

  Definition op_event2out_to_byz {Sp} {eo : EventOrdering} {e}
             (x : option (event2out Sp e))
    : event2M_byz_output Sp e :=
    match x with
    | Some z => event2out_to_byz z
    | None => m_byz_output_no _ _
    end.*)

(*  Definition trigger_info2state {A} cn (i : trigger_info A) : Type :=
    match i with
    | trigger_info_data d => sf cn
    | trigger_info_arbitrary => False
    | trigger_info_trusted j => sf (pre2trusted (it_name j))
    end.

  Definition event2state cn {eo : EventOrdering} (e : Event) : Type :=
    trigger_info2out cn (trigger e).*)

  Fixpoint procs2byz {n} (ls : n_procs n) : n_procs n :=
    match ls with
    | [] => []
    | comp :: rest =>
      if is_trusted comp then comp :: procs2byz rest
      else procs2byz rest
    end.

  Definition M_run_ls_on_trusted
             {n}
             (ls : n_procs n)
             (t  : PosDTime)
             (i  : ITrusted) : n_procs n * option (cio_O (fio (pre2trusted (it_name i)))) :=
    M_run_ls_on_input ls (pre2trusted (it_name i)) t (it_input i).

  Definition M_byz_run_ls_on_input
             {n}
             (ls : n_procs n)
             cn
             (t  : PosDTime)
             (i  : trigger_info (cio_I (fio cn)))
    : n_procs n * option (trigger_info2out cn i) :=
    match i with
    | trigger_info_data d => M_run_ls_on_input ls cn t d
    | trigger_info_arbitrary => (procs2byz ls, None)
    | trigger_info_trusted j => M_run_ls_on_trusted (procs2byz ls) t j
    end.

  Definition to_snd_byz_msg
             {A} {B} {i : trigger_info B} {cn}
             (x : A * option (cio_O (fio cn)))
  : A * M_byz_output cn i :=
    match x with
    | (a,Some o) => (a,m_byz_output_msg _ _ o)
    | (a,None) => (a,m_byz_output_msg _ _ (cio_default_O (fio cn)))
    end.

  Lemma mk_ti2out_trusted
        {A : Type} {cn : CompName} {t : ITrusted}
        (x : iot_output (iot_fun (it_name t)))
    : @trigger_info2out A cn (trigger_info_trusted t).
  Proof.
    exact x.
  Defined.

  Lemma to_snd_byz_event
        {I A : Type} {cn : CompName}{t : ITrusted}
        (x : A * option (iot_output (iot_fun (it_name t))))
    : A * @M_byz_output I cn (trigger_info_trusted t).
  Proof.
    destruct x as [a o]; simpl in *.
    destruct o as [o|].
    { exact (a,m_byz_output_event _ _ (mk_ti2out_trusted o)). }
    { exact (a,m_byz_output_no _ _). }
  Defined.

  (*(* Similar to [M_byz_run_ls_on_trig], but tags the output here *)
  Definition M_byz_run_ls_on_input_B
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             cn
             (i  : trigger_info (cio_I (fio cn)))
    : LocalSystem Lv Sp * M_byz_output cn i :=
    match i with
    | trigger_info_data d => to_snd_byz_msg (M_run_ls_on_input ls cn d)
    | trigger_info_arbitrary => (ls2byz ls, m_byz_output_no _ _)
    | trigger_info_trusted j => to_snd_byz_event (M_run_ls_on_trusted (ls2byz ls) j)
    end.*)

  Definition M_byz_run_ls_on_one_event
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event)
    : LocalSystem Lv Sp * option (event2out Sp e) :=
    M_byz_run_ls_on_input ls (msg_comp_name Sp) (time e) (trigger e).

  (*Definition M_byz_run_ls_on_one_event_B
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event)
    : LocalSystem Lv Sp * event2M_byz_output Sp e :=
    M_byz_run_ls_on_input_B ls (msg_comp_name Sp) (trigger e).*)

  Fixpoint M_byz_run_ls_on_inputs
           {n}
           (ls : n_procs n)
           cn
           (l  : list (PosDTime * trigger_info (cio_I (fio cn))))
    : n_procs n :=
    match l with
    | [] => ls
    | (t, i) :: rest =>
      let ls' := fst (M_byz_run_ls_on_input ls cn t i) in
      M_byz_run_ls_on_inputs ls' cn rest
    end.

  Definition M_byz_run_ls_before_event
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event) : LocalSystem Lv Sp :=
    M_byz_run_ls_on_inputs
      ls
      (msg_comp_name Sp)
      (map (fun e => (time e, trigger e)) (@localPreds pn pk pm _ _ eo e)).

  Definition M_byz_output_ls_on_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (event2out S e) :=
    let ls' := M_byz_run_ls_before_event ls e in
    snd (M_byz_run_ls_on_one_event ls' e).

  (*Definition M_byz_output_ls_on_event_B
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : event2M_byz_output S e :=
    let ls' := M_byz_run_ls_before_event ls e in
    snd (M_byz_run_ls_on_one_event_B ls' e).*)

  Definition M_byz_output_sys_on_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : option (event2out _ e) :=
    M_byz_output_ls_on_event (sys (loc e)) e.

  (*Definition M_byz_output_sys_on_event_B
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : event2M_byz_output _ e :=
    M_byz_output_ls_on_event_B (sys (loc e)) e.*)

(*  Definition M_byz_output_sys_on_event_to_byz
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : iot_output :=
    on_M_trusted_out
      (M_byz_output_sys_on_event sys e)
      (fun _ => iot_def_output)
      (fun out => out).*)

(*  Definition M_byz_run_sm_on_list {n} {cn}
             (sm : n_proc n cn)
             (l  : list (trigger_info (cio_I (fio cn))))
    : M_n (sm2level sm) (option (M_trusted (sf cn))) :=
    M_byz_run_update_on_list (sm2state sm) (sm2update sm) l.*)

(*  Definition M_byz_state_sm_before_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event)
    : M_n (sm2level sm) (option (M_trusted (sf (msg_comp_name k)))) :=
    M_byz_run_sm_on_list sm (map trigger (@localPreds pn pk pm _ _ eo e)).*)

(*  Definition map_untrusted {T} {A}
             (x : M_trusted T)
             (F : T -> A) : M_trusted A :=
    on_M_trusted x (fun t => M_nt (F t)) M_t.*)

(*  Definition map_untrusted_op {T} {A}
             (x : M_trusted T)
             (F : T -> option A) : option (M_trusted A) :=
    on_M_trusted
      x
      (fun t => option_map M_nt (F t))
      (fun tsm => Some (M_t tsm)).*)

(*  Definition map_op_untrusted {T} {A}
             (x : option (M_trusted T))
             (F : T -> A) : option (M_trusted A) :=
    option_map (fun mt => map_untrusted mt F) x.*)

(*  Definition map_op_untrusted_op {T} {A}
             (x : option (M_trusted T))
             (F : T -> option A) : option (M_trusted A) :=
    map_option (fun mt => map_untrusted_op mt F) x.*)

(*  Definition M_byz_run_ls_before_event
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (M_trusted (LocalSystem _ _)) :=
    M_break
      (M_byz_state_sm_before_event (at2sm (ls_main ls)) e)
      (ls_subs ls)
      (fun subs' out =>
         map_op_untrusted
           out
           (fun s => upd_ls_main_state_and_subs ls s subs')).*)

  Definition M_byz_state_ls_before_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event)
             (cn : CompName) : option (sf cn) :=
    let ls' := M_byz_run_ls_before_event ls e in
    state_of_component cn ls'.

  Definition M_byz_state_sys_before_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event)
             (cn  : CompName) : option (sf cn) :=
    M_byz_state_ls_before_event (sys (loc e)) e cn.

(*  Definition state_of_trusted_in_ls {L S} (ls : LocalSystem L S) : option tsf :=
    option_map state_of_trusted (find_trusted_sub ls).*)

(*  Definition M_byz_state_ls_before_event_of_trusted
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option tsf :=
    map_option
      (fun mt =>
         on_M_trusted
           mt
           state_of_trusted_in_ls
           (fun tsm => Some (state_of_trusted tsm)))
      (M_byz_run_ls_before_event ls e).*)

(*  Definition M_byz_state_sys_before_event_of_trusted
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : option tsf :=
    M_byz_state_ls_before_event_of_trusted (sys (loc e)) e.*)

(*  Definition M_byz_state_sm_on_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (option (M_trusted (sf (msg_comp_name k)))) :=
  (M_byz_run_sm_on_event sm e)
    >>o= fun mt => ret _ (to_op_M_trusted mt).*)

  Definition M_byz_run_ls_on_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : LocalSystem L S :=
    let ls' := M_byz_run_ls_before_event ls e in
    fst (M_byz_run_ls_on_one_event ls' e).

  Definition M_byz_state_ls_on_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event)
             (cn : CompName) : option (sf cn) :=
    let ls' := M_byz_run_ls_on_event ls e in
    state_of_component cn ls'.

  Definition M_byz_state_sys_on_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event)
             (cn  : CompName) : option (sf cn) :=
    M_byz_state_ls_on_event (sys (loc e)) e cn.

(*  Definition M_byz_state_ls_on_event_of_trusted
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option tsf :=
    map_option
      (fun mt =>
         on_M_trusted
           mt
           state_of_trusted_in_ls
           (fun tsm => Some (state_of_trusted tsm)))
      (M_byz_run_ls_on_event ls e).*)

(*  Definition M_byz_state_sys_on_event_of_trusted
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : option tsf :=
    M_byz_state_ls_on_event_of_trusted (sys (loc e)) e.*)

(*  Lemma M_byz_state_sys_before_event_of_trusted_unfold :
    forall {F}
           (sys : M_USystem F)
           {eo  : EventOrdering}
           (e   : Event),
      M_byz_state_sys_before_event_of_trusted sys e
      = map_option
          (fun mt =>
             on_M_trusted
               mt
               state_of_trusted_in_ls
               (fun tsm => Some (state_of_trusted tsm)))
          (M_byz_run_ls_before_event (sys (loc e)) e).
  Proof.
    tcsp.
  Qed.*)

(*  Lemma map_op_untrusted_option_map_M_nt :
    forall {T A} (t : option T) (F : T -> A),
      map_op_untrusted
        (option_map M_nt t)
        F
      = option_map
          (fun x => M_nt (F x))
          t.
  Proof.
    introv.
    destruct t; simpl; auto.
  Qed.
  Hint Rewrite @map_op_untrusted_option_map_M_nt : comp.*)

(*  Lemma M_break_map_op_untrusted_option_map_M_nt :
    forall {n S T A}
           (t    : n_procs n -> S -> option T)
           (F    : n_procs n -> S -> T -> A)
           (sm   : M_n n S)
           (subs : n_procs n),
      M_break
        sm subs
        (fun subs' s =>
           map_op_untrusted
             (option_map M_nt (t subs' s))
             (F subs' s))
      = M_break
          sm subs
          (fun subs' s =>
             option_map
               (fun x => M_nt (F subs' s x))
               (t subs' s)).
  Proof.
    introv.
    apply eq_M_break; introv; autorewrite with comp; auto.
  Qed.
  Hint Rewrite @M_break_map_op_untrusted_option_map_M_nt : comp.*)

  Definition M_byz_run_ls_on_this_one_event
             {L S}
             (ls : LocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : LocalSystem _ _ :=
    fst (M_byz_run_ls_on_one_event ls e).

(*  Lemma M_nt_inj :
    forall {T} (t1 t2 : T),
      M_nt t1 = M_nt t2
      -> t1 = t2.
  Proof.
    introv h; injection h; auto.
  Qed.*)

(*  Lemma M_byz_run_ls_on_this_one_event_Some_M_nt_implies :
    forall {L S}
           (ls1 : MLocalSystem L S)
           {eo  : EventOrdering}
           (e   : Event)
           (ls2 : MLocalSystem L S),
      M_byz_run_ls_on_this_one_event ls1 e = Some (M_nt ls2)
      ->
      exists m,
        msg_triggered_event m e
        /\ M_break
             (sm_update (ls_main ls1) (sm_state (ls_main ls1)) m)
             (ls_subs ls1)
             (fun subs' out =>
                option_map
                  (fun s => upd_ls_main_state_and_subs ls1 s subs')
                  (fst out)) = Some ls2.
  Proof.
    introv h.
    unfold M_byz_run_ls_on_this_one_event in h.
    remember (trigger e) as trig; destruct trig; simpl in *;
      try (complete (apply option_map_Some in h; exrepnd; inversion h0));[].

    exists d; dands; auto; eauto 3 with eo.
    { unfold msg_triggered_event, trigger_op; allrw <-; simpl; auto. }
    unfold M_break in *.
    remember (sm_update (ls_main ls1) (sm_state (ls_main ls1)) d (ls_subs ls1)) as xx.
    destruct xx; repnd; simpl in *.
    apply option_map_Some in h; exrepnd; subst; simpl in *.
    apply M_nt_inj in h0; subst; auto.
  Qed.*)

(*  Definition M_byz_run_M_trusted_ls_on_this_one_event
             {L S}
             (mt : M_trusted (MLocalSystem L S))
             {eo : EventOrdering}
             (e  : Event) : option (M_trusted (MLocalSystem L S)) :=
    on_M_trusted
      mt
      (fun ls => M_byz_run_ls_on_this_one_event ls e)
      (fun tsm => Some (M_t (fst (run_trustedSM_on_trigger_info tsm (trigger e))))).*)

(*  Lemma on_M_trusted_map_untrusted :
    forall {U T A} (x : M_trusted U) (f : U -> T) (F : T -> A) (G : trustedSM -> A),
      on_M_trusted (map_untrusted x f) F G
      = on_M_trusted x (compose F f) G.
  Proof.
    introv; unfold map_untrusted, on_M_trusted.
    destruct x; simpl; auto.
  Qed.
  Hint Rewrite @on_M_trusted_map_untrusted : comp.*)

(*  Lemma on_M_trusted_implies_or :
    forall {T} {A}
           (x : M_trusted T)
           (F : T -> A)
           (G : trustedSM -> A)
           (a : A),
      on_M_trusted x F G = a
      -> (exists t, x = M_nt t /\ a = F t)
         \/ (exists tsm, x = M_t tsm /\ a = G tsm).
  Proof.
    introv h.
    destruct x; simpl in *; subst; tcsp;[left|right]; eexists; dands; reflexivity.
  Qed.*)

(*  Lemma on_M_trusted_M_nt :
    forall {T A} (x : T) (F : T -> A) (G : trustedSM -> A),
      on_M_trusted (M_nt x) F G = F x.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @on_M_trusted_M_nt : comp.*)

(*  Lemma on_M_trusted_M_t :
    forall {T A} (x : trustedSM) (F : T -> A) (G : trustedSM -> A),
      on_M_trusted (M_t x) F G = G x.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @on_M_trusted_M_t : comp.*)

(*  Lemma M_break_on_M_trusted :
    forall {n} {A} {S} {O}
           (a    : M_trusted A)
           (f    : A -> M_n n S)
           (g    : trustedSM -> M_n n S)
           (subs : n_procs n)
           (F    : n_procs n -> S -> O),
      M_break (on_M_trusted a f g) subs F
      = on_M_trusted
          a
          (fun a => M_break (f a) subs F)
          (fun tsm => M_break (g tsm) subs F).
  Proof.
    introv; destruct a; simpl; auto.
  Qed.*)

(*  Lemma eq_on_M_trusted :
    forall {T} {A}
           (x : M_trusted T)
           (F1 F2 : T -> A)
           (G1 G2 : trustedSM -> A),
      (forall t, F1 t = F2 t)
      -> (forall tsm, G1 tsm = G2 tsm)
      -> on_M_trusted x F1 G1 = on_M_trusted x F2 G2.
  Proof.
    introv impa impb.
    destruct x; simpl; tcsp.
  Qed.*)

  Lemma M_break_if_trigger_info_data :
    forall {n} {S} {O} {D}
           (a    : trigger_info D)
           (f    : D -> M_n n S)
           (g    : M_n n S)
           (subs : n_procs n)
           (F    : n_procs n -> S -> O),
      M_break (if_trigger_info_data a f g) subs F
      = if_trigger_info_data
          a
          (fun a => M_break (f a) subs F)
          (M_break g subs F).
  Proof.
    introv; destruct a; simpl; auto.
  Qed.

  Lemma eq_if_trigger_info_data :
    forall {A} {D}
           (x : trigger_info D)
           (F1 F2 : D -> A)
           (G1 G2 : A),
      (forall t, F1 t = F2 t)
      -> G1 = G2
      -> if_trigger_info_data x F1 G1 = if_trigger_info_data x F2 G2.
  Proof.
    introv impa impb.
    destruct x; simpl; tcsp.
  Qed.

  Lemma M_byz_run_ls_on_event_unroll :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_run_ls_on_event ls e
      = if dec_isFirst e
        then M_byz_run_ls_on_this_one_event ls e
        else
          let ls' := M_byz_run_ls_before_event ls e in
          M_byz_run_ls_on_this_one_event ls' e.
  Proof.
    introv.
    unfold M_byz_run_ls_on_event; simpl.
    destruct (dec_isFirst e) as [d|d]; simpl in *; auto.
    unfold M_byz_run_ls_before_event.
    rewrite isFirst_implies_localPreds_eq; auto.
  Qed.

  Lemma on_M_some_ret_Some :
    forall {T} {U} {n} (a : hoption T) (F : T -> U),
      (a >>o>> (fun s => ret n (hsome (F s))))
      = ret n (hoption_map F a).
  Proof.
    introv; destruct a; simpl; auto.
  Qed.
  Hint Rewrite @on_M_some_ret_Some : comp.

  Lemma bind_some_if_trigger_info_data :
    forall {n} {S} {O} {D}
           (a    : trigger_info D)
           (f    : D -> M_n n (hoption S))
           (g    : M_n n (hoption S))
           (F    : S -> M_n n (hoption O)),
      ((if_trigger_info_data a f g) >>o= F)
      = if_trigger_info_data
          a
          (fun a => (f a) >>o= F)
          (g >>o= F).
  Proof.
    introv; destruct a; simpl; auto.
  Qed.

(*  Lemma run_trustedSM_on_trigger_info_list_snoc :
    forall {D} (l : list (trigger_info D)) x (tsm : trustedSM),
      run_trustedSM_on_trigger_info_list tsm (snoc l x)
      = fst (run_trustedSM_on_trigger_info
               (run_trustedSM_on_trigger_info_list tsm l)
               x).
  Proof.
    induction l; introv; simpl; auto.
  Qed.*)

(*  Lemma M_byz_run_update_on_list_snoc :
    forall {S} {n} {cn}
           (upd : M_Update n cn S)
           (l : list (trigger_info (cio_I (fio cn))))
           (s : S)
           (x : trigger_info (cio_I (fio cn))),
      M_byz_run_update_on_list s upd (snoc l x)
      = ((M_byz_run_update_on_list s upd l)
           >>o= fun mt => on_M_trusted
                            mt
                            (fun s =>
                               if_trigger_info_data
                                 x
                                 (fun m => (upd s m) >>= fun so => ret _ (option_map M_nt (fst so)))
                                 (M_find_trusted >>o= fun tsm => ret _ (Some (M_t (fst (run_trustedSM_on_trigger_info tsm x))))))
                            (fun tsm => ret _ (Some (M_t (fst (run_trustedSM_on_trigger_info tsm x)))))).
  Proof.
    induction l; introv; simpl; auto.

    {
      destruct x; simpl; auto; autorewrite with comp; simpl; auto.
      { apply eq_bind; introv; repnd; simpl; auto_rw_bind. }
      { unfold M_run_trusted_on_trigger_info_list; simpl.
        unfold run_trusted_on_trigger_info_list; simpl.
        rewrite bind_some_bind_some.
        apply eq_bind_some; introv; auto_rw_bind. }
      { unfold M_run_trusted_on_trigger_info_list; simpl.
        unfold run_trusted_on_trigger_info_list; simpl.
        rewrite bind_some_bind_some.
        apply eq_bind_some; introv; auto_rw_bind. }
    }

    rewrite bind_some_if_trigger_info_data.
    apply eq_if_trigger_info_data; introv; auto_rw_bind.

    {
      apply eq_bind; introv.
      rewrite M_on_some_bind_some.
      apply eq_M_on_some; introv; auto.
    }

    simpl.
    unfold M_run_trusted_on_trigger_info_list; simpl.
    unfold run_trusted_on_trigger_info_list; simpl.
    repeat rewrite bind_some_bind_some.
    apply eq_bind_some; introv; auto_rw_bind.
    rewrite run_trustedSM_on_trigger_info_list_snoc; auto.
  Qed.*)

  Lemma M_byz_run_ls_on_inputs_snoc :
    forall {Lv Sp}
           (ls : LocalSystem Lv Sp)
           cn
           (t  : PosDTime)
           (i  : trigger_info (cio_I (fio cn)))
           (l  : list (PosDTime * trigger_info (cio_I (fio cn)))),
      M_byz_run_ls_on_inputs ls cn (snoc l (t,i))
      = let ls' := M_byz_run_ls_on_inputs ls cn l in
        fst (M_byz_run_ls_on_input ls' cn t i).
  Proof.
    introv; revert ls; induction l; introv; simpl; tcsp.
  Qed.

  Lemma M_byz_run_ls_before_event_unroll :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_run_ls_before_event ls e
      = if dec_isFirst e
        then ls
        else let ls' := M_byz_run_ls_before_event ls (local_pred e) in
             M_byz_run_ls_on_this_one_event ls' (local_pred e).
  Proof.
    introv.
    unfold M_byz_run_ls_before_event.
    destruct (dec_isFirst e) as [d|d]; simpl in *; auto.
    { rewrite isFirst_implies_localPreds_eq; auto. }
    rewrite (localPreds_unroll e); auto.
    rewrite map_snoc; simpl.
    rewrite @M_byz_run_ls_on_inputs_snoc; auto.
  Qed.

  Lemma M_byz_run_ls_before_event_as_M_byz_run_ls_on_event_pred :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      ~ isFirst e
      -> M_byz_run_ls_before_event ls e = M_byz_run_ls_on_event ls (local_pred e).
  Proof.
    introv ni.
    rewrite M_byz_run_ls_on_event_unroll.
    rewrite M_byz_run_ls_before_event_unroll.

    destruct (dec_isFirst e) as [d1|d1]; tcsp;[].
    destruct (dec_isFirst (local_pred e)) as [d2|d2]; tcsp;[].

    rewrite M_byz_run_ls_before_event_unroll.
    destruct (dec_isFirst (local_pred e)); tcsp; GC.
  Qed.

  Lemma M_byz_run_ls_before_event_unroll_on :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_run_ls_before_event ls e
      = if dec_isFirst e
        then ls
        else M_byz_run_ls_on_event ls (local_pred e).
  Proof.
    introv.
    destruct (dec_isFirst e) as [d|d];
      [|apply M_byz_run_ls_before_event_as_M_byz_run_ls_on_event_pred;auto].
    rewrite M_byz_run_ls_before_event_unroll.
    destruct (dec_isFirst e); tcsp.
  Qed.

(*  Lemma unroll_M_byz_state_ls_before_event_of_trusted :
    forall {eo : EventOrdering} (e : Event)
           {L S} (ls : MLocalSystem L S),
      M_byz_state_ls_before_event_of_trusted ls e
      = if dec_isFirst e
        then state_of_trusted_in_ls ls
        else M_byz_state_ls_on_event_of_trusted ls (local_pred e).
  Proof.
    introv.
    unfold M_byz_state_ls_before_event_of_trusted.
    unfold M_byz_state_ls_on_event_of_trusted.
    rewrite M_byz_run_ls_before_event_unroll_on.
    destruct (dec_isFirst e); simpl; auto.
  Qed.*)


  Lemma M_byz_run_ls_on_this_one_event_eq :
    forall {Lv Sp}
           (ls : LocalSystem Lv Sp)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_run_ls_on_this_one_event ls e
      = match trigger e with
        | trigger_info_data d => fst (M_run_ls_on_input ls (msg_comp_name Sp) (time e) d)
        | trigger_info_arbitrary => procs2byz ls
        | trigger_info_trusted j => fst (M_run_ls_on_trusted (procs2byz ls) (time e) j)
        end.
  Proof.
    introv.
    unfold M_byz_run_ls_on_this_one_event.
    unfold M_byz_run_ls_on_one_event.
    remember (M_byz_run_ls_on_input ls (msg_comp_name Sp) (time e) (trigger e)) as h; repnd; simpl in *.
    unfold M_byz_run_ls_on_input in *.
    destruct (trigger e); simpl in *; ginv; auto.
  Qed.

  Lemma M_run_ls_on_this_one_event_M_byz_run_ls_on_this_one_event :
    forall {Lv Sp}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : LocalSystem Lv Sp),
      M_run_ls_on_this_one_event ls1 e = Some ls2
      -> M_byz_run_ls_on_this_one_event ls1 e = ls2.
  Proof.
    introv h.
    unfold M_run_ls_on_this_one_event in *.
    rewrite M_byz_run_ls_on_this_one_event_eq.
    rewrite option_map_Some in h; exrepnd; rev_Some.

    unfold trigger_op in *.
    destruct (trigger e) as [d|d|d]; ginv; [].
    unfold M_run_ls_on_input_ls; simpl in *; auto.
  Qed.

(*  Lemma M_byz_run_ls_on_this_one_event_M_run_ls_on_this_one_event :
    forall {L S}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : MLocalSystem L S),
      M_byz_run_ls_on_this_one_event ls1 e = Some ls2
      -> M_run_ls_on_this_one_event ls1 e = Some ls2.
  Proof.
    introv h.
    unfold M_run_ls_on_this_one_event in *.
    unfold M_byz_run_ls_on_this_one_event in *.
    rewrite map_option_Some.

    (* TODO: do not unfold *)
    unfold if_trigger_info_data in *.
    unfold trigger_op in *.
    unfold ti2op in *.
    simpl in *.
    destruct (trigger e) as [d|d|d];
      try (unfold option_map in *; dest_cases w);[].

    unfold M_break in *. simpl in *.

    eexists; dands; eauto.

    dest_cases w.
    unfold option_map in *.
    repnd.
    simpl in *.
    destruct w2 as [X|X]; ginv.
    inversion h; subst; auto.
  Qed.
  Hint Resolve M_byz_run_ls_on_this_one_event_M_run_ls_on_this_one_event : comp.
*)

  Lemma M_run_ls_on_event_M_byz_run_ls_on_event :
    forall {L S}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : LocalSystem L S),
      M_run_ls_on_event ls1 e = Some ls2
      -> M_byz_run_ls_on_event ls1 e = ls2.
  Proof.
    intros L S eo e.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_run_ls_on_event_unroll in h.
    rewrite M_byz_run_ls_on_event_unroll.
    destruct (dec_isFirst e).

    { eapply M_run_ls_on_this_one_event_M_byz_run_ls_on_this_one_event; eauto. }

    {
      rewrite M_run_ls_before_event_unroll_on in h.
      rewrite M_byz_run_ls_before_event_unroll_on.
      destruct (dec_isFirst e); tcsp;[].
      apply map_option_Some in h; exrepnd.
      symmetry in h0.
      apply ind in h1; eauto 3 with eo; rewrite h1;[]; simpl.

      eapply M_run_ls_on_this_one_event_M_byz_run_ls_on_this_one_event; eauto.
    }
  Qed.

  Lemma M_run_ls_on_this_one_event_implies_isCorrect :
    forall {eo : EventOrdering} (e : Event) {L S} (ls1 ls2 : LocalSystem L S),
      M_run_ls_on_this_one_event ls1 e = Some ls2
      -> isCorrect e.
  Proof.
    introv h.
    unfold M_run_ls_on_this_one_event in h.
    apply map_option_Some in h; exrepnd; rev_Some; simpl in *.
    eauto 3 with eo.
  Qed.
  Hint Resolve M_run_ls_on_this_one_event_implies_isCorrect : comp.

  Lemma M_run_ls_on_event_implies_has_correct_trace_before :
    forall {eo : EventOrdering} (e : Event) {L S} (ls1 ls2 : LocalSystem L S),
      M_run_ls_on_event ls1 e = Some ls2
      -> has_correct_trace_before e (loc e).
  Proof.
    intro es.
    induction e as [e ind] using predHappenedBeforeInd_type; introv h.
    rewrite M_run_ls_on_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; eauto 3 with eo comp;[].
    apply map_option_Some in h; exrepnd; rev_Some; simpl in *.
    rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred in h1; auto;[].
    apply ind in h1; autorewrite with eo in *; eauto 3 with eo comp.
  Qed.
  Hint Resolve M_run_ls_on_event_implies_has_correct_trace_before : comp.

  Lemma M_run_ls_on_event_implies_has_correct_trace_bounded :
    forall {eo : EventOrdering} (e : Event) {L S} (ls1 ls2 : LocalSystem L S),
      M_run_ls_on_event ls1 e = Some ls2
      -> has_correct_trace_bounded e.
  Proof.
    introv run; apply M_run_ls_on_event_implies_has_correct_trace_before in run; eauto 3 with eo.
  Qed.
  Hint Resolve M_run_ls_on_event_implies_has_correct_trace_bounded : comp.

  Lemma M_run_ls_before_event_implies_has_correct_trace_bounded_lt :
    forall {eo : EventOrdering} (e : Event) {L S} (ls1 ls2 : LocalSystem L S),
      M_run_ls_before_event ls1 e = Some ls2
      -> has_correct_trace_bounded_lt e.
  Proof.
    introv run.
    rewrite M_run_ls_before_event_unroll_on in run.
    destruct (dec_isFirst e); ginv; eauto 3 with comp eo.

  Qed.
  Hint Resolve M_run_ls_before_event_implies_has_correct_trace_bounded_lt : comp.

(*
  Lemma M_byz_run_ls_on_event_M_run_ls_on_event :
    forall {L S}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : LocalSystem L S),
      M_byz_run_ls_on_event ls1 e = Some (M_nt ls2)
      -> M_run_ls_on_event ls1 e = Some ls2.
  Proof.
    intros L S eo e.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_byz_run_ls_on_event_unroll in h.
    rewrite M_run_ls_on_event_unroll.
    destruct (dec_isFirst e).

    { eapply M_byz_run_ls_on_this_one_event_M_run_ls_on_this_one_event; eauto. }

    {
      rewrite M_run_ls_before_event_unroll_on.
      rewrite M_byz_run_ls_before_event_unroll_on in h.
      destruct (dec_isFirst e); tcsp;[].
      apply map_option_Some in h; exrepnd; rev_Some.

      unfold M_byz_run_M_trusted_ls_on_this_one_event in h0.
      apply on_M_trusted_implies_or in h0; repndors; exrepnd; subst; ginv;[]; rev_Some.
      eapply ind in h1; eauto 3 with eo.
      allrw; simpl; eauto 3 with comp.
    }
  Qed.
  Hint Resolve M_byz_run_ls_on_event_M_run_ls_on_event : comp.
*)

  Lemma M_byz_state_sys_on_event_if_M_state_sys_on_event :
    forall {F}
           (sys : M_USystem F)
           {eo  : EventOrdering}
           (e   : Event)
           (cn  : CompName)
           (s   : sf cn),
      M_state_sys_on_event sys e cn = Some s
      -> M_byz_state_sys_on_event sys e cn = Some s.
  Proof.
    introv h.
    rewrite M_state_sys_on_event_unfold in h.
    apply map_option_Some in h; exrepnd; symmetry in h0.

    eapply M_run_ls_on_event_M_byz_run_ls_on_event in h1.

    unfold M_byz_state_sys_on_event.
    unfold M_byz_state_ls_on_event.
    allrw; auto.
  Qed.
  Hint Resolve M_byz_state_sys_on_event_if_M_state_sys_on_event : comp.

(*  Lemma M_byz_state_sys_on_event_implies_M_state_sys_on_event :
    forall {F}
           (sys : M_USystem F)
           {eo  : EventOrdering}
           (e   : Event)
           (cn  : CompName)
           (s   : sf cn),
      M_byz_state_sys_on_event sys e cn = Some (M_nt s)
      -> M_state_sys_on_event sys e cn = Some s.
  Proof.
    introv h.

    unfold M_byz_state_sys_on_event in *.
    unfold M_byz_state_ls_on_event in *.
    unfold map_op_untrusted_op in *.
    rewrite map_option_Some in h.
    exrepnd.

    rewrite M_state_sys_on_event_unfold.
    apply map_option_Some; rev_Some.

    unfold map_untrusted_op in h0; simpl in *.
    apply on_M_trusted_implies_or in h0; repndors; exrepnd; subst; ginv; rev_Some.
    apply M_byz_run_ls_on_event_M_run_ls_on_event in h1.
    allrw.
    eexists; dands; eauto.
    apply option_map_Some in h2; exrepnd; ginv.
  Qed.
  Hint Resolve M_byz_state_sys_on_event_implies_M_state_sys_on_event : comp.
*)

  Definition M_byz_output_ls_on_this_one_event
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event) : option (event2out Sp e) :=
    snd (M_byz_run_ls_on_one_event ls e).

  Lemma M_byz_output_ls_on_event_as_run :
    forall {Lv Sp}
           (ls : LocalSystem Lv Sp)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_output_ls_on_event ls e
      = let ls' := M_byz_run_ls_before_event ls e
        in M_byz_output_ls_on_this_one_event ls' e.
  Proof.
    auto.
  Qed.

  Lemma M_run_ls_before_event_M_byz_run_ls_before_event :
    forall {L S}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : LocalSystem L S),
      M_run_ls_before_event ls1 e = Some ls2
      -> M_byz_run_ls_before_event ls1 e = ls2.
  Proof.
    intros L S eo e.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_run_ls_before_event_unroll in h.
    rewrite M_byz_run_ls_before_event_unroll.
    destruct (dec_isFirst e); ginv; auto;[].

    apply map_option_Some in h; exrepnd; rev_Some.
    apply ind in h1; eauto 3 with eo.
    allrw; simpl.
    eapply M_run_ls_on_this_one_event_M_byz_run_ls_on_this_one_event; eauto.
  Qed.

  (* Use this one instead of the other one *)
  Lemma M_byz_run_ls_on_event_unroll2 :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_run_ls_on_event ls e
      = let ls' := M_byz_run_ls_before_event ls e in
        M_byz_run_ls_on_this_one_event ls' e.
  Proof.
    introv; auto.
  Qed.

  (* Use this one instead of the other one *)
  Lemma M_run_ls_on_event_unroll2 :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_run_ls_on_event ls e
      = map_option
            (fun ls => M_run_ls_on_this_one_event ls e)
            (M_run_ls_before_event ls e).
  Proof.
    introv.
    rewrite M_run_ls_on_event_unroll.
    rewrite M_run_ls_before_event_unroll_on.
    destruct (dec_isFirst e); tcsp.
  Qed.

  Lemma in_M_output_ls_on_this_one_event_implies :
    forall {eo : EventOrdering} (e : Event)
           {Lv Sp} (ls : LocalSystem Lv Sp) out,
      In out (M_output_ls_on_this_one_event ls e)
      ->
      exists m comp,
        trigger_op e = Some m
        /\ find_name (msg_comp_name Sp) ls = Some comp
        /\ In out (M_break
                     (M_run_sm_on_input comp (time e) m)
                     ls
                     (fun subs out => snd out)).
  Proof.
    introv i.
    unfold M_output_ls_on_this_one_event in *.
    unfold time_trigger_op in *.
    remember (trigger_op e) as trig; symmetry in Heqtrig; destruct trig; simpl in *; ginv; tcsp; eauto.
    unfold M_run_ls_on_input_out in i.
    unfold M_run_ls_on_input in i.
    unfold on_comp in i.
    dest_cases w.
    eexists; eexists; dands; eauto.
    unfold M_break in *; dest_cases w; repnd; simpl in *; auto.
  Qed.

  Lemma M_break_mp :
    forall {n} {S}
           (sm   : M_n n S)
           (subs : n_procs n)
           (F G  : n_procs n -> S -> Prop),
      (forall subs out, F subs out -> G subs out)
      -> M_break sm subs F
      -> M_break sm subs G.
  Proof.
    introv imp m.
    unfold M_break in *.
    dest_cases w; tcsp.
  Qed.

  Lemma has_correct_trace_before_implies_trigger_eq :
    forall {eo : EventOrdering} (e : Event),
      has_correct_trace_before e (loc e)
      -> exists m, trigger e = trigger_info_data m.
  Proof.
    introv cor.
    pose proof (cor e) as cor; repeat (autodimp cor hyp); eauto 3 with eo.
    pose proof (cor e) as cor; repeat (autodimp cor hyp); eauto 3 with eo.
    unfold isCorrect, trigger_op in cor.
    remember (trigger e) as trig; destruct trig; simpl in *; tcsp; eauto.
  Qed.

  Lemma M_byz_run_ls_on_this_one_event_as_M_run_ls_on_this_one_event :
    forall {L S}
           {eo  : EventOrdering}
           (e   : Event)
           (ls1 : LocalSystem L S),
      has_correct_trace_before e (loc e)
      -> M_run_ls_on_this_one_event ls1 e
         = Some (M_byz_run_ls_on_this_one_event ls1 e).
  Proof.
    introv cor.
    unfold M_run_ls_on_this_one_event.
    unfold M_byz_run_ls_on_this_one_event.
    unfold M_byz_run_ls_on_one_event.
    applydup has_correct_trace_before_implies_trigger_eq in cor; exrepnd.
    unfold trigger_op.
    remember (M_byz_run_ls_on_input ls1 (msg_comp_name S) (time e) (trigger e)) as run; repnd; simpl in *.
    revert dependent run.
    rewrite cor1; simpl; introv h.
    unfold M_run_ls_on_input_ls; rewrite <- h; simpl; auto.
  Qed.

  Lemma has_correct_trace_bounded_lt_implies_before_local_pred :
    forall {eo : EventOrdering} (e : Event),
      ~isFirst e
      -> has_correct_trace_bounded_lt e
      -> has_correct_trace_before (local_pred e) (loc e).
  Proof.
    introv ni cor h q w.
    apply cor.
    assert (e' ⊏ e) as lte; eauto 3 with eo.
    destruct h as [h|h]; subst; eauto 3 with eo.
    split; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_bounded_lt_implies_before_local_pred : eo.

  Lemma has_correct_trace_before_local_implies_implies_lt :
    forall {eo : EventOrdering} (e : Event),
      has_correct_trace_before (local_pred e) (loc e)
      -> has_correct_trace_bounded_lt e.
  Proof.
    introv cor h.
    pose proof (cor e') as cor; repeat (autodimp cor hyp); eauto 3 with eo.
    assert (e' ⊑ (local_pred e)) as lte; eauto 3 with eo.
    apply localHappenedBefore_implies_le_local_pred; auto.
  Qed.
  Hint Resolve has_correct_trace_before_local_implies_implies_lt : eo.

  Lemma M_byz_run_ls_before_event_as_M_run_ls_before_event :
    forall {L S}
           {eo  : EventOrdering}
           (e   : Event)
           (ls1 : LocalSystem L S),
      has_correct_trace_bounded_lt e
      -> M_run_ls_before_event ls1 e
         = Some (M_byz_run_ls_before_event ls1 e).
  Proof.
    intros L S eo e.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_run_ls_before_event_unroll.
    rewrite M_byz_run_ls_before_event_unroll.
    destruct (dec_isFirst e); ginv; auto;[].

    rewrite ind; autorewrite with eo; eauto 3 with eo;[].
    simpl.
    rewrite M_byz_run_ls_on_this_one_event_as_M_run_ls_on_this_one_event;
      autorewrite with eo; eauto 3 with eo.
  Qed.

  (*Lemma correct_implies_byz_output_eq :
    forall {eo : EventOrdering} (e : Event)
           {Lv Sp}
           (ls : LocalSystem Lv Sp),
      has_correct_trace_before e (loc e)
      -> M_byz_output_ls_on_event_B ls e
         = m_byz_output_msg (msg_comp_name Sp) _ (M_output_ls_on_event ls e).
  Proof.
    introv cor.
    unfold M_byz_output_ls_on_event_B.
    rewrite M_output_ls_on_event_as_run_before.
    rewrite M_byz_run_ls_before_event_as_M_run_ls_before_event; auto.

    remember (M_byz_run_ls_before_event ls e) as w; clear Heqw.
    unfold M_byz_run_ls_on_one_event_B.
    unfold M_output_ls_on_this_one_event.
    applydup @has_correct_trace_before_implies_trigger_eq in cor; exrepnd.

    unfold event2M_byz_output, trigger_op.
    rewrite cor1; simpl.
    unfold M_run_ls_on_input_out; simpl; auto.
    remember (M_run_ls_on_input w (msg_comp_name Sp) m) as z; repnd; simpl.
    destruct z; simpl in *; auto.
  Qed.

  Lemma in_M_output_ls_on_event_implies_byz_eq :
    forall {eo : EventOrdering} (e : Event)
           {Lv Sp}
           (ls : LocalSystem Lv Sp)
           out,
      In out (M_output_ls_on_event ls e)
      -> M_byz_output_ls_on_event_B ls e
         = m_byz_output_msg (msg_comp_name Sp) _ (M_output_ls_on_event ls e).
  Proof.
    introv i.
    unfold M_byz_output_ls_on_event_B.
    unfold M_byz_run_ls_on_one_event_B.
    rewrite M_output_ls_on_event_as_run_before in i.
    rewrite M_output_ls_on_event_as_run_before.
    remember (M_run_ls_before_event ls e) as q; symmetry in Heqq; destruct q; simpl in *; tcsp.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in Heqq as w.
    rewrite w; simpl.
    applydup @in_M_output_ls_on_this_one_event_implies in i as j; exrepnd.
    unfold M_output_ls_on_this_one_event.
    allrw; simpl.
    applydup trigger_op_Some_implies_trigger_message in j0.
    unfold event2M_byz_output; simpl.
    allrw; simpl.
    unfold M_run_ls_on_input_out; simpl.
    remember (M_run_ls_on_input l (msg_comp_name Sp) m) as z; repnd; simpl in *; tcsp.
    destruct z; simpl; auto.
  Qed.*)

  Lemma dmsg_is_in_out {s} {eo : EventOrdering} {e : Event}
        (m : DirectedMsg)
        (o : event2out s e) : Prop.
  Proof.
    unfold event2out in o.
    remember (trigger e) as trig; destruct trig; simpl in *.
    { exact (In m o). }
    { destruct o. }
    { exact False. }
  Defined.

  Lemma dmsgs_are_out {s} {eo : EventOrdering} {e : Event}
        (l : DirectedMsgs)
        (o : event2out s e) : Prop.
  Proof.
    unfold event2out in o.
    remember (trigger e) as trig; destruct trig; simpl in *.
    { exact (o = l). }
    { destruct o. }
    { exact False. }
  Defined.

  Lemma in_M_output_ls_on_event_implies_byz_eq :
    forall {eo : EventOrdering} (e : Event)
           {Lv Sp}
           (ls : LocalSystem Lv Sp)
           (m  : DirectedMsg),
      In m (M_output_ls_on_event ls e)
      -> exists o,
        M_byz_output_ls_on_event ls e = Some o
        /\ dmsg_is_in_out m o.
  Proof.
    introv i.
    unfold M_byz_output_ls_on_event.
    apply M_output_ls_on_event_implies_run in i; exrepnd.
    apply M_run_ls_before_event_M_byz_run_ls_before_event in i1; allrw; simpl.
    clear i1.

    unfold M_output_ls_on_this_one_event in i0.
    unfold M_run_ls_on_input_out in i0.
    unfold M_byz_run_ls_on_one_event.
    unfold time_trigger_op, trigger_op, event2out, dmsg_is_in_out in *; simpl in *.
    remember (trigger e) as trig; clear Heqtrig.
    destruct trig; simpl in *; tcsp.
    apply in_olist2list in i0; exrepnd; simpl in *.
    unfold LocalSystem in *; simpl in *; rewrite i0.
    eexists; dands; eauto.
  Qed.

  Lemma eq_cons :
    forall {T} (x1 x2 : T) l1 l2,
      x1 :: l1 = x2 :: l2 -> x1 = x2 /\ l1 = l2.
  Proof.
    introv h; inversion h; auto.
  Qed.

  Lemma incr_n_proc_inj :
    forall {n} {cn} (p q : n_proc n cn),
      incr_n_proc p = incr_n_proc q
      -> p = q.
  Proof.
    unfold incr_n_proc; introv h; inversion h; auto.
  Qed.

  Lemma incr_n_nproc_inj :
    forall {n} (a b : n_nproc n),
      incr_n_nproc a = incr_n_nproc b
      -> a = b.
  Proof.
    introv h.
    destruct a, b; simpl in *.
    inversion h; subst.
    apply decomp_p_nproc in h.
    apply incr_n_proc_inj in h; subst; auto.
  Qed.

  Lemma incr_n_procs_inj :
    forall {n} (l k : n_procs n),
      incr_n_procs l = incr_n_procs k
      -> l = k.
  Proof.
    unfold incr_n_procs.
    induction l; destruct k; introv h; simpl in *; tcsp.
    apply eq_cons in h; repnd.
    apply IHl in h; clear IHl; subst.
    apply incr_n_nproc_inj in h0; subst; auto.
  Qed.

  Definition M_byz_output_sys_on_this_one_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : option (event2out (fls_space F (loc e)) e) :=
    M_byz_output_ls_on_this_one_event (sys (loc e)) e.

  Definition is_trusted_event {eo : EventOrdering} (e : Event) (i : ITrusted) :=
    trigger e = trigger_info_trusted i.

  Lemma trusted_is_in_out {s} {eo : EventOrdering} {e : Event}
        {i}
        (p : is_trusted_event e i)
        (x : iot_output (iot_fun (it_name i)))
        (o : event2out s e) : Prop.
  Proof.
    unfold event2out in o.
    unfold is_trusted_event in p.
    rewrite p in o; simpl in *.
    exact (x = o).
  Defined.

  Lemma has_correct_trace_before_implies_isCorrect :
    forall {eo : EventOrdering} (e : Event),
      has_correct_trace_before e (loc e) -> isCorrect e.
  Proof.
    introv cor; eapply cor; eauto 3 with eo.
  Qed.
  Hint Resolve has_correct_trace_before_implies_isCorrect : eo.

  Lemma correct_byz_output_implies :
    forall {n} {s} (ls : LocalSystem n s) {eo : EventOrdering} (e : Event) (o : event2out s e),
      has_correct_trace_before e (loc e)
      -> M_byz_output_ls_on_event ls e = Some o
      ->
      exists (i : msg) (msgs : DirectedMsgs),
        trigger e = trigger_info_data i
        /\ dmsgs_are_out msgs o
        /\ M_output_ls_on_event ls e = msgs.
  Proof.
    introv cor out.
    applydup has_correct_trace_before_implies_isCorrect in cor.
    unfold M_byz_output_ls_on_event in *.
    unfold M_byz_run_ls_on_one_event in *.
    unfold M_output_ls_on_event in *.
    unfold event2out, dmsgs_are_out, isCorrect, trigger_op in *; simpl in *.
    remember (trigger e) as trig; destruct trig; simpl in *; tcsp; GC.
    exists d o; dands; auto.
    rewrite M_byz_run_ls_before_event_as_M_run_ls_before_event; auto; simpl.
    unfold M_output_ls_on_this_one_event.
    unfold time_trigger_op, trigger_op; allrw <-; simpl.
    unfold M_run_ls_on_input_out; simpl in *.
    unfold LocalSystem in *; rewrite out; simpl; auto.
    eauto 3 with eo comp.
  Qed.

  Lemma in_M_output_ls_on_this_one_event_implies_in_byz :
    forall {eo : EventOrdering} (e : Event) {n} {s} (ls : LocalSystem n s) m,
      In m (M_output_ls_on_this_one_event ls e)
      -> exists (o : event2out _ e),
          M_byz_output_ls_on_this_one_event ls e = Some o /\ dmsg_is_in_out m o.
  Proof.
    introv out.
    unfold M_output_ls_on_this_one_event in out.
    apply in_olist2list in out; exrepnd.
    apply map_option_Some in out1; exrepnd; rev_Some; simpl in *.
    unfold M_run_ls_on_input_out in out2.

    unfold M_byz_output_ls_on_this_one_event.
    unfold M_byz_run_ls_on_one_event.
    applydup time_trigger_op_some_implies_time in out1; subst.
    applydup time_trigger_op_some_implies_time_trigger_op in out1 as trig.
    apply trigger_op_Some_implies_trigger_message in trig.
    remember (M_byz_run_ls_on_input ls (msg_comp_name s) (time e) (trigger e)) as z; symmetry in Heqz; repnd; simpl in *.
    revert z Heqz; clear out1.
    unfold event2out, dmsg_is_in_out in *; rewrite trig; simpl; introv run.
    rewrite run in out2; simpl in *; subst; simpl in *.
    exists l; dands; auto.
  Qed.

  Lemma in_M_output_sys_on_event_implies_in_byz :
    forall {eo : EventOrdering} (e : Event) {F} (sys : M_USystem F) m,
      In m (M_output_sys_on_event sys e)
      -> exists (o : event2out _ e),
        M_byz_output_sys_on_event sys e = Some o
        /\ dmsg_is_in_out m o.
  Proof.
    introv out.
    apply M_output_ls_on_event_as_run in out; exrepnd.
    unfold M_byz_output_sys_on_event.
    rewrite M_byz_output_ls_on_event_as_run.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in out1 as xx.
    allrw; simpl; clear xx.
    apply in_M_output_ls_on_this_one_event_implies_in_byz; auto.
  Qed.

  (*Definition M_byz_output_ls_on_event_trusted
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event)
             (i  : ITrusted) : option (iot_output (iot_fun (it_name i))) :=
    snd (M_run_ls_on_trusted
           (M_byz_run_ls_before_event ls e)
           i).

  Definition M_byz_output_sys_on_event_trusted
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event)
             (i   : ITrusted) : option (iot_output (iot_fun (it_name i))) :=
    M_byz_output_ls_on_event_trusted (sys (loc e)) e i.*)

End ComponentSM.


Hint Constructors similar_procs.
Hint Constructors similar_subs.


Hint Resolve similar_subs_refl : comp.
Hint Resolve similar_sms_refl : comp.
Hint Resolve similar_procs_refl : comp.
Hint Resolve similar_subs_refl : comp.
Hint Resolve similar_sms_sym : comp.
Hint Resolve similar_procs_sym : comp.
Hint Resolve similar_subs_sym : comp.
Hint Resolve similar_sms_trans : comp.
Hint Resolve similar_procs_trans : comp.
Hint Resolve similar_subs_trans : comp.
Hint Resolve state_of_component_if_similar : comp.
Hint Resolve ls_preserves_subs_implies_M_run_update_on_list : comp.
(*Hint Resolve ls_preserves_subs_implies_M_run_update_on_list2 : comp.*)
Hint Resolve M_run_ls_on_this_one_event_implies_isCorrect : comp.
Hint Resolve M_run_ls_on_event_implies_has_correct_trace_before : comp.
Hint Resolve M_run_ls_on_event_implies_has_correct_trace_bounded : comp.
Hint Resolve M_run_ls_before_event_implies_has_correct_trace_bounded_lt : comp.
(*Hint Resolve M_byz_run_ls_on_this_one_event_M_run_ls_on_this_one_event : comp.*)
(*Hint Resolve M_byz_run_ls_on_event_M_run_ls_on_event : comp.*)
Hint Resolve M_byz_state_sys_on_event_if_M_state_sys_on_event : comp.
(*Hint Resolve M_byz_state_sys_on_event_implies_M_state_sys_on_event : comp.*)
Hint Resolve similar_sms_at_refl : comp.
Hint Resolve similar_sms_at_sym : comp.
Hint Resolve similar_sms_at_trans : comp.


Hint Rewrite @select_n_proc_trivial : comp.
Hint Rewrite @select_n_procs_trivial : comp.
Hint Rewrite @lift_n_procs_0 : comp.
Hint Rewrite @mapOption_fun_Some : list.
Hint Rewrite @mapOption_fun_None : list.


Hint Rewrite @crazy_bind_option1 : comp.
Hint Rewrite @bind_ret : comp.
Hint Rewrite @bind_ret_fun : comp.
Hint Rewrite @M_on_some_some : comp.
Hint Rewrite @crazy_bind_option2 : comp.
Hint Rewrite @M_break_ret : comp.
Hint Rewrite @bind_some_ret_some : comp.
Hint Rewrite @bind_some_ret_some_fun : comp.
Hint Rewrite @M_on_some_ret_some : comp.
Hint Rewrite @M_on_some_ret_some_fun : comp.
(*Hint Rewrite @map_op_untrusted_option_map_M_nt : comp.*)
(*Hint Rewrite @M_break_map_op_untrusted_option_map_M_nt : comp.*)
(*Hint Rewrite @on_M_trusted_map_untrusted : comp.*)
Hint Rewrite @on_M_some_ret_Some : comp.
(*Hint Rewrite @on_M_trusted_M_nt : comp.*)
(*Hint Rewrite @on_M_trusted_M_t : comp.*)
Hint Rewrite @M_break_bind : comp.
Hint Rewrite @M_break_bind_pair : comp.
Hint Rewrite @M_break_bind_ret : comp.


Hint Resolve M_state_sys_before_event_if_on_event_direct_pred : proc.


Hint Resolve sub_local_key_map_preserves_in_lookup_receiving_keys : eo.
Hint Resolve verify_authenticated_data_if_sub_keys : eo.
Hint Resolve has_correct_trace_before_implies_isCorrect : eo.
Hint Resolve has_correct_trace_bounded_lt_implies_before_local_pred : eo.
Hint Resolve has_correct_trace_before_local_implies_implies_lt : eo.


Delimit Scope comp with comp.


Notation "a >>= f"   := (bind a f)      (at level 80).
Notation "a >>>= f"  := (bind_pair a f) (at level 80).
Notation "a >p>= f"  := (pbind a f)     (at level 80).
Notation "a >>o>> f" := (M_on_some f a) (at level 80).
Notation "a >>o= f"  := (bind_some a f) (at level 80).

Notation "d ∈ sys ⇝ e" := (In d (M_output_sys_on_event sys e)) (at level 70).
