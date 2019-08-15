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
  Context { iot : @IOTrusted }.


  Definition CompNameKind  := String.string.
  Definition CompNameSpace := nat.
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
        comp_name_kind  : CompNameKind;
        comp_name_space : CompNameSpace;
        comp_name_trust : CompNameTrust (* TrustTag *);
      }.

  Definition MkCN
             (k : CompNameKind)
             (s : CompNameSpace)
             (t : CompNameTrust)
    : CompName :=
    MkCompName k s t.

  Lemma CompNameDeq : Deq CompName.
  Proof.
    introv; unfold deceq; destruct x as [n1 s1 b1], y as [n2 s2 b2].
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

  (* monad update function of the component that can halt *)
  Definition MP_Update (p : CompName -> Type) (I O S : Type) :=
    S -> I -> M_p p (option S * O).

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

  Definition CIOtrusted : ComponentIO :=
    MkComponentIO iot_input iot_output iot_def_output.

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
        tsf : Type;
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
  Definition msg_comp_name_trust : CompNameTrust := false.
  Definition msg_comp_name_state : CompNameState := 0.
  Definition msg_comp_name n : CompName :=
    MkCN
      msg_comp_name_kind
      n
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
    if comp_name_trust nm then CIOtrusted
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
    if comp_name_trust nm then tsf
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
  Definition lookup_table : ref (list {cn : CompName & {b : bool & cio_I (fio cn) -> (unit * cio_O (fio cn))}}) :=
    ref_cons [].

  Definition update_lookup
             (level   : nat)
             (name    : CompName)
             (sm      : cio_I (fio name) -> (unit * cio_O (fio name))) :=
    update_ref
      lookup_table
      ((existT _ name (existT _ (comp_name_trust name) sm)) :: get_ref lookup_table).
  (* ====== ======= *)


  (* state machine as monad -- one level state machine*)
  Record MP_StateMachine (p : CompName -> Type) (cn : CompName) : Type :=
    MkMPSM
      {
        sm_halted : bool;
        sm_update :> MP_Update p (cio_I (fio cn)) (cio_O (fio cn)) (sf cn);
        sm_state  : sf cn;
      }.
  Global Arguments MkMPSM    [p] [cn] _ _ _.
  Global Arguments sm_halted [p] [cn] _.
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
    S -> cio_I (fio nm) -> M_n n (option S * cio_O (fio nm)).

  (* return state and output ? *)
  Definition ret {A} (n : nat) (a : A) : M_n n A := fun s => (s, a).

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

  Fixpoint replace_name {n:nat} {nm : CompName} (pr : n_proc n nm) (l : n_procs n) : n_procs n :=
    match l with
    | [] => []
    | MkPProc m q :: rest =>
      if CompNameDeq m nm then MkPProc nm pr :: rest
      else MkPProc m q :: replace_name pr rest
    end.

  Definition at2sm
             {n  : nat}
             {cn : CompName}
             (p  : n_proc_at n cn) : n_proc (S n) cn :=
    sm_or_at p.

  (* halted state machine as monad -- one level state machine*)
  Definition MP_haltedSM
             (cn : CompName)
             (n  : nat)
             (d  : sf cn) : n_proc_at n cn :=
    MkMPSM
      true
      (fun s i p => (p, (None, cio_default_O (fio cn))))
      d.

  (* halted state machine as monad -- state machine can have multiple levels*)
  Definition M_haltedSM
             (nm : CompName)
             (n  : nat)
             (d  : sf nm) : n_proc 1 nm :=
    at2sm
      (MkMPSM
         true
         (fun s i p => (p, (None, cio_default_O (fio nm))))
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
    | 0 => fun p => Some p
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
    | 0 => fun p => p
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
      (sm_halted sm)
      (sm_update sm)
      s.

  Definition halt_machine {n} {cn} (sm : n_proc_at n cn) : n_proc_at n cn :=
    MkMPSM
      true
      (sm_update sm)
      (sm_state  sm).

  (* lift form state to state machine; here x is sub-component with state and output*)
  Definition app_n_proc_at {n} {nm}
             (sm : n_proc_at n nm)
             (i  : cio_I (fio nm))
    : M_n n (n_proc_at n nm * cio_O (fio nm)) :=
    (sm_update sm (sm_state sm) i)
      >>>=
      fun ops o =>
        match ops with
        | Some s => ret _ (update_state sm s,o)
        | None => ret _ (halt_machine sm, o)
        end.

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

  (* apply process to the input; monad takes care of the sub-levels *)
  Fixpoint app_m_proc {n} {nm}
    : n_proc n nm
      -> cio_I (fio nm)
      -> M_n (pred n) (n_proc n nm * cio_O (fio nm)) :=
    match n return n_proc n nm -> cio_I (fio nm) -> M_n (pred n) (n_proc n nm * cio_O (fio nm)) with
    | 0 =>
      fun pr i => match pr with end
    | S m =>
      fun pr i =>
        match pr with
        | sm_or_at sm => lift_M_O (app_n_proc_at sm i)
        | sm_or_sm pr' => lift_M_O2 (app_m_proc pr' i)
        end
    end.

  (* replace subprocess *)
  Fixpoint replace_sub {n} {nm}
           (ps : n_procs n)
           (p  : n_proc (pred n) nm) : n_procs n :=
    match ps with
    | [] => []
    | MkPProc m q :: rest =>
      if CompNameDeq nm m then MkPProc nm (incr_pred_n_proc p) :: rest
      else MkPProc m q :: replace_sub rest p
    end.

  (* replace subprocesses in a list*)
  Fixpoint replace_subs {n} (ps : n_procs n) (l : n_procs (pred n)) : n_procs n :=
    match l with
    | [] => ps
    | p :: rest =>
      match p with
      | MkPProc nm q => replace_subs (replace_sub ps q) rest
      end
    end.

  (* used in MinBFT *)
  Definition call_proc {n:nat} (nm : CompName) (i : cio_I (fio nm)) : M_n n (cio_O (fio nm)) :=
    fun (l : n_procs n) =>
      match find_name nm l with
      | Some pr =>
        match app_m_proc pr i (decr_n_procs l) with
        | (l',(pr',o)) => (replace_subs (replace_name pr' l) l',o)
        end
      | None => (l,cio_default_O (fio nm))
      end.

  (* We had to break the abstraction because Coq didn't like [build_m_process]. *)
  Definition build_mp_sm {n}
             {nm  : CompName}
             (upd : M_Update n nm (sf nm))
             (s   : sf nm) : n_proc_at n nm :=
    MkMPSM false upd s.

  Definition build_m_sm {n}
             {nm  : CompName}
             (upd : M_Update n nm (sf nm))
             (s   : sf nm) : n_proc (S n) nm :=
    at2sm (build_mp_sm upd s).

  (* ??? *)
  Fixpoint run_n_proc {n} {nm} (p : n_proc n nm) (l : list (cio_I (fio nm)))
    : M_n (pred n) (list (cio_O (fio nm)) * n_proc n nm) :=
    match l with
    | [] => ret _ ([], p)
    | i :: rest =>
      (app_m_proc p i)
        >>>= fun p' o =>
               (run_n_proc p' rest)
                 >>>= fun outs p'' => ret _ (o :: outs, p'')
    end.

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

  Fixpoint sm2level {n} {nm} : n_proc n nm -> nat :=
    match n return n_proc n nm -> nat with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | sm_or_at q => m
               | sm_or_sm q => sm2level q
               end
    end.

  Record LocalSystem (lvl : nat) (cn : CompName) :=
    MkLocalSystem
      {
        ls_main :> n_proc_at lvl cn;
        ls_subs : n_procs lvl;
      }.
  Global Arguments MkLocalSystem [lvl] [cn] _ _.
  Global Arguments ls_main [lvl] [cn] _.
  Global Arguments ls_subs [lvl] [cn] _.

  Definition MLocalSystem lvl space := LocalSystem lvl (msg_comp_name space).

  Definition defaultLocalSystem : MLocalSystem 0 1 :=
    MkLocalSystem
      (MP_haltedSM munit_comp_name 0 tt)
      [].

  Lemma decomp_LocalSystem {L} {S} :
    forall (ls1 ls2 : LocalSystem L S),
      ls1 = ls2 -> ls_main ls1 = ls_main ls2 /\ ls_subs ls1 = ls_subs ls2.
  Proof.
    introv h; subst; dands; auto.
  Qed.

  Definition upd_ls_main {L} {S} (ls : LocalSystem L S) (m : n_proc_at _ _) : LocalSystem L S :=
    MkLocalSystem
      m
      (ls_subs ls).

  Definition upd_ls_main_state {L} {S} (ls : LocalSystem L S) (s : sf _) : LocalSystem L S :=
    MkLocalSystem
      (update_state (ls_main ls) s)
      (ls_subs ls).

  Definition upd_ls_subs {L} {S} (ls : LocalSystem L S) (ss : n_procs _) : LocalSystem L S :=
    MkLocalSystem
      (ls_main  ls)
      ss.

  Definition upd_ls_main_state_and_subs
             {L} {S}
             (ls : LocalSystem L S)
             (s  : sf _)
             (ss : n_procs _) : LocalSystem _ _ :=
    MkLocalSystem
      (update_state (ls_main ls) s)
      ss.

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
        fls_level : name -> nat;
        fls_space : name -> nat;
      }.

  Definition M_USystem (F : funLevelSpace) :=
    forall (n : name), MLocalSystem (fls_level F n) (fls_space F n).

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
             (f : A -> M_n n (option B))
             (xop : option A) : M_n n (option B) :=
    match xop with
    | Some a => f a
    | None => ret _ None
    end.

  Notation "a >>o>> f" := (M_on_some f a) (at level 80).

  Definition bind_some {A B} {n:nat}
             (m : M_n n (option A))
             (f : A -> M_n n (option B)) : M_n n (option B) :=
    m >>= fun x => x >>o>> f.

  Notation "a >>o= f" := (bind_some a f) (at level 80).

  Definition M_op_update {S} {n} {nm}
             (upd : M_Update n nm S)
             (s   : S)
             (o   : option (cio_I (fio nm)))
    : M_n n (option (option S * cio_O (fio nm))) :=
    o >>o>> (fun i => (upd s i) >>= fun so => ret _ (Some so)).

  Definition M_op_state {S} {n} {nm}
             (upd : M_Update n nm S)
             (s   : S)
             (o   : option (cio_I (fio nm)))
    : M_n n (option S) :=
    o >>o>> (fun i => (upd s i) >>= fun so => ret _ (fst so)).

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
  Fixpoint M_run_update_on_list {S} {n} {nm}
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
    end.

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

  Definition M_run_sm_on_list {n} {nm}
             (sm : n_proc n nm)
             (l  : oplist (cio_I (fio nm))) : M_n (sm2level sm) (option (sf nm)) :=
    M_run_update_on_list (sm2state sm) (sm2update sm) l.

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

  Definition M_run_update_on_event {S} {n} {k}
             (s    : S)
             (upd  : M_Update n (msg_comp_name k) S)
             {eo   : EventOrdering}
             (e    : Event) : M_n n (op_state_out S) :=
    (M_run_update_on_list s upd (map trigger_op (@localPreds pn pk pm _ _ eo e)))
      >>o= fun s => M_op_update upd s (trigger_op e).

  Definition M_run_sm_on_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (op_state_out (sf (msg_comp_name k))) :=
    M_run_update_on_event (sm2state sm) (sm2update sm) e.

  Definition M_state_sm_on_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (option (sf (msg_comp_name k))) :=
  (M_run_sm_on_event sm e)
    >>o= fun p => ret _ (fst p).

  Definition M_state_sm_before_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (option (sf (msg_comp_name k))) :=
    M_run_sm_on_list sm (map trigger_op (@localPreds pn pk pm _ _ eo e)).



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

  Definition M_run_ls_on_event
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (LocalSystem _ _) :=
    M_break
      (M_state_sm_on_event (at2sm (ls_main ls)) e)
      (ls_subs ls)
      (fun subs' out =>
         option_map
           (fun s => upd_ls_main_state_and_subs ls s subs')
           out).

  Definition M_run_ls_before_event
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (LocalSystem _ _) :=
    M_break
      (M_state_sm_before_event (at2sm (ls_main ls)) e)
      (ls_subs ls)
      (fun subs' out =>
         option_map
           (fun s => upd_ls_main_state_and_subs ls s subs')
           out).


  (*Lemma break_M_run_ls_before_event :
    forall (ls  : LocalSystem)
           {eo  : EventOrdering}
           (e   : Event)
           (ls' : LocalSystem),
      M_run_ls_before_event ls e = Some ls'
      -> exists s,
        M_state_sm_before_event (n_proc_at2nproc (ls_main ls)) e (ls_subs ls)
        = (ls_subs ls', Some (sm_state (ls_main ls'))).*)


  Definition state_of_subcomponents
             {n}
             (procs : n_procs n)
             (cn : CompName) : option (sf cn) :=
    option_map sm2state (find_name cn procs).

  Definition state_of_component
             {L S}
             (cn : CompName)
             (ls : LocalSystem L S) : option (sf cn) :=
    match ls with
    | MkLocalSystem main subs =>
      match CompNameDeq S cn with
      | left p => Some (eq_rect _ _ (sm_state main) _ p)
      | right q => state_of_subcomponents subs cn
      end
    end.

  Definition on_state_of_component
             {L S}
             (cn : CompName)
             (ls : LocalSystem L S)
             (F  : sf cn -> Prop) : Prop :=
    match state_of_component cn ls with
    | Some s => F s
    | None => True
    end.

  Definition M_state_ls_on_event
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event)
             (cn : CompName) : option (sf cn) :=
    map_option
      (state_of_component cn)
      (M_run_ls_on_event ls e).

  Definition M_state_ls_before_event
             {L S}
             (ls : MLocalSystem L S)
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
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (LocalSystem _ _) :=
    map_option
      (fun i =>
         M_break
           (sm_update (ls_main ls) (sm_state (ls_main ls)) i)
           (ls_subs ls)
           (fun subs' out =>
              option_map
                (fun s => upd_ls_main_state_and_subs ls s subs')
                (fst out)))
      (trigger_op e).

  Lemma crazy_bind_option1 :
    forall {n A O} (F : A -> M_n n (option A ## O)),
      (fun a : option A =>
         (a >>o>>
            (fun s : A => (F s) >>= (fun so : option A ## O => ret _ (Some so))))
           >>o= fun p : option A ## O => ret _ (fst p))
      = fun (a : option A) =>
          a >>o>> fun s => F s >>= fun x => ret _ (fst x).
  Proof.
    introv.
    apply functional_extensionality; introv; simpl.
    apply functional_extensionality; introv; simpl.
    unfold bind_some, bind, M_on_some; simpl.
    destruct x; simpl; auto.
    destruct (F a x0); simpl; auto.
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
    forall {n A B} a (f : A -> M_n n (option B)),
      ((Some a) >>o>> f) = f a.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @M_on_some_some : comp.

  Lemma M_on_some_some_fun :
    forall {n A B X} (x : X) (F : X -> A) (f : A -> M_n n (option B)),
      (fun x => (Some (F x)) >>o>> f) = (fun x => f (F x)).
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
    forall {n nm A} a (upd : M_Update n nm A) (o : option (cio_I (fio nm))),
      ((a >>o= fun s : A => M_op_update upd s o)
         >>o= fun p : option A ## cio_O (fio nm) => ret n (fst p))
      = (a >>o= fun s => M_op_state upd s o).
  Proof.
    introv; apply functional_extensionality; introv; simpl.
    unfold M_op_update, M_op_state, bind_some, bind, M_on_some, ret; simpl.
    destruct (a x); simpl.
    destruct o0; auto.
    destruct o; auto.
    destruct (upd a0 c n0); auto.
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
           (a    : option A)
           (sm   : A -> M_n n (option S))
           (subs : n_procs n)
           (F    : n_procs n -> option S -> option O),
      (forall subs', F subs' None = None)
      -> M_break
           (a >>o>> sm)
           subs
           F
         = map_option
             (fun a => M_break (sm a) subs F)
             a.
  Proof.
    introv imp.
    unfold option_map, map_option, M_break, M_on_some, ret.
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
    forall {n} {A B} (a : A) (f : A -> M_n n (option B)),
      ((ret n (Some a)) >>o= f) = f a.
  Proof.
    introv.
    apply functional_extensionality; introv; simpl.
    unfold bind_some, bind; simpl.
    destruct (f a x); auto.
  Qed.
  Hint Rewrite @bind_some_ret_some : comp.

  Definition bind_some_ret_some_fun :
    forall {n} {T A B} (f : A -> M_n n (option B)) (F : T -> A),
      (fun a => ((ret n (Some (F a))) >>o= f)) = fun x => f (F x).
  Proof.
    introv.
    apply functional_extensionality; introv; simpl; autorewrite with comp; auto.
  Qed.
  Hint Rewrite @bind_some_ret_some_fun : comp.

  Lemma bind_bind_some :
    forall {n} {A B C} (m : M_n n A) (f : A -> M_n n (option B)) (g : B -> M_n n (option C)),
      ((m >>= f) >>o= g)
      = (m >>= (fun a => ((f a) >>o= g))).
  Proof.
    introv; apply functional_extensionality; introv; simpl.
    unfold bind_some, bind, M_on_some; simpl.
    destruct (m x).
    destruct (f a n0).
    destruct o; simpl; auto.
    destruct (g b n1); auto.
  Qed.

  Lemma M_break_bind_some :
    forall {n A B O}
           (a    : M_n n (option A))
           (G    : A -> M_n n (option B))
           (subs : n_procs n)
           (F    : n_procs n -> option B -> option O),
      (forall subs, F subs None = None)
      -> M_break
           (a >>o= G)
           subs
           F
         = M_break
             a
             subs
             (fun subs' (aop : option A) =>
                map_option
                  (fun (a : A) => M_break (G a) subs' F)
                  aop).
  Proof.
    introv imp.
    unfold M_break, bind_some, bind, M_on_some; simpl.
    destruct (a subs); auto.
    destruct o; simpl; auto.
    destruct (G a0 n0); auto.
  Qed.

  Lemma M_break_bind_some_ret :
    forall {n A B O}
           (a    : M_n n (option A))
           (G    : A -> option B)
           (subs : n_procs n)
           (F    : n_procs n -> option B -> option O),
      (forall subs, F subs None = None)
      -> M_break
           (a >>o= fun p => ret _ (G p))
           subs
           F
         = M_break
             a
             subs
             (fun subs' aop => map_option (fun a => F subs' (G a)) aop).
  Proof.
    introv imp.
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

  Lemma M_run_ls_on_event_unroll :
    forall {L S}
           (ls : MLocalSystem L S)
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
    unfold M_run_ls_on_event, M_run_ls_before_event; simpl.
    destruct ls; simpl.
    unfold M_state_sm_on_event, M_state_sm_before_event.
    unfold M_run_sm_on_event.
    unfold M_run_update_on_event; simpl.
    unfold M_run_sm_on_list; simpl.
    unfold M_run_ls_on_this_one_event; simpl.

    destruct (dec_isFirst e) as [d|d].

    {
      rewrite isFirst_implies_localPreds_eq; simpl; auto.
      unfold M_op_update; simpl.
      destruct (trigger_op e); simpl; auto;[].
      auto_rw_bind.
    }

    auto_rw_bind.
    rewrite M_break_bind_some; simpl; tcsp.
    rewrite map_option_M_break.
    apply eq_M_break; introv.
    rewrite map_option_option_map; unfold compose; simpl.
    apply equal_map_options; introv eqs; subst; simpl in *.
    unfold M_op_update; rewrite M_break_M_on_some_option_map; simpl; auto;[].
    apply equal_map_options; introv eqs; subst; simpl in *.
    rewrite M_break_bind.
    apply eq_M_break; introv; autorewrite with comp; auto.
  Qed.

  Lemma M_on_some_ret_some :
    forall {n A} (a : option A),
      (a >>o>> fun a => ret n (Some a))
      = ret _ a.
  Proof.
    destruct a; simpl; auto.
  Qed.
  Hint Rewrite @M_on_some_ret_some : comp.

  Lemma M_on_some_ret_some_fun :
    forall {n A B} (F : B -> option A),
      (fun x => F x >>o>> fun a => ret n (Some a))
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
    forall {A B} {n:nat} (m : option A) (f g : A -> M_n n (option B)),
      (forall a, f a = g a)
      -> (m >>o>> f) = (m >>o>> g).
  Proof.
    introv imp; apply functional_extensionality; introv; unfold M_on_some; simpl; auto.
    destruct m; auto.
    rewrite imp; auto.
  Qed.

  Lemma M_on_some_bind_M_on_some :
    forall {n A B C}
           (xop : option A)
           (f : A -> M_n n (option B))
           (g : B -> M_n n (option C)),
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
           (i    : option (cio_I (fio nm)))
           (subs : n_procs n)
           (F    : n_procs n -> _ -> option O),
      (forall subs', F subs' None = None)
      -> M_break
           (M_op_state upd s i)
           subs
           F
         = map_option
             (fun i => M_break (upd s i) subs (fun subs' s => F subs' (fst s)))
             i.
  Proof.
    introv imp.
    unfold M_break; destruct i; simpl; auto.
    unfold bind; simpl.
    destruct (upd s c subs); auto.
  Qed.

  Lemma bind_some_bind_M_on_some :
    forall {n} {A B C}
           (m : M_n n (option A))
           (f : A -> M_n n (option B))
           (g : B -> M_n n (option C)),
      ((m >>o= f) >>= (fun b => b >>o>> g))
      = (m >>o= fun a => (f a) >>= fun b => b >>o>> g).
  Proof.
    introv; apply functional_extensionality; introv; simpl.
    unfold bind_some, bind, M_on_some; simpl.
    destruct (m x).
    destruct o; simpl; auto.
    destruct (f a n0).
    destruct o; simpl; auto.
    destruct (g b n1); auto.
  Qed.

  Lemma bind_some_bind_some :
    forall {n A B C}
           (a : M_n n (option A))
           (f : A -> M_n n (option B))
           (g : B -> M_n n (option C)),
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
           (a : option A)
           (f : A -> M_n n (option B))
           (g : B -> M_n n (option C)),
      ((a >>o>> f) >>o= g)
      = (a >>o>> (fun a => (f a) >>o= g)).
  Proof.
    introv; unfold M_on_some, bind_some.
    destruct a; simpl; auto.
  Qed.

  Lemma eq_bind_some :
    forall {A B} {n:nat} (m : M_n n (option A)) (f g : A -> M_n n (option B)),
      (forall a, f a = g a)
      -> (m >>o= f) = (m >>o= g).
  Proof.
    introv imp; apply functional_extensionality; introv.
    unfold bind_some, bind, M_on_some; simpl; auto.
    destruct (m x); auto.
    destruct o; simpl; auto.
    rewrite imp; auto.
  Qed.

  Lemma M_run_update_on_list_snoc :
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
  Qed.

  Lemma M_run_ls_before_event_unroll :
    forall {L S}
           (ls : MLocalSystem L S)
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
    unfold M_run_ls_before_event; destruct ls; simpl.
    unfold M_state_sm_before_event.

    destruct (dec_isFirst e) as [d|d].

    { rewrite isFirst_implies_localPreds_eq; simpl; auto.
      destruct ls_main0; simpl; auto. }

    rewrite (localPreds_unroll e) at 1; auto; simpl.
    unfold M_run_sm_on_list; simpl.
    rewrite map_snoc; simpl.

    rewrite @M_run_update_on_list_snoc.
    rewrite map_option_M_break.
    rewrite M_break_bind_some; simpl; tcsp;[].
    apply eq_M_break; introv; simpl.
    rewrite map_option_option_map; unfold compose; simpl.
    apply equal_map_options; introv; introv eqs; subst; simpl in *.

    unfold M_run_ls_on_this_one_event; simpl.
    rewrite M_break_M_op_state; simpl; auto.
  Qed.

  Lemma M_run_ls_before_event_as_M_run_ls_on_event_pred :
    forall {L S}
           (ls : MLocalSystem L S)
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
           (ls : MLocalSystem L S)
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
    forall {L S} {eo : EventOrdering} (e : Event) (ls : MLocalSystem L S),
      isFirst e
      -> M_run_ls_before_event ls e = Some ls.
  Proof.
    introv isf.
    unfold M_run_ls_before_event;simpl.
    destruct ls; simpl.
    unfold M_state_sm_before_event; simpl.
    rewrite isFirst_implies_localPreds_eq; auto; simpl.
    destruct ls_main0; simpl; auto.
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



  (***************************)

  Definition M_output_sm_on_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (option DirectedMsgs) :=
    (M_run_sm_on_event sm e)
      >>o= fun x => ret _ (Some (snd x)).

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
    : MLocalSystem (fls_level F (loc e)) (fls_space F (loc e)) :=
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



  Fixpoint find_state_machine_with_name {n}
           (L  : n_procs n)
           (nm : CompName) : option (sf nm) :=
    state_of_subcomponents L nm.

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

  Lemma M_run_update_on_list_app :
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
  Qed.

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

  Lemma M_run_update_on_list_snoc_fun :
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
  Qed.

  Definition similar_sms_at {cn} {k} (p1 p2 : n_proc_at k cn) : Prop :=
    sm_halted p1 = sm_halted p2
    /\ sm_update p1 = sm_update p2.

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
             -> similar_subs subs' (ls_subs ls))
      -> M_break sm subs F = Some ls
      -> similar_subs subs (ls_subs ls).
  Proof.
    introv impsm impF h.
    unfold M_break in h.
    remember (sm subs) as k; repnd; symmetry in Heqk.
    apply impsm in Heqk; eauto 3 with comp.
  Qed.

  Lemma M_run_update_on_list_preserves_subs :
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
      -> similar_subs subs (ls_subs ls).
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
  Qed.

  Lemma similar_subs_preserves_find_name :
    forall {n} cn (subs1 subs2 : n_procs n) s,
      similar_subs subs1 subs2
      -> find_name cn subs1 = Some s
      -> exists s', find_name cn subs2 = Some s'.
  Proof.
    induction subs1; introv sim h; simpl in *; ginv;[].
    inversion sim; subst; clear sim.
    destruct a, p2; simpl in *; repeat dest_cases w; subst; simpl in *; ginv; eauto.
    inversion simp; subst; clear simp; tcsp.
  Qed.

  Lemma state_of_subcomponents_if_similar :
    forall {n} cn (subs1 subs2 : n_procs n) s,
      similar_subs subs1 subs2
      -> state_of_subcomponents subs1 cn = Some s
      -> exists s', state_of_subcomponents subs2 cn = Some s'.
  Proof.
    introv sim h.
    unfold state_of_subcomponents in *.
    apply option_map_Some in h; exrepnd; subst.
    eapply similar_subs_preserves_find_name in h1;[|eauto].
    exrepnd; rewrite h0; simpl; eauto.
  Qed.
  Hint Resolve state_of_subcomponents_if_similar : comp.

  Definition ls_preserves_subs {L S} (ls : LocalSystem L S) :=
    forall s i subs1,
      similar_subs (ls_subs ls) subs1
      -> M_break
           (sm_update (ls_main ls) s i)
           subs1
           (fun subs2 _ => similar_subs subs1 subs2).

  Definition sys_preserves_subs {F} (sys : M_USystem F) :=
    forall cn, ls_preserves_subs (sys cn).

  Lemma ls_preserves_subs_implies_M_run_update_on_list :
    forall {Lv Sp} (ls : LocalSystem Lv Sp) L s subs1,
      ls_preserves_subs ls
      -> similar_subs (ls_subs ls) subs1
      -> M_break
           (M_run_update_on_list
              s
              (sm_update (ls_main ls))
              L)
           subs1
           (fun subs2 _ => similar_subs (ls_subs ls) subs2).
  Proof.
    induction L; introv pres q; simpl in *; autorewrite with comp; tcsp.
    destruct a; simpl; autorewrite with comp; tcsp.
    unfold M_break, M_on_some; repeat (dest_cases w); repnd; simpl in *;
      subst; simpl in *; ginv; unfold ret in *; simpl in *; ginv;[|].

    { pose proof (IHL w w0) as IHL.
      pose proof (pres s c subs1 q) as pres'.
      unfold M_break in *; simpl in *; repeat (dest_cases z); ginv.
      repeat (autodimp IHL hyp); eauto 3 with comp. }

    { pose proof (pres s c subs1 q) as pres'.
      unfold M_break in *; simpl in *; repeat (dest_cases z); ginv.
      eauto 3 with comp. }
  Qed.
  Hint Resolve ls_preserves_subs_implies_M_run_update_on_list : comp.

  Lemma ls_preserves_subs_implies_M_run_update_on_list2 :
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
  Hint Resolve ls_preserves_subs_implies_M_run_update_on_list2 : comp.

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
    unfold M_state_sm_on_event in *; simpl in *.
    unfold M_run_sm_on_event in *; simpl in *.
    unfold M_run_update_on_event in *; simpl in *.

    pose proof (local_happened_before_implies_history_app2 _ _ lte) as q; exrepnd.

    assert (History(e1) ++ e1 :: l = snoc (History(e1)) e1 ++ l) as eqx.
    { simpl.
      rewrite snoc_as_app.
      rewrite <- app_assoc; simpl; auto. }
    rewrite eqx in q0; clear eqx.
    rewrite q0 in eqs; clear q0.

    rewrite map_app in eqs.
    rewrite map_snoc in eqs.

    rewrite @M_run_update_on_list_app in eqs.
    rewrite @M_run_update_on_list_snoc in eqs.
    rewrite (crazy_bind_option2 _ (sm_update (ls_main ls))).
    rewrite (crazy_bind_option2 _ (sm_update (ls_main ls))) in eqs.

    fold (M_StateMachine (fls_level F (loc e1))) in *.
    fold (n_proc (fls_level F (loc e1))) in *.
    simpl in *.
    match goal with
    | [ |- context[M_break ?x] ] => remember x as w
    end.

    rewrite <- M_run_update_on_list_snoc in Heqw.
    assert (M_break w (ls_subs ls) (fun subs _ => similar_subs (ls_subs ls) subs)) as sub1.
    { subst; eauto 3 with comp. }

    clear Heqw.
    repeat rewrite bind_some_bind_some in eqs.
    rewrite <- M_run_update_on_list_snoc_fun in eqs.
    rewrite M_break_bind_some in eqs; simpl; tcsp;[].

    erewrite eq_M_break in eqs;
      [|introv;rewrite @M_break_M_on_some_option_map;[reflexivity|];simpl;auto].

    apply map_option_Some in eqs; exrepnd.
    symmetry in eqs0.


    (* REDO WITHOUT UNFOLDING  *)
    unfold M_break in eqs1 at 1; unfold M_break.
    remember (w (ls_subs ls)) as q; repnd; symmetry in Heqq.
    Opaque CompNameDeq.
    destruct q; simpl in *; ginv;[].
    repnd.
    apply M_run_update_on_list_preserves_subs in eqs1; simpl; auto;
      try (complete (introv z; destruct out; simpl; ginv; simpl; eauto 3 with comp));[|].

    { dest_cases w; eauto.
      unfold state_of_component in eqs0.
      destruct a; simpl in *; subst.
      dest_cases w; GC; eauto 3 with comp. }

    { introv eqls sim.
      pose proof (pres s1 i subs1) as pres.
      unfold M_break in pres;rewrite eqls in pres; apply pres.
      unfold M_break in sub1; rewrite Heqq in sub1; eauto 3 with comp. }
  Qed.


  Definition M_output_ls_on_event
             {Lv Sp}
             (ls : MLocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event) : DirectedMsgs :=
    M_break
      (M_output_sm_on_event (at2sm (ls_main ls)) e)
      (ls_subs ls)
      (fun subs' out =>
         match out with
         | Some msgs => msgs
         | None => []
         end).

  Definition M_output_sys_on_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : DirectedMsgs :=
    M_output_ls_on_event (sys (loc e)) e.

  Definition M_output_ls_on_this_one_event
             {Lv Sp}
             (ls : MLocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event) : DirectedMsgs :=
    match trigger_op e with
    | Some i =>
      M_break
        (sm_update (ls_main ls) (sm_state (ls_main ls)) i)
        (ls_subs ls)
        (fun subs' out => snd out)
    | None => []
    end.

  (* REDO WITHOUT UNFOLDING MONAD *)
  Lemma M_output_ls_on_event_as_run_before :
    forall {Lv Sp}
           (ls : MLocalSystem Lv Sp)
           {eo : EventOrdering}
           (e  : Event),
      M_output_ls_on_event ls e
      = match M_run_ls_before_event ls e with
        | Some ls' => M_output_ls_on_this_one_event ls' e
        | None => []
        end.
  Proof.
    introv.
    unfold M_output_ls_on_event, M_break in *.
    unfold M_output_sm_on_event, M_on_some, bind in *.
    unfold M_run_sm_on_event in *.
    unfold M_run_ls_before_event.
    unfold M_state_sm_before_event.
    unfold M_run_update_on_event.
    unfold M_run_sm_on_list.
    remember (M_run_update_on_list
                (sm2state (at2sm ls))
                (sm2update (at2sm ls))
                (map trigger_op History( e))) as q.
    unfold M_output_ls_on_this_one_event.
    unfold M_op_update.
    unfold bind_some, bind, M_on_some, M_break; simpl.

    fold (M_StateMachine Lv) in *.
    fold (n_proc Lv) in *.
    repeat (dest_cases w; subst; repnd; simpl in *; ginv);[].
    inversion Heqw1; subst; auto.
  Qed.

  Lemma M_output_ls_on_event_as_run :
    forall {Lv Sp}
           (ls : MLocalSystem Lv Sp)
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
           (ls : MLocalSystem Lv Sp)
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

  Definition state_of_trusted (tsm : trustedSM) : tsf :=
    sm_state (tsm_sm tsm).

  Definition updateTrustedSM (tsm : trustedSM) (new : tsf) : trustedSM :=
    match tsm with
    | MktrustedSM l k s sm => MktrustedSM l k s (update_state sm new)
    end.

  Definition haltTrustedSM (tsm : trustedSM) : trustedSM :=
    match tsm with
    | MktrustedSM l k s sm => MktrustedSM l k s (halt_machine sm)
    end.

  Fixpoint find_trusted {n:nat} (l : n_procs n) : option trustedSM :=
    match l with
    | [] => None
    | MkPProc (MkCompName k s true) pr :: rest =>
      Some (MktrustedSM (sm2level pr) k s (sm2at pr))
    | _ :: rest => find_trusted rest
    end.

  Definition find_trusted_sub {L S} (ls : LocalSystem L S) : option trustedSM :=
    find_trusted (ls_subs ls).

  Definition state_of_trusted_in_ls {L S} (ls : LocalSystem L S) : option tsf :=
    option_map state_of_trusted (find_trusted_sub ls).

  (* We run the trusted with no subcomponents *)
  Definition run_trustedSM_on_trigger_info {D}
             (tsm : trustedSM)
             (ti  : trigger_info D) : trustedSM * iot_output :=
    match ti with
    | trigger_info_data d => (tsm, iot_def_output)
    | trigger_info_arbitrary => (tsm, iot_def_output)
    | trigger_info_trusted i =>
      match sm_update (tsm_sm tsm) (state_of_trusted tsm) i [] with
      | (_, (Some s, out)) => (updateTrustedSM tsm s, out)
      | (_, (None, out)) => (haltTrustedSM tsm, out)
      end
    end.

  Fixpoint run_trustedSM_on_trigger_info_list {D}
           (tsm : trustedSM)
           (l   : list (trigger_info D)) : trustedSM :=
    match l with
    | [] => tsm
    | ti :: l =>
      run_trustedSM_on_trigger_info_list
        (fst (run_trustedSM_on_trigger_info tsm ti))
        l
    end.

  Definition M_find_trusted {n} : M_n n (option trustedSM) :=
    fun subs => ([], find_trusted subs).

  Definition run_trusted_on_trigger_info_list {n} {D}
             (l : list (trigger_info D)) : M_n n (option trustedSM) :=
    M_find_trusted
      >>o= fun tsm => ret _ (Some (run_trustedSM_on_trigger_info_list tsm l)).

  Definition M_trusted (T : Type) := T [+] trustedSM.
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
      >>o= fun tsm => ret _ (Some (M_t tsm)).

  (* As opposed to [M_run_update_on_list] below, this one starts running the (first)
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
    end.

  Definition M_byz_output_ls_on_event
             {Lv Sp}
             (ls : MLocalSystem Lv Sp)
             {eo : EventOrdering}
             (e  : Event) : M_trusted_msgs :=
    M_break
      (M_byz_output_sm_on_event (at2sm (ls_main ls)) e)
      (ls_subs ls)
      (fun subs' out => on_Some_t_o out (fun x => x)).

  Definition M_byz_output_sys_on_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : M_trusted_msgs :=
    M_byz_output_ls_on_event (sys (loc e)) e.

  Definition M_byz_output_sys_on_event_to_byz
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : iot_output :=
    on_M_trusted_out
      (M_byz_output_sys_on_event sys e)
      (fun _ => iot_def_output)
      (fun out => out).

  Definition M_byz_run_sm_on_list {n} {cn}
             (sm : n_proc n cn)
             (l  : list (trigger_info (cio_I (fio cn))))
    : M_n (sm2level sm) (option (M_trusted (sf cn))) :=
    M_byz_run_update_on_list (sm2state sm) (sm2update sm) l.

  Definition M_byz_state_sm_before_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event)
    : M_n (sm2level sm) (option (M_trusted (sf (msg_comp_name k)))) :=
    M_byz_run_sm_on_list sm (map trigger (@localPreds pn pk pm _ _ eo e)).

  Definition map_untrusted {T} {A}
             (x : M_trusted T)
             (F : T -> A) : M_trusted A :=
    on_M_trusted x (fun t => M_nt (F t)) M_t.

  Definition map_untrusted_op {T} {A}
             (x : M_trusted T)
             (F : T -> option A) : option (M_trusted A) :=
    on_M_trusted
      x
      (fun t => option_map M_nt (F t))
      (fun tsm => Some (M_t tsm)).

  Definition map_op_untrusted {T} {A}
             (x : option (M_trusted T))
             (F : T -> A) : option (M_trusted A) :=
    option_map (fun mt => map_untrusted mt F) x.

  Definition map_op_untrusted_op {T} {A}
             (x : option (M_trusted T))
             (F : T -> option A) : option (M_trusted A) :=
    map_option (fun mt => map_untrusted_op mt F) x.

  Definition M_byz_run_ls_before_event
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
           (fun s => upd_ls_main_state_and_subs ls s subs')).

  Definition M_byz_state_ls_before_event
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event)
             (cn : CompName) : option (M_trusted (sf cn)) :=
    map_op_untrusted_op
      (M_byz_run_ls_before_event ls e)
      (state_of_component cn).

  Definition M_byz_state_sys_before_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event)
             (cn  : CompName) : option (M_trusted (sf cn)) :=
    M_byz_state_ls_before_event (sys (loc e)) e cn.

  Definition M_byz_state_ls_before_event_of_trusted
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
      (M_byz_run_ls_before_event ls e).

  Definition M_byz_state_sys_before_event_of_trusted
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : option tsf :=
    M_byz_state_ls_before_event_of_trusted (sys (loc e)) e.

  Definition M_byz_state_sm_on_event {n} {k}
             (sm : n_proc n (msg_comp_name k))
             {eo : EventOrdering}
             (e  : Event) : M_n (sm2level sm) (option (M_trusted (sf (msg_comp_name k)))) :=
  (M_byz_run_sm_on_event sm e)
    >>o= fun mt => ret _ (to_op_M_trusted mt).

  Definition M_byz_run_ls_on_event
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (M_trusted (LocalSystem _ _)) :=
    M_break
      (M_byz_state_sm_on_event (at2sm (ls_main ls)) e)
      (ls_subs ls)
      (fun subs' out =>
         map_op_untrusted
           out
           (fun s => upd_ls_main_state_and_subs ls s subs')).

  Definition M_byz_state_ls_on_event
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event)
             (cn : CompName) : option (M_trusted (sf cn)) :=
    map_op_untrusted_op
      (M_byz_run_ls_on_event ls e)
      (state_of_component cn).

  Definition M_byz_state_sys_on_event
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event)
             (cn  : CompName) : option (M_trusted (sf cn)) :=
    M_byz_state_ls_on_event (sys (loc e)) e cn.

  Definition M_byz_state_ls_on_event_of_trusted
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
      (M_byz_run_ls_on_event ls e).

  Definition M_byz_state_sys_on_event_of_trusted
             {F}
             (sys : M_USystem F)
             {eo  : EventOrdering}
             (e   : Event) : option tsf :=
    M_byz_state_ls_on_event_of_trusted (sys (loc e)) e.

  Lemma M_byz_state_sys_before_event_of_trusted_unfold :
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
  Qed.

  Lemma map_op_untrusted_option_map_M_nt :
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
  Hint Rewrite @map_op_untrusted_option_map_M_nt : comp.

  Lemma M_break_map_op_untrusted_option_map_M_nt :
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
  Hint Rewrite @M_break_map_op_untrusted_option_map_M_nt : comp.

  Definition M_byz_run_ls_on_this_one_event
             {L S}
             (ls : MLocalSystem L S)
             {eo : EventOrdering}
             (e  : Event) : option (M_trusted (LocalSystem _ _)) :=
    if_trigger_info_data
      (trigger e)
      (fun m =>
         M_break
           (sm_update (ls_main ls) (sm_state (ls_main ls)) m)
           (ls_subs ls)
           (fun subs' out =>
              option_map
                (fun s => M_nt (upd_ls_main_state_and_subs ls s subs'))
                (fst out)))
      (option_map
         (fun tsm => M_t (fst (run_trustedSM_on_trigger_info tsm (trigger e))))
         (find_trusted (ls_subs ls))).

  Lemma M_nt_inj :
    forall {T} (t1 t2 : T),
      M_nt t1 = M_nt t2
      -> t1 = t2.
  Proof.
    introv h; injection h; auto.
  Qed.

  Lemma M_byz_run_ls_on_this_one_event_Some_M_nt_implies :
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
  Qed.

  Definition M_byz_run_M_trusted_ls_on_this_one_event
             {L S}
             (mt : M_trusted (MLocalSystem L S))
             {eo : EventOrdering}
             (e  : Event) : option (M_trusted (MLocalSystem L S)) :=
    on_M_trusted
      mt
      (fun ls => M_byz_run_ls_on_this_one_event ls e)
      (fun tsm => Some (M_t (fst (run_trustedSM_on_trigger_info tsm (trigger e))))).

  Lemma on_M_trusted_map_untrusted :
    forall {U T A} (x : M_trusted U) (f : U -> T) (F : T -> A) (G : trustedSM -> A),
      on_M_trusted (map_untrusted x f) F G
      = on_M_trusted x (compose F f) G.
  Proof.
    introv; unfold map_untrusted, on_M_trusted.
    destruct x; simpl; auto.
  Qed.
  Hint Rewrite @on_M_trusted_map_untrusted : comp.

  Lemma on_M_trusted_implies_or :
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
  Qed.

  Lemma on_M_trusted_M_nt :
    forall {T A} (x : T) (F : T -> A) (G : trustedSM -> A),
      on_M_trusted (M_nt x) F G = F x.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @on_M_trusted_M_nt : comp.

  Lemma on_M_trusted_M_t :
    forall {T A} (x : trustedSM) (F : T -> A) (G : trustedSM -> A),
      on_M_trusted (M_t x) F G = G x.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @on_M_trusted_M_t : comp.

  Lemma M_break_on_M_trusted :
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
  Qed.

  Lemma eq_on_M_trusted :
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
  Qed.

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
           (ls : MLocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_run_ls_on_event ls e
      = if dec_isFirst e
        then M_byz_run_ls_on_this_one_event ls e
        else
          map_option
            (fun ls => M_byz_run_M_trusted_ls_on_this_one_event ls e)
            (M_byz_run_ls_before_event ls e).
  Proof.
    introv.
    unfold M_byz_run_ls_on_event, M_byz_run_ls_before_event; simpl.
    destruct ls; simpl.
    unfold M_byz_state_sm_on_event, M_byz_state_sm_before_event.
    unfold M_byz_run_sm_on_event.
    unfold M_byz_run_update_on_event; simpl.
    unfold M_byz_run_sm_on_list; simpl.
    unfold M_byz_run_M_trusted_ls_on_this_one_event; simpl.
    unfold M_byz_run_ls_on_this_one_event; simpl.
    unfold trigger_op; simpl.

    destruct (dec_isFirst e) as [d|d].

    {
      rewrite isFirst_implies_localPreds_eq; simpl; auto.
      autorewrite with comp; simpl.
      unfold M_op2M_trusted_with_out; simpl.
      unfold M_op_update; simpl.
      destruct (trigger e); simpl; auto;[| |]; auto_rw_bind.
    }

    auto_rw_bind.
    rewrite M_break_bind_some; simpl; tcsp;[].
    rewrite map_option_M_break.
    apply eq_M_break; introv.
    unfold map_op_untrusted.
    rewrite map_option_option_map; unfold compose; simpl.
    apply equal_map_options; introv eqs; subst; simpl in *.
    autorewrite with comp; unfold compose; simpl.
    rewrite M_break_on_M_trusted.
    apply eq_on_M_trusted; introv; auto_rw_bind;[].
    rewrite M_break_if_trigger_info_data.
    apply eq_if_trigger_info_data; introv; auto_rw_bind;[].
    apply eq_M_break; introv; auto_rw_bind.
    rewrite option_map_option_map; unfold compose; simpl; auto.
  Qed.

  Lemma on_M_some_ret_Some :
    forall {T} {U} {n} (a : option T) (F : T -> U),
      (a >>o>> (fun s => ret n (Some (F s))))
      = ret n (option_map F a).
  Proof.
    introv; destruct a; simpl; auto.
  Qed.
  Hint Rewrite @on_M_some_ret_Some : comp.

  Lemma bind_some_if_trigger_info_data :
    forall {n} {S} {O} {D}
           (a    : trigger_info D)
           (f    : D -> M_n n (option S))
           (g    : M_n n (option S))
           (F    : S -> M_n n (option O)),
      ((if_trigger_info_data a f g) >>o= F)
      = if_trigger_info_data
          a
          (fun a => (f a) >>o= F)
          (g >>o= F).
  Proof.
    introv; destruct a; simpl; auto.
  Qed.

  Lemma run_trustedSM_on_trigger_info_list_snoc :
    forall {D} (l : list (trigger_info D)) x (tsm : trustedSM),
      run_trustedSM_on_trigger_info_list tsm (snoc l x)
      = fst (run_trustedSM_on_trigger_info
               (run_trustedSM_on_trigger_info_list tsm l)
               x).
  Proof.
    induction l; introv; simpl; auto.
  Qed.

  Lemma M_byz_run_update_on_list_snoc :
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
  Qed.

  Lemma M_byz_run_ls_before_event_unroll :
    forall {L S}
           (ls : MLocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_run_ls_before_event ls e
      = if dec_isFirst e
        then Some (M_nt ls)
        else map_option
               (fun ls => M_byz_run_M_trusted_ls_on_this_one_event ls (local_pred e))
               (M_byz_run_ls_before_event ls (local_pred e)).
  Proof.
    introv.
    unfold M_byz_run_ls_before_event; destruct ls; simpl.
    unfold M_byz_state_sm_before_event.

    destruct (dec_isFirst e) as [d|d].

    { rewrite isFirst_implies_localPreds_eq; simpl; auto.
      destruct ls_main0; simpl; auto. }

    rewrite (localPreds_unroll e) at 1; auto; simpl.
    unfold M_byz_run_sm_on_list; simpl.
    rewrite map_snoc; simpl.
    rewrite @M_byz_run_update_on_list_snoc.
    rewrite map_option_M_break.
    rewrite M_break_bind_some; simpl; tcsp;[].
    apply eq_M_break; introv; simpl.
    unfold map_op_untrusted.
    rewrite map_option_option_map; unfold compose; simpl.
    apply equal_map_options; introv; introv eqs; subst; simpl in *.

    unfold M_byz_run_M_trusted_ls_on_this_one_event; simpl.
    rewrite M_break_on_M_trusted; auto_rw_bind.
    unfold compose; simpl.
    apply eq_on_M_trusted; introv; auto_rw_bind;[].

    unfold M_byz_run_ls_on_this_one_event.
    rewrite M_break_if_trigger_info_data.
    apply eq_if_trigger_info_data; introv; auto_rw_bind;[].
    apply eq_M_break; introv; auto_rw_bind.
    rewrite option_map_option_map; unfold compose; simpl; auto.
  Qed.

  Lemma M_byz_run_ls_before_event_as_M_byz_run_ls_on_event_pred :
    forall {L S}
           (ls : MLocalSystem L S)
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
           (ls : MLocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_run_ls_before_event ls e
      = if dec_isFirst e
        then Some (M_nt ls)
        else M_byz_run_ls_on_event ls (local_pred e).
  Proof.
    introv.
    destruct (dec_isFirst e) as [d|d];
      [|apply M_byz_run_ls_before_event_as_M_byz_run_ls_on_event_pred;auto].
    rewrite M_byz_run_ls_before_event_unroll.
    destruct (dec_isFirst e); tcsp.
  Qed.

  Lemma unroll_M_byz_state_ls_before_event_of_trusted :
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
  Qed.

  Lemma M_run_ls_on_this_one_event_M_byz_run_ls_on_this_one_event :
    forall {L S}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : MLocalSystem L S),
      M_run_ls_on_this_one_event ls1 e = Some ls2
      -> M_byz_run_ls_on_this_one_event ls1 e = Some (M_nt ls2).
  Proof.
    introv h.
    unfold M_run_ls_on_this_one_event in *.
    unfold M_byz_run_ls_on_this_one_event.

    rewrite map_option_Some in h.
    exrepnd.
    symmetry in h0.

    (* TODO: do not unfold *)
    unfold if_trigger_info_data in *.
    unfold trigger_op in *.
    unfold ti2op in *.
    simpl in *.
    destruct (trigger e) as [d|d|d]; ginv; [].

    unfold M_break in *. simpl in *.

    dest_cases w.
    repnd.
    simpl in *.
    destruct w2 as [X|X]; ginv.
  Qed.

  Lemma M_byz_run_ls_on_this_one_event_M_run_ls_on_this_one_event :
    forall {L S}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : MLocalSystem L S),
      M_byz_run_ls_on_this_one_event ls1 e = Some (M_nt ls2)
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


  Lemma M_run_ls_on_event_M_byz_run_ls_on_event :
    forall {L S}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : MLocalSystem L S),
      M_run_ls_on_event ls1 e = Some ls2
      -> M_byz_run_ls_on_event ls1 e = Some (M_nt ls2).
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
    forall {eo : EventOrdering} (e : Event) {L S} (ls1 ls2 : MLocalSystem L S),
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
    forall {eo : EventOrdering} (e : Event) {L S} (ls1 ls2 : MLocalSystem L S),
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


  Lemma M_byz_run_ls_on_event_M_run_ls_on_event :
    forall {L S}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : MLocalSystem L S),
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

  Lemma M_byz_state_sys_on_event_if_M_state_sys_on_event :
    forall {F}
           (sys : M_USystem F)
           {eo  : EventOrdering}
           (e   : Event)
           (cn  : CompName)
           (s   : sf cn),
      M_state_sys_on_event sys e cn = Some s
      -> M_byz_state_sys_on_event sys e cn = Some (M_nt s).
  Proof.
    introv h.
    rewrite M_state_sys_on_event_unfold in h.
    apply map_option_Some in h; exrepnd; symmetry in h0.

    eapply M_run_ls_on_event_M_byz_run_ls_on_event in h1.

    unfold M_byz_state_sys_on_event.
    unfold M_byz_state_ls_on_event.
    unfold map_op_untrusted_op.
    rewrite map_option_Some.
    eexists; dands; eauto.

    unfold map_untrusted_op.
    simpl in *.
    rewrite h0. eauto.
  Qed.
  Hint Resolve M_byz_state_sys_on_event_if_M_state_sys_on_event : comp.

  Lemma M_byz_state_sys_on_event_implies_M_state_sys_on_event :
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


  Definition M_byz_output_ls_on_this_one_event
             {L S}
             (ts : M_trusted (MLocalSystem L S))
             {eo : EventOrdering}
             (e  : Event) : M_trusted_msgs :=
    on_M_trusted
      ts
      (fun ls =>
         if_trigger_info_data
           (trigger e)
           (fun m =>
              M_break
                (sm_update (ls_main ls) (sm_state (ls_main ls)) m)
                (ls_subs ls)
                (fun subs' out => M_nt_o (snd out)))
           (on_Some_t_o
              (find_trusted (ls_subs ls))
              (fun tsm => M_t_o (snd (run_trustedSM_on_trigger_info tsm (trigger e))))))
      (fun tsm => M_t_o (snd (run_trustedSM_on_trigger_info tsm (trigger e)))).

  Lemma M_byz_output_ls_on_event_as_run :
    forall {Lv Sp}
           (ls : MLocalSystem Lv Sp)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_output_ls_on_event ls e
      = on_Some_t_o
          (M_byz_run_ls_before_event ls e)
          (fun ls => M_byz_output_ls_on_this_one_event ls e).
  Proof.
    introv.
    unfold M_byz_output_ls_on_event; simpl.
    unfold M_byz_output_sm_on_event; simpl.
    unfold M_byz_run_ls_before_event; simpl.
    unfold M_byz_state_sm_before_event; simpl.
    unfold M_byz_run_sm_on_event; simpl.
    unfold M_byz_run_update_on_event; simpl.
    unfold M_byz_run_sm_on_list; simpl.

    fold (M_StateMachine Lv) in *.
    fold (n_proc Lv) in *.
    unfold bind_some, M_break, bind; simpl.
    remember (M_byz_run_update_on_list (sm_state (ls_main ls)) (sm_update (ls_main ls)) (map trigger History( e)) (ls_subs ls)) as w.
    simpl in *.
    rewrite <- Heqw.
    clear Heqw.

    repnd; simpl.
    unfold M_on_some; simpl.
    destruct w; simpl; auto;[].
    destruct m; simpl; auto;[].

    remember (trigger e) as trig.
    destruct trig; simpl; auto;[| |].

    { unfold M_break; simpl.
      destruct (sm_update (ls_main ls) s d w0); simpl; auto. }

    { destruct (find_trusted w0); simpl; auto. }

    { destruct (find_trusted w0); simpl; auto. }
  Qed.

  Lemma M_run_ls_before_event_M_byz_run_ls_before_event :
    forall {L S}
           {eo      : EventOrdering}
           (e       : Event)
           (ls1 ls2 : MLocalSystem L S),
      M_run_ls_before_event ls1 e = Some ls2
      -> M_byz_run_ls_before_event ls1 e = Some (M_nt ls2).
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
           (ls : MLocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      M_byz_run_ls_on_event ls e
      = map_option
          (fun ls => M_byz_run_M_trusted_ls_on_this_one_event ls e)
          (M_byz_run_ls_before_event ls e).
  Proof.
    introv.
    rewrite M_byz_run_ls_on_event_unroll.
    rewrite M_byz_run_ls_before_event_unroll_on.
    destruct (dec_isFirst e); simpl; auto.
  Qed.

  (* Use this one instead of the other one *)
  Lemma M_run_ls_on_event_unroll2 :
    forall {L S}
           (ls : MLocalSystem L S)
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
    forall {eo : EventOrdering} (e : Event) {L S} (ls : MLocalSystem L S) out,
      In out (M_output_ls_on_this_one_event ls e)
      ->
      exists m,
        trigger_op e = Some m
        /\ In out (M_break (sm_update (ls_main ls) (sm_state (ls_main ls)) m) (ls_subs ls) (fun _ out => snd out)).
  Proof.
    introv i.
    unfold M_output_ls_on_this_one_event in *.
    remember (trigger_op e) as trig; symmetry in Heqtrig; destruct trig; simpl in *; ginv; tcsp; eauto.
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

  Lemma in_M_output_ls_on_event_implies_byz_eq :
    forall {eo : EventOrdering} (e : Event)
           {Lv Sp}
           (ls : MLocalSystem Lv Sp)
           out,
      In out (M_output_ls_on_event ls e)
      -> M_byz_output_ls_on_event ls e = M_nt_o (M_output_ls_on_event ls e).
  Proof.
    introv i.
    rewrite M_byz_output_ls_on_event_as_run.
    rewrite M_output_ls_on_event_as_run_before in i.
    rewrite M_output_ls_on_event_as_run_before.
    remember (M_run_ls_before_event ls e) as q; symmetry in Heqq; destruct q; simpl in *; tcsp.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in Heqq as w.
    rewrite w; simpl.
    applydup @in_M_output_ls_on_this_one_event_implies in i as j; exrepnd.
    unfold M_output_ls_on_this_one_event.
    allrw.
    applydup trigger_op_Some_implies_trigger_message in j1.
    allrw; simpl.
    unfold M_break in *.
    remember (sm_update (ls_main l) (sm_state (ls_main l)) m (ls_subs l)) as z; repnd; simpl in *; auto.
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
           (ls1 : MLocalSystem L S),
      has_correct_trace_before e (loc e)
      -> M_byz_run_ls_on_this_one_event ls1 e
         = option_map M_nt (M_run_ls_on_this_one_event ls1 e).
  Proof.
    introv cor.
    unfold M_run_ls_on_this_one_event.
    unfold M_byz_run_ls_on_this_one_event.
    applydup has_correct_trace_before_implies_trigger_eq in cor; exrepnd.
    unfold trigger_op.
    rewrite cor1; simpl.
    unfold M_break; simpl in *.
    dest_cases w; repnd; simpl in *; tcsp.
    rewrite option_map_option_map; unfold compose; simpl; auto.
  Qed.

  Lemma M_byz_run_ls_before_event_as_M_run_ls_before_event :
    forall {L S}
           {eo  : EventOrdering}
           (e   : Event)
           (ls1 : MLocalSystem L S),
      has_correct_trace_before e (loc e)
      -> M_byz_run_ls_before_event ls1 e
         = option_map M_nt (M_run_ls_before_event ls1 e).
  Proof.
    intros L S eo e.
    induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_run_ls_before_event_unroll.
    rewrite M_byz_run_ls_before_event_unroll.
    destruct (dec_isFirst e); ginv; auto;[].

    rewrite option_map_map_option; unfold option_compose; simpl.
    rewrite ind; autorewrite with eo; eauto 3 with eo;[].
    rewrite map_option_option_map; unfold compose; simpl.

    apply equal_map_options; introv i.
    rewrite M_byz_run_ls_on_this_one_event_as_M_run_ls_on_this_one_event; autorewrite with eo; eauto 3 with eo.
  Qed.

  Lemma correct_implies_byz_output_eq :
    forall {eo : EventOrdering} (e : Event)
           {Lv Sp}
           (ls : MLocalSystem Lv Sp),
      has_correct_trace_before e (loc e)
      -> M_byz_output_ls_on_event ls e = M_nt_o (M_output_ls_on_event ls e).
  Proof.
    introv cor.
    rewrite M_byz_output_ls_on_event_as_run.
    rewrite M_output_ls_on_event_as_run_before.
    rewrite M_byz_run_ls_before_event_as_M_run_ls_before_event; auto.
    remember (M_run_ls_before_event ls e) as q; symmetry in Heqq; destruct q; simpl in *; tcsp.
    unfold M_output_ls_on_this_one_event, trigger_op.
    applydup @has_correct_trace_before_implies_trigger_eq in cor; exrepnd; rewrite cor1; simpl.
    unfold M_break; dest_cases w; auto.
  Qed.

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
Hint Resolve state_of_subcomponents_if_similar : comp.
Hint Resolve ls_preserves_subs_implies_M_run_update_on_list : comp.
Hint Resolve ls_preserves_subs_implies_M_run_update_on_list2 : comp.
Hint Resolve M_run_ls_on_this_one_event_implies_isCorrect : comp.
Hint Resolve M_run_ls_on_event_implies_has_correct_trace_before : comp.
Hint Resolve M_byz_run_ls_on_this_one_event_M_run_ls_on_this_one_event : comp.
Hint Resolve M_byz_run_ls_on_event_M_run_ls_on_event : comp.
Hint Resolve M_byz_state_sys_on_event_if_M_state_sys_on_event : comp.
Hint Resolve M_byz_state_sys_on_event_implies_M_state_sys_on_event : comp.
Hint Resolve similar_sms_at_refl : comp.
Hint Resolve similar_sms_at_sym : comp.
Hint Resolve similar_sms_at_trans : comp.


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
Hint Rewrite @map_op_untrusted_option_map_M_nt : comp.
Hint Rewrite @M_break_map_op_untrusted_option_map_M_nt : comp.
Hint Rewrite @on_M_trusted_map_untrusted : comp.
Hint Rewrite @on_M_some_ret_Some : comp.
Hint Rewrite @on_M_trusted_M_nt : comp.
Hint Rewrite @on_M_trusted_M_t : comp.
Hint Rewrite @M_break_bind : comp.
Hint Rewrite @M_break_bind_pair : comp.
Hint Rewrite @M_break_bind_ret : comp.


Hint Resolve M_state_sys_before_event_if_on_event_direct_pred : proc.


Hint Resolve sub_local_key_map_preserves_in_lookup_receiving_keys : eo.
Hint Resolve verify_authenticated_data_if_sub_keys : eo.


Delimit Scope comp with comp.


Notation "a >>= f"   := (bind a f)      (at level 80).
Notation "a >>>= f"  := (bind_pair a f) (at level 80).
Notation "a >p>= f"  := (pbind a f)     (at level 80).
Notation "a >>o>> f" := (M_on_some f a) (at level 80).
Notation "a >>o= f"  := (bind_some a f) (at level 80).

Notation "d ∈ sys ⇝ e" := (In d (M_output_sys_on_event sys e)) (at level 70).
