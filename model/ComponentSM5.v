Require Export ComponentSM2.



Section ComponentSM5.

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


  Inductive SpawnProc: forall (O : Type), Type :=
  | SPROC_RET   : forall O (f : O), SpawnProc O
  | SPROC_BIND  : forall A B (p : SpawnProc A) (q : A -> SpawnProc B), SpawnProc B
  | SPROC_CALL  : forall (cn : CompName) (i : cio_I (fio cn)), SpawnProc (cio_O (fio cn))
  | SPROC_SPAWN : forall B
                         (cn : CompName)
                         (u : sf cn -> cio_I (fio cn) -> SpawnProc (sf cn * cio_O (fio cn)))
                         (s : sf cn)
                         (b : B),
      SpawnProc B.
  Global Arguments SPROC_RET  [O] _.
  Global Arguments SPROC_BIND [A] [B] _ _.
  Global Arguments SPROC_SPAWN [B] _ _ _ _.

  Notation "a [[>>=]] f" := (SPROC_BIND a f) (at level 80).
  Notation "[[R]] a" := (SPROC_RET a) (at level 80).
  Notation "a [[C]] b" := (SPROC_CALL a b) (at level 80).

  Definition spawn {B} {n:nat} {cn}
             (upd : M_Update n cn (sf cn))
             (s   : sf cn)
             (b   : B) : M_n (S n) B :=
    fun subs => (MkPProc _ (build_m_sm upd s) :: subs,b).

  Definition spawn_proc_bind_pair {A B C} (m : SpawnProc (A * B)) (f : A -> B -> SpawnProc C) : SpawnProc C :=
    m [[>>=]] fun p => let (a,b) := p in f a b.

  Notation "a [[>>>=]] f" := (spawn_proc_bind_pair a f) (at level 80).

  Definition to_spawn_proc_some_state {S} {O} (m : SpawnProc (S * O)) : SpawnProc (option S * O) :=
    m [[>>>=]] fun s o => [[R]] (Some s, o).

  (*  sf cn -> cio_I (fio_cn) -> SpawnProc (sf cn * cio_O (fio cn)))*)

  Definition interp_spawn_proc
             {O : Type}
             (p : SpawnProc O) : forall {n : nat}, M_n n O.
  Proof.
    induction p; introv.
    - exact (ret _ f).
    - exact (bind (IHp n) (fun a => X a n)).
    - exact (call_proc cn i).
    - destruct n.
      { (* It doesn't use sub-components *) exact (ret _ b). }
      exact (spawn (fun s i => to_M_n_some_state (X s i n)) s b).
  Defined.

End ComponentSM5.
