Require Export ComponentSM.



Section ComponentSM2.

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


  (* m <= n *)
  Fixpoint select_n_proc {n} {cn} m : n_proc n cn -> option (n_proc m cn) :=
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

  Definition lift_eq_rev {n j k} (e : n = S (j + k)) : j + k = pred n.
  Proof.
    introv; subst; simpl; auto.
  Defined.

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


  Inductive Proc: forall (O : Type), Type :=
  | PROC_RET  : forall O (f : O), Proc O
  | PROC_BIND : forall A B (p : Proc A) (q : A -> Proc B), Proc B
  | PROC_CALL : forall (cn : CompName) (i : cio_I (fio cn)), Proc (cio_O (fio cn)).
  Global Arguments PROC_RET  [O] _.
  Global Arguments PROC_BIND [A] [B] _ _.

  Notation "a [>>=] f" := (PROC_BIND a f) (at level 80).
  Notation "[R] a" := (PROC_RET a) (at level 80).
  Notation "a [C] b" := (PROC_CALL a b) (at level 80).

  Definition proc_bind_pair {A B C} (m : Proc (A * B)) (f : A -> B -> Proc C) : Proc C :=
    m [>>=] fun p => let (a,b) := p in f a b.

  Notation "a [>>>=] f" := (proc_bind_pair a f) (at level 80).

  Definition interp_proc
             {O : Type}
             {n : nat}
             (p : Proc O) : M_n n O.
  Proof.
    induction p.
    - exact (ret _ f).
    - exact (bind IHp X).
    - exact (call_proc cn i).
  Defined.

  Definition to_proc_some_state {S} {O} (m : Proc (S * O)) :=
    m [>>>=] fun s o => [R] (Some s, o).

  Definition to_M_n_some_state {n} {S} {O} (m : M_n n (S * O)) :=
    m >>>= fun s o => ret _ (Some s, o).

  Definition old_interp_s_proc
             {S : Type}
             {O : Type}
             {n : nat}
             (p : Proc (S * O)) : M_n n (option S * O) :=
    to_M_n_some_state (interp_proc p).

  Definition interp_s_proc
             {S : Type}
             {O : Type}
             {n : nat}
             (p : Proc (S * O)) : M_n n (option S * O) :=
    interp_proc (to_proc_some_state p).

  Definition UProc (cn : CompName) S := S -> cio_I (fio cn) -> Proc (S * cio_O (fio cn)).

  Definition proc2upd {S} {n} {cn} (p : UProc cn S) : M_Update n cn S :=
    fun s i => interp_s_proc (p s i).

  Lemma interp_s_proc_as :
    forall {S : Type}
           {O : Type}
           {n : nat}
           (p : Proc (S * O)),
      interp_s_proc p
      = (interp_proc p >>>= fun s o => ret n (Some s, o)).
  Proof.
    introv; simpl.
    unfold interp_s_proc; simpl.
    unfold bind_pair, bind; simpl.
    apply functional_extensionality; introv; dest_cases w; repnd; simpl; auto.
  Qed.
  Hint Rewrite @interp_s_proc_as : comp.


  (* ================================================================ *)
  (* ====== TEST ====== *)

  Definition TESTmain  : CompName := msg_comp_name 1.
  Definition TESTcompa : CompName := bool_comp_name.
  Definition TESTcompb : CompName := nat_comp_name.

  Definition TESTcompa_upd : M_Update 0 TESTcompa _ :=
    fun (s : bool) (m : bool) =>
      interp_s_proc
        (let b := andb s m in
         [R] (b, b)).

  Definition TESTcompa_sm : n_proc 1 TESTcompa :=
    build_m_sm TESTcompa_upd true.

  Definition TESTcompb_upd : M_Update 0 TESTcompb _ :=
    fun (s : nat) (m : nat) =>
      interp_s_proc
        (let k := s + m in
         [R] (k, k)).

  Definition TESTcompb_sm : n_proc 1 TESTcompb :=
    build_m_sm TESTcompb_upd 0.

  Definition TESTmain_upd1 : M_Update 1 TESTmain _ :=
    fun (s : nat) m =>
      (call_proc TESTcompa true) >>= fun b =>
      let n := if b then 0 else 1 in
      (call_proc TESTcompb n) >>= fun m =>
      ret _ (Some (s + m), []).

  Definition TESTmain_upd2 : M_Update 1 TESTmain _ :=
    fun (s : unit) m =>
      interp_s_proc
        ((TESTcompa [C] true) [>>=] fun b =>
         let n := if b then 0 else 1 in
         (TESTcompb [C] n) [>>=] fun m =>
         [R] (s, [])).

  Definition TESTmain_sm : n_proc_at 1 TESTmain :=
    build_mp_sm TESTmain_upd2 tt.

  Definition TESTls : LocalSystem _ _ :=
    MkLocalSystem
      TESTmain_sm
      [MkPProc TESTcompa TESTcompa_sm,
       MkPProc TESTcompb TESTcompb_sm].

  (* ================================================================ *)


  Definition is_proc_n_proc_at {n} {cn} (sm : n_proc_at n cn) : Prop :=
    exists (p : sf cn -> cio_I (fio cn) -> Proc (sf cn * cio_O (fio cn))),
      forall s i, sm_update sm s i = proc2upd p s i.

  Definition is_proc_n_proc {n} {cn} (sm : n_proc n cn) : Prop :=
    exists (p : sf cn -> cio_I (fio cn) -> Proc (sf cn * cio_O (fio cn))),
    forall s i, sm2update sm s i = proc2upd p s i.

  Definition is_proc_n_nproc {n} (np : n_nproc n) : Prop :=
    match np with
    | MkPProc cn sm => is_proc_n_proc sm
    end.

  Definition are_procs_n_procs {n} (l : n_procs n) : Prop :=
    forall p, In p l -> is_proc_n_nproc p.

  Definition are_procs_ls {L S} (ls : LocalSystem L S) : Prop :=
    is_proc_n_proc_at (ls_main ls)
    /\ are_procs_n_procs (ls_subs ls).

  Definition are_procs_sys {f} (sys : M_USystem f) :=
    forall n, are_procs_ls (sys n).

  Lemma are_procs_n_procs_cons :
    forall n p (ps : n_procs n),
      are_procs_n_procs (p :: ps)
      <-> (is_proc_n_nproc p /\ are_procs_n_procs ps).
  Proof.
    introv; split; intro h; repnd; dands.
    - pose proof (h p) as h; simpl in *; apply h; tcsp.
    - introv i; apply h; simpl; tcsp.
    - introv i; simpl in *; repndors; subst; tcsp.
  Qed.

  Lemma similar_sms_implies_eq_sm2levels :
    forall cn k (p1 p2 : n_proc k cn),
      similar_sms p1 p2
      -> sm2level p1 = sm2level p2.
  Proof.
    induction k; introv sim; simpl in *; tcsp; destruct p1, p2; simpl in *; tcsp.
  Qed.

  Lemma similar_sms_implies_eq_sm2update :
    forall cn k (p1 p2 : n_proc k cn) (q : sm2level p2 = sm2level p1),
      similar_sms p1 p2
      -> sm2update p1 = eq_rect _ (fun n => M_Update n cn (sf cn)) (sm2update p2) _ q.
  Proof.
    induction k; introv sim; simpl in *; tcsp.
    destruct p1, p2; simpl in *; repnd; subst; tcsp.
    pose proof (UIP_refl_nat _ q) as w; subst; simpl; auto.
    destruct sim; auto.
  Qed.

  Lemma similar_procs_preserves_is_proc_n_nproc :
    forall n (p1 p2 : n_nproc n),
      similar_procs p1 p2
      -> is_proc_n_nproc p1
      -> is_proc_n_nproc p2.
  Proof.
    introv sim isp.
    destruct p1 as [cn1 p1], p2 as [cn2 p2]; simpl in *.
    applydup @similar_procs_implies_same_name in sim; simpl in *; subst.
    apply similar_procs_implies_same_proc in sim.
    unfold is_proc_n_proc in *; exrepnd.
    exists p.
    introv.
    pose proof (isp0 s i) as isp0.
    applydup similar_sms_implies_eq_sm2levels in sim.
    symmetry in sim0.
    pose proof (similar_sms_implies_eq_sm2update cn2 n p1 p2 sim0) as q.
    repeat (autodimp q hyp).
    rewrite q in isp0; clear q sim.

    remember (sm2level p1) as n1; clear Heqn1.
    subst; simpl in *; auto.
  Qed.
  Hint Resolve similar_procs_preserves_is_proc_n_nproc : comp.

  Lemma similar_subs_preserves_are_procs_n_procs :
    forall {n} (subs1 subs2 : n_procs n),
      similar_subs subs1 subs2
      -> are_procs_n_procs subs1
      -> are_procs_n_procs subs2.
  Proof.
    introv sim.
    induction sim; introv aps; auto.
    allrw are_procs_n_procs_cons; repnd; dands; tcsp.
    eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_preserves_are_procs_n_procs : comp.

  Lemma decr_n_proc_some_preserves_sm2update_eq_proc2upd :
    forall cn n (a : n_proc n cn) p s i b,
      decr_n_proc a = Some b
      -> sm2update a s i = proc2upd p s i
      -> sm2update b s i = proc2upd p s i.
  Proof.
    introv d e.
    destruct n; simpl in *; ginv; tcsp;[].
    destruct a; simpl in *; ginv; tcsp.
    inversion d; subst; auto.
  Qed.

  Lemma select_n_proc_preserves_sm2update_eq_proc2upd :
    forall cn k n (a : n_proc n cn) b p s i,
      select_n_proc k a = Some b
      -> sm2update a s i = proc2upd p s i
      -> sm2update b s i = proc2upd p s i.
  Proof.
    induction n; introv u v; simpl in *; tcsp;[].
    destruct k.

    { destruct a; simpl in *; tcsp. }

    destruct (deq_nat n k); subst; tcsp; ginv;[].
    destruct a; simpl in *; tcsp;[].
    pose proof (IHn b0 b p s i) as IHn.
    repeat (autodimp IHn hyp).
  Qed.

  Lemma is_proc_n_nproc_select_n_nproc_decr_n_nproc :
    forall n k (a : n_nproc n) (b : n_nproc (Init.Nat.pred n)) c,
      is_proc_n_nproc a
      -> decr_n_nproc a = Some b
      -> select_n_nproc k b = Some c
      -> is_proc_n_nproc c.
  Proof.
    introv isp dec sel.
    destruct a as [cn a].
    simpl in *.
    unfold is_proc_n_proc in *; exrepnd.
    remember (decr_n_proc a) as d; symmetry in Heqd.
    destruct d; ginv;[].
    inversion dec; subst; clear dec.
    simpl in *.
    apply option_map_Some in sel; exrepnd; subst; simpl in *.
    exists p.
    introv.
    pose proof (isp0 s i) as isp0.
    eapply decr_n_proc_some_preserves_sm2update_eq_proc2upd in Heqd;[|eauto].
    eapply select_n_proc_preserves_sm2update_eq_proc2upd; eauto.
  Qed.
  Hint Resolve is_proc_n_nproc_select_n_nproc_decr_n_nproc : comp.

  Lemma are_procs_n_procs_select_n_procs_decr_n_procs :
    forall n k (subs : n_procs n),
      are_procs_n_procs subs
      -> are_procs_n_procs (select_n_procs k (decr_n_procs subs)).
  Proof.
    induction subs; introv aps; simpl in *; tcsp.
    { introv i; simpl in *; tcsp. }
    allrw are_procs_n_procs_cons; repnd.
    unfold decr_n_procs; simpl.
    remember (decr_n_nproc a) as d; symmetry in Heqd.
    destruct d; simpl; tcsp;[].

    unfold select_n_procs; simpl.
    remember (select_n_nproc k n0) as q; symmetry in Heqq.
    destruct q; simpl; tcsp;[].
    allrw are_procs_n_procs_cons.
    dands; tcsp; eauto 3 with comp.
  Qed.
  Hint Resolve are_procs_n_procs_select_n_procs_decr_n_procs : comp.

  Fixpoint halt_machine_m {n} {cn} :
    forall (sm : n_proc n cn), n_proc n cn :=
    match n with
    | 0 => fun sm => match sm with end
    | S m =>
      fun sm =>
        match sm with
        | sm_or_at p => sm_or_at (halt_machine p)
        | sm_or_sm q => sm_or_sm (halt_machine_m q)
        end
    end.

  Definition update_state_or_halt_m {n} {cn} (sm : n_proc n cn) sop : n_proc n cn :=
    match sop with
    | Some s => update_state_m sm s
    | None => halt_machine_m sm
    end.

  Definition lift_n_procs_eq {n j k} (e : n = S (j + k)) (l : n_procs k) : n_procs (pred n) :=
    eq_rect _ _ (lift_n_procs j l) _ (lift_eq_rev e).

  Lemma app_m_proc_some :
    forall {n} {cn}
           (sm : n_proc n cn)
           (i  : cio_I (fio cn)),
    exists (k : nat) (j : nat) (p : n_proc_at k cn) (e : n = S (j + k)),
    forall (subs : n_procs (pred n)),
      app_m_proc sm i subs
      = match sm_update p (sm_state p) i (select_n_procs k subs) with
        | (subs', (sop, out)) => (lift_n_procs_eq e subs', (update_state_or_halt_m sm sop, out))
        end.
  Proof.
    induction n; introv; simpl in *; ginv; tcsp;[].
    destruct sm as [sm|sm].

    { exists n 0 sm (eq_refl (S n)).
      introv.
      unfold n_proc in *.
      remember (sm_update sm (sm_state sm) i (select_n_procs n subs)) as w; symmetry in Heqw.
      repnd.

      unfold lift_n_procs_eq; simpl; autorewrite with comp in *.
      unfold lift_M_O, app_n_proc_at, bind_pair, bind; simpl.
      fold M_StateMachine in *.
      fold n_proc in *.
      rewrite Heqw; simpl; auto.
      destruct w1; simpl; tcsp. }

    { pose proof (IHn cn sm i) as IHn; exrepnd.
      exists k (S j) p (eq_S _ _ e).
      introv.
      pose proof (IHn1 (select_n_procs (pred n) subs)) as ap0.
      rewrite select_n_procs_select_n_procs_le in ap0; auto; try omega;[].
      remember (sm_update p (sm_state p) i (select_n_procs k subs)) as w.
      symmetry in Heqw; repnd.

      unfold lift_n_procs_eq; simpl; autorewrite with comp in *.
      remember (app_m_proc sm i) as ap.
      subst n.
      simpl.
      unfold lift_M_O2, bind_pair, bind, M_on_pred.
      simpl in *.
      rewrite <- decr_n_procs_as_select_n_procs in ap0.
      rewrite ap0; auto; simpl.
      f_equal;[|].

      { unfold lift_n_procs_eq; simpl.
        clear ap0 Heqw w.
        induction w0; simpl; auto.
        rewrite IHw0; clear IHw0; f_equal.
        destruct a; simpl; f_equal. }

      { destruct w1; simpl; tcsp. } }
  Qed.

  (* n <= m*)
  Fixpoint raise_to_n_proc {n} {cn} m (p : n_proc n cn) : option (n_proc m cn) :=
    match deq_nat n m with
    | left q => Some (eq_rect _ (fun n => n_proc n cn) p _ q)
    | right q =>
      match m with
      | 0 => None
      | S k => option_map incr_n_proc (raise_to_n_proc k p)
      end
    end.

  Definition raise_to_n_nproc {n} m (p : n_nproc n) : option (n_nproc m) :=
    match p with
    | MkPProc cn p => option_map (MkPProc cn) (raise_to_n_proc m p)
    end.

  Definition raise_to_n_procs {n} m (ps : n_procs n) : n_procs m :=
    mapOption (raise_to_n_nproc m) ps.

  Lemma raise_to_n_proc_trivial :
    forall cn n (p : n_proc n cn),
      raise_to_n_proc n p = Some p.
  Proof.
    introv.
    destruct n; simpl in *; tcsp.
    destruct (deq_nat n n); try omega; simpl in *.
    pose proof (UIP_refl_nat _ e) as w; subst; simpl in *; ginv; auto.
  Qed.
  Hint Rewrite raise_to_n_proc_trivial : comp.

  Lemma raise_to_n_procs_trivial :
    forall n (l : n_procs n),
      raise_to_n_procs n l = l.
  Proof.
    induction l; simpl; tcsp.
    unfold raise_to_n_procs in *; simpl.
    rewrite IHl; clear IHl.
    destruct a as [cn p]; simpl; autorewrite with comp in *; simpl; auto.
  Qed.
  Hint Rewrite raise_to_n_procs_trivial : comp.

  Lemma sm2level_le_pred :
    forall cn n (sm : n_proc n cn),
      sm2level sm <= Init.Nat.pred n.
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct sm as [sm|sm]; auto; tcsp;[].
    pose proof (IHn sm) as IHn; try omega.
  Qed.
  Hint Resolve sm2level_le_pred : comp.

  Lemma decr_n_procs_as_select_n_procs_pred :
    forall {k} (subs : n_procs k),
      decr_n_procs subs = select_n_procs (pred k) subs.
  Proof.
    introv; simpl.
    unfold decr_n_procs, select_n_procs.
    induction subs; simpl; auto.
    destruct a as [cn p].
    unfold select_n_nproc at 1.
    destruct k.

    { simpl in *; tcsp. }

    rewrite select_n_nproc_succ.
    simpl.
    destruct p; simpl in *; auto.
    unfold n_procs in *; rewrite IHsubs; auto.
  Qed.

  Lemma implies_raise_to_n_proc_none :
    forall cn n m (p : n_proc n cn),
      m < n
      -> raise_to_n_proc m p = None.
  Proof.
    induction m; introv ltn; simpl in *.
    { destruct (deq_nat n 0); subst; try omega; auto. }
    destruct (deq_nat n (S m)); subst; try omega.
    rewrite IHm; try omega; auto.
  Qed.

  Lemma incr_pred_n_procs_raise_to_n_procs :
    forall n k (l : n_procs k),
      k <= pred n
      -> incr_pred_n_procs (raise_to_n_procs (Init.Nat.pred n) l)
         = raise_to_n_procs n l.
  Proof.
    induction l; introv len; simpl; tcsp;[].
    repeat (autodimp IHl hyp).
    unfold raise_to_n_procs in *; simpl in *.
    destruct a as [cn p]; simpl.
    remember (raise_to_n_proc (pred n) p) as w; symmetry in Heqw.
    destruct w; simpl.

    { destruct n; simpl in *; tcsp.
      destruct (deq_nat k (S n)); subst; try simpl in *; try omega.
      allrw; simpl; tcsp. }

    rewrite IHl; clear IHl.
    destruct n; simpl in *; tcsp.
    { destruct (deq_nat k 0); subst; simpl in *; ginv; auto. }

    destruct (deq_nat k (S n)); subst; try simpl in *; try omega.
    allrw; simpl; auto.
  Qed.

  Lemma app_m_proc_some2 :
    forall {n} {cn}
           (sm : n_proc n cn)
           (i  : cio_I (fio cn))
           (subs : n_procs (pred n)),
      app_m_proc sm i subs
      = match sm2update sm (sm2state sm) i (select_n_procs (sm2level sm) subs) with
        | (subs', (sop, out)) => (raise_to_n_procs (pred n) subs', (update_state_or_halt_m sm sop, out))
        end.
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct sm as [sm|sm].

    { unfold n_proc in *.
      fold M_StateMachine in *.
      fold n_proc in *.
      remember (sm_update sm (sm_state sm) i (select_n_procs n subs)) as w; symmetry in Heqw.
      repnd.

      unfold lift_n_procs_eq; simpl; autorewrite with comp in *.
      unfold lift_M_O, app_n_proc_at, bind_pair, bind; simpl.
      rewrite Heqw; simpl; auto.
      destruct w1; simpl; tcsp. }

    { pose proof (IHn cn sm i (select_n_procs (pred n) subs)) as IHn.
      rewrite select_n_procs_select_n_procs_le in IHn; auto; eauto 3 with comp; try omega;[].

      remember (sm2update sm (sm2state sm) i (select_n_procs (sm2level sm) subs)) as w.
      symmetry in Heqw; repnd.

      unfold lift_M_O2, bind_pair, bind, M_on_pred.
      simpl in *.

      rewrite <- decr_n_procs_as_select_n_procs_pred in IHn.
      rewrite IHn; auto.
      rewrite incr_pred_n_procs_raise_to_n_procs; eauto 3 with comp;[].
      f_equal;[].
      f_equal;[].
      destruct w1; simpl; tcsp. }
  Qed.

  Lemma are_procs_n_procs_find_name :
    forall cn n (subs : n_procs n) p,
      are_procs_n_procs subs
      -> find_name cn subs = Some p
      -> is_proc_n_proc p.
  Proof.
    induction subs; introv aps fd; simpl in *; tcsp.
    destruct a as [cn' p']; simpl in *.
    allrw are_procs_n_procs_cons; repnd; simpl in *.
    destruct (CompNameDeq cn' cn); subst; ginv; tcsp.
  Qed.

  Lemma sm_update_sm2at :
    forall cn n (sm : n_proc n cn),
      sm_update (sm2at sm) = sm2update sm.
  Proof.
    induction n; introv; simpl in *; tcsp; destruct sm as [sm|sm]; tcsp.
  Qed.
  Hint Rewrite sm_update_sm2at : comp.

  Lemma implies_is_proc_n_proc_at_sm2at :
    forall cn n (sm : n_proc n cn),
      is_proc_n_proc sm
      -> is_proc_n_proc_at (sm2at sm).
  Proof.
    introv h.
    unfold is_proc_n_proc in *.
    unfold is_proc_n_proc_at; exrepnd.
    exists p; introv.
    pose proof (h0 s i) as h0.
    autorewrite with comp; auto.
  Qed.
  Hint Resolve implies_is_proc_n_proc_at_sm2at : comp.

  Lemma raise_to_n_procs_nil :
    forall k n,
      raise_to_n_procs k (@nil (n_nproc n)) = [].
  Proof.
    tcsp.
  Qed.
  Hint Rewrite raise_to_n_procs_nil : comp.

  Lemma raise_to_n_procs_cons :
    forall k n p (l : n_procs n),
      raise_to_n_procs k (p :: l)
      = match raise_to_n_nproc k p with
        | Some q => q :: raise_to_n_procs k l
        | None => raise_to_n_procs k l
        end.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite raise_to_n_procs_cons : comp.

  Lemma select_n_procs_nil :
    forall k n,
      select_n_procs k (@nil (n_nproc n)) = [].
  Proof.
    tcsp.
  Qed.
  Hint Rewrite select_n_procs_nil : comp.

  Lemma select_n_procs_cons :
    forall k n p (l : n_procs n),
      select_n_procs k (p :: l)
      = match select_n_nproc k p with
        | Some q => q :: select_n_procs k l
        | None => select_n_procs k l
        end.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite select_n_procs_cons : comp.

  Lemma similar_sms_implies_similar_raise_to_n_proc :
    forall k n cn (p1 p2 : n_proc n cn),
      similar_sms p1 p2
      ->
      (exists q1 q2,
          raise_to_n_proc k p1 = Some q1
          /\ raise_to_n_proc k p2 = Some q2
          /\ similar_sms q1 q2)
      \/
      (raise_to_n_proc k p1 = None
       /\ raise_to_n_proc k p2 = None).
  Proof.
    induction k; introv sim; simpl in *; tcsp.

    { destruct (deq_nat n 0); subst; simpl in *; tcsp. }

    destruct (deq_nat n (S k)); subst; simpl in *; tcsp.

    { left; eexists; eexists; dands; eauto. }

    apply IHk in sim; clear IHk.
    repndors; exrepnd; allrw; simpl; tcsp;[].
    left; eexists; eexists; dands; eauto.
  Qed.

  Lemma similar_procs_implies_similar_raise_to_n_nproc :
    forall n k (p1 p2 : n_nproc n),
      similar_procs p1 p2
      ->
      (exists q1 q2,
          raise_to_n_nproc k p1 = Some q1
          /\ raise_to_n_nproc k p2 = Some q2
          /\ similar_procs q1 q2)
      \/
      (raise_to_n_nproc k p1 = None
       /\ raise_to_n_nproc k p2 = None).
  Proof.
    introv sim.
    destruct p1 as [cn1 p1], p2 as [cn2 p2]; simpl in *.
    applydup @similar_procs_implies_same_name in sim; simpl in *; subst.
    apply similar_procs_implies_same_proc in sim.
    apply (similar_sms_implies_similar_raise_to_n_proc k) in sim.
    repndors; exrepnd; allrw; simpl; tcsp.
    left; eexists; eexists; dands; eauto.
  Qed.

  Lemma raise_to_n_procs_similar_subs :
    forall {n} k (subs1 subs2 : n_procs n),
      similar_subs subs1 subs2
      -> similar_subs (raise_to_n_procs k subs1) (raise_to_n_procs k subs2).
  Proof.
    introv sim; induction sim; simpl in *; autorewrite with comp in *; auto.
    apply (similar_procs_implies_similar_raise_to_n_nproc _ k) in simp.
    repndors; exrepnd; allrw; tcsp.
  Qed.

  Lemma implies_select_n_proc_S_incr :
    forall cn n m (p : n_proc n cn) (q : n_proc m cn),
      m < n
      -> select_n_proc m p = Some q
      -> select_n_proc (S m) p = Some (incr_n_proc q).
  Proof.
    induction n; introv ltn sel; try (complete (simpl in *; tcsp)).

    simpl in sel.
    destruct m; try (complete (simpl in *; tcsp)).
    destruct (deq_nat n m); subst.

    { simpl in *; ginv.
      destruct (deq_nat m (S m)); try omega. }

    simpl in *.
    destruct (deq_nat n (S m)); subst; tcsp.

    { simpl.
      destruct p as [p|p]; ginv.
      autorewrite with comp in *; ginv; auto. }

    destruct p as [p|p]; ginv.
    pose proof (IHn (S m) p q) as IHn.
    repeat (autodimp IHn hyp); try omega.
  Qed.

  Lemma select_n_proc_some_raise_to_n_proc_some_implies :
    forall cn n i j (a : n_proc n cn) b c,
      j <= i <= n
      -> select_n_proc j a = Some b
      -> raise_to_n_proc i b = Some c
      -> select_n_proc i a = Some c.
  Proof.
    induction n; introv lenn sel rais; simpl in *.

    { destruct j; simpl in *; ginv; tcsp. }

    destruct j; simpl in *; tcsp;[].
    destruct (deq_nat n j); simpl in *; ginv; tcsp; simpl in *;[|].

    { destruct i; simpl in *; ginv.
      destruct (deq_nat j i); subst; simpl in *; ginv; try omega. }

    destruct a as [a|a]; simpl in *; ginv;[].

    destruct i; simpl in *; tcsp;[].
    destruct (deq_nat j i); subst; ginv.

    { destruct (deq_nat n i); subst; tcsp. }

    destruct (deq_nat n i); subst; tcsp; try omega; ginv.

    { apply option_map_Some in rais; exrepnd; subst; simpl in *.
      pose proof (IHn i (S j) a b a0) as IHn.
      repeat (autodimp IHn hyp); try omega;[].
      autorewrite with comp in *; ginv. }

    apply option_map_Some in rais; exrepnd; subst.
    pose proof (IHn i (S j) a b a0) as IHn.
    repeat (autodimp IHn hyp); try omega;[].
    apply implies_select_n_proc_S_incr; auto; try omega.
  Qed.

  Lemma select_n_nproc_some_raise_to_n_nproc_some_implies :
    forall n i j (a : n_nproc n) b c,
      j <= i <= n
      -> select_n_nproc j a = Some b
      -> raise_to_n_nproc i b = Some c
      -> select_n_nproc i a = Some c.
  Proof.
    introv lenn sel rais.
    destruct a as [cna a]; simpl in *.
    apply option_map_Some in sel; exrepnd; subst; simpl in *.
    apply option_map_Some in rais; exrepnd; subst; simpl in *.
    pose proof (select_n_proc_some_raise_to_n_proc_some_implies cna n i j a a0 a1) as w.
    repeat (autodimp w hyp).
    rewrite w; simpl; auto.
  Qed.

  Lemma raise_to_n_proc_none_implies :
    forall cn n i (a : n_proc n cn),
      raise_to_n_proc i a = None
      -> i < n.
  Proof.
    induction i; introv rais; simpl in *; tcsp.

    { destruct (deq_nat n 0); simpl in *; ginv; tcsp; try omega. }

    destruct (deq_nat n (S i)); simpl in *; ginv; tcsp; simpl in *; try omega.
    remember (raise_to_n_proc i a) as r; symmetry in Heqr.
    destruct r; simpl in *; ginv.
    apply IHi in Heqr; try omega.
  Qed.

  Lemma raise_to_n_nproc_none_implies :
    forall n i (a : n_nproc n),
      raise_to_n_nproc i a = None
      -> i < n.
  Proof.
    introv rais.
    destruct a as [cna a]; simpl in *.
    remember (raise_to_n_proc i a) as r; symmetry in Heqr.
    destruct r; simpl in *; ginv.
    apply raise_to_n_proc_none_implies in Heqr; auto.
  Qed.

  Lemma select_n_proc_implies_lt :
    forall cn n j (a : n_proc n cn),
      j <= n
      -> select_n_proc j a = None
      -> j <= sm2level a.
  Proof.
    induction n; introv len sel; simpl in *; tcsp;[].
    destruct j; tcsp.

    { repndors; ginv; try omega. }

    destruct (deq_nat n j); subst; simpl in *; ginv.
    destruct a as [a|a]; ginv; try omega.
    pose proof (IHn (S j) a) as IHn.
    repeat (autodimp IHn hyp); try omega.
  Qed.

  Lemma select_n_nproc_implies_lt :
    forall n j (a : n_nproc n),
      j <= n
      -> select_n_nproc j a = None
      -> j <= sm2level (pp_proc a).
  Proof.
    introv len sel.
    destruct a as [cn a]; simpl in *.
    remember (select_n_proc j a) as r; symmetry in Heqr.
    destruct r; simpl in *; ginv.
    apply select_n_proc_implies_lt in Heqr; auto.
  Qed.

  Lemma similar_sms_incr_pred_n_proc :
    forall cn n (p1 p2 : n_proc (pred n) cn),
      similar_sms p1 p2
      -> similar_sms (incr_pred_n_proc p1) (incr_pred_n_proc p2).
  Proof.
    destruct n; simpl in *; tcsp.
  Qed.
  Hint Resolve similar_sms_incr_pred_n_proc : comp.

  Lemma similar_subs_replace_sub :
    forall n cn (p1 p2 : n_proc (pred n) cn) (subs1 subs2 : n_procs n),
      similar_sms p1 p2
      -> similar_subs subs1 subs2
      -> similar_subs (replace_sub subs1 p1) (replace_sub subs2 p2).
  Proof.
    introv simp sims.
    induction sims; simpl in *; auto.
    destruct p0 as [ca pa], p3 as [cb pb]; simpl in *.
    applydup @similar_procs_implies_same_name in simp0; simpl in *; subst.
    apply similar_procs_implies_same_proc in simp0.
    destruct (CompNameDeq cn cb); subst; tcsp.
    constructor; auto.
    constructor; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_replace_sub : comp.

  Lemma similar_subs_replace_subs :
    forall n subsa subsb (subs1 subs2 : n_procs (pred n)),
      similar_subs subs1 subs2
      -> similar_subs subsa subsb
      -> similar_subs (replace_subs subsa subs1) (replace_subs subsb subs2).
  Proof.
    introv sim; revert subsa subsb.
    induction sim; introv simab; simpl in *; eauto 3 with comp.
    destruct p1 as [cn1 p1], p2 as [cn2 p2]; simpl in *.
    applydup @similar_procs_implies_same_name in simp; simpl in *; subst.
    apply similar_procs_implies_same_proc in simp.
    apply IHsim; clear IHsim; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_replace_subs : comp.

  Lemma is_proc_n_proc_update_implies_some :
    forall cn n (p : n_proc n cn) s i subs1 subs2 sop out,
      is_proc_n_proc p
      -> sm2update p s i subs1 = (subs2, (sop, out))
      -> exists s, sop = Some s.
  Proof.
    introv isp e.
    unfold is_proc_n_proc in isp; exrepnd.
    rewrite isp0 in e; clear isp0.
    unfold proc2upd in *; simpl in *.
    unfold interp_s_proc, to_proc_some_state in *; simpl in *.
    unfold bind_pair, bind in *; simpl in *.
    remember (interp_proc (p0 s i) subs1) as w; repnd; simpl in *; ginv; eauto.
  Qed.

  Lemma similar_sms_update_state_m :
    forall cn n (p : n_proc n cn) (s : sf cn),
      similar_sms (update_state_m p s) p.
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct p; simpl in *; tcsp.
    split; simpl; auto.
  Qed.
  Hint Resolve similar_sms_update_state_m : comp.

  Lemma similar_subs_replace_name_update_state_m_find :
    forall cn n (subs : n_procs n) (p : n_proc n cn) (s : sf cn),
      find_name cn subs = Some p
      -> similar_subs
           (replace_name (update_state_m p s) subs)
           subs.
  Proof.
    induction subs; introv fd; simpl in *; ginv.
    destruct a as [cn' p']; simpl in *.
    destruct (CompNameDeq cn' cn); subst; simpl in *; tcsp; ginv;
      constructor; auto; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_replace_name_update_state_m_find : comp.

  Lemma select_n_nproc_a_decr_n_nproc :
    forall n (a : n_nproc n),
      select_n_nproc (pred n) a = decr_n_nproc a.
  Proof.
    introv.
    destruct a as [cn p]; simpl in *.
    destruct n; auto.
    rewrite select_n_nproc_succ.
    simpl in *; repndors; simpl; auto.
  Qed.

  Lemma in_raise_select_implies :
    forall n i (subs : n_procs n),
      i <= pred n
      ->
      forall p,
        In p (raise_to_n_procs (pred n) (select_n_procs i subs))
        -> exists q, In q subs /\ decr_n_nproc q = Some p.
  Proof.
    induction subs; introv len ins; simpl in *; tcsp.
    autorewrite with comp in *.
    remember (select_n_nproc i a) as sela; symmetry in Heqsela.
    destruct sela; simpl in *; autorewrite with comp in *.

    { remember (raise_to_n_nproc (pred n) n0) as raisa; symmetry in Heqraisa.
      destruct raisa; simpl in *; repndors; subst; tcsp.

      { pose proof (select_n_nproc_some_raise_to_n_nproc_some_implies
                      n (pred n) i a n0 p) as w.
        repeat (autodimp w hyp); try omega;[].
        rewrite select_n_nproc_a_decr_n_nproc in w.
        eexists; dands; eauto. }

      { apply IHsubs in ins; auto.
        exrepnd.
        eexists; dands; eauto. }

      { apply IHsubs in ins; auto.
        exrepnd.
        eexists; dands; eauto. } }

    apply IHsubs in ins; auto.
    exrepnd.
    eexists; dands; eauto.
  Qed.

  Definition procs_names {n} (subs : n_procs n) :=
    map (fun p => pp_name p) subs.

  Definition wf_procs {n} (subs : n_procs n) : Prop :=
    no_repeats (procs_names subs).

  Lemma wf_procs_cons :
    forall n p (subs : n_procs n),
      wf_procs (p :: subs) <-> (~In (pp_name p) (procs_names subs) /\ wf_procs subs).
  Proof.
    introv; unfold wf_procs; simpl.
    rewrite no_repeats_cons; split; tcsp.
  Qed.

  Lemma proc_names_replace_sub :
    forall n cn (subs : n_procs n) (p : n_proc (pred n) cn),
      procs_names (replace_sub subs p) = procs_names subs.
  Proof.
    induction subs; introv; simpl in *; tcsp.
    pose proof (IHsubs p) as IHsubs.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq cn c); simpl; subst; tcsp; try congruence.
  Qed.
  Hint Rewrite proc_names_replace_sub : comp.

  Lemma wf_procs_replace_sub :
    forall cn n (subs : n_procs n) (p : n_proc (pred n) cn),
      wf_procs subs
      -> wf_procs (replace_sub subs p).
  Proof.
    induction subs; introv wf; simpl in *; tcsp.
    rewrite wf_procs_cons in wf; repnd.
    pose proof (IHsubs p wf) as IHsubs.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq cn c); subst; apply wf_procs_cons; dands; tcsp; simpl in *.
    autorewrite with comp; auto.
  Qed.
  Hint Resolve wf_procs_replace_sub : comp.

  Lemma in_replace_sub_if_diff :
    forall cn n (subs : n_procs n) (p : n_proc (pred n) cn) q,
      pp_name q <> cn
      -> In q subs
      -> In q (replace_sub subs p).
  Proof.
    induction subs; introv d i; simpl in *; tcsp.
    destruct a as [c a].
    destruct (CompNameDeq cn c); subst; simpl in *; tcsp;[].
    repndors; subst; simpl in *; tcsp.
  Qed.
  Hint Resolve in_replace_sub_if_diff : comp.

  Lemma name_of_decr_n_nproc :
    forall n (q : n_nproc n) p,
      decr_n_nproc q = Some p
      -> pp_name q = pp_name p.
  Proof.
    introv h.
    destruct q as [c1 p1], p as [c2 p2]; simpl in *.
    destruct n; simpl in *; tcsp.
    destruct p1; simpl in *; ginv.
    inversion h; auto.
  Qed.

  Lemma in_implies_in_proc_names :
    forall n (subs : n_procs n) a,
      In a subs
      -> In (pp_name a) (procs_names subs).
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    repndors; subst; tcsp.
  Qed.
  Hint Resolve in_implies_in_proc_names : comp.

  Lemma wf_procs_same_names_implies :
    forall n (subs : n_procs n) a b,
      wf_procs subs
      -> In a subs
      -> In b subs
      -> pp_name a = pp_name b
      -> a = b.
  Proof.
    induction subs; introv wf i j e; simpl in *; tcsp.
    allrw wf_procs_cons; repnd.
    repndors; subst; tcsp.

    { applydup in_implies_in_proc_names in i.
      rewrite e in i0; tcsp. }

    { applydup in_implies_in_proc_names in j.
      rewrite <- e in j0; tcsp. }
  Qed.

  Lemma in_replace_sub_if_in_names :
    forall n (p : n_nproc (pred n)) subs,
      In (pp_name p) (procs_names subs)
      -> In (incr_pred_n_nproc p) (replace_sub subs (pp_proc p)).
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [cn a]; simpl in *.
    destruct p as [c p]; simpl in *.
    destruct (CompNameDeq c cn); subst; simpl; tcsp.
  Qed.

  Lemma implies_similar_subs_replace_sub :
    forall cn n (subs : n_procs n) (q : n_nproc n) (p : n_proc (pred n) cn),
      wf_procs subs
      -> In q subs
      -> decr_n_nproc q = Some (MkPProc cn p)
      -> similar_subs subs (replace_sub subs p).
  Proof.
    induction subs; introv wf i e; simpl in *; tcsp.
    allrw wf_procs_cons; repnd.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq cn c); subst; simpl in *; tcsp;
      repndors; subst; simpl in *; tcsp.

    { constructor; eauto 3 with comp.
      constructor.
      destruct n; simpl in *; tcsp.
      destruct a as [a|a]; ginv;[].
      inversion e; subst.
      match goal with
      | [ H : context[p] |- _ ] => rename H into h1
      end.
      apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp. }

    { assert False; tcsp.
      apply name_of_decr_n_nproc in e; simpl in *; subst.
      destruct wf0; eauto 3 with comp. }

    {  destruct n; simpl in *; tcsp;[].
       destruct a as [a|a]; ginv.
       inversion e; subst.
       match goal with
       | [ H : context[p] |- _ ] => rename H into h1
       end.
       apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp; tcsp. }

    { constructor; eauto 3 with comp. }
  Qed.
  Hint Resolve implies_similar_subs_replace_sub : comp.

  Lemma similar_subs_replace_subs_raise_select :
    forall n l (subs : n_procs n),
      wf_procs subs
      -> (forall p, In p l -> exists q, In q subs /\ decr_n_nproc q = Some p)
      -> similar_subs subs (replace_subs subs l).
  Proof.
    induction l; introv wf imp; simpl in *; eauto 3 with comp.
    pose proof (imp a) as h; autodimp h hyp; exrepnd.
    destruct a as [cn p]; simpl in *.
    pose proof (IHl (replace_sub subs p)) as IHl.
    repeat (autodimp IHl hyp); eauto 3 with comp;[].

    introv i.
    pose proof (imp p0) as w; clear imp; autodimp w hyp; exrepnd.
    destruct (CompNameDeq (pp_name q0) cn); subst;
      [|exists q0; dands; auto; eauto 3 with comp;
        apply in_replace_sub_if_diff; auto].
    applydup name_of_decr_n_nproc in h0; simpl in *.
    eapply wf_procs_same_names_implies in h1; try exact w1; auto; subst; GC.
    rewrite h0 in w0; ginv; simpl in *.
    exists (MkPProc (pp_name q) (incr_pred_n_proc p)); simpl; dands; auto;
      [|destruct n; simpl; auto];[].
    pose proof (in_replace_sub_if_in_names n (MkPProc (pp_name q) p) subs) as w.
    simpl in *; apply w; clear w; eauto 3 with comp.
  Qed.

  Lemma similar_subs_preserves_procs_names :
    forall n (subs1 subs2 : n_procs n),
      similar_subs subs1 subs2
      -> procs_names subs1 = procs_names subs2.
  Proof.
    introv sim; induction sim; introv; auto.
    unfold procs_names in *; simpl.
    f_equal; auto;[].
    inversion simp; subst.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
  Qed.

  Lemma similar_subs_preserves_wf_procs :
    forall n (subs1 subs2 : n_procs n),
      similar_subs subs1 subs2
      -> wf_procs subs1
      -> wf_procs subs2.
  Proof.
    introv sim; apply similar_subs_preserves_procs_names in sim.
    unfold wf_procs.
    rewrite sim; auto.
  Qed.
  Hint Resolve similar_subs_preserves_wf_procs : comp.

  Lemma name_of_select_n_nproc :
    forall n i (q : n_nproc n) p,
      select_n_nproc i q = Some p
      -> pp_name q = pp_name p.
  Proof.
    introv h.
    destruct q as [c1 p1], p as [c2 p2]; simpl in *.
    apply option_map_Some in h; exrepnd; ginv.
    inversion h0; subst.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into q
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in q; subst; eauto 3 with comp.
  Qed.
  Hint Resolve name_of_select_n_nproc : comp.

  Lemma subset_procs_names_select_n_procs :
    forall n i (subs : n_procs n),
      subset (procs_names (select_n_procs i subs)) (procs_names subs).
  Proof.
    induction subs; introv j; simpl in *; tcsp.
    autorewrite with comp in *.
    remember (select_n_nproc i a) as sel; symmetry in Heqsel.
    destruct sel; simpl in *; repndors; subst; tcsp.
    left; eauto 3 with comp.
  Qed.

  Lemma wf_procs_select_n_procs :
    forall n i (subs : n_procs n),
      wf_procs subs
      -> wf_procs (select_n_procs i subs).
  Proof.
    induction subs; introv wf; simpl in *; tcsp.
    allrw wf_procs_cons; repnd.
    autorewrite with comp.
    remember (select_n_nproc i a) as sel; symmetry in Heqsel.
    destruct sel; auto;[].
    apply wf_procs_cons; dands; auto;[].
    introv j.
    apply subset_procs_names_select_n_procs in j; tcsp.
    apply name_of_select_n_nproc in Heqsel.
    rewrite Heqsel in wf0; tcsp.
  Qed.
  Hint Resolve wf_procs_select_n_procs : comp.

  Lemma wf_procs_decr_n_procs :
    forall n (subs : n_procs n),
      wf_procs subs
      -> wf_procs (decr_n_procs subs).
  Proof.
    introv wf.
    rewrite decr_n_procs_as_select_n_procs_pred; eauto 3 with comp.
  Qed.
  Hint Resolve wf_procs_decr_n_procs : comp.

  Lemma implies_wf_procs_replace_subs :
    forall n l (subs : n_procs n),
      wf_procs subs
      -> wf_procs l
      -> wf_procs (replace_subs subs l).
  Proof.
    induction l; introv wfa wfb; simpl in *; tcsp.
    allrw wf_procs_cons; repnd.
    destruct a as [c a]; simpl in *; tcsp.
    apply IHl; auto; eauto 3 with comp.
  Qed.
  Hint Resolve implies_wf_procs_replace_subs : comp.

  Lemma procs_names_replace_name :
    forall n cn (p : n_proc n cn) (subs : n_procs n),
      procs_names (replace_name p subs) = procs_names subs.
  Proof.
    induction subs; introv; simpl; auto.
    destruct a as [c a].
    destruct (CompNameDeq c cn); subst; simpl in *; tcsp.
    rewrite IHsubs; auto.
  Qed.
  Hint Rewrite procs_names_replace_name : comp.

  Lemma wf_procs_replace_name :
    forall n cn (p : n_proc n cn) (subs : n_procs n),
      wf_procs subs
      -> wf_procs (replace_name p subs).
  Proof.
    introv wf; unfold wf_procs in *; autorewrite with comp; auto.
  Qed.
  Hint Resolve wf_procs_replace_name : comp.

  Lemma name_of_raise_to_n_nproc :
    forall n i (q : n_nproc n) p,
      raise_to_n_nproc i q = Some p
      -> pp_name q = pp_name p.
  Proof.
    introv h.
    destruct q as [c1 p1], p as [c2 p2]; simpl in *.
    apply option_map_Some in h; exrepnd; ginv.
    inversion h0; subst.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into q
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in q; subst; eauto 3 with comp.
  Qed.
  Hint Resolve name_of_raise_to_n_nproc : comp.

  Lemma subset_procs_names_raise_to_n_procs :
    forall n i (subs : n_procs n),
      subset (procs_names (raise_to_n_procs i subs)) (procs_names subs).
  Proof.
    induction subs; introv j; simpl in *; tcsp.
    autorewrite with comp in *.
    remember (raise_to_n_nproc i a) as sel; symmetry in Heqsel.
    destruct sel; simpl in *; repndors; subst; tcsp.
    left; eauto 3 with comp.
  Qed.

  Lemma implies_wf_procs_raise_to_n_procs :
    forall n j (subs : n_procs n),
      wf_procs subs
      -> wf_procs (raise_to_n_procs j subs).
  Proof.
    induction subs; introv wf; simpl in *; tcsp.
    allrw raise_to_n_procs_cons.
    allrw wf_procs_cons; repnd.
    remember (raise_to_n_nproc j a) as w; symmetry in Heqw.
    destruct w; auto.
    allrw wf_procs_cons; dands; tcsp.
    intro i; apply subset_procs_names_raise_to_n_procs in i.
    apply name_of_raise_to_n_nproc in Heqw; rewrite <- Heqw in i; tcsp.
  Qed.
  Hint Resolve implies_wf_procs_raise_to_n_procs : comp.

  Lemma similar_subs_replace_name_update_state_m_find_name :
    forall n (subs : n_procs n) cn (p : n_proc n cn) s,
      find_name cn subs = Some p
      -> similar_subs
           (replace_name (update_state_m p s) subs)
           subs.
  Proof.
    induction subs; introv fd; simpl in *; ginv.
    destruct a as [cn' p']; simpl in *.
    repeat (dest_cases w; simpl in *; ginv; tcsp);
      repeat (constructor; auto; eauto 3 with comp);
        simpl in *; subst; simpl in *; tcsp;
          assert (w = eq_refl) as xx by (apply UIP_refl_PreCompName; auto); subst; simpl;
            unfold eq_rect_r; simpl; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_replace_name_update_state_m_find_name : comp.

  Lemma interp_proc_preserves_subs :
    forall {A} (p : Proc A) {n} (subs1 : n_procs n),
      (forall (m     : nat)
              (cn    : CompName)
              (main  : n_proc_at m cn)
              (s     : sf cn)
              (i     : cio_I (fio cn))
              (subs1 : n_procs m),
          m < n
          -> is_proc_n_proc_at main
          -> are_procs_n_procs subs1
          -> wf_procs subs1
          -> M_break
               (sm_update main s i)
               subs1
               (fun subs2 _ =>
                  similar_subs subs1 subs2
                  /\ wf_procs subs2))
      -> are_procs_n_procs subs1
      -> wf_procs subs1
      -> M_break
           (interp_proc p)
           subs1
           (fun subs2 _ =>
              similar_subs subs1 subs2
              /\ wf_procs subs2).
  Proof.
    induction p as [| |]; introv imp wf aps; simpl; autorewrite with comp; eauto 3 with comp.

    { pose proof (IHp _ subs1) as IHp.
      repeat (autodimp IHp hyp).
      unfold M_break in *.
      destruct (interp_proc p subs1); repnd.
      rename_hyp_with @interp_proc w.
      pose proof (w a _ n0) as w.
      repeat (autodimp w hyp); eauto 3 with comp;[].
      destruct (interp_proc (q a) n0); repnd; dands; eauto 3 with comp. }

    { unfold M_break, call_proc; simpl.
      remember (find_name cn subs1) as fd; symmetry in Heqfd; destruct fd; eauto 3 with comp;[].
      rename n0 into p.
      remember (app_m_proc p i (decr_n_procs subs1)) as ap; symmetry in Heqap; repnd.
      rewrite (app_m_proc_some2 p i) in Heqap.
      remember (sm2update p (sm2state p) i (select_n_procs (sm2level p) (decr_n_procs subs1))) as w; symmetry in Heqw.
      repnd; ginv; simpl in *.

      pose proof (sm2level_le_pred _ _ p) as ln0.

      pose proof (are_procs_n_procs_find_name _ _ subs1 p) as isp; simpl in isp.
      repeat (autodimp isp hyp).

      applydup is_proc_n_proc_update_implies_some in Heqw; auto;[]; exrepnd; subst; simpl in *.

      pose proof (imp (sm2level p) _ (sm2at p) (sm2state p) i (select_n_procs (sm2level p) (decr_n_procs subs1))) as imp.
      repeat (autodimp imp hyp); try omega; eauto 3 with comp;
        try (complete (destruct n; simpl in *; tcsp; try omega));[].
      autorewrite with comp in *.

      simpl in *.
      unfold M_break in imp.
      rewrite Heqw in imp; repnd.
      apply (raise_to_n_procs_similar_subs (pred n)) in imp0.

      rewrite decr_n_procs_as_select_n_procs_pred in imp0.
      rewrite select_n_procs_select_n_procs_le in imp0; try omega.
      apply (similar_subs_replace_subs
               _
               (replace_name (update_state_m p s) subs1)
               (replace_name (update_state_m p s) subs1)) in imp0; eauto 3 with comp.

      dands; eauto 4 with comp;[].

      eapply similar_subs_trans;[|eauto].
      clear imp0.

      pose proof (similar_subs_replace_name_update_state_m_find_name _ subs1 _ p s) as w.
      autodimp w hyp.
      apply (similar_subs_replace_subs
               _ _ _
               (raise_to_n_procs (Init.Nat.pred n) (select_n_procs (sm2level p) subs1))
               (raise_to_n_procs (Init.Nat.pred n) (select_n_procs (sm2level p) subs1))) in w; eauto 3 with comp.
      eapply similar_subs_trans;[|apply similar_subs_sym;eauto].
      clear w.

      pose proof (in_raise_select_implies n (sm2level p) subs1) as w.
      autodimp w hyp.
      apply similar_subs_replace_subs_raise_select; auto. }
  Qed.

  Lemma interp_s_proc_preserves_subs :
    forall {S O} (p : Proc (S * O)) {n} (subs1 : n_procs n),
      (forall (m     : nat)
              (cn    : CompName)
              (main  : n_proc_at m cn)
              (s     : sf cn)
              (i     : cio_I (fio cn))
              (subs1 : n_procs m),
          m < n
          -> is_proc_n_proc_at main
          -> are_procs_n_procs subs1
          -> wf_procs subs1
          -> M_break
               (sm_update main s i)
               subs1
               (fun subs2 _ =>
                  similar_subs subs1 subs2
                  /\ wf_procs subs2))
      -> are_procs_n_procs subs1
      -> wf_procs subs1
      -> M_break
           (interp_s_proc p)
           subs1
           (fun subs2 _ =>
              similar_subs subs1 subs2
              /\ wf_procs subs2).
  Proof.
    introv imp aps wf.
    unfold interp_s_proc, to_proc_some_state.
    pose proof (interp_proc_preserves_subs p subs1) as q; repeat (autodimp q hyp).
    clear imp aps wf.
    simpl; autorewrite with comp.
    unfold M_break in *.
    destruct (interp_proc p subs1); repnd; simpl; auto.
  Qed.

  Lemma are_procs_implies_preserves_sub :
    forall {n} {cn}
           (main  : n_proc_at n cn)
           (s     : sf cn)
           (i     : cio_I (fio cn))
           (subs1 : n_procs n),
      is_proc_n_proc_at main
      -> are_procs_n_procs subs1
      -> wf_procs subs1
      -> M_break (sm_update main s i)
                 subs1
                 (fun subs2 _ =>
                    similar_subs subs1 subs2
                    /\ wf_procs subs2).
  Proof.
    induction n as [? ind] using comp_ind; introv ip ap wf;[].
    unfold is_proc_n_proc_at in ip; exrepnd.
    rewrite ip0.
    unfold proc2upd; simpl.
    apply interp_s_proc_preserves_subs; auto.
  Qed.

  Definition wf_ls {L S} (ls : LocalSystem L S) :=
    ~In S (procs_names (ls_subs ls))
    /\ wf_procs (ls_subs ls).

  Definition wf_sys {f} (sys : M_USystem f) :=
    forall n, wf_ls (sys n).

  Lemma are_procs_ls_implies_ls_preserves_sub :
    forall {L S} (ls : LocalSystem L S),
      are_procs_ls ls
      -> wf_ls ls
      -> ls_preserves_subs ls.
  Proof.
    introv h wf sim.
    destruct h as [isp1 ips2]; simpl in *.
    destruct ls as [main subs]; simpl in *.
    destruct wf as [wf1 wf2]; simpl in *.
    eapply similar_subs_preserves_are_procs_n_procs in ips2;[|eauto];[].
    eapply similar_subs_preserves_wf_procs in wf2;[|simpl;eauto];[].

    clear subs sim wf1.

    pose proof (are_procs_implies_preserves_sub main s i subs1) as w.
    repeat (autodimp w hyp);[].
    unfold M_break in *; dest_cases z; tcsp.
  Qed.
  Hint Resolve are_procs_ls_implies_ls_preserves_sub : comp.



  (* ================================================================ *)
  (* ====== TEST ====== *)

  Lemma are_procs_ls_TEST : are_procs_ls TESTls.
  Proof.
    split; simpl.
    { eexists; introv; unfold proc2upd;  reflexivity. }
    { introv i; simpl in *; repndors; subst; tcsp; simpl;
        eexists; introv; unfold proc2upd;  reflexivity. }
  Qed.

  Lemma wf_ls_TEST : wf_ls TESTls.
  Proof.
    unfold wf_ls, wf_procs; simpl.
    dands; try (complete (introv xx; repndors; tcsp; ginv));[].
    constructor; simpl; tcsp; try (complete (introv xx; repndors; tcsp; ginv)).
  Qed.

  Lemma ls_preserves_subs_TEST : ls_preserves_subs TESTls.
  Proof.
    apply are_procs_ls_implies_ls_preserves_sub;
      try apply are_procs_ls_TEST;
      try apply wf_ls_TEST.
  Qed.

  (* ================================================================ *)


  Definition find_sub (cn : CompName) {L S} (ls : LocalSystem L S) : option (n_proc L cn) :=
    find_name cn (ls_subs ls).

  Definition state_of_main_or_sub
             {n} {cn}
             (name : CompName)
             (s    : sf cn)
             (subs : n_procs n) : option (sf name) :=
    match CompNameDeq cn name with
    | left p => Some (eq_rect _ _ s _ p)
    | right q => state_of_subcomponents subs name
    end.

  Lemma M_byz_state_ls_before_event_as :
    forall {L S}
           (ls : MLocalSystem L S)
           {eo : EventOrdering}
           (e  : Event)
           (cn : CompName),
      M_byz_state_ls_before_event ls e cn
      = M_break
          (M_byz_run_update_on_list (sm_state (ls_main ls)) (sm_update (ls_main ls)) (map trigger (History(e))))
          (ls_subs ls)
          (fun subs' out =>
             map_op_untrusted_op
               out
               (fun s => state_of_main_or_sub cn s subs')).
  Proof.
    introv.
    unfold M_byz_state_ls_before_event; simpl.
    unfold M_byz_run_ls_before_event; simpl.
    unfold upd_ls_main_state_and_subs; simpl.
    unfold M_byz_state_sm_before_event; simpl.
    unfold M_byz_run_sm_on_list; simpl.
    destruct ls as [main subs]; simpl.
    fold M_StateMachine.
    fold n_proc.
    unfold M_break.
    remember (M_byz_run_update_on_list (sm_state main) (sm_update main) (map trigger History(e)) subs) as w; symmetry in Heqw.
    simpl in *.
    rewrite Heqw.
    repnd.
    destruct w; simpl; auto.
    destruct m; simpl; auto.
  Qed.

  Lemma find_name_implies_in_procs_names :
    forall cn n (subs : n_procs n) sm,
      find_name cn subs = Some sm
      -> In cn (procs_names subs).
  Proof.
    induction subs; introv fd; simpl in *; ginv.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq c cn); subst; tcsp.
    apply IHsubs in fd; tcsp.
  Qed.
  Hint Resolve find_name_implies_in_procs_names : comp.

  Lemma find_name_not_in_procs_names_implies :
    forall cn name n (subs : n_procs n) sm,
      find_name cn subs = Some sm
      -> ~ In name (procs_names subs)
      -> cn <> name.
  Proof.
    introv fd ni.
    apply find_name_implies_in_procs_names in fd.
    intro xx; subst; tcsp.
  Qed.

  Lemma find_sub_wf_ls_implies :
    forall cn {L} {S} (ls : LocalSystem L S) sm,
      find_sub cn ls = Some sm
      -> wf_ls ls
      -> cn <> S.
  Proof.
    introv fd ni.
    destruct ls as [main subs]; simpl in *.
    unfold find_sub in *; simpl in *.
    destruct ni as [ni1 ni2]; simpl in *.
    eapply find_name_not_in_procs_names_implies; eauto.
  Qed.

  Lemma state_of_component_eq :
    forall {L S}
           (cn : CompName)
           (ls : LocalSystem L S),
      state_of_component cn ls
      = match CompNameDeq S cn with
        | left p => Some (eq_rect _ _ (sm_state (ls_main ls)) _ p)
        | right q => state_of_subcomponents (ls_subs ls) cn
        end.
  Proof.
    introv.
    unfold state_of_component.
    destruct ls as [main subs].
    destruct (CompNameDeq S cn); auto.
  Qed.

  (*
  map_op_untrusted_op
      (M_byz_run_ls_before_event ls e)
      (state_of_component cn).

  Lemma M_byz_compose_step :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      are_procs_ls ls
      -> find_sub cn ls = Some sm
      -> wf_ls ls
      ->
      exists (l : list (trigger_info (cio_I (fio cn)))),
        M_break
          (M_byz_run_sm_on_list sm l)
          (select_n_procs (sm2level sm) (ls_subs ls))
          (fun _ s => M_byz_run_ls_on_this_one_event ls e = s).
  Proof.
    introv aps fs wf.
    destruct ls as [main subs]; simpl in *.
    destruct aps as [aps1 aps2]; simpl in *.
    destruct wf as [wf1 wf2]; simpl in *.
    unfold find_sub in fs; simpl in *.
    rewrite M_byz_state_ls_before_event_as; simpl.

    remember (map trigger (History(e))) as K; clear HeqK.

      : option (M_trusted (LocalSystem _ _)) :=
*)

  Lemma in_combine_same :
    forall {T} a b (l : list T),
      In (a,b) (combine l l) -> a = b.
  Proof.
    induction l; introv i; simpl in *; tcsp.
    repndors; ginv; tcsp.
  Qed.

  Lemma in_replace_sub_implies :
    forall {n} {cn} (p : n_nproc n) (subs : n_procs n) (a : n_proc (pred n) cn),
      In p (replace_sub subs a)
      -> In p subs \/ p = MkPProc cn (incr_pred_n_proc a).
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [c a].
    destruct (CompNameDeq cn c); subst; simpl in *; repndors; tcsp.
    apply IHsubs in i; repndors; tcsp.
  Qed.

  Lemma in_replace_subs_implies :
    forall {n} (l : n_procs (pred n)) (ps : n_procs n) (p : n_nproc n),
      In p (replace_subs ps l)
      -> In p ps \/ In p (raise_to_n_procs n l).
  Proof.
    induction l; introv i; simpl in *; tcsp.
    destruct a as [cn a]; simpl in *.
    autorewrite with comp; simpl.
    apply IHl in i; clear IHl.
    repndors.

    { apply in_replace_sub_implies in i; repndors; subst; tcsp.
      right.
      destruct n; simpl in *; tcsp.
      destruct (deq_nat n (S n)); try omega.
      autorewrite with comp; simpl; tcsp. }

    { destruct (raise_to_n_proc n a); simpl; tcsp. }
  Qed.

  Definition op_compose {A B C} (f : A -> option B) (g : B -> option C) : A -> option C :=
    fun a => map_option g (f a).

  Lemma mapOption_idem :
    forall {A B C} (f : A -> option B) (g : B -> option C) (l : list A),
      mapOption g (mapOption f l)
      = mapOption (op_compose f g) l.
  Proof.
    induction l; introv; simpl; tcsp.
    unfold op_compose.
    destruct (f a); simpl; tcsp.
    destruct (g b); simpl; tcsp.
    rewrite IHl; auto.
  Qed.

  Lemma eq_mapOptions :
    forall {A B} (f g : A -> option B) (l : list A),
      (forall a, f a = g a)
      -> mapOption f l = mapOption g l.
  Proof.
    induction l; introv imp; simpl; tcsp.
    rewrite imp.
    destruct (g a); simpl; tcsp.
    rewrite IHl; auto.
  Qed.

  Lemma raise_to_n_proc_incr_n_proc :
    forall cn i j (a : n_proc j cn),
      j < i
      -> raise_to_n_proc i (incr_n_proc a)
         = raise_to_n_proc i a.
  Proof.
    induction i; introv lti; simpl in *; tcsp;[].
    destruct (deq_nat j i); subst; simpl in *; tcsp.

    { destruct (deq_nat i (S i)); subst; try omega; auto.
      autorewrite with comp; simpl; auto. }

    destruct (deq_nat j (S i)); subst; try omega.
    rewrite IHi; try omega; auto.
  Qed.

  Lemma option_map_None :
    forall {A B} (f : A -> B) o,
      option_map f o = None -> o = None.
  Proof.
    destruct o; simpl in *; tcsp.
  Qed.

  Lemma raise_to_n_nproc_idem :
    forall i j k (a : n_nproc k),
      k <= j <= i
      -> map_option (raise_to_n_nproc i) (raise_to_n_nproc j a)
         = raise_to_n_nproc i a.
  Proof.
    introv lei.
    destruct a as [cn a]; simpl.
    rewrite map_option_option_map.
    revert i k a lei.
    induction j; introv lei; simpl in *.

    { assert (k = 0) by omega; subst; simpl in *; tcsp. }

    destruct (deq_nat k (S j)); subst; tcsp;[].
    rewrite map_option_option_map.
    unfold compose in *.

    destruct i; simpl in *; tcsp; try omega.
    destruct (deq_nat j i); subst; simpl in *; tcsp.

    { destruct (deq_nat k (S i)); subst; simpl in *; tcsp;[].
      unfold map_option; simpl.
      remember (raise_to_n_proc i a) as w; symmetry in Heqw.
      destruct w; simpl; auto. }

    destruct (deq_nat k (S i)); subst; simpl in *; tcsp; try omega;[].
    rewrite option_map_option_map.
    pose proof (IHj i k a) as IHj.
    autodimp IHj hyp; try omega.
    remember (raise_to_n_proc i a) as w; symmetry in Heqw.
    destruct w; simpl in *; tcsp.

    { apply map_option_Some in IHj; exrepnd.
      symmetry in IHj0.
      apply option_map_Some in IHj0; exrepnd; ginv.
      inversion IHj2.
      match goal with
      | [ H : context[a1] |- _ ] => rename H into h1
      end.
      apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp; GC.
      allrw; simpl.
      rewrite option_map_option_map.
      rewrite raise_to_n_proc_incr_n_proc; try omega.
      allrw; simpl; auto. }

    remember (raise_to_n_proc j a) as z; symmetry in Heqz.
    destruct z; simpl in *; ginv;[].
    apply option_map_None in IHj.
    rewrite raise_to_n_proc_incr_n_proc; try omega.
    allrw; simpl; auto.
  Qed.

  Lemma raise_to_n_procs_idem :
    forall i j k (subs : n_procs k),
      k <= j <= i
      -> raise_to_n_procs i (raise_to_n_procs j subs)
         = raise_to_n_procs i subs.
  Proof.
    introv lei.
    unfold raise_to_n_procs.
    rewrite mapOption_idem.
    apply eq_mapOptions; introv.
    unfold op_compose.
    apply raise_to_n_nproc_idem; auto.
  Qed.

  Lemma implies_is_proc_n_proc_update_state_m :
    forall n cn (p : n_proc n cn) s,
      is_proc_n_proc p
      -> is_proc_n_proc (update_state_m p s).
  Proof.
    introv i.
    unfold is_proc_n_proc in *; exrepnd.
    exists p0.
    introv.
    pose proof (i0 s0 i) as i0.
    induction n; simpl in *; tcsp; destruct p as [p|p]; tcsp.
  Qed.
  Hint Resolve implies_is_proc_n_proc_update_state_m : comp.

  Lemma in_replace_name_update_state_m_implies_is_proc_n_proc :
    forall n cn (subs : n_procs n) (p : n_proc n cn) s q,
      are_procs_n_procs subs
      -> is_proc_n_proc p
      -> In q (replace_name (update_state_m p s) subs)
      -> is_proc_n_nproc q.
  Proof.
    induction subs; introv aps ips j; simpl in *; tcsp.
    allrw are_procs_n_procs_cons; repnd.
    destruct a as [c a].
    destruct (CompNameDeq c cn); subst; simpl in *;
      repndors; subst; simpl in *; tcsp; eauto 3 with comp.
  Qed.
  Hint Resolve in_replace_name_update_state_m_implies_is_proc_n_proc : comp.

  Lemma raise_to_n_proc_preserves_is_proc_n_proc :
    forall cn n k (a : n_proc k cn) p,
      raise_to_n_proc n a = Some p
      -> is_proc_n_proc a
      -> is_proc_n_proc p.
  Proof.
    induction n; introv e j; simpl in *; tcsp.
    destruct (deq_nat k (S n)); subst; simpl in *; ginv; tcsp.
    apply option_map_Some in e; exrepnd; subst; simpl in *.
    apply IHn in e1; auto.
  Qed.
  Hint Resolve raise_to_n_proc_preserves_is_proc_n_proc : comp.

  Lemma raise_to_n_nproc_preserves_is_proc_n_nproc :
    forall n k (a : n_nproc k) p,
      raise_to_n_nproc n a = Some p
      -> is_proc_n_nproc a
      -> is_proc_n_nproc p.
  Proof.
    introv e j.
    destruct a as [c a]; simpl in *.
    apply option_map_Some in e; exrepnd; subst; simpl in *; eauto 3 with comp.
  Qed.
  Hint Resolve raise_to_n_nproc_preserves_is_proc_n_nproc : comp.

  Lemma raise_to_n_procs_preserves_proc :
    forall n k (subs : n_procs k) p,
      In p (raise_to_n_procs n subs)
      -> are_procs_n_procs subs
      -> is_proc_n_nproc p.
  Proof.
    introv j aps.
    apply in_mapOption in j; exrepnd.
    apply aps in j1; clear aps; eauto 3 with comp.
  Qed.
  Hint Resolve raise_to_n_procs_preserves_proc : comp.

  Lemma are_procs_n_procs_fst_interp_proc :
    forall {n} {A} (subs : n_procs n) (p : Proc A),
      are_procs_n_procs subs
      -> are_procs_n_procs (fst (interp_proc p subs)).
  Proof.
    induction n as [? ind] using comp_ind; introv aps i;[].

    revert subs aps p0 i.
    induction p as [| |]; introv aps j; simpl in *; autorewrite with comp; eauto 3 with comp.

    { unfold bind in j.
      split_pairs.
      simpl in *.
      apply H in j; auto.
      introv k.
      apply IHp in k; auto. }

    { unfold call_proc in j.
      remember (find_name cn subs) as fn; symmetry in Heqfn.
      destruct fn; simpl in *; tcsp;[].
      rename n0 into p.
      remember (app_m_proc p i (decr_n_procs subs)) as ap; symmetry in Heqap; repnd.
      simpl in *.
      rewrite (app_m_proc_some2 p i) in Heqap.
      remember (sm2update p (sm2state p) i (select_n_procs (sm2level p) (decr_n_procs subs))) as w; symmetry in Heqw.
      repnd; simpl in *.

      pose proof (are_procs_n_procs_find_name _ n subs p) as isp.
      repeat (autodimp isp hyp).

      pose proof (sm2level_le_pred _ _ p) as ln0.

      applydup is_proc_n_proc_update_implies_some in Heqw; auto;[]; exrepnd; subst; simpl in *.
      dup isp as isp'.
      unfold is_proc_n_proc in isp; exrepnd.
      rewrite isp0 in Heqw.
      unfold proc2upd in Heqw; simpl in *.
      unfold interp_s_proc, to_proc_some_state in Heqw; simpl in *.
      unfold bind_pair, bind in Heqw; simpl in *.
      remember (interp_proc (p1 (sm2state p) i) (select_n_procs (sm2level p) (decr_n_procs subs))) as itr; symmetry in Heqitr.
      repnd; simpl in *; ginv.

      pose proof (ind (sm2level p)) as ind.
      autodimp ind hyp; try (complete (destruct n; simpl in *; tcsp; try omega));[].
      pose proof (ind _ (select_n_procs (sm2level p) (decr_n_procs subs)) (p1 (sm2state p) i)) as ind.
      rewrite Heqitr in ind; simpl in *.
      autodimp ind hyp; eauto 3 with comp;[].

      applydup @in_replace_subs_implies in j.
      rewrite raise_to_n_procs_idem in j0; try omega.

      repndors; eauto 3 with comp. }
  Qed.
  Hint Resolve are_procs_n_procs_fst_interp_proc : comp.

  Lemma wf_procs_replace_subs :
    forall n l (subs : n_procs n),
      wf_procs subs
      -> wf_procs (replace_subs subs l).
  Proof.
    induction l; introv wf; simpl in *; auto.
    destruct a as [c a]; simpl in *.
    apply IHl; clear IHl; eauto 3 with comp.
  Qed.
  Hint Resolve wf_procs_replace_subs : comp.

  Lemma wf_procs_replace_name_implies :
    forall cn n (subs : n_procs n) (p : n_proc n cn),
      procs_names (replace_name p subs) = procs_names subs.
  Proof.
    induction subs; introv; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq c cn); subst; simpl in *; tcsp.
    rewrite IHsubs; auto.
  Qed.
  Hint Rewrite wf_procs_replace_name_implies : comp.

  Lemma wf_procs_fst_interp_proc :
    forall {n} {A} (subs : n_procs n) (p : Proc A),
      wf_procs subs
      -> wf_procs (fst (interp_proc p subs)).
  Proof.
    induction n as [? ind] using comp_ind.

    introv.
    revert subs.
    induction p as [| |]; introv wf; simpl in *; autorewrite with comp; eauto 3 with comp.

    { unfold bind.
      split_pairs; simpl in *.
      apply IHp in wf; tcsp. }

    { unfold call_proc.
      remember (find_name cn subs) as fn; symmetry in Heqfn.
      destruct fn; simpl in *; tcsp;[].
      rename n0 into p.
      remember (app_m_proc p i (decr_n_procs subs)) as ap; symmetry in Heqap; repnd.
      rewrite (app_m_proc_some2 p i) in Heqap.
      remember (sm2update p (sm2state p) i (select_n_procs (sm2level p) (decr_n_procs subs))) as w; symmetry in Heqw.
      repnd; simpl in *; eauto 3 with comp. }
  Qed.
  Hint Resolve wf_procs_fst_interp_proc : comp.

  Definition update_state_op_m
             {n} {cn}
             (sm  : n_proc n cn)
             (sop : option (sf cn)) : n_proc n cn :=
    match sop with
    | Some s => update_state_m sm s
    | None => sm
    end.

  Fixpoint run_sm_on_inputs {n} {cn}
           (p : n_proc n cn)
           (l : list (cio_I (fio cn)))
           (subs : n_procs n) : n_procs n * n_proc n cn :=
    match l with
    | [] => (subs, p)
    | i :: l =>
      match sm2update p (sm2state p) i (select_n_procs (sm2level p) subs) with
      | (subs', (sop, o)) =>
        run_sm_on_inputs
          (update_state_op_m p sop)
          l
          (raise_to_n_procs n subs')
      end
    end.

  (*
    - In combination with this one, we also have to assume wf_subs
      to ensure no duplicates

    - This is not quite right because other components can also
      interact with the sub-components in the middle of the computation,
      while this definition assumes that other sub-components don't change
      the sub-components from one input to another.

    - Therefore, we require that ([sm2level sm = 0]) so that [sm] cannot use
      sub-components.  Otherwise, other components might modify those
      sub-components, and we would have to take that into account in the
      computation for [sm].

    - Another alternative would be to require in [run_sm_on_inputs] to take
      those changes in the subcomponents as parameter.  This is left for later.
   *)
  Definition run_subs_leaves {n} (subs1 subs2 : n_procs n) : Prop :=
    forall cn (p : n_proc n cn),
      sm2level p = 0
      -> In (MkPProc cn p) subs1
      ->
      exists (l : list (cio_I (fio cn))),
        In (MkPProc cn (snd (run_sm_on_inputs p l subs1))) subs2.

  Lemma run_subs_leaves_refl :
    forall {n} (subs : n_procs n),
      run_subs_leaves subs subs.
  Proof.
    introv lvl i.
    exists ([] : list (cio_I (fio cn))); simpl; auto.
  Qed.
  Hint Resolve run_subs_leaves_refl : comp.

  Definition ls_run_subs {L S} (ls : LocalSystem L S) :=
    forall s i,
      run_subs_leaves (ls_subs ls) (fst (sm_update (ls_main ls) s i (ls_subs ls))).

  Lemma run_sm_on_inputs_app :
    forall {n} {cn : CompName}
           (l1 l2 : list (cio_I (fio cn)))
           (p     : n_proc n cn)
           (subs  : n_procs n),
      run_sm_on_inputs p (l1 ++ l2) subs
      = let (subs',q) := run_sm_on_inputs p l1 subs
        in run_sm_on_inputs q l2 subs'.
  Proof.
    induction l1; introv; simpl; auto.
    remember (sm2update p (sm2state p) a (select_n_procs (sm2level p) subs)) as w; symmetry in Heqw.
    repnd.
    destruct w1; simpl; auto.
  Qed.

  Lemma sm2level_update_state_m :
    forall cn n (p : n_proc n cn) s,
      sm2level (update_state_m p s) = sm2level p.
  Proof.
    induction n; introv; simpl in *; tcsp; destruct p as [p|p]; tcsp.
  Qed.
  Hint Rewrite sm2level_update_state_m : comp.

  Lemma sm2level_update_state_op_m :
    forall cn n (p : n_proc n cn) sop,
      sm2level (update_state_op_m p sop) = sm2level p.
  Proof.
    destruct sop; introv; simpl; autorewrite with comp; auto.
  Qed.
  Hint Rewrite sm2level_update_state_op_m : comp.

  Lemma run_sm_on_inputs_preserves_sm2level :
    forall n cn l (p : n_proc n cn) subs,
      sm2level (snd (run_sm_on_inputs p l subs)) = sm2level p.
  Proof.
    induction l; introv; simpl; auto.
    split_pairs; simpl.
    rewrite IHl; auto; autorewrite with comp; auto.
  Qed.
  Hint Rewrite run_sm_on_inputs_preserves_sm2level : comp.

  Lemma select_n_proc_0 :
    forall cn n (a : n_proc n cn),
      select_n_proc 0 a = None.
  Proof.
    induction n; introv; simpl in *; tcsp; destruct a as [a|a]; tcsp.
  Qed.
  Hint Rewrite select_n_proc_0 : comp.

  Lemma select_n_procs_0 :
    forall n (subs : n_procs n),
      select_n_procs 0 subs = [].
  Proof.
    induction subs; simpl; auto.
    rewrite select_n_procs_cons; rewrite IHsubs.
    destruct a as [c a]; simpl; autorewrite with comp; simpl; auto.
  Qed.
  Hint Rewrite select_n_procs_0 : comp.

  Lemma select_n_procs_nil_if_leaf :
    forall cn n (p : n_proc n cn) m (subs : n_procs m),
      sm2level p = 0
      -> select_n_procs (sm2level p) subs = [].
  Proof.
    introv h; rewrite h; simpl; autorewrite with comp; auto.
  Qed.

  Lemma eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf :
    forall {cn} {n} l (p : n_proc n cn) subs1 subs2,
      sm2level p = 0
      -> snd (run_sm_on_inputs p l subs1)
         = snd (run_sm_on_inputs p l subs2).
  Proof.
    induction l; introv lvl; simpl in *; auto.
    repeat (rewrite select_n_procs_nil_if_leaf; auto).
  Qed.

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

  Lemma find_name_in_implies_eq :
    forall cn n (subs : n_procs n) p q,
      find_name cn subs = Some p
      -> In (MkPProc cn q) subs
      -> wf_procs subs
      -> p = q.
  Proof.
    induction subs; introv fn i wf; simpl in *; tcsp.
    allrw wf_procs_cons; repnd.
    repndors; subst; simpl in *; tcsp.

    { destruct (CompNameDeq cn cn); tcsp; ginv.
      pose proof (UIP_refl_CompName _ e) as w; subst; simpl in *; ginv; auto. }

    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq c cn); simpl in *; ginv; simpl; tcsp;[].
    apply in_implies_in_proc_names in i; simpl in *; tcsp.
  Qed.

  Lemma are_procs_n_procs_nil :
    forall n, are_procs_n_procs ([] : n_procs n).
  Proof.
    introv i; simpl in *; tcsp.
  Qed.
  Hint Resolve are_procs_n_procs_nil : comp.

  Lemma wf_procs_nil :
    forall n, wf_procs ([] : n_procs n).
  Proof.
    tcsp.
  Qed.
  Hint Resolve wf_procs_nil : comp.

  Lemma implies_in_replace_name :
    forall cn n (subs : n_procs n) p,
      In cn (procs_names subs)
      -> In (MkPProc cn p) (replace_name p subs).
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq c cn); tcsp.
  Qed.
  Hint Resolve implies_in_replace_name : comp.

  Lemma select_n_procs_decr_n_procs :
    forall n j (subs : n_procs n),
      j <= pred n
      -> select_n_procs j (decr_n_procs subs)
         = select_n_procs j subs.
  Proof.
    introv len.
    rewrite decr_n_procs_as_select_n_procs_pred.
    rewrite select_n_procs_select_n_procs_le; auto; try omega.
  Qed.

  Lemma select_n_nproc_preserves_is_proc_n_nproc :
    forall n k (a : n_nproc n) b,
      select_n_nproc k a = Some b
      -> is_proc_n_nproc a
      -> is_proc_n_nproc b.
  Proof.
    introv sel isp.
    destruct a as [cn a].
    simpl in *.
    unfold is_proc_n_proc in *; exrepnd.
    apply option_map_Some in sel; exrepnd; subst; simpl in *.
    unfold is_proc_n_proc; exists p; introv.
    pose proof (isp0 s i) as isp0.
    eapply select_n_proc_preserves_sm2update_eq_proc2upd in sel1; eauto.
  Qed.
  Hint Resolve select_n_nproc_preserves_is_proc_n_nproc : comp.

  Lemma select_n_procs_preserves_are_procs_n_procs :
    forall n k (subs : n_procs n),
      are_procs_n_procs subs
      -> are_procs_n_procs (select_n_procs k subs).
  Proof.
    induction subs; introv aps; simpl in *; tcsp.
    { introv i; simpl in *; tcsp. }
    allrw are_procs_n_procs_cons; repnd.
    rewrite select_n_procs_cons.
    remember (select_n_nproc k a) as q; symmetry in Heqq.
    destruct q; simpl; tcsp;[].
    allrw are_procs_n_procs_cons.
    dands; tcsp; eauto 3 with comp.
  Qed.
  Hint Resolve select_n_procs_preserves_are_procs_n_procs : comp.

  Lemma select_n_procs_level_lt_implies_some :
    forall cn n j (p : n_proc n cn),
      sm2level p < j
      -> j <= n
      -> exists q, select_n_proc j p = Some q.
  Proof.
    induction n; introv ltj len; simpl in *; tcsp.
    destruct j; simpl in *; tcsp.
    destruct p as [p|p]; simpl in *; tcsp.

    { destruct (deq_nat n j); subst; try omega; simpl in *; tcsp; eauto. }

    destruct (deq_nat n j); subst; simpl in *; try omega; tcsp; eauto.
    pose proof (IHn (S j) p) as IHn.
    repeat (autodimp IHn hyp); try omega.
  Qed.

  Lemma implies_in_proc_names_select_n_procs :
    forall cn n (p : n_proc n cn) j subs,
      j <= n
      -> sm2level p < j
      -> In (MkPProc cn p) subs
      -> In cn (procs_names (select_n_procs j subs)).
  Proof.
    induction subs; introv len lvl i; simpl in *; tcsp.
    rewrite select_n_procs_cons in *.
    repndors; subst; simpl in *; tcsp; dest_cases w; symmetry in Heqw.

    { apply option_map_Some in Heqw; exrepnd; subst; simpl in *; tcsp. }

    { apply option_map_None in Heqw.
      pose proof (select_n_procs_level_lt_implies_some cn n j p) as z.
      repeat (autodimp z hyp); exrepnd.
      rewrite z0 in Heqw; ginv. }
  Qed.

  Lemma lt_level_implies_in_select_n_procs :
    forall cn n j (p : n_proc n cn) (subs : n_procs n) q,
      j <= n
      -> sm2level p < j
      -> In (MkPProc cn p) subs
      -> In cn (procs_names (select_n_procs j subs))
      -> select_n_proc j p = Some q
      -> In (MkPProc cn q) (select_n_procs j subs).
  Proof.
    induction subs; introv len lvl ins inn sel; simpl in *; tcsp.
    rewrite select_n_procs_cons in *.
    repndors; subst; simpl in *; tcsp.

    { dest_cases w; simpl in *; tcsp; symmetry in Heqw; repndors; subst; tcsp.

      { destruct w as [c w]; simpl in *.
        apply option_map_Some in Heqw; exrepnd; subst; simpl in *.
        inversion Heqw0; subst.
        match goal with
        | [ H : context[a] |- _ ] => rename H into h1
        end.
        apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp; GC.
        rewrite Heqw1 in sel; ginv. }

      { destruct w as [c w]; simpl in *.
        apply option_map_Some in Heqw; exrepnd; subst; simpl in *.
        inversion Heqw0; subst.
        match goal with
        | [ H : context[a] |- _ ] => rename H into h1
        end.
        apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp; GC.
        rewrite Heqw1 in sel; ginv. }

      { apply option_map_None in Heqw.
        rewrite Heqw in sel; ginv. } }

    { dest_cases w; symmetry in Heqw; simpl in *.
      destruct w as [c w]; simpl in *.
      repndors; subst; tcsp.
      apply IHsubs in sel; auto.
      eapply implies_in_proc_names_select_n_procs; eauto. }
  Qed.

  Lemma select_n_proc_S_incr_implies_level :
    forall cn n j (p : n_proc n cn) (q : n_proc_at j cn),
      select_n_proc (S j) p = Some (sm_or_at q)
      -> sm2level p = j.
  Proof.
    induction n; introv sel; simpl in *; tcsp.
    destruct (deq_nat n j); subst; simpl in *; tcsp; ginv.
    { inversion sel; subst; simpl in *; auto. }
    destruct p as [p|p]; ginv; tcsp.
    eapply IHn; eauto.
  Qed.
  Hint Resolve select_n_proc_S_incr_implies_level : comp.

  Lemma select_n_proc_preserves_sm2level :
    forall cn n j (p : n_proc n cn) q,
      select_n_proc j p = Some q
      -> sm2level p = sm2level q.
  Proof.
    induction n; introv sel; simpl in *; tcsp;[].
    destruct j; simpl in *; tcsp;[].
    destruct (deq_nat n j); subst; simpl in *; tcsp; ginv; auto;[].
    destruct p as [p|p], q as [q|q]; simpl in *; tcsp; eauto 3 with comp;[].
    apply select_n_proc_S_sm_implies in sel; tcsp.
  Qed.

  Lemma implies_in_replace_sub_left :
    forall c n (a : n_proc (pred n) c) (subs : n_procs n) (p : n_nproc n),
      In p subs
      -> c <> pp_name p
      -> In p (replace_sub subs a).
  Proof.
    induction subs; introv i d; simpl in *; tcsp.
    destruct a0 as [cn a0].
    destruct (CompNameDeq c cn); subst; simpl in *; tcsp.
    repndors; subst; simpl in *; tcsp.
  Qed.
  Hint Resolve implies_in_replace_sub_left : comp.

  Lemma implies_in_replace_subs_left :
    forall n (l : n_procs (pred n)) (subs : n_procs n) (p : n_nproc n),
      In p subs
      -> ~In (pp_name p) (procs_names l)
      -> In p (replace_subs subs l).
  Proof.
    induction l; introv i ni; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    apply not_or in ni; repnd.
    apply IHl; auto; eauto 3 with comp.
  Qed.
  Hint Resolve implies_in_replace_subs_left : comp.

  Lemma implies_in_replace_subs_right :
    forall n (l : n_procs (pred n)) (subs : n_procs n) (p : n_nproc n),
      wf_procs l
      -> In p (incr_pred_n_procs l)
      -> In (pp_name p) (procs_names subs)
      -> In p (replace_subs subs l).
  Proof.
    induction l; introv wf i j; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    allrw wf_procs_cons; repnd; simpl in *.
    repndors; subst; simpl in *; tcsp; eauto 3 with comp.

    { apply implies_in_replace_subs_left; simpl; auto; eauto 3 with comp.
      apply (in_replace_sub_if_in_names n (MkPProc c a) subs); simpl; auto. }

    { apply IHl; auto; autorewrite with comp; auto. }
  Qed.
  Hint Resolve implies_in_replace_subs_right : comp.

  Lemma implies_in_raise_to_n_procs :
    forall j n (p : n_nproc j) (subs : n_procs n),
      n <= j
      -> (In p (raise_to_n_procs j subs)
          <-> exists (q : n_nproc n), raise_to_n_nproc j q = Some p /\ In q subs).
  Proof.
    induction subs; introv lej; simpl in *; split; intro h; tcsp.

    { rewrite raise_to_n_procs_cons in *.
      remember (raise_to_n_nproc j a) as r; symmetry in Heqr.
      destruct r; simpl in *; tcsp; repndors; subst; tcsp; eauto;
        apply IHsubs in h; auto; exrepnd; eauto. }

    { exrepnd.
      allrw raise_to_n_procs_cons.
      remember (raise_to_n_nproc j a) as r; symmetry in Heqr.
      destruct r; simpl in *; repndors; subst; tcsp;
        try (rewrite IHsubs;[|auto];[]); eauto;
          rewrite h1 in Heqr; ginv. }
  Qed.

  Lemma raise_to_n_proc_as_select_n_proc :
    forall cn j n (p : n_proc n cn) (q : n_proc j cn) (len : j <= n),
      select_n_proc j p = Some q
      <-> raise_to_n_proc n q = Some p.
  Proof.
    induction n; introv len; simpl in *; tcsp;[].
    destruct j; simpl in *; tcsp;[].
    destruct (deq_nat j n); subst; tcsp.

    { destruct (deq_nat n n); tcsp; simpl in *.
      pose proof (UIP_refl_nat _ e) as w; subst; simpl in *; ginv; tcsp.
      split; intro h; ginv. }

    { destruct (deq_nat n j); subst; simpl in *; tcsp.
      destruct p as [p|p]; simpl in *; split; intro h; ginv.

      { apply option_map_Some in h; exrepnd; ginv. }

      { apply option_map_Some.
        eexists; dands; [|reflexivity].
        apply IHn; auto; try omega. }

      { apply option_map_Some in h; exrepnd; ginv.
        inversion h0; subst; clear h0.
        apply IHn in h1; auto; try omega. } }
  Qed.

  Lemma select_n_proc_preserves_sm2update :
    forall cn n k (a : n_proc n cn) b s i (subs : n_procs n),
      k <= n
      -> select_n_proc k a = Some b
      -> sm2update b s i (select_n_procs (sm2level b) subs)
         = match sm2update a s i (select_n_procs (sm2level a) subs) with
           | (subs', o) => (select_n_procs (sm2level b) subs', o)
           end.
  Proof.
    induction n; introv len sel; simpl in *; tcsp;[].
    destruct k.

    { destruct a; simpl in *; tcsp. }

    destruct (deq_nat n k); subst; simpl in *; tcsp; ginv;[|].

    { destruct b as [b|b];[|]; simpl in *; tcsp;
        split_pairs; simpl;
          autorewrite with comp; auto. }

    destruct a as [a|a], b as [b|b]; simpl in *; ginv.

    { applydup select_n_proc_S_incr_implies_level in sel; subst.
      split_pairs.
      autorewrite with comp.
      pose proof (IHn (S (sm2level a)) a (sm_or_at b) s i (decr_n_procs subs)) as IHn.
      repeat (autodimp IHn hyp); try omega.
      simpl in *.
      pose proof (select_n_procs_decr_n_procs (S n) (sm2level a) subs) as q; simpl in *.
      rewrite q in IHn; try omega; clear q;[].
      rewrite IHn.
      split_pairs; simpl; autorewrite with comp; auto. }

    { apply select_n_proc_S_sm_implies in sel.
      pose proof (IHn k a b s i (decr_n_procs subs)) as IHn; simpl in *.
      repeat (autodimp IHn hyp); try omega.
      applydup select_n_proc_preserves_sm2level in sel.
      pose proof (sm2level_le_pred _ _ a) as lvl.
      pose proof (select_n_procs_decr_n_procs (S n) (sm2level b) subs) as q; simpl in *.
      rewrite q in IHn; try omega; clear q.
      rewrite IHn; clear IHn.
      pose proof (select_n_procs_decr_n_procs (S n) (sm2level a) subs) as q; simpl in *.
      rewrite q; try omega; clear q; auto. }
  Qed.

  Lemma select_n_proc_preserves_sm2state :
    forall cn n j (p : n_proc n cn) q,
      select_n_proc j p = Some q
      -> sm2state p = sm2state q.
  Proof.
    induction n; introv sel; simpl in *; tcsp;[].
    destruct j; simpl in *; tcsp;[].
    destruct (deq_nat n j); subst; simpl in *; tcsp; ginv; auto;[].
    destruct p as [p|p], q as [q|q]; simpl in *; tcsp; eauto 3 with comp.
    { apply (IHn (S j) p (sm_or_at q)) in sel; simpl in *; auto. }
    { apply select_n_proc_S_sm_implies in sel; tcsp. }
  Qed.

  Lemma raise_to_n_proc_some_select_n_proc_some_back_implies :
    forall cn i j (a : n_proc j cn) b c,
      j <= i
      -> raise_to_n_proc i a = Some b
      -> select_n_proc j b = Some c
      -> a = c.
  Proof.
    induction i; introv lenn sel rais; simpl in *; destruct j; simpl in *; tcsp.

    destruct (deq_nat j i); subst; simpl in *.

    { destruct (deq_nat i i); subst; simpl in *; ginv.
      pose proof (UIP_refl_nat _ e) as w; subst; simpl in *; ginv; tcsp. }

    destruct (deq_nat i j); subst; simpl in *; ginv.
    apply option_map_Some in sel; exrepnd; subst; simpl in *.
    eapply IHi in sel1; eauto; try omega.
  Qed.

  Lemma raise_to_n_proc_some_select_n_proc_some_implies :
    forall cn i j n (a : n_proc n cn) b c,
      n <= j <= i
      -> raise_to_n_proc i a = Some b
      -> select_n_proc j b = Some c
      -> raise_to_n_proc j a = Some c.
  Proof.
    induction i; introv len rais sel; simpl in *; tcsp;[].
    destruct j; simpl in *; tcsp;[].
    destruct (deq_nat n (S i)); subst; simpl in *; tcsp; try omega; ginv.

    { destruct (deq_nat i j); subst; simpl in *; ginv; tcsp; try omega. }

    apply option_map_Some in rais; exrepnd; subst; simpl in *.
    destruct (deq_nat i j); subst; simpl in *; ginv; tcsp; try omega;
      destruct (deq_nat n (S j)); subst; simpl in *; ginv; tcsp; try omega;
        allrw; simpl; auto.

    { eapply raise_to_n_proc_some_select_n_proc_some_back_implies in rais1; eauto; try omega.
      subst; auto. }

    pose proof (IHi (S j) n a a0 c) as IHi.
    repeat (autodimp IHi hyp); try omega.
    simpl in *.
    destruct (deq_nat n (S j)); subst; simpl in *; try omega; tcsp.
  Qed.

  Lemma raise_to_n_nproc_some_select_n_nproc_some_implies :
    forall n i j (a : n_nproc n) b c,
      n <= j <= i
      -> raise_to_n_nproc i a = Some b
      -> select_n_nproc j b = Some c
      -> raise_to_n_nproc j a = Some c.
  Proof.
    introv lenn sel rais.
    destruct a as [cna a]; simpl in *.
    apply option_map_Some in sel; exrepnd; subst; simpl in *.
    apply option_map_Some in rais; exrepnd; subst; simpl in *.
    pose proof (raise_to_n_proc_some_select_n_proc_some_implies cna i j n a a0 a1) as w.
    repeat (autodimp w hyp).
    rewrite w; simpl; auto.
  Qed.

  Lemma raise_to_n_proc_preserves_sm2level :
    forall cn n j (p : n_proc n cn) q,
      raise_to_n_proc j p = Some q
      -> sm2level p = sm2level q.
  Proof.
    induction j; introv sel; simpl in *; tcsp;[].
    destruct (deq_nat n (S j)); subst; simpl in *; try omega; tcsp; ginv.

    { destruct q; simpl; auto. }

    apply option_map_Some in sel; exrepnd; subst; simpl in *.
    apply IHj in sel1; auto.
  Qed.

  Lemma raise_to_n_nproc_preserves_sm2level :
    forall n j (p : n_nproc n) q,
      raise_to_n_nproc j p = Some q
      -> sm2level (pp_proc p) = sm2level (pp_proc q).
  Proof.
    introv rais.
    destruct p as [c p]; simpl in *.
    apply option_map_Some in rais; exrepnd; subst; simpl in *.
    eapply raise_to_n_proc_preserves_sm2level; eauto.
  Qed.

  Lemma raise_to_n_procs_select_n_procs :
    forall n i j (subs : n_procs n),
      n <= j <= i
      -> select_n_procs j (raise_to_n_procs i subs)
         = raise_to_n_procs j subs.
  Proof.
    induction subs; introv len; simpl in *; tcsp.
    autodimp IHsubs hyp;[].
    allrw select_n_procs_cons.
    allrw raise_to_n_procs_cons.

    remember (raise_to_n_nproc i a) as rais; symmetry in Heqrais.
    destruct rais; simpl; allrw select_n_procs_cons.

    { remember (select_n_nproc j n0) as sel; symmetry in Heqsel.
      destruct sel; simpl in *; rewrite IHsubs; clear IHsubs.

      { eapply raise_to_n_nproc_some_select_n_nproc_some_implies in Heqrais; eauto.
        allrw; auto. }

      { applydup select_n_nproc_implies_lt in Heqsel; try omega.
        applydup raise_to_n_nproc_preserves_sm2level in Heqrais.
        pose proof (sm2level_le_pred _ _ (pp_proc n0)) as lvl1.
        pose proof (sm2level_le_pred _ _ (pp_proc a)) as lvl2.
        assert (j = sm2level (pp_proc n0)) as xx by omega; subst.
        assert (n = sm2level (pp_proc n0)) as xx by omega; subst.
        assert (sm2level (pp_proc a) = 0) as xx by omega.
        rewrite xx in *.
        rewrite <- Heqrais0 in *; simpl in *.
        revert a Heqrais xx subs.
        rewrite <- Heqrais0; simpl.
        introv rais xx; destruct a; simpl in *; tcsp. } }

    { applydup raise_to_n_nproc_none_implies in Heqrais; try omega. }
  Qed.

  Lemma implies_select_n_proc_update_state_m :
    forall cn n j (p : n_proc n cn) (q : n_proc j cn) w,
      j <= n
      -> select_n_proc j p = Some q
      -> select_n_proc j (update_state_m p w) = Some (update_state_m q w).
  Proof.
    induction n; introv len sel; simpl in *; tcsp;[].
    destruct j; simpl in *; try omega; tcsp;[].
    destruct (deq_nat n j); subst; simpl in *; tcsp; try omega; ginv; auto;[].
    destruct p as [p|p]; ginv.

    pose proof (IHn (S j) p q w) as IHn.
    repeat (autodimp IHn hyp); tcsp; try omega.
  Qed.
  Hint Resolve implies_select_n_proc_update_state_m : comp.

  Lemma implies_select_n_proc_update_state_op_m :
    forall cn n j (p : n_proc n cn) (q : n_proc j cn) w,
      j <= n
      -> select_n_proc j p = Some q
      -> select_n_proc j (update_state_op_m p w) = Some (update_state_op_m q w).
  Proof.
    introv len sel.
    destruct w; simpl; tcsp; eauto 3 with comp.
  Qed.
  Hint Resolve implies_select_n_proc_update_state_op_m : comp.

  Lemma select_n_proc_fst_run_sm_in_inputs :
    forall (cn : CompName) n j
           (l : list (cio_I (fio cn)))
           (p : n_proc n cn)
           (q : n_proc j cn)
           (subs : n_procs n),
      j <= n
      -> select_n_proc j p = Some q
      -> select_n_proc j (snd (run_sm_on_inputs p l subs))
         = Some (snd (run_sm_on_inputs q l (select_n_procs j subs))).
  Proof.
    induction l; introv len sel; simpl in *; auto;[].
    split_pairs; simpl.

    applydup select_n_proc_preserves_sm2level in sel.
    applydup select_n_proc_preserves_sm2state in sel.
    pose proof (sm2level_le_pred _ _ q) as lvl.
    rewrite select_n_procs_select_n_procs_le; try omega;[].

    destruct (deq_nat j 0) as [d|d];[subst; simpl in *; tcsp|];[].

    pose proof (select_n_proc_preserves_sm2update cn n j p q (sm2state q) a subs) as w.
    repeat (autodimp w hyp).
    simpl in *.
    rewrite w; clear w.
    split_pairs; simpl.
    rewrite <- sel1.

    remember (fst (snd (sm2update p (sm2state p) a (select_n_procs (sm2level p) subs)))) as w; symmetry in Heqw.
    simpl in *; rewrite Heqw.

    pose proof (IHl
                  (update_state_op_m p w)
                  (update_state_op_m q w)
                  (raise_to_n_procs n (fst (sm2update p (sm2state p) a (select_n_procs (sm2level p) subs)))))
      as IHl.
    simpl in *.
    rewrite IHl; clear IHl; auto; eauto 3 with comp;[].
    remember (fst (sm2update p (sm2state p) a (select_n_procs (sm2level p) subs))) as subs'; symmetry in Heqsubs'.
    simpl in *; rewrite Heqsubs'.
    rewrite <- sel0.
    autorewrite with comp.
    rewrite raise_to_n_procs_select_n_procs; try omega; auto.
  Qed.

  Lemma in_replace_name_right :
    forall cn n (p : n_nproc n) (subs : n_procs n) (q : n_proc n cn),
      cn <> pp_name p
      -> In p subs
      -> In p (replace_name q subs).
  Proof.
    induction subs; introv d i; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    repndors; subst; simpl in *; tcsp;
      destruct (CompNameDeq c cn); subst; simpl in *; tcsp.
  Qed.

  Lemma interp_proc_run_subs_leaves :
    forall {A} (p : Proc A) {n} (subs : n_procs n),
      (forall (m    : nat)
              (cn   : CompName)
              (main : n_proc_at m cn)
              (s    : sf cn)
              (i    : cio_I (fio cn))
              (subs : n_procs m),
          m < n
          -> is_proc_n_proc_at main
          -> are_procs_n_procs subs
          -> wf_procs subs
          -> run_subs_leaves subs (fst (sm_update main s i subs)))
      -> are_procs_n_procs subs
      -> wf_procs subs
      -> run_subs_leaves subs (fst (interp_proc p subs)).
  Proof.
    induction p as [| |]; introv imp wf aps; simpl in *; autorewrite with comp in *; eauto 3 with comp.

    { unfold bind.
      split_pairs; simpl in *.
      introv lvl i; simpl in *.
      applydup IHp in i; auto;[].
      exrepnd.
      dup i1 as i2.
      apply (H (snd (interp_proc p subs))) in i2; eauto; autorewrite with comp; eauto 3 with comp;[].
      exrepnd.
      exists (l ++ l0).
      rewrite run_sm_on_inputs_app; simpl.
      split_pairs; simpl.
      rewrite (eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf
                 l0
                 (snd (run_sm_on_inputs p0 l subs))
                 (fst (run_sm_on_inputs p0 l subs))
                 (fst (interp_proc p subs)));
        autorewrite with comp; auto. }

    { unfold call_proc.
      remember (find_name cn subs) as fn; symmetry in Heqfn.
      destruct fn; simpl; eauto 3 with comp;[].
      rename n0 into p.
      remember (app_m_proc p i (decr_n_procs subs)) as ap; symmetry in Heqap; repnd.
      split_pairs; simpl.

      pose proof (sm2level_le_pred _ _ p) as ln0.

      rewrite (app_m_proc_some2 p i) in Heqap; simpl.
      rewrite select_n_procs_decr_n_procs in Heqap; auto;[].
      remember (sm2update p (sm2state p) i (select_n_procs (sm2level p) subs)) as w; symmetry in Heqw.
      repnd; simpl.

      pose proof (are_procs_n_procs_find_name _ n subs p) as isp.
      repeat (autodimp isp hyp);[].

      introv lvl j.

      applydup is_proc_n_proc_update_implies_some in Heqw; auto;[]; exrepnd; subst; simpl in *.
      dup isp as isp'.
      unfold is_proc_n_proc in isp; exrepnd.
      rewrite isp0 in Heqw.
      unfold proc2upd in Heqw; simpl in *.
      unfold interp_s_proc, to_M_n_some_state in Heqw; simpl in *.
      unfold bind_pair, bind in Heqw; simpl in *.
      remember (interp_proc (p1 (sm2state p) i) (select_n_procs (sm2level p) subs)) as itr; symmetry in Heqitr.
      repnd; simpl in *; ginv.

      pose proof (are_procs_implies_preserves_sub (sm2at p) (sm2state p) i (select_n_procs (sm2level p) subs)) as q.
      repeat (autodimp q hyp); eauto 3 with comp;[].
      rewrite sm_update_sm2at in q.
      rewrite isp0 in q.
      unfold proc2upd, M_break in q; simpl in q.
      unfold interp_s_proc, to_M_n_some_state in q; simpl in q.
      unfold bind_pair, bind in q; simpl in q.
      rewrite Heqitr in q; simpl in q; repnd.

      destruct (CompNameDeq cn0 cn); subst.

      { eapply find_name_in_implies_eq in j; eauto; subst.
        rewrite select_n_procs_nil_if_leaf in Heqitr; auto.
        rewrite select_n_procs_nil_if_leaf in q0; auto.
        inversion q0; subst; clear q0.
        exists [i]; simpl.
        rewrite select_n_procs_nil_if_leaf; auto.
        rewrite isp0.
        unfold proc2upd; simpl.
        unfold interp_s_proc, to_M_n_some_state; simpl.
        unfold bind_pair, bind; simpl.
        rewrite Heqitr; simpl; eauto 3 with comp. }

      pose proof (imp (sm2level p) _ (sm2at p) (sm2state p) i (select_n_procs (sm2level p) subs)) as imp.
      repeat (autodimp imp hyp); try omega; eauto 3 with comp;
        try (complete (destruct n; simpl in *; tcsp; try omega));[].
      autorewrite with comp in *.
      rewrite isp0 in imp.
      unfold proc2upd in imp; simpl in *.
      unfold interp_s_proc, to_M_n_some_state in imp; simpl in *.
      unfold bind_pair, bind in imp; simpl in *.
      rewrite Heqitr in imp; simpl in *.
      applydup in_implies_in_proc_names in j; simpl in *.

      destruct (in_dec CompNameDeq cn0 (procs_names (select_n_procs (sm2level p) subs))) as [d|d].

      { destruct (deq_nat (sm2level p) 0) as [d1|d1];
          [rewrite d1 in *; autorewrite with comp in *; simpl in *; tcsp|];[].
        pose proof (select_n_procs_level_lt_implies_some cn0 n (sm2level p) p0) as eqs.
        rewrite lvl in eqs.
        repeat (autodimp eqs hyp); try omega.
        exrepnd.
        pose proof (lt_level_implies_in_select_n_procs cn0 n (sm2level p) p0 subs q1) as z.
        repeat (autodimp z hype); try omega;[].
        applydup select_n_proc_preserves_sm2level in eqs0.
        apply imp in z; auto; try omega;[].
        exrepnd.

        exists l.
        apply implies_in_replace_subs_right; simpl; autorewrite with comp; eauto 3 with comp;[].
        rewrite incr_pred_n_procs_raise_to_n_procs; auto;[].
        rewrite lvl in eqs1; symmetry in eqs1.
        apply implies_in_raise_to_n_procs; try omega.
        eexists;dands;[|eauto];[].
        simpl.
        rewrite option_map_Some.
        eexists;dands;[|eauto];[].

        pose proof (sm2level_le_pred _ _ p) as lvln0.
        apply raise_to_n_proc_as_select_n_proc; try omega.
        apply select_n_proc_fst_run_sm_in_inputs; auto; try omega. }

      { applydup similar_subs_preserves_procs_names in q0 as eqns.
        dup d as d'; rewrite eqns in d'.
        exists ([] : list (cio_I (fio cn0))); simpl.
        apply implies_in_replace_subs_left; simpl;
          [|intro xx; apply subset_procs_names_raise_to_n_procs in xx; tcsp];[].
        apply in_replace_name_right; auto. } }
  Qed.

  Lemma interp_s_proc_run_subs :
    forall {S O} (p : Proc (S * O)) {n} (subs : n_procs n),
      (forall (m    : nat)
              (cn   : CompName)
              (main : n_proc_at m cn)
              (s    : sf cn)
              (i    : cio_I (fio cn))
              (subs : n_procs m),
          m < n
          -> is_proc_n_proc_at main
          -> are_procs_n_procs subs
          -> wf_procs subs
          -> run_subs_leaves subs (fst (sm_update main s i subs)))
      -> are_procs_n_procs subs
      -> wf_procs subs
      -> run_subs_leaves subs (fst (interp_s_proc p subs)).
  Proof.
    introv imp aps wf.
    unfold interp_s_proc, to_M_n_some_state; simpl.
    unfold bind_pair, bind; simpl.
    rewrite (surjective_pairing (interp_proc p subs)); simpl.
    rewrite (surjective_pairing (snd (interp_proc p subs))); simpl.
    apply interp_proc_run_subs_leaves; auto.
  Qed.

  Lemma are_procs_implies_run_subs :
    forall {n} {cn}
           (main : n_proc_at n cn)
           (s    : sf cn)
           (i    : cio_I (fio cn))
           (subs : n_procs n),
      is_proc_n_proc_at main
      -> are_procs_n_procs subs
      -> wf_procs subs
      -> run_subs_leaves subs (fst (sm_update main s i subs)).
  Proof.
    induction n as [? ind] using comp_ind; introv ip ap wf;[].
    unfold is_proc_n_proc_at in ip; exrepnd.
    rewrite ip0.
    unfold proc2upd; simpl.
    apply interp_s_proc_run_subs; auto.
  Qed.

  Lemma are_procs_ls_implies_ls_run_sub :
    forall {L S} (ls : LocalSystem L S),
      are_procs_ls ls
      -> wf_ls ls
      -> ls_run_subs ls.
  Proof.
    introv h wf.
    destruct h as [isp1 ips2]; simpl in *.
    destruct ls as [main subs]; simpl in *.
    destruct wf as [wf1 wf2]; simpl in *.
    introv; simpl.
    apply (are_procs_implies_run_subs main); auto.
  Qed.

  Lemma run_subs_leaves_trans :
    forall n (subs1 subs2 subs3 : n_procs n),
      run_subs_leaves subs1 subs2
      -> run_subs_leaves subs2 subs3
      -> run_subs_leaves subs1 subs3.
  Proof.
    introv runa runb lvl i.
    apply runa in i; auto; exrepnd;[].
    apply runb in i0; autorewrite with comp in *; auto; exrepnd;[].
    exists (l ++ l0).
    rewrite run_sm_on_inputs_app.
    split_pair; auto.
    erewrite eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf; eauto.
    autorewrite with comp; auto.
  Qed.
  Hint Resolve run_subs_leaves_trans : comp.

  Lemma similar_sms_at_update_state :
    forall n cn (p : n_proc_at n cn) a,
      similar_sms_at p (update_state p a).
  Proof.
    introv; split; simpl; auto.
  Qed.
  Hint Resolve similar_sms_at_update_state : comp.

  Lemma M_byz_run_ls_on_this_one_event_M_nt_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : MLocalSystem L S),
      wf_ls ls1
      -> are_procs_ls ls1
      -> M_byz_run_ls_on_this_one_event ls1 e = Some (M_nt ls2)
      -> (wf_ls ls2
          /\ are_procs_ls ls2
          /\ similar_sms_at (ls_main ls1) (ls_main ls2)
          /\ similar_subs (ls_subs ls1) (ls_subs ls2)
          /\ run_subs_leaves (ls_subs ls1) (ls_subs ls2)).
  Proof.
    introv wf aps run.
    unfold M_byz_run_ls_on_this_one_event in run; simpl in *.
    remember (trigger e) as trig; clear Heqtrig.
    destruct trig; simpl in *;[| |];
      try (complete (apply option_map_Some in run; exrepnd; ginv));[].

    unfold M_break in run.
    dest_cases w; symmetry in Heqw; repnd; simpl in *.
    apply option_map_Some in run; exrepnd; subst; simpl in *.
    rename_hyp_with @M_nt mnt.
    inversion mnt; subst; simpl in *; clear mnt.
    destruct ls1 as [main subs]; simpl in *.
    destruct wf as [wf1 wf2]; simpl in *.
    destruct aps as [aps1 aps2]; simpl in *.
    unfold upd_ls_main_state_and_subs; simpl.
    unfold wf_ls, are_procs_ls; simpl.

    pose proof (are_procs_implies_preserves_sub main (sm_state main) d subs) as h.
    repeat (autodimp h hyp).
    pose proof (are_procs_implies_run_subs main (sm_state main) d subs) as q.
    repeat (autodimp q hyp).

    unfold M_break in h; simpl in *.
    rewrite Heqw in h; rewrite Heqw in q; repnd; simpl in *.
    dands; auto; eauto 3 with comp;[].
    applydup similar_subs_preserves_procs_names in h0 as eqns.
    rewrite <- eqns; auto.
  Qed.

  Lemma M_byz_run_ls_on_event_M_nt_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : MLocalSystem L S),
      wf_ls ls1
      -> are_procs_ls ls1
      -> M_byz_run_ls_on_event ls1 e = Some (M_nt ls2)
      -> (wf_ls ls2
          /\ are_procs_ls ls2
          /\ similar_sms_at (ls_main ls1) (ls_main ls2)
          /\ similar_subs (ls_subs ls1) (ls_subs ls2)
          /\ run_subs_leaves (ls_subs ls1) (ls_subs ls2)).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv wf aps run.
    rewrite M_byz_run_ls_on_event_unroll in run.

    destruct (dec_isFirst e) as [d|d]; ginv; auto;[|].
    { apply M_byz_run_ls_on_this_one_event_M_nt_preserves_subs in run; tcsp. }

    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo;[].
    pose proof (ind L S ls1) as ind.

    apply map_option_Some in run; exrepnd.
    symmetry in run0.
    destruct a as [ls'|t]; simpl in *; ginv;[].

    rewrite M_byz_run_ls_before_event_as_M_byz_run_ls_on_event_pred in run1; eauto 3 with eo;[].
    apply ind in run1; auto;[]; repnd; clear ind.
    apply M_byz_run_ls_on_this_one_event_M_nt_preserves_subs in run0; auto.
    repnd; dands; eauto 3 with comp.
  Qed.

  Lemma M_byz_run_ls_before_event_M_nt_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : MLocalSystem L S),
      wf_ls ls1
      -> are_procs_ls ls1
      -> M_byz_run_ls_before_event ls1 e = Some (M_nt ls2)
      -> (wf_ls ls2
          /\ are_procs_ls ls2
          /\ similar_sms_at (ls_main ls1) (ls_main ls2)
          /\ similar_subs (ls_subs ls1) (ls_subs ls2)
          /\ run_subs_leaves (ls_subs ls1) (ls_subs ls2)).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv wf aps run.
    rewrite M_byz_run_ls_before_event_unroll in run.

    destruct (dec_isFirst e) as [d|d]; ginv; auto;[|].
    { dands; eauto 3 with comp. }

    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo;[].
    pose proof (ind L S ls1) as ind.

    apply map_option_Some in run; exrepnd.
    symmetry in run0.
    destruct a as [ls'|t]; simpl in *; ginv;[].

    apply ind in run1; auto;[]; repnd; clear ind.
    apply M_byz_run_ls_on_this_one_event_M_nt_preserves_subs in run0; auto.
    repnd; dands; eauto 3 with comp.
  Qed.

  Lemma M_run_ls_on_event_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : MLocalSystem L S),
      wf_ls ls1
      -> are_procs_ls ls1
      -> M_run_ls_on_event ls1 e = Some ls2
      -> (wf_ls ls2
          /\ are_procs_ls ls2
          /\ similar_sms_at (ls_main ls1) (ls_main ls2)
          /\ similar_subs (ls_subs ls1) (ls_subs ls2)
          /\ run_subs_leaves (ls_subs ls1) (ls_subs ls2)).
  Proof.
    introv wf aps run.
    apply M_run_ls_on_event_M_byz_run_ls_on_event in run.
    apply M_byz_run_ls_on_event_M_nt_preserves_subs in run; tcsp.
  Qed.

  Lemma M_run_ls_before_event_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : MLocalSystem L S),
      wf_ls ls1
      -> are_procs_ls ls1
      -> M_run_ls_before_event ls1 e = Some ls2
      -> (wf_ls ls2
          /\ are_procs_ls ls2
          /\ similar_sms_at (ls_main ls1) (ls_main ls2)
          /\ similar_subs (ls_subs ls1) (ls_subs ls2)
          /\ run_subs_leaves (ls_subs ls1) (ls_subs ls2)).
  Proof.
    introv wf aps run.
    apply M_run_ls_before_event_M_byz_run_ls_before_event in run.
    apply M_byz_run_ls_before_event_M_nt_preserves_subs in run; tcsp.
  Qed.

  Lemma are_procs_ls_implies_some :
    forall {L S} (ls : LocalSystem L S) s i subs subs' sop o,
      are_procs_ls ls
      -> sm_update (ls_main ls) s i subs = (subs', (sop, o))
      -> exists s, sop = Some s.
  Proof.
    introv aps upd.
    destruct aps as [aps1 aps2].
    unfold is_proc_n_proc_at in aps1; exrepnd.
    rewrite aps0 in upd; clear aps0.
    unfold proc2upd in *; simpl in *.
    unfold interp_s_proc, to_M_n_some_state in *; simpl in *.
    unfold bind_pair, bind in *; simpl in *.
    repeat dest_cases w; repnd; simpl in *.
    unfold ret in *; simpl in *; ginv.
    inversion upd; subst; clear upd; ginv; eauto.
  Qed.

  Lemma reduces_option_map_some :
    forall {A B} (a : A) (f : A -> B),
      option_map f (Some a) = Some (f a).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduces_option_map_some : comp.

  Lemma reduce_map_op_untrusted_op_some :
    forall {T} {A} (x : M_trusted T) (F : T -> option A),
      map_op_untrusted_op (Some x) F
      = map_untrusted_op x F.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduce_map_op_untrusted_op_some : comp.

  Lemma reduce_map_op_untrusted_some :
    forall {T} {A} (x : M_trusted T) (F : T -> A),
      map_op_untrusted (Some x) F
      = Some (map_untrusted x F).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduce_map_op_untrusted_some : comp.

  Lemma reduce_map_untrusted_op_M_nt :
    forall {T} {A} (x : T) (F : T -> option A),
      map_untrusted_op (M_nt x) F = option_map M_nt (F x).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduce_map_untrusted_op_M_nt : comp.

  Lemma find_name_implies_in :
    forall {n} {cn} (subs : n_procs n) (sm : n_proc n cn),
      find_name cn subs = Some sm
      -> In (MkPProc cn sm) subs.
  Proof.
    induction subs; introv fn; simpl in *; tcsp.
    destruct a as [c a].
    destruct (CompNameDeq c cn); subst; simpl in *; ginv; tcsp.
  Qed.
  Hint Resolve find_name_implies_in : comp.

  Lemma find_sub_implies_in :
    forall {L S} {cn} (ls : LocalSystem L S) (sm : n_proc L cn),
      find_sub cn ls = Some sm
      -> In (MkPProc cn sm) (ls_subs ls).
  Proof.
    introv fs.
    unfold find_sub in fs; eauto 3 with comp.
  Qed.

  Lemma in_implies_find_name :
    forall {n} {cn} (subs : n_procs n) (sm : n_proc n cn),
      wf_procs subs
      -> In (MkPProc cn sm) subs
      -> find_name cn subs = Some sm.
  Proof.
    induction subs; introv wf fn; simpl in *; tcsp.
    allrw wf_procs_cons; repnd.
    destruct a as [c a].
    destruct (CompNameDeq c cn); subst; simpl in *; ginv; tcsp;
      repndors; ginv; tcsp.

    { inversion fn.
      match goal with
      | [ H : context[a] |- _ ] => rename H into h1
      end.
      apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp; GC. }

    { apply in_implies_in_proc_names in fn; simpl in *; tcsp. }

    { inversion fn; subst; tcsp. }
  Qed.
  Hint Resolve in_implies_find_name : comp.

  Lemma in_implies_find_sub :
    forall {L S} {cn} (ls : LocalSystem L S) (sm : n_proc L cn),
      wf_procs (ls_subs ls)
      -> In (MkPProc cn sm) (ls_subs ls)
      -> find_sub cn ls = Some sm.
  Proof.
    introv wf i.
    unfold find_sub; eauto 3 with comp.
  Qed.

  Lemma run_subs_leaves_of_find_sub :
    forall {L S} {cn} (ls ls' : LocalSystem L S) (sm : n_proc L cn),
      sm2level sm = 0
      -> wf_procs (ls_subs ls')
      -> find_sub cn ls = Some sm
      -> run_subs_leaves (ls_subs ls) (ls_subs ls')
      -> exists l,
          find_sub cn ls' = Some (snd (run_sm_on_inputs sm l (ls_subs ls))).
  Proof.
    introv lvl wf fs run.
    applydup @find_sub_implies_in in fs.
    apply run in fs0; auto;[].
    exrepnd.
    exists l.
    apply in_implies_find_sub; auto.
  Qed.

  Lemma wf_ls_implies_wf_procs :
    forall {L S} (ls : LocalSystem L S),
      wf_ls ls
      -> wf_procs (ls_subs ls).
  Proof.
    introv wf; destruct wf; auto.
  Qed.
  Hint Resolve wf_ls_implies_wf_procs : comp.

  Lemma find_sub_implies_state_of_component :
    forall {L S} {cn} (ls : LocalSystem L S) (sm : n_proc L cn),
      wf_ls ls
      -> find_sub cn ls = Some sm
      -> state_of_component cn ls = Some (sm2state sm).
  Proof.
    introv wf fs.
    unfold state_of_component.
    unfold find_sub in fs.
    destruct wf as [ni wf].
    destruct ls as [main subs].
    simpl in ni, wf, fs.
    dup fs as d.
    eapply find_name_not_in_procs_names_implies in d;[|eauto].
    destruct (CompNameDeq S cn); tcsp.
    unfold state_of_subcomponents.
    allrw; simpl; auto.
  Qed.

  Lemma state_of_components_upd_ls_main_state_and_subs_if_in :
    forall {cn L S} s (ls : LocalSystem L S) (p : n_proc L cn) (l : n_procs L),
      wf_ls ls
      -> wf_procs l
      -> In (MkPProc cn p) l
      -> In cn (procs_names (ls_subs ls))
      -> state_of_component cn (upd_ls_main_state_and_subs ls s l)
         = Some (sm2state p).
  Proof.
    introv wf wfl i j.
    destruct wf as [ni wf].
    destruct ls as [main subs].
    simpl in ni, wf, j.
    unfold state_of_component.
    unfold upd_ls_main_state_and_subs.
    destruct (CompNameDeq S cn); subst; tcsp;[].
    unfold state_of_subcomponents.
    apply in_implies_find_name in i; auto.
    rewrite i; simpl; auto.
  Qed.

  Lemma sm2state_update_state_m :
    forall cn n (p : n_proc n cn) s,
      sm2state (update_state_m p s) = s.
  Proof.
    induction n; introv; simpl in *; tcsp; destruct p as [p|p]; tcsp.
  Qed.
  Hint Rewrite sm2state_update_state_m : comp.

  Lemma sm2update_update_state_m :
    forall {cn n} (p : n_proc n cn) s x i subs,
      let (subs', o) := sm2update (update_state_m p s) x i subs in
      sm2update p x i (select_n_procs (sm2level p) subs) = (select_n_procs (sm2level p ) subs', o).
  Proof.
    induction n; introv; simpl in *; tcsp;[].
    destruct p as [p|p]; simpl in *; tcsp.

    { fold (M_StateMachine n) in *; fold (n_proc n) in *.
      remember (sm_update p x i subs) as xx; symmetry in Heqxx; repnd; simpl.
      autorewrite with comp; auto. }

    apply IHn; auto.
  Qed.

  Lemma M_byz_run_update_on_list_update_state_m_eq :
    forall cn n l j x (sm : n_proc n cn) s (subs : n_procs j) (lej : j <= sm2level sm),
      let (subs', o) := M_byz_run_update_on_list
                          x
                          (sm2update (update_state_m sm s))
                          l
                          (raise_to_n_procs (sm2level (update_state_m sm s)) subs) in
      M_byz_run_update_on_list
        x
        (sm2update sm)
        l
        (raise_to_n_procs (sm2level sm) subs)
      = (select_n_procs (sm2level sm) subs', o).
  Proof.
    induction l; introv lej; simpl in *; tcsp.
    { unfold ret; simpl.
      autorewrite with comp; auto. }

    destruct a; simpl; tcsp.

    { unfold bind; simpl.
      autorewrite with comp.
      pose proof (sm2update_update_state_m sm s x d (raise_to_n_procs (sm2level (update_state_m sm s)) subs)) as w.
      remember (sm2update (update_state_m sm s) x d (raise_to_n_procs (sm2level (update_state_m sm s)) subs)) as z; symmetry in Heqz.
      repnd; simpl in *.
      rewrite raise_to_n_procs_select_n_procs in w; autorewrite with comp; try omega;[].
      rewrite w; simpl.
      destruct z1; simpl; auto.
      pose proof (IHl (sm2level (update_state_m sm s)) s0 sm s z0) as IHl.
      autodimp IHl hyp; autorewrite with comp in *; auto.
      remember (M_byz_run_update_on_list s0 (sm2update (update_state_m sm s)) l z0) as zz; symmetry in Heqzz; repnd.
      rewrite <- IHl; clear IHl.
      clear Heqz w Heqzz; revert z0.
      autorewrite with comp; introv; autorewrite with comp.
      remember (M_byz_run_update_on_list s0 (sm2update sm) l z0); repnd; auto. }

    { autorewrite with comp.
      remember (M_run_trusted_on_trigger_info_list (trigger_info_arbitrary :: l) (raise_to_n_procs (sm2level sm) subs)) as xx; repnd.
      autorewrite with comp; auto. }

    { autorewrite with comp.
      remember (M_run_trusted_on_trigger_info_list (trigger_info_trusted i :: l) (raise_to_n_procs (sm2level sm) subs)) as xx; repnd.
      autorewrite with comp; auto. }
  Qed.

  Lemma M_byz_run_sm_on_list_as_run_sm_on_inputs :
    forall cn n l (sm : n_proc n cn) (subs : n_procs n),
      is_proc_n_proc sm
      -> let (subs',sm') := run_sm_on_inputs sm l subs in
         M_byz_run_sm_on_list
           sm
           (map (fun x => trigger_info_data x) l)
           (select_n_procs (sm2level sm) subs)
         = (select_n_procs (sm2level sm) subs', Some (M_nt (sm2state sm'))).
  Proof.
    unfold M_byz_run_sm_on_list.
    induction l; introv isp; simpl; tcsp;[].

    pose proof (sm2level_le_pred _ _ sm) as lvl.

    unfold bind.
    remember (sm2update sm (sm2state sm) a (select_n_procs (sm2level sm) subs)) as w; symmetry in Heqw; repnd; simpl.
    destruct w1; simpl; tcsp.

    { pose proof (IHl (update_state_m sm s) (raise_to_n_procs n w0)) as IHl.
      remember (run_sm_on_inputs (update_state_m sm s) l (raise_to_n_procs n w0)) as z; symmetry in Heqz; repnd.
      simpl in *.
      rewrite raise_to_n_procs_select_n_procs in IHl; autorewrite with comp; try omega;[].
      autorewrite with comp in *.

      pose proof (M_byz_run_update_on_list_update_state_m_eq
                    cn n
                    (map (fun x : cio_I (funIOd_msg_nm cn) => trigger_info_data x) l)
                    (sm2level sm)
                    s sm s w0) as xx; autodimp xx hyp.
      simpl in *; rewrite IHl in xx; eauto 3 with comp;[].
      autorewrite with comp in *.
      rewrite xx; auto. }

    { apply is_proc_n_proc_update_implies_some in Heqw; auto; exrepnd; ginv. }
  Qed.

  Lemma are_procs_ls_find_sub :
    forall {L S} {cn} (p : n_proc L cn) (ls : LocalSystem L S),
      are_procs_ls ls
      -> find_sub cn ls = Some p
      -> is_proc_n_proc p.
  Proof.
    introv aps fs.
    unfold find_sub in fs.
    destruct aps as [aps1 aps2].
    eapply are_procs_n_procs_find_name; eauto.
  Qed.
  Hint Resolve are_procs_ls_find_sub : comp.

  Fixpoint is_trusted {n:nat} (cn : CompName) (l : n_procs n) : bool :=
    match l with
    | [] => false
    | MkPProc (MkCompName k s true) pr :: rest =>
      if CompNameDeq cn (MkCN k s true) then true else false
    | _ :: rest => is_trusted cn rest
    end.

  Lemma ls_subs_MkLocalSystem :
    forall L S (main : n_proc_at L (msg_comp_name S)) (subs : n_procs L),
      ls_subs (MkLocalSystem main subs) = subs.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite ls_subs_MkLocalSystem : comp.

  Lemma is_trusted_implies_in_procs_names :
    forall cn n (subs : n_procs n),
      is_trusted cn subs = true
      -> In cn (procs_names subs).
  Proof.
    induction subs; introv ist; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    destruct c as [k s t]; simpl in *.
    destruct t; simpl in *; tcsp.
    destruct (CompNameDeq cn (MkCN k s true)); subst; simpl in *; tcsp.
  Qed.

  Lemma wf_is_trusted_implies_state_of_subcomponents :
    forall cn {L S} (ls : LocalSystem L S),
      wf_ls ls
      -> is_trusted cn (ls_subs ls) = true
      -> state_of_component cn ls
         = state_of_subcomponents (ls_subs ls) cn.
  Proof.
    introv wf ist.
    rewrite state_of_component_eq.
    destruct (CompNameDeq S cn); auto; subst.
    assert False; tcsp.
    destruct ls as [main subs]; simpl in *.
    destruct wf as [wf1 wf2]; simpl in *.
    apply is_trusted_implies_in_procs_names in ist; tcsp.
  Qed.

  Lemma is_trusted_implies_find_trusted :
    forall cn n (subs : n_procs n),
      is_trusted cn subs = true
      ->
      exists (tsm : trustedSM)
             (sm  : n_proc n cn)
             (eql : tsm_level tsm = sm2level sm)
             (eqn : cn = MkCN (tsm_kind tsm) (tsm_space tsm) true),
        find_trusted subs = Some tsm
        /\ find_name cn subs = Some sm
        /\ eq_rect _ (fun n => n_proc_at n _) (tsm_sm tsm) _ eql
           = eq_rect _ _ (sm2at sm) _ eqn.
  Proof.
    induction subs; introv ist; simpl in *; tcsp;[].
    destruct a as [c a];[].
    destruct c as [k s t];[].
    destruct t; simpl in *; tcsp;[|].

    { destruct (CompNameDeq cn (MkCN k s true)); subst; simpl in *; simpl; ginv;[].

      destruct (CompNameKindDeq k k); tcsp;[].
      destruct (CompNameSpaceDeq s s); tcsp;[].
      pose proof (UIP_refl_CompNameKind _ e) as w; subst; simpl in *; ginv; tcsp.
      pose proof (UIP_refl_CompNameSpace _ e0) as w; subst; simpl in *; ginv; tcsp.

      assert (tsm_level (MktrustedSM (sm2level a) k s (sm2at a)) = (sm2level a)) as eql.
      { simpl; auto. }

      assert (MkCN k s true
              = MkCN
                  (tsm_kind (MktrustedSM (sm2level a) k s (sm2at a)))
                  (tsm_space (MktrustedSM (sm2level a) k s (sm2at a)))
                  true) as eqs.
      { simpl; auto. }

      exists (MktrustedSM (sm2level a) k s (sm2at a)) a eql eqs.
      simpl in *.
      pose proof (UIP_refl_nat _ eql) as w; subst; simpl in *; ginv; tcsp.
      pose proof (UIP_refl_CompName _ eqs) as w; subst; simpl in *; ginv; tcsp. }

    { autodimp IHsubs hyp; exrepnd.
      exists tsm sm eql eqn; simpl in *; auto.
      subst; simpl in *; tcsp;[].
      destruct (CompNameKindDeq k (tsm_kind tsm)); subst; simpl in *; tcsp;[|];
        destruct (CompNameSpaceDeq s (tsm_space tsm)); subst; simpl in *; tcsp;
          destruct (CompNameStateDeq x (tsm_state tsm)); subst; simpl in *; tcsp. }
  Qed.

  Lemma M_byz_run_sm_on_list_as_run_sm_on_inputs_app :
    forall cn n l k (sm : n_proc n cn) (subs : n_procs n),
      is_proc_n_proc sm
      -> let (subs',sm') := run_sm_on_inputs sm l subs in
         M_byz_run_sm_on_list
           sm
           (map (fun x => trigger_info_data x) l ++ k)
           (select_n_procs (sm2level sm) subs)
         = let (subs'', o) := M_byz_run_sm_on_list sm' k (select_n_procs (sm2level sm') subs')
           in (select_n_procs (sm2level sm) subs'', o).
  Proof.
    unfold M_byz_run_sm_on_list.
    induction l; introv isp; simpl; tcsp.

    { remember (M_byz_run_update_on_list
                  (sm2state sm) (sm2update sm) k
                  (select_n_procs (sm2level sm) subs)) as w; symmetry in Heqw.
      simpl in *; rewrite Heqw; repnd; autorewrite with comp; auto. }

    pose proof (sm2level_le_pred _ _ sm) as lvl.

    unfold bind.
    remember (sm2update sm (sm2state sm) a (select_n_procs (sm2level sm) subs)) as w; symmetry in Heqw; repnd; simpl.
    destruct w1; simpl; tcsp.

    { pose proof (IHl k (update_state_m sm s) (raise_to_n_procs n w0)) as IHl.
      remember (run_sm_on_inputs (update_state_m sm s) l (raise_to_n_procs n w0)) as z; symmetry in Heqz; repnd.
      simpl in *.
      rewrite raise_to_n_procs_select_n_procs in IHl; autorewrite with comp; try omega;[].
      autorewrite with comp in *.

      pose proof (M_byz_run_update_on_list_update_state_m_eq
                    cn n
                    (map (fun x : cio_I (funIOd_msg_nm cn) => trigger_info_data x) l ++ k)
                    (sm2level sm)
                    s sm s w0) as xx; autodimp xx hyp.
      simpl in *; rewrite IHl in xx; eauto 3 with comp;[].
      remember (M_byz_run_update_on_list
                  (sm2state z) (sm2update z) k
                  (select_n_procs (sm2level z) z0)) as zz; symmetry in Heqzz.
      simpl in *.
      rewrite Heqzz; rewrite Heqzz in xx.
      repnd; simpl in *.
      autorewrite with comp in *.
      rewrite xx; auto. }

    { apply is_proc_n_proc_update_implies_some in Heqw; auto; exrepnd; ginv. }
  Qed.

  Lemma reduce_map_option_some :
    forall {A B} (f : A -> option B) (a : A),
      map_option f (Some a) = f a.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduce_map_option_some : comp.

  Lemma M_run_update_on_list_update_state_m_eq :
    forall cn n l j x (sm : n_proc n cn) s (subs : n_procs j) (lej : j <= sm2level sm),
      let (subs', o) := M_run_update_on_list
                          x
                          (sm2update (update_state_m sm s))
                          l
                          (raise_to_n_procs (sm2level (update_state_m sm s)) subs) in
      M_run_update_on_list
        x
        (sm2update sm)
        l
        (raise_to_n_procs (sm2level sm) subs)
      = (select_n_procs (sm2level sm) subs', o).
  Proof.
    induction l; introv lej; simpl in *; tcsp.
    { unfold ret; simpl.
      autorewrite with comp; auto. }

    destruct a; simpl; tcsp.

    { unfold bind; simpl.
      autorewrite with comp.
      pose proof (sm2update_update_state_m sm s x c (raise_to_n_procs (sm2level (update_state_m sm s)) subs)) as w.
      remember (sm2update (update_state_m sm s) x c (raise_to_n_procs (sm2level (update_state_m sm s)) subs)) as z; symmetry in Heqz.
      repnd; simpl in *.
      rewrite raise_to_n_procs_select_n_procs in w; autorewrite with comp; try omega;[].
      rewrite w; simpl.
      destruct z1; simpl; auto.
      pose proof (IHl (sm2level (update_state_m sm s)) s0 sm s z0) as IHl.
      autodimp IHl hyp; autorewrite with comp in *; auto.
      remember (M_run_update_on_list s0 (sm2update (update_state_m sm s)) l z0) as zz; symmetry in Heqzz; repnd.
      rewrite <- IHl; clear IHl.
      clear Heqz w Heqzz; revert z0.
      autorewrite with comp; introv; autorewrite with comp.
      remember (M_run_update_on_list s0 (sm2update sm) l z0); repnd; auto. }

    { autorewrite with comp; tcsp. }
  Qed.

  Lemma M_run_sm_on_list_as_run_sm_on_inputs :
    forall cn n l (sm : n_proc n cn) (subs : n_procs n),
      is_proc_n_proc sm
      -> let (subs',sm') := run_sm_on_inputs sm l subs in
         M_run_sm_on_list
           sm
           (map (fun x => Some x) l)
           (select_n_procs (sm2level sm) subs)
         = (select_n_procs (sm2level sm) subs', Some (sm2state sm')).
  Proof.
    unfold M_run_sm_on_list.
    induction l; introv isp; simpl; tcsp;[].

    pose proof (sm2level_le_pred _ _ sm) as lvl.

    unfold bind.
    remember (sm2update sm (sm2state sm) a (select_n_procs (sm2level sm) subs)) as w; symmetry in Heqw; repnd; simpl.
    destruct w1; simpl; tcsp.

    { pose proof (IHl (update_state_m sm s) (raise_to_n_procs n w0)) as IHl.
      remember (run_sm_on_inputs (update_state_m sm s) l (raise_to_n_procs n w0)) as z; symmetry in Heqz; repnd.
      simpl in *.
      rewrite raise_to_n_procs_select_n_procs in IHl; autorewrite with comp; try omega;[].
      autorewrite with comp in *.

      pose proof (M_run_update_on_list_update_state_m_eq
                    cn n
                    (map (fun x => Some x) l)
                    (sm2level sm)
                    s sm s w0) as xx; autodimp xx hyp.
      simpl in *; rewrite IHl in xx; eauto 3 with comp;[].
      autorewrite with comp in *.
      rewrite xx; auto. }

    { apply is_proc_n_proc_update_implies_some in Heqw; auto; exrepnd; ginv. }
  Qed.


  Lemma M_non_byz_compose :
    forall {eo : EventOrdering} (e : Event)
           {L S}
           (ls : MLocalSystem L S)
           {cn}
           (sm : n_proc L cn),
      are_procs_ls ls
      -> find_sub cn ls = Some sm
      -> wf_ls ls
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      ->
      exists (l : oplist (cio_I (fio cn))),
        snd (M_run_sm_on_list sm l (select_n_procs (sm2level sm) (ls_subs ls)))
        = M_state_ls_before_event ls e cn.
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv aps fs wf lvl.
    unfold M_state_ls_before_event.
    rewrite M_run_ls_before_event_unroll.

    destruct (dec_isFirst e) as [d|d].

    { simpl.
      rewrite state_of_component_eq.
      pose proof (find_sub_wf_ls_implies cn ls sm) as dn.
      repeat (autodimp dn hyp).
      destruct (CompNameDeq (msg_comp_name S) cn); tcsp.
      unfold state_of_subcomponents.
      unfold find_sub in fs; rewrite fs; simpl.
      exists ([] : oplist (cio_I (fio cn))); simpl; auto. }

    pose proof (ind (local_pred e)) as ind.
    autodimp ind hyp; eauto 3 with eo.
    pose proof (ind L S ls cn sm) as ind.
    repeat (autodimp ind hyp).
    exrepnd.

    unfold M_state_ls_before_event in ind0.

    remember (M_run_ls_before_event ls (local_pred e)) as run; symmetry in Heqrun.
    destruct run; simpl in *; eauto;[].
    rename l0 into ls'.

    unfold M_run_ls_on_this_one_event, M_break.
    applydup M_run_ls_before_event_preserves_subs in Heqrun as prp; auto; repnd;[].

    pose proof (are_procs_ls_implies_ls_run_sub ls') as lsr; repeat (autodimp lsr hyp).
    pose proof (are_procs_ls_implies_ls_preserves_sub ls') as lps; repeat (autodimp lps hyp).
    pose proof (run_subs_leaves_of_find_sub ls ls' sm) as z.
    repeat (autodimp z hyp); eauto 3 with comp;[].
    exrepnd.
    applydup @find_sub_implies_state_of_component in z0; auto.
    rewrite z1 in ind0; simpl in ind0.
    applydup @find_sub_implies_in in z0.

    remember (trigger_op (local_pred e)) as trig; clear Heqtrig.
    destruct trig; simpl;[|].

    { remember (sm_update (ls_main ls') (sm_state (ls_main ls')) m (ls_subs ls')) as w; symmetry in Heqw.
      repnd; simpl.
      applydup @are_procs_ls_implies_some in Heqw; auto;[].
      exrepnd; subst.
      autorewrite with comp.

      pose proof (lsr (sm_state (ls_main ls')) m) as lsr.
      pose proof (lps (sm_state (ls_main ls')) m (ls_subs ls')) as lps.
      autodimp lps hyp; eauto 3 with comp.
      unfold M_break in lps; split_pair.
      rewrite Heqw in lsr; simpl in lsr.
      rewrite Heqw in lps; simpl in lps.

      apply lsr in z2; auto; autorewrite with comp; auto; exrepnd;[].
      dup z3 as v.
      apply (state_of_components_upd_ls_main_state_and_subs_if_in s ls') in v; eauto; eauto 3 with comp;[].
      rewrite v; simpl.

      pose proof (run_sm_on_inputs_app l0 l1 sm (ls_subs ls)) as xx.
      split_pair.
      erewrite (eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf l1 _ _ (fst (run_sm_on_inputs sm l0 (ls_subs ls))));
        autorewrite with comp; auto;[].
      rewrite <- xx; clear xx.

      exists (map (fun x => Some x) (l0 ++ l1)).
      pose proof (M_run_sm_on_list_as_run_sm_on_inputs
                    cn L (l0 ++ l1) sm (ls_subs ls)) as xx.
      autodimp xx hyp; eauto 3 with comp;[].

      remember (run_sm_on_inputs sm (l0 ++ l1) (ls_subs ls)) as rn.
      symmetry in Heqrn; repnd; simpl.
      simpl in xx; rewrite xx; clear xx; simpl; auto. }

    { exists [None : option (cio_I (fio cn))]; simpl; auto. }
  Qed.

  Definition is_trusted_ls {L S} cn (ls : LocalSystem L S) : Prop :=
    is_trusted cn (ls_subs ls) = true.

  Definition to_trusted {n:nat} {cn : CompName} : n_proc n cn -> option trustedSM :=
    match cn with
    | MkCompName k s true =>
      fun pr => Some (MktrustedSM (sm2level pr) k s (sm2at pr))
    | _ => fun _ => None
    end.

  (* Byzantine mode, where we also react to Byzantine events *)
  Definition byz_run_sm_on_byz_inputs {n} {cn}
             (p : n_proc n cn)
             (l : list (trigger_info (cio_I (fio cn))))
             (subs : n_procs n) : n_procs n * M_trusted (n_proc n cn) :=
    match to_trusted p with
    | Some tsm => ([], M_t (run_trustedSM_on_trigger_info_list tsm l))
    | None => (subs, M_nt p)
    end.

  (* If we encounter a byzantine events, we switch to the Byzantine mode *)
  Fixpoint run_sm_on_byz_inputs {n} {cn}
           (p : n_proc n cn)
           (l : list (trigger_info (cio_I (fio cn))))
           (subs : n_procs n) : n_procs n * M_trusted (n_proc n cn) :=
    match l with
    | [] => (subs, M_nt p)
    | i :: l =>
      if_trigger_info_data
        i
        (fun m =>
           match sm2update p (sm2state p) m (select_n_procs (sm2level p) subs) with
           | (subs', (ops, o)) =>
             run_sm_on_byz_inputs
               (update_state_op_m p ops)
               l
               (raise_to_n_procs n subs')
           end)
        (byz_run_sm_on_byz_inputs p (i :: l) subs)
    end.

  Lemma implies_is_proc_n_proc_update_state_op_m :
    forall n cn (p : n_proc n cn) sop,
      is_proc_n_proc p
      -> is_proc_n_proc (update_state_op_m p sop).
  Proof.
    introv i.
    destruct sop; simpl; auto; eauto 3 with comp.
  Qed.
  Hint Resolve implies_is_proc_n_proc_update_state_op_m : comp.

  Lemma run_sm_on_byz_inputs_as_run_sm_on_inputs :
    forall cn n l (sm : n_proc n cn) (subs : n_procs n),
      is_proc_n_proc sm
      -> let (subs',sm') := run_sm_on_inputs sm l subs in
         run_sm_on_byz_inputs sm (map (fun x => trigger_info_data x) l) subs
         = (subs', M_nt sm').
  Proof.
    induction l; introv isp; simpl; tcsp;[].

    pose proof (sm2level_le_pred _ _ sm) as lvl.

    remember (sm2update sm (sm2state sm) a (select_n_procs (sm2level sm) subs)) as w; symmetry in Heqw; repnd; simpl.

    pose proof (IHl (update_state_op_m sm w1) (raise_to_n_procs n w0)) as IHl.
    autodimp IHl hyp; eauto 3 with comp.
  Qed.

  Lemma similar_subs_preserves_is_trusted :
    forall n cn (subs1 subs2 : n_procs n),
      similar_subs subs1 subs2
      -> is_trusted cn subs2 = is_trusted cn subs1.
  Proof.
    introv sim.
    induction sim; simpl in *; tcsp;[].
    destruct p2 as [c2 p2], p1 as [c1 p1].
    destruct c1 as [k1 s1 t1], c2 as [k2 s2 t2].
    inversion simp; subst; simpl in *.

    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
    destruct t2; tcsp.
  Qed.

  Lemma run_sm_on_byz_inputs_as_run_sm_on_inputs_app :
    forall cn n l k (sm : n_proc n cn) (subs : n_procs n),
      let (subs',sm') := run_sm_on_inputs sm l subs in
      run_sm_on_byz_inputs
        sm
        (map (fun x => trigger_info_data x) l ++ k)
        subs
      = run_sm_on_byz_inputs sm' k subs'.
  Proof.
    induction l; introv; simpl; tcsp;[].

    pose proof (sm2level_le_pred _ _ sm) as lvl.

    remember (sm2update sm (sm2state sm) a (select_n_procs (sm2level sm) subs)) as w; symmetry in Heqw; repnd; simpl.

    pose proof (IHl k (update_state_op_m sm w1) (raise_to_n_procs n w0)) as IHl.
    remember (run_sm_on_inputs (update_state_op_m sm w1) l (raise_to_n_procs n w0)) as z; symmetry in Heqz; repnd; tcsp.
  Qed.

  Lemma is_trusted_implies_find_trusted2 :
    forall cn n (subs : n_procs n),
      is_trusted cn subs = true
      ->
      exists (sm  : n_proc n cn)
             (eqn : cn = MkCN (comp_name_kind cn) (comp_name_space cn) true),
        find_trusted subs
        = Some (MktrustedSM
                  (sm2level sm)
                  (comp_name_kind cn)
                  (comp_name_space cn)
                  (eq_rect _ _ (sm2at sm) _ eqn))
        /\ find_name cn subs = Some sm.
  Proof.
    induction subs; introv ist; simpl in *; tcsp;[].
    destruct a as [c a];[].
    destruct c as [k s t];[].
    destruct t; simpl in *; tcsp;[|].

    { destruct (CompNameDeq cn (MkCN k s true)); subst; simpl in *; simpl; ginv;
        try (complete (dest_cases w));[].

      destruct (CompNameKindDeq k k); tcsp;[].
      destruct (CompNameSpaceDeq s s); tcsp;[].
      pose proof (UIP_refl_CompNameKind _ e) as w; subst; simpl in *; ginv; tcsp.
      pose proof (UIP_refl_CompNameSpace _ e0) as w; subst; simpl in *; ginv; tcsp.

      assert (MkCN k s true
              = MkCN
                  (tsm_kind (MktrustedSM (sm2level a) k s (sm2at a)))
                  (tsm_space (MktrustedSM (sm2level a) k s (sm2at a)))
                  true
             ) as eqs.
      { simpl; auto. }

      exists a eqs.
      simpl in *.
      pose proof (UIP_refl_CompName _ eqs) as w; subst; simpl in *; ginv; tcsp. }

    { autodimp IHsubs hyp; exrepnd.
      exists sm eqn; simpl in *; auto.
      subst; simpl in *; tcsp;[].
      destruct cn as [k' s' t']; simpl in *; ginv.
      inversion eqn; subst; simpl in *; tcsp.
      destruct (CompNameKindDeq k k'); subst; simpl in *; tcsp;[|];
        destruct (CompNameSpaceDeq s s'); subst; simpl in *; tcsp;
          destruct (CompNameStateDeq x x'); subst; simpl in *; tcsp. }
  Qed.

  Lemma to_trusted_eq :
    forall {n} {cn} (p : n_proc n cn) {k s} (e : cn = MkCN k s true),
      to_trusted p
      = Some (MktrustedSM
                (sm2level p)
                k
                s
                (eq_rect _ _ (sm2at p) _ e)).
  Proof.
    introv.
    unfold to_trusted.
    destruct cn as [k' s' t']; simpl in *.
    inversion e; subst; simpl in *; auto.
    pose proof (UIP_refl_CompName _ e) as z; subst; simpl in *; auto.
  Qed.

  Lemma map_untrusted_op_Some_M_t_implies :
    forall {T} {A} (x : M_trusted T) (F : T -> option A) (a : trustedSM),
      map_untrusted_op x F = Some (M_t a)
      -> x = M_t a.
  Proof.
    introv h.
    destruct x; simpl in *; ginv; tcsp;[].
    apply option_map_Some in h; exrepnd; ginv.
  Qed.

  Lemma trusted_rn_sm_on_byz_inputs_throws_away_subs :
    forall {n} {cn} l (sm : n_proc n cn) subs subs' t,
      run_sm_on_byz_inputs sm l subs = (subs', M_t t)
      -> subs' = [].
  Proof.
    induction l; introv h; simpl in *; tcsp; ginv.
    destruct a as [m| |i]; simpl in *; tcsp.

    { remember (sm2update sm (sm2state sm) m (select_n_procs (sm2level sm) subs)) as w; symmetry in Heqw.
      repnd.
      apply IHl in h; auto. }

    { unfold byz_run_sm_on_byz_inputs in h; simpl in *.
      destruct (to_trusted sm); ginv.
      inversion h; subst; auto. }

    { unfold byz_run_sm_on_byz_inputs in h; simpl in *.
      destruct (to_trusted sm); ginv.
      inversion h; subst; auto. }
  Qed.

  Lemma run_trustedSM_on_trigger_info_list_snoc :
    forall {D} (l k : list (trigger_info D)) (tsm : trustedSM),
      run_trustedSM_on_trigger_info_list tsm (l ++ k)
      = run_trustedSM_on_trigger_info_list
          (run_trustedSM_on_trigger_info_list tsm l)
          k.
  Proof.
    induction l; introv; simpl; auto.
  Qed.

  Lemma run_sm_on_byz_inputs_as_run_sm_on_inputs_app_trusted :
    forall {cn} {n} l k (sm : n_proc n cn) (subs subs' : n_procs n) (t : trustedSM),
      run_sm_on_byz_inputs sm l subs = (subs', M_t t)
      -> run_sm_on_byz_inputs sm (l ++ k) subs
         = ([], M_t (run_trustedSM_on_trigger_info_list t k)).
  Proof.
    induction l; introv h; simpl in *; ginv; tcsp;[].
    destruct a as [m| | i]; simpl in *.

    { remember (sm2update sm (sm2state sm) m (select_n_procs (sm2level sm) subs)) as w; symmetry in Heqw; repnd; simpl.
      apply (IHl k) in h; auto. }

    { unfold byz_run_sm_on_byz_inputs in h; simpl in *.
      unfold byz_run_sm_on_byz_inputs; simpl in *.
      remember (to_trusted sm) as tsm; symmetry in Heqtsm; destruct tsm; simpl; ginv;[].
      inversion h; subst; simpl in *; tcsp; clear h.
      rewrite run_trustedSM_on_trigger_info_list_snoc; auto. }

    { unfold byz_run_sm_on_byz_inputs in h; simpl in *.
      unfold byz_run_sm_on_byz_inputs; simpl in *.
      remember (to_trusted sm) as tsm; symmetry in Heqtsm; destruct tsm; simpl; ginv;[].
      inversion h; subst; simpl in *; tcsp; clear h.
      rewrite run_trustedSM_on_trigger_info_list_snoc; auto. }
  Qed.



  (* If [sm] is the trusted component, it cannot search through its
     sub-components for the trusted one!
     Even if it's not, it cannot search for the trusted one because it's
     a leaf.  In which case, it cannot transition to the trusted component
     if we meet a Byzantine event.  But then if we meet a Byzantine event,
     we don't really care about the non-trusted component.
     We have another such lemma for non-byz computations ([M_non_byz_compose]),
     and this one assumes that the component is the trusted one.
   *)

  Lemma M_byz_compose :
    forall {eo : EventOrdering} (e : Event)
           {L S}
           (ls : MLocalSystem L S)
           {cn}
           (sm : n_proc L cn),
      are_procs_ls ls
      -> wf_ls ls
      -> find_sub cn ls = Some sm
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      -> is_trusted_ls cn ls
      ->
      exists (l : list (trigger_info (cio_I (fio cn)))),
        map_untrusted_op
          (snd (run_sm_on_byz_inputs sm l (ls_subs ls)))
          (fun p => Some (sm2state p))
        = M_byz_state_ls_before_event ls e cn.
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv aps wf fs lvl trust.
    unfold M_byz_state_ls_before_event.
    rewrite M_byz_run_ls_before_event_unroll.

    destruct (dec_isFirst e) as [d|d].

    { simpl.
      rewrite state_of_component_eq.
      pose proof (find_sub_wf_ls_implies cn ls sm) as dn.
      repeat (autodimp dn hyp).
      destruct (CompNameDeq (msg_comp_name S) cn); tcsp.
      unfold state_of_subcomponents.
      unfold find_sub in fs; rewrite fs; simpl.
      exists ([] : list (trigger_info (cio_I (fio cn)))); simpl; auto. }

    pose proof (ind (local_pred e)) as ind.
    autodimp ind hyp; eauto 3 with eo.
    pose proof (ind L S ls cn sm) as ind.
    repeat (autodimp ind hyp).
    exrepnd.

    unfold M_byz_state_ls_before_event in ind0.

    remember (M_byz_run_ls_before_event ls (local_pred e)) as run; symmetry in Heqrun.
    destruct run; simpl in *; eauto;[].

    unfold M_byz_run_M_trusted_ls_on_this_one_event.
    destruct m as [ls'|t]; simpl;[|].

    { applydup M_byz_run_ls_before_event_M_nt_preserves_subs in Heqrun as prp; auto; repnd;[].
      unfold map_untrusted_op in ind0; simpl in *.
      unfold M_byz_run_ls_on_this_one_event, M_break.

      pose proof (are_procs_ls_implies_ls_run_sub ls') as lsr; repeat (autodimp lsr hyp).
      pose proof (are_procs_ls_implies_ls_preserves_sub ls') as lps; repeat (autodimp lps hyp).
      pose proof (run_subs_leaves_of_find_sub ls ls' sm) as z.
      repeat (autodimp z hyp); eauto 3 with comp;[].
      exrepnd.
      applydup @find_sub_implies_state_of_component in z0; auto.
      rewrite z1 in ind0; simpl in ind0.
      applydup @find_sub_implies_in in z0.

      remember (trigger (local_pred e)) as trig; clear Heqtrig.
      destruct trig; simpl;[| |].

      { remember (sm_update (ls_main ls') (sm_state (ls_main ls')) d0 (ls_subs ls')) as w; symmetry in Heqw.
        repnd; simpl.
        applydup @are_procs_ls_implies_some in Heqw; auto;[].
        exrepnd; subst.
        autorewrite with comp.

        pose proof (lsr (sm_state (ls_main ls')) d0) as lsr.
        pose proof (lps (sm_state (ls_main ls')) d0 (ls_subs ls')) as lps.
        autodimp lps hyp; eauto 3 with comp.
        unfold M_break in lps; split_pair.
        rewrite Heqw in lsr; simpl in lsr.
        rewrite Heqw in lps; simpl in lps.

        apply lsr in z2; auto; autorewrite with comp; auto; exrepnd;[].
        dup z3 as v.
        apply (state_of_components_upd_ls_main_state_and_subs_if_in s ls') in v; eauto; eauto 3 with comp;[].
        rewrite v; simpl.

        pose proof (run_sm_on_inputs_app l0 l1 sm (ls_subs ls)) as xx.
        split_pair.
        erewrite (eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf l1 _ _ (fst (run_sm_on_inputs sm l0 (ls_subs ls))));
          autorewrite with comp; auto;[].
        rewrite <- xx; clear xx.

        exists (map (fun x => trigger_info_data x) (l0 ++ l1)).

        pose proof (run_sm_on_byz_inputs_as_run_sm_on_inputs
                      cn L (l0 ++ l1) sm (ls_subs ls)) as xx.
        autodimp xx hyp; eauto 3 with comp;[].

        remember (run_sm_on_inputs sm (l0 ++ l1) (ls_subs ls)) as rn.
        symmetry in Heqrn; repnd; simpl.
        simpl in xx; rewrite xx; clear xx; simpl; auto. }

      { dup trust as trust'.
        unfold is_trusted_ls in trust'.
        erewrite <- (similar_subs_preserves_is_trusted L cn) in trust';[|eauto].

        exists (snoc (map (fun x => trigger_info_data x) l0) trigger_info_arbitrary).
        pose proof (run_sm_on_byz_inputs_as_run_sm_on_inputs_app
                      cn L l0 [trigger_info_arbitrary] sm (ls_subs ls)) as h.
        remember (run_sm_on_inputs sm l0 (ls_subs ls)) as rn; symmetry in Heqrn.
        repnd; simpl in *.
        rewrite <- snoc_as_app in h.
        rewrite h; clear h.

        unfold byz_run_sm_on_byz_inputs; simpl.
        applydup is_trusted_implies_find_trusted2 in trust'; exrepnd.
        unfold find_sub in z0.
        rewrite trust'0 in z0.
        inversion z0; subst sm0.

        rewrite trust'1; simpl.
        rewrite (to_trusted_eq _ eqn); simpl; auto. }

      { dup trust as trust'.
        unfold is_trusted_ls in trust'.
        erewrite <- (similar_subs_preserves_is_trusted L cn) in trust';[|eauto].

        exists (snoc (map (fun x => trigger_info_data x) l0) (trigger_info_trusted i)).
        pose proof (run_sm_on_byz_inputs_as_run_sm_on_inputs_app
                      cn L l0 [trigger_info_trusted i] sm (ls_subs ls)) as h.
        remember (run_sm_on_inputs sm l0 (ls_subs ls)) as rn; symmetry in Heqrn.
        repnd; simpl in *.
        rewrite <- snoc_as_app in h.
        rewrite h; clear h.

        unfold byz_run_sm_on_byz_inputs; simpl.
        applydup is_trusted_implies_find_trusted2 in trust'; exrepnd.
        unfold find_sub in z0.
        rewrite trust'0 in z0.
        inversion z0; subst sm0.

        rewrite trust'1; simpl.
        rewrite (to_trusted_eq _ eqn); simpl; auto. } }

    { simpl in *.
      remember (trigger (local_pred e)) as trig.
      destruct trig; simpl;[| |];
        try (complete (exists l; rewrite ind0; simpl; auto));[].

      exists (snoc l (trigger_info_trusted i)).
      remember (sm_update (tsm_sm t) (state_of_trusted t) i []) as z; symmetry in Heqz.
      simpl in *; repnd.
      apply map_untrusted_op_Some_M_t_implies in ind0.

      rewrite snoc_as_app.
      remember (run_sm_on_byz_inputs sm l (ls_subs ls)) as w; symmetry in Heqw; repnd; simpl in *; subst.
      applydup (run_sm_on_byz_inputs_as_run_sm_on_inputs_app_trusted
                  l [trigger_info_trusted i] sm) in Heqw; simpl in *.
      rewrite Heqw0; clear Heqw0.
      rewrite Heqz; auto. }
  Qed.

  Definition unit_update : M_Update 0 (msg_comp_name 1) unit :=
    fun s m => interp_s_proc ([R] (s,[])).

  Definition unit_sm : n_proc_at 0 (msg_comp_name 1) :=
    build_mp_sm unit_update tt.

  Definition unit_ls : MLocalSystem 0 1 :=
    MkLocalSystem
      unit_sm
      [].

  Lemma are_procs_unit_ls : are_procs_ls unit_ls.
  Proof.
    split; simpl.
    { eexists; introv; unfold proc2upd;  reflexivity. }
    { introv i; simpl in *; repndors; subst; tcsp; simpl;
        eexists; introv; unfold proc2upd;  reflexivity. }
  Qed.
  Hint Resolve are_procs_unit_ls : comp.

  Lemma wf_unit_ls : wf_ls unit_ls.
  Proof.
    unfold wf_ls, wf_procs; simpl.
    dands; try (complete (introv xx; repndors; tcsp; ginv));[].
    constructor; simpl; tcsp; try (complete (introv xx; repndors; tcsp; ginv)).
  Qed.
  Hint Resolve wf_unit_ls : comp.

  Lemma M_run_ls_before_event_unit_ls :
    forall {eo : EventOrdering} (e : Event) ls,
      M_run_ls_before_event unit_ls e = Some ls
      -> ls = unit_ls.
  Proof.
    intros eo e; induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_run_ls_before_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; ginv.

    { inversion h; subst; GC; simpl; tcsp. }

    apply map_option_Some in h; exrepnd; rev_Some.
    apply ind in h1; eauto 3 with eo; subst.
    apply map_option_Some in h0; exrepnd; rev_Some.
    simpl in *.
    unfold M_break, unit_update in h1; simpl in *; ginv.
  Qed.

  Lemma sm_halted_update_state :
    forall {L S} (a : n_proc_at L S) x,
      sm_halted (update_state a x) = sm_halted a.
  Proof.
    introv; tcsp.
  Qed.
  Hint Rewrite @sm_halted_update_state : comp.

  Lemma M_byz_run_ls_on_this_one_event_M_nt_implies_similar_sms_at :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : MLocalSystem L S),
      M_byz_run_ls_on_this_one_event ls1 e = Some (M_nt ls2)
      -> similar_sms_at (ls_main ls1) (ls_main ls2).
  Proof.
    introv run.
    unfold M_byz_run_ls_on_this_one_event in run; simpl in *.
    remember (trigger e) as trig; clear Heqtrig.
    destruct trig; simpl in *;[| |];
      try (complete (apply option_map_Some in run; exrepnd; ginv));[].

    unfold M_break in run.
    dest_cases w; symmetry in Heqw; repnd; simpl in *.
    apply option_map_Some in run; exrepnd; subst; simpl in *.
    rename_hyp_with @M_nt mnt.
    inversion mnt; subst; simpl in *; clear mnt.
    destruct ls1 as [main subs]; simpl in *.
    unfold similar_sms_at; autorewrite with comp; dands; auto.
  Qed.

  Lemma M_byz_run_ls_before_event_M_nt_implies_similar_sms_at :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : MLocalSystem L S),
      M_byz_run_ls_before_event ls1 e = Some (M_nt ls2)
      -> similar_sms_at (ls_main ls1) (ls_main ls2).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv run.
    rewrite M_byz_run_ls_before_event_unroll in run.

    destruct (dec_isFirst e) as [d|d]; ginv; auto;[|].
    { dands; eauto 3 with comp. }

    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo;[].
    pose proof (ind L S ls1) as ind.

    apply map_option_Some in run; exrepnd.
    symmetry in run0.
    destruct a as [ls'|t]; simpl in *; ginv;[].

    apply ind in run1; auto;[]; repnd; clear ind.

    apply M_byz_run_ls_on_this_one_event_M_nt_implies_similar_sms_at in run0; eauto 3 with comp.
  Qed.

  Lemma M_run_ls_before_event_implies_similar_sms_at :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : MLocalSystem L S),
      M_run_ls_before_event ls1 e = Some ls2
      -> similar_sms_at (ls_main ls1) (ls_main ls2).
  Proof.
    introv run.
    apply M_run_ls_before_event_M_byz_run_ls_before_event in run.
    apply M_byz_run_ls_before_event_M_nt_implies_similar_sms_at in run; tcsp.
  Qed.

  Lemma n_procs_0 :
    forall (l : n_procs 0), l = [].
  Proof.
    induction l; tcsp.
    destruct a; simpl in *; tcsp.
  Qed.

  Lemma decr_n_procs_0 :
    forall (l : n_procs 0), decr_n_procs l = [].
  Proof.
    introv; rewrite (n_procs_0 l); simpl; auto.
  Qed.
  Hint Rewrite decr_n_procs_0 : comp.

  Lemma M_byz_run_ls_on_this_one_event_unit_ls :
    forall {eo : EventOrdering} (e : Event) ls,
      M_byz_run_ls_on_this_one_event unit_ls e = Some ls
      -> ls = M_nt unit_ls.
  Proof.
    introv h.
    unfold M_byz_run_ls_on_this_one_event in h; simpl in *.
    unfold if_trigger_info_data in h.
    remember (trigger e) as trig; destruct trig; simpl in *;
      unfold M_break in h; simpl in *; ginv.
  Qed.

  Lemma M_byz_run_ls_before_event_unit_ls :
    forall {eo : EventOrdering} (e : Event) ls,
      M_byz_run_ls_before_event unit_ls e = Some ls
      -> ls = M_nt unit_ls.
  Proof.
    intros eo e; induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_byz_run_ls_before_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; ginv.

    { inversion h; subst; GC; simpl; tcsp. }

    apply map_option_Some in h; exrepnd; rev_Some.
    apply ind in h1; eauto 3 with eo; subst.
    unfold M_byz_run_M_trusted_ls_on_this_one_event in *; simpl in *.
    eapply M_byz_run_ls_on_this_one_event_unit_ls; eauto.
  Qed.

  Lemma M_byz_run_ls_on_event_unit_ls :
    forall {eo : EventOrdering} (e : Event) ls,
      M_byz_run_ls_on_event unit_ls e = Some ls
      -> ls = M_nt unit_ls.
  Proof.
    introv run.
    rewrite M_byz_run_ls_on_event_unroll2 in run; apply map_option_Some in run; exrepnd; rev_Some.
    apply M_byz_run_ls_before_event_unit_ls in run1; subst; simpl in *.
    eapply M_byz_run_ls_on_this_one_event_unit_ls; eauto.
  Qed.

  Lemma M_run_ls_on_event_unit_ls :
    forall {eo : EventOrdering} (e : Event) ls,
      M_run_ls_on_event unit_ls e = Some ls
      -> ls = unit_ls.
  Proof.
    introv run.
    rewrite M_run_ls_on_event_unroll2 in run; apply map_option_Some in run; exrepnd; rev_Some.
    apply M_run_ls_before_event_unit_ls in run1; subst; simpl in *.
    apply map_option_Some in run0; exrepnd; rev_Some.
    simpl in *.
    unfold M_break, unit_update in run1; simpl in *; ginv.
  Qed.

End ComponentSM2.


Hint Resolve similar_procs_preserves_is_proc_n_nproc : comp.
Hint Resolve similar_subs_preserves_are_procs_n_procs : comp.
Hint Resolve is_proc_n_nproc_select_n_nproc_decr_n_nproc : comp.
Hint Resolve are_procs_n_procs_select_n_procs_decr_n_procs : comp.
Hint Resolve sm2level_le_pred : comp.
Hint Resolve implies_is_proc_n_proc_at_sm2at : comp.
Hint Resolve similar_sms_incr_pred_n_proc : comp.
Hint Resolve similar_subs_replace_sub : comp.
Hint Resolve similar_subs_replace_subs : comp.
Hint Resolve similar_sms_update_state_m : comp.
Hint Resolve similar_subs_replace_name_update_state_m_find : comp.
Hint Resolve wf_procs_replace_sub : comp.
Hint Resolve in_replace_sub_if_diff : comp.
Hint Resolve in_implies_in_proc_names : comp.
Hint Resolve implies_similar_subs_replace_sub : comp.
Hint Resolve similar_subs_preserves_wf_procs : comp.
Hint Resolve name_of_select_n_nproc : comp.
Hint Resolve wf_procs_select_n_procs : comp.
Hint Resolve wf_procs_decr_n_procs : comp.
Hint Resolve implies_wf_procs_replace_subs : comp.
Hint Resolve wf_procs_replace_name : comp.
Hint Resolve name_of_raise_to_n_nproc : comp.
Hint Resolve implies_wf_procs_raise_to_n_procs : comp.
Hint Resolve are_procs_ls_implies_ls_preserves_sub : comp.
Hint Resolve find_name_implies_in_procs_names : comp.
Hint Resolve implies_is_proc_n_proc_update_state_m : comp.
Hint Resolve in_replace_name_update_state_m_implies_is_proc_n_proc : comp.
Hint Resolve raise_to_n_proc_preserves_is_proc_n_proc : comp.
Hint Resolve raise_to_n_nproc_preserves_is_proc_n_nproc : comp.
Hint Resolve raise_to_n_procs_preserves_proc : comp.
Hint Resolve are_procs_n_procs_fst_interp_proc : comp.
Hint Resolve wf_procs_replace_subs : comp.
Hint Resolve wf_procs_fst_interp_proc : comp.
Hint Resolve run_subs_leaves_refl : comp.
Hint Resolve are_procs_n_procs_nil : comp.
Hint Resolve wf_procs_nil : comp.
Hint Resolve implies_in_replace_name : comp.
Hint Resolve select_n_nproc_preserves_is_proc_n_nproc : comp.
Hint Resolve select_n_procs_preserves_are_procs_n_procs : comp.
Hint Resolve select_n_proc_S_incr_implies_level : comp.
Hint Resolve implies_in_replace_sub_left : comp.
Hint Resolve implies_in_replace_subs_left : comp.
Hint Resolve implies_in_replace_subs_right : comp.
Hint Resolve implies_select_n_proc_update_state_m : comp.
Hint Resolve implies_select_n_proc_update_state_op_m : comp.
Hint Resolve run_subs_leaves_trans : comp.
Hint Resolve similar_sms_at_update_state : comp.
Hint Resolve find_name_implies_in : comp.
Hint Resolve in_implies_find_name : comp.
Hint Resolve wf_ls_implies_wf_procs : comp.
Hint Resolve are_procs_ls_find_sub : comp.
Hint Resolve implies_is_proc_n_proc_update_state_op_m : comp.
Hint Resolve are_procs_unit_ls : comp.
Hint Resolve wf_unit_ls : comp.


Hint Rewrite @interp_s_proc_as : comp.
Hint Rewrite @select_n_proc_trivial : comp.
Hint Rewrite @select_n_procs_trivial : comp.
Hint Rewrite @lift_n_procs_0 : comp.
Hint Rewrite @mapOption_fun_Some : list.
Hint Rewrite @mapOption_fun_None : list.
Hint Rewrite @raise_to_n_proc_trivial : comp.
Hint Rewrite @raise_to_n_procs_trivial : comp.
Hint Rewrite @sm_update_sm2at : comp.
Hint Rewrite @raise_to_n_procs_nil : comp.
Hint Rewrite @raise_to_n_procs_cons : comp.
Hint Rewrite @select_n_procs_nil : comp.
Hint Rewrite @select_n_procs_cons : comp.
Hint Rewrite @proc_names_replace_sub : comp.
Hint Rewrite @wf_procs_replace_name_implies : comp.
Hint Rewrite @sm2level_update_state_m : comp.
Hint Rewrite @sm2level_update_state_op_m : comp.
Hint Rewrite @run_sm_on_inputs_preserves_sm2level : comp.
Hint Rewrite @select_n_proc_0 : comp.
Hint Rewrite @select_n_procs_0 : comp.
Hint Rewrite @reduces_option_map_some : comp.
Hint Rewrite @reduce_map_op_untrusted_op_some : comp.
Hint Rewrite @reduce_map_op_untrusted_some : comp.
Hint Rewrite @reduce_map_untrusted_op_M_nt : comp.
Hint Rewrite @sm2state_update_state_m : comp.
Hint Rewrite @ls_subs_MkLocalSystem : comp.
Hint Rewrite @reduce_map_option_some : comp.
Hint Rewrite @procs_names_replace_name : comp.
Hint Rewrite @sm_halted_update_state : comp.
Hint Rewrite @decr_n_procs_0 : comp.


Notation "a [>>=] f" := (PROC_BIND a f) (at level 80).
Notation "[R] a" := (PROC_RET a) (at level 80).
Notation "a [C] b" := (PROC_CALL a b) (at level 80).
Notation "a [>>>=] f" := (proc_bind_pair a f) (at level 80).
