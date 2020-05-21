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
  Context { iot : @IOTrustedFun }.

  Context { base_fun_io       : baseFunIO }.
  Context { base_state_fun    : baseStateFun }.
  Context { trusted_state_fun : trustedStateFun }.



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

  Definition TESTmain_sm : n_proc 2 TESTmain :=
    build_m_sm TESTmain_upd2 tt.

  Definition TESTls : LocalSystem _ 1 :=
      [
        MkPProc TESTmain  TESTmain_sm,
        MkPProc TESTcompa (incr_n_proc TESTcompa_sm),
        MkPProc TESTcompb (incr_n_proc TESTcompb_sm)
      ].

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

  Definition are_procs_sys {f} (sys : M_USystem f) :=
    forall n, are_procs_n_procs (sys n).

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
  Qed.

  Lemma similar_sms_preserves_is_proc_n_proc :
    forall cn n (p1 p2 : n_proc n cn),
      similar_sms p1 p2
      -> is_proc_n_proc p1
      -> is_proc_n_proc p2.
  Proof.
    introv sim isp.
    unfold is_proc_n_proc in *; exrepnd.
    exists p.
    introv.
    pose proof (isp0 s i) as isp0.
    applydup similar_sms_implies_eq_sm2levels in sim.
    symmetry in sim0.
    pose proof (similar_sms_implies_eq_sm2update cn n p1 p2 sim0) as q.
    repeat (autodimp q hyp).
    rewrite q in isp0; clear q sim.

    remember (sm2level p1) as n1; clear Heqn1.
    subst; simpl in *; auto.
  Qed.
  Hint Resolve similar_sms_preserves_is_proc_n_proc : comp.

  Lemma similar_procs_preserves_is_proc_n_nproc :
    forall n (p1 p2 : n_nproc n),
      similar_procs p1 p2
      -> is_proc_n_nproc p1
      -> is_proc_n_nproc p2.
  Proof.
    introv sim isp.
    destruct p1 as [cn1 p1], p2 as [cn2 p2]; simpl in *.
    applydup @similar_procs_implies_same_name in sim; simpl in *; subst.
    apply similar_procs_implies_same_proc in sim; eauto 3 with comp.
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

  (*Fixpoint halt_machine_m {n} {cn} :
    forall (sm : n_proc n cn), n_proc n cn :=
    match n with
    | 0 => fun sm => match sm with end
    | S m =>
      fun sm =>
        match sm with
        | sm_or_at p => sm_or_at (halt_machine p)
        | sm_or_sm q => sm_or_sm (halt_machine_m q)
        end
    end.*)

  (*Definition update_state_or_halt_m {n} {cn} (sm : n_proc n cn) sop : n_proc n cn :=
    match sop with
    | Some s => update_state_m sm s
    | None => halt_machine_m sm
    end.*)

  Definition lift_eq_rev {n j k} (e : n = S (j + k)) : S j + k = n.
  Proof.
    introv; subst; simpl; auto.
  Defined.

  Definition lift_n_procs_eq {n j k} (e : n = S (j + k)) (l : n_procs k) : n_procs n :=
    eq_rect _ _ (lift_n_procs (S j) l) _ (lift_eq_rev e).

  Lemma incr_n_procs_app :
    forall {n} (l k : n_procs n),
      incr_n_procs (l ++ k) = incr_n_procs l ++ incr_n_procs k.
  Proof.
    introv; unfold incr_n_procs; rewrite map_app; auto.
  Qed.

  Lemma incr_n_procs_lift_n_procs :
    forall j {n} (l : n_procs n),
      incr_n_procs (lift_n_procs j l) = lift_n_procs (S j) l.
  Proof.
    introv; unfold incr_n_procs, lift_n_procs.
    rewrite map_map.
    apply map_ext; introv.
    destruct a as [cn p]; simpl in *; auto.
  Qed.
  Hint Rewrite incr_n_procs_lift_n_procs : comp.

  Lemma remove_names_app :
    forall {n} (l k : list CompName) (subs : n_procs n),
      remove_names subs (l ++ k)
      = remove_names (remove_names subs l) k.
  Proof.
    induction l; introv; simpl in *; auto.
  Qed.

  Lemma get_names_app :
    forall {n} (l k : n_procs n),
      get_names (l ++ k)
      = get_names l ++ get_names k.
  Proof.
    introv; unfold get_names; rewrite map_app; auto.
  Qed.

  Lemma remove_subs_app :
    forall {n m} (l k : n_procs m) (subs : n_procs n),
      remove_subs subs (l ++ k)
      = remove_subs (remove_subs subs l) k.
  Proof.
    introv; unfold remove_subs; simpl.
    rewrite get_names_app.
    rewrite remove_names_app; auto.
  Qed.

  Lemma remove_name_swap :
    forall {n} (l : n_procs n) a b,
      remove_name (remove_name l a) b
      = remove_name (remove_name l b) a.
  Proof.
    induction l; introv; simpl; auto.
    repeat (dest_cases w; subst; simpl in *; tcsp).
    rewrite IHl; auto.
  Qed.

  Lemma remove_names_remove_name_swap :
    forall k {n} a (l : n_procs n),
      remove_names (remove_name l a) k
      = remove_name (remove_names l k) a.
  Proof.
    induction k; introv; simpl; auto.
    rewrite (IHk _ a l).
    rewrite (IHk _ a).
    rewrite (IHk _ a0).
    rewrite remove_name_swap; auto.
  Qed.

  Lemma remove_names_swap :
    forall {n} (l k : list CompName) (subs : n_procs n),
      remove_names subs (l ++ k)
      = remove_names subs (k ++ l).
  Proof.
    induction l; introv; simpl in *; auto.
    { rewrite app_nil_r; auto. }
    { rewrite IHl.
      repeat rewrite remove_names_app.
      simpl; f_equal.
      rewrite remove_names_remove_name_swap; auto. }
  Qed.

  Lemma remove_subs_swap :
    forall {n m} (l k : n_procs m) (subs : n_procs n),
      remove_subs subs (l ++ k)
      = remove_subs subs (k ++ l).
  Proof.
    introv; unfold remove_subs; simpl.
    repeat rewrite get_names_app.
    rewrite remove_names_swap; auto.
  Qed.

  Lemma get_names_lift_n_procs :
    forall m {k} (l : n_procs k),
      get_names (lift_n_procs m l) = get_names l.
  Proof.
    introv; unfold get_names.
    induction l; introv; simpl; auto.
    rewrite IHl; auto.
    destruct a as [cn p]; simpl; auto.
  Qed.

  Lemma remove_subs_lift_n_procs :
    forall {n} (subs : n_procs n) m {k} (l : n_procs k),
      remove_subs subs (lift_n_procs m l) = remove_subs subs l.
  Proof.
    introv; unfold remove_subs.
    rewrite get_names_lift_n_procs; auto.
  Qed.
  Hint Rewrite @remove_subs_lift_n_procs : comp.

(*  Lemma app_m_proc_some :
    forall {n} {cn}
           (sm : n_proc n cn)
           (i  : cio_I (fio cn)),
    exists (k : nat) (j : nat) (p : n_proc_at k cn) (e : n = S (j + k)),
    forall (subs : n_procs n),
      app_m_proc sm i subs
      = match sm_update p (sm_state p) i (select_n_procs k subs) with
        | (subs', (sop, out)) =>
          (lift_n_procs_eq e subs' ++ remove_subs subs subs',
           (update_state_or_halt_m sm sop, out))
        end.
  Proof.
    induction n; introv; simpl in *; ginv; tcsp;[].
    destruct sm as [sm|sm].

    { exists n 0 sm (eq_refl (S n)).
      introv.
      unfold n_proc in *.
      remember (sm_update sm (sm_state sm) i (select_n_procs n subs)) as w;
        symmetry in Heqw.
      repnd.

      unfold lift_n_procs_eq; simpl; autorewrite with comp in *.
      unfold lift_M_1, M_on_decr, app_n_proc_at, bind_pair, bind; simpl.
      fold M_StateMachine in *.
      fold n_proc in *.
      rewrite decr_n_procs_as_select_n_procs.
      rewrite Heqw; simpl; auto.
      destruct w1; simpl; tcsp. }

    { pose proof (IHn cn sm i) as IHn; exrepnd.
      exists k (S j) p (eq_S _ _ e).
      introv.
      pose proof (IHn1 (select_n_procs n subs)) as ap0.
      rewrite select_n_procs_select_n_procs_le in ap0; auto; try omega;[].
      remember (sm_update p (sm_state p) i (select_n_procs k subs)) as w.
      symmetry in Heqw; repnd.

      unfold lift_n_procs_eq; simpl; autorewrite with comp in *.
      remember (app_m_proc sm i) as ap.
      subst n.
      simpl.
      unfold lift_M_2, M_on_decr, bind_pair, bind, M_on_pred.
      simpl in *.
      rewrite <- decr_n_procs_as_select_n_procs in ap0.
      rewrite ap0; auto; simpl.
      f_equal;[|].

      { unfold lift_n_procs_eq, update_subs; simpl.
        rewrite incr_n_procs_app.
        unfold p_procs in *; fold (n_nproc k) in *; fold (n_procs k) in *.
        pose proof (incr_n_procs_lift_n_procs (S j) w0) as h.
        simpl in *; rewrite h.
        rewrite <- app_assoc; f_equal.
        rewrite remove_subs_app.
        pose proof (remove_subs_lift_n_procs subs (S j) w0) as q.
        simpl in *; rewrite q.

  Qed.*)

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
      sm2level sm <= pred n.
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct sm as [sm|sm]; auto; tcsp;[].
    pose proof (IHn sm) as IHn; try omega.
  Qed.
  Hint Resolve sm2level_le_pred : comp.

  Lemma sm2level_lt :
    forall cn n (sm : n_proc n cn),
      sm2level sm < n.
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct sm as [sm|sm]; auto; tcsp;[].
    pose proof (IHn sm) as IHn; try omega.
  Qed.
  Hint Resolve sm2level_lt : comp.

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

  Lemma raise_to_n_procs_as_incr_n_procs :
    forall {n} (l : n_procs n),
      raise_to_n_procs (S n) l
      = incr_n_procs l.
  Proof.
    unfold raise_to_n_procs, incr_n_procs; induction l; introv; simpl; auto.
    destruct a as [cn p]; simpl.
    destruct (deq_nat n (S n)); try omega.
    rewrite IHl; autorewrite with comp; simpl; auto.
  Qed.

  Lemma option_map_None :
    forall {A B} (f : A -> B) (o : option A),
      option_map f o = None
      <-> o = None.
  Proof.
    destruct o; simpl in *; introv; tcsp; split; intro h; tcsp.
  Qed.

  Lemma incr_n_procs_raise_to_n_procs :
    forall j {n} (l : n_procs n),
      n <= j
      -> incr_n_procs (raise_to_n_procs j l) = raise_to_n_procs (S j) l.
  Proof.
    unfold incr_n_procs, raise_to_n_procs.
    induction l; introv lej; simpl; tcsp.
    destruct a as [cn p]; simpl in *.
    repeat (dest_cases w); subst; simpl in *; tcsp; ginv; rev_Some; try omega;
      try (rewrite IHl; auto; clear IHl).
    { apply option_map_Some in Heqw; exrepnd; subst; simpl in *.
      apply option_map_Some in Heqw0; exrepnd; subst; simpl in *.
      apply option_map_Some in Heqw0; exrepnd; subst; simpl in *.
      rewrite Heqw2 in Heqw0; ginv. }
    { apply option_map_Some in Heqw; exrepnd; subst; simpl in *.
      symmetry in Heqw0.
      apply option_map_None in Heqw0.
      apply option_map_None in Heqw0.
      rewrite Heqw2 in Heqw0; ginv. }
    { symmetry in Heqw.
      apply option_map_None in Heqw.
      apply option_map_Some in Heqw0; exrepnd; subst; simpl in *.
      apply option_map_Some in Heqw0; exrepnd; subst; simpl in *.
      rewrite Heqw in Heqw0; ginv. }
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

  Lemma get_names_raise_to_n_procs :
    forall m {k} (l : n_procs k),
      k <= m
      -> get_names (raise_to_n_procs m l) = get_names l.
  Proof.
    unfold get_names, raise_to_n_procs.
    induction l; introv lem; simpl; auto.
    destruct a as [cn p]; simpl.
    remember (raise_to_n_proc m p) as r; symmetry in Heqr; destruct r; simpl;
      rewrite IHl; auto.
    apply raise_to_n_proc_none_implies in Heqr; try omega.
  Qed.

  Lemma remove_subs_raise_to_n_procs :
    forall {n} (subs : n_procs n) m {k} (l : n_procs k),
      k <= m
      -> remove_subs subs (raise_to_n_procs m l) = remove_subs subs l.
  Proof.
    introv lem; unfold remove_subs.
    rewrite get_names_raise_to_n_procs; auto.
  Qed.

  Definition lower_head (i : nat) {n} (l : n_procs n) : bool :=
    match l with
    | [] => true
    | p :: _ => sm2level (pp_proc p) <=? i
    end.

  Fixpoint ordered_subs {n} (l : n_procs n) : bool :=
    match l with
    | [] => true
    | p1 :: rest =>
      (lower_head (sm2level (pp_proc p1)) rest)
        && ordered_subs rest
    end.

  Fixpoint all_lower (i : nat) {n} (l : n_procs n) : bool :=
    match l with
    | [] => true
    | p :: k => (sm2level (pp_proc p) <=? i) && all_lower i k
    end.

  Lemma implies_all_lower :
    forall {n} (l : n_procs n) i,
      lower_head i l = true
      -> ordered_subs l = true
      -> all_lower i l = true.
  Proof.
    induction l; introv h q; simpl in *; auto.
    allrw andb_true; repnd.
    allrw Nat.leb_le.
    dands; auto.
    apply IHl; auto.
    destruct l; simpl in *; allrw Nat.leb_le; auto; try omega.
  Qed.
  Hint Resolve implies_all_lower : comp.

  Definition no_dup_subs {n} (l : n_procs n) : bool :=
    norepeatsb CompNameDeq (get_names l).

  Fixpoint remove_fst {A} (deq : Deq A) (x : A) (l : list A) : list A :=
    match l with
    | [] => []
    | y :: tl => if deq x y then tl else y :: remove_fst deq x tl
    end.

  Lemma remove_names_cons :
    forall (l : list CompName) {n} p (ps : n_procs n),
      remove_names (p :: ps) l
      = if in_dec CompNameDeq (pp_name p) l
        then remove_names ps (remove_fst CompNameDeq (pp_name p) l)
        else p :: remove_names ps l.
  Proof.
    induction l; introv; simpl; tcsp.
    repeat dest_cases w; repndors; subst; simpl in *; tcsp;
      rewrite IHl; dest_cases w.
    apply not_or in n1; repnd; tcsp.
  Qed.

  Lemma subset_get_names_decr_n_procs :
    forall {n} (l : n_procs n),
      subset (get_names (decr_n_procs l)) (get_names l).
  Proof.
    introv h.
    apply in_map_iff in h; exrepnd; subst.
    apply in_mapOption in h0; exrepnd.
    apply in_map_iff.
    exists a; dands; auto.
    destruct a as [cn p]; simpl in *.
    dest_cases w; ginv; rev_Some; simpl in *.
  Qed.

  Lemma get_names_remove_name :
    forall {n} (l : n_procs n) a,
      get_names (remove_name l a)
      = remove_fst CompNameDeq a (get_names l).
  Proof.
    unfold get_names; induction l; introv; simpl; tcsp.
    repeat dest_cases w; simpl.
    rewrite IHl; tcsp.
  Qed.

  Lemma remove_name_trivial :
    forall {n} (l : n_procs n) a,
      ~ In a (get_names l)
      -> remove_name l a = l.
  Proof.
    induction l; introv ni; simpl in *; tcsp.
    apply not_or in ni; repnd.
    dest_cases w.
    rewrite IHl; auto.
  Qed.

  Lemma remove_name_twice :
    forall {n} (l : n_procs n) a,
      no_dup_subs l = true
      -> remove_name (remove_name l a) a
         = remove_name l a.
  Proof.
    induction l; introv nodup; simpl; auto.
    unfold no_dup_subs in *; simpl in *.
    repeat (dest_cases w; subst; simpl in *; tcsp).
    { rewrite remove_name_trivial; auto. }
    rewrite IHl; auto.
  Qed.

  Lemma in_remove_fst_implies :
    forall {A} deq a b (l : list A),
      In a (remove_fst deq b l)
      -> In a l.
  Proof.
    induction l; introv h; simpl in *; tcsp.
    dest_cases w.
  Qed.

  Lemma implies_norepeatsb_remove_fst :
    forall {A} deq a (l : list A),
      norepeatsb deq l = true
      -> norepeatsb deq (remove_fst deq a l) = true.
  Proof.
    induction l; introv h; simpl in *; tcsp.
    repeat (dest_cases w; simpl in *; tcsp).
    apply in_remove_fst_implies in i; tcsp.
  Qed.

  Lemma implies_no_dub_subs_remove_names :
    forall l {n} (subs : n_procs n),
      no_dup_subs subs = true
      -> no_dup_subs (remove_names subs l) = true.
  Proof.
    unfold no_dup_subs.
    induction l; introv h; simpl in *; auto.
    rewrite remove_names_remove_name_swap.
    rewrite get_names_remove_name.
    apply implies_norepeatsb_remove_fst; tcsp.
  Qed.
  Hint Resolve implies_no_dub_subs_remove_names : comp.

  Lemma all_lower_implies_lower_head :
    forall {n} (l : n_procs n) (i : nat),
      all_lower i l = true
      -> lower_head i l = true.
  Proof.
    destruct l; introv h; simpl in *; tcsp.
    allrw andb_true; tcsp.
  Qed.
  Hint Resolve all_lower_implies_lower_head : comp.

  Lemma lower_head_remove_name :
    forall i {n} (l : n_procs n) a,
      all_lower i l = true
      -> lower_head i (remove_name l a) = true.
  Proof.
    induction l; introv h; simpl in *; tcsp.
    allrw andb_true; repnd.
    dest_cases w; simpl in *; allrw Nat.leb_le; tcsp; eauto 3 with comp.
  Qed.
  Hint Resolve lower_head_remove_name : comp.

  Lemma implies_ordered_subs_remove_name :
    forall {n} (subs : n_procs n) a,
      ordered_subs subs = true
      -> ordered_subs (remove_name subs a) = true.
  Proof.
    induction subs; introv h; simpl in *; auto.
    dest_cases w; simpl in *; allrw andb_true; repnd; dands; auto; eauto 3 with comp.
  Qed.
  Hint Resolve implies_ordered_subs_remove_name : comp.

  Lemma implies_ordered_subs_remove_names :
    forall l {n} (subs : n_procs n),
      ordered_subs subs = true
      -> ordered_subs (remove_names subs l) = true.
  Proof.
    induction l; introv h; simpl in *; auto.
    apply IHl; eauto 3 with comp.
  Qed.
  Hint Resolve implies_ordered_subs_remove_names : comp.

  Lemma remove_names_remove_name_remove_fst :
    forall l a {n} (subs : n_procs n),
      no_dup_subs subs = true
      -> remove_names (remove_name subs a) (remove_fst CompNameDeq a l)
         = remove_name (remove_names subs l) a.
  Proof.
    induction l; introv nodup; simpl; auto.
    dest_cases w; subst; simpl in *; tcsp.
    { repeat rewrite remove_names_remove_name_swap.
      rewrite remove_name_twice; auto.
      apply implies_no_dub_subs_remove_names; auto. }
    { rewrite remove_names_remove_name_swap.
      rewrite IHl; auto.
      repeat (rewrite remove_names_remove_name_swap).
      rewrite remove_name_swap; auto. }
  Qed.

  Lemma remove_subs_nested :
    forall {n} (subs : n_procs n) {m} (l : n_procs m) {j} (k : n_procs j),
      no_dup_subs subs = true
      -> remove_subs (remove_subs subs (remove_subs l k)) k
         = remove_subs (remove_subs subs l) k.
  Proof.
    unfold remove_subs; introv nodup.
    remember (get_names k) as K; clear HeqK.
    revert subs l nodup.
    induction K; introv nodup; simpl; auto.
    repeat rewrite <- remove_names_remove_name_swap.
    rewrite (remove_names_remove_name_swap K a l).
    rewrite get_names_remove_name.
    rewrite remove_names_remove_name_remove_fst; auto.
    repeat rewrite remove_names_remove_name_swap.
    rewrite IHK; auto.
  Qed.

  Lemma no_dup_subs_decr_n_procs :
    forall {n} (subs : n_procs n),
      no_dup_subs subs = true
      -> no_dup_subs (decr_n_procs subs) = true.
  Proof.
    unfold no_dup_subs, decr_n_procs; induction subs; introv h; simpl in *; tcsp.
    repeat (dest_cases w; simpl in *; tcsp; rev_Some).
    apply in_map_iff in i; exrepnd; subst; simpl in *.
    apply in_mapOption in i0; exrepnd.
    destruct n0.
    apply in_map_iff.
    exists a0; dands; auto.
    destruct a as [n1 p1]; simpl in *.
    destruct a0 as [n2 p2]; simpl in *.
    repeat (dest_cases w; ginv; rev_Some; simpl in *; subst).
    inversion Heqw; subst; simpl in *; auto.
  Qed.
  Hint Resolve no_dup_subs_decr_n_procs : comp.

  Lemma le_preserves_lower_head :
    forall i j {n} (subs : n_procs n),
      j <= i
      -> lower_head j subs = true
      -> lower_head i subs = true.
  Proof.
    introv h q.
    destruct subs; simpl in *; tcsp.
    allrw Nat.leb_le; try omega.
  Qed.
  Hint Resolve le_preserves_lower_head : comp.

  Lemma lower_head_decr_n_procs :
    forall {n} (subs : n_procs n) i,
      ordered_subs subs = true
      -> lower_head i subs = true
      -> lower_head i (decr_n_procs subs) = true.
  Proof.
    unfold decr_n_procs.
    induction subs; introv ord h; simpl in *; tcsp.
    allrw Nat.leb_le.
    allrw andb_true; repnd.
    unfold decr_n_procs; simpl.
    destruct a as [cn p]; simpl in *.
    destruct n; simpl in *; tcsp.
    destruct p; simpl in *; tcsp; allrw Nat.leb_le; auto.
    apply IHsubs; auto; eauto 3 with comp.
  Qed.
  Hint Resolve lower_head_decr_n_procs : comp.

  Lemma ordered_subs_decr_n_procs :
    forall {n} (subs : n_procs n),
      ordered_subs subs = true
      -> ordered_subs (decr_n_procs subs) = true.
  Proof.
    unfold decr_n_procs; induction subs; introv h; simpl in *; tcsp.
    repeat (dest_cases w; simpl in *; tcsp; rev_Some);
      allrw andb_true; repnd; tcsp.
    dands; tcsp.
    destruct a as [c1 p1], w as [c2 p2]; simpl in *.
    destruct n; simpl in *; tcsp.
    destruct p1; simpl in *; tcsp; ginv.
    apply Some_inj in Heqw.
    inversion Heqw; subst.
    apply decomp_p_nproc in Heqw; subst.
    apply (lower_head_decr_n_procs subs (sm2level p2)); auto.
  Qed.
  Hint Resolve ordered_subs_decr_n_procs : comp.

  Lemma incr_n_procs_remove_name :
    forall a {n} (subs : n_procs n),
      incr_n_procs (remove_name subs a)
      = remove_name (incr_n_procs subs) a.
  Proof.
    unfold incr_n_procs.
    induction subs; introv; simpl; auto.
    repeat (dest_cases w; subst; simpl in *; tcsp);
      destruct a0 as [x y]; simpl in *; tcsp.
  Qed.

  Lemma incr_n_procs_remove_subs :
    forall {m} (l : n_procs m) {n} (subs : n_procs n),
      incr_n_procs (remove_subs subs l)
      = remove_subs (incr_n_procs subs) l.
  Proof.
    unfold incr_n_procs, remove_subs.
    induction l; introv; simpl; auto.
    repeat rewrite remove_names_remove_name_swap.
    rewrite <- IHl.
    apply incr_n_procs_remove_name.
  Qed.

  Definition rm_highest_proc {n} {cn} : n_proc n cn -> option (n_proc n cn) :=
    match n with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | sm_or_at _ => None
               | sm_or_sm q => Some p
               end
    end.

  Definition rm_highest_nproc {n} (np : n_nproc n) : option (n_nproc n) :=
    match np with
    | MkPProc m p =>
      match rm_highest_proc p with
      | Some q => Some (MkPProc m q)
      | None => None
      end
    end.

  Definition rm_highest_procs {n} (ps : n_procs n) : n_procs n :=
    mapOption rm_highest_nproc ps.

  Definition keep_highest_proc {n} {cn} : n_proc n cn -> option (n_proc n cn) :=
    match n with
    | 0 => fun p => match p with end
    | S m => fun p =>
               match p with
               | sm_or_at _ => Some p
               | sm_or_sm q => None
               end
    end.

  Definition keep_highest_nproc {n} (np : n_nproc n) : option (n_nproc n) :=
    match np with
    | MkPProc m p =>
      match keep_highest_proc p with
      | Some q => Some (MkPProc m q)
      | None => None
      end
    end.

  Definition keep_highest_procs {n} (ps : n_procs n) : n_procs n :=
    mapOption keep_highest_nproc ps.

  Lemma incr_n_procs_decr_n_procs_as_rm_highest :
    forall {n} (subs : n_procs (S n)),
      incr_n_procs (decr_n_procs subs)
      = rm_highest_procs subs.
  Proof.
    unfold incr_n_procs, decr_n_procs, rm_highest_procs.
    induction subs; introv; simpl; auto.
    destruct a as [cn p]; simpl in *.
    destruct p; simpl in *; tcsp.
    rewrite IHsubs; auto.
  Qed.

  Lemma remove_subs_decr_n_procs_as_keep_highest_subs :
    forall {n} (subs : n_procs n),
      no_dup_subs subs = true
      -> remove_subs subs (decr_n_procs subs)
         = keep_highest_procs subs.
  Proof.
    unfold remove_subs, decr_n_procs, keep_highest_procs, no_dup_subs.
    induction subs; introv nodup; simpl in *; tcsp.
    destruct a as [cn p]; simpl in *.
    destruct n; simpl in *; tcsp.
    destruct p; simpl in *; tcsp;
      repeat (dest_cases w; simpl in *; tcsp).

    rewrite remove_names_cons; simpl.
    dest_cases w; simpl in *; tcsp.

    { apply in_map_iff in i; exrepnd; subst; simpl in *.
      apply in_mapOption in i0; exrepnd.
      destruct n0.
      apply in_map_iff; eexists; dands; eauto; auto.
      destruct a0 as [cn p], x, p; simpl in *; auto; ginv.
      inversion i1; subst; auto. }

    { rewrite IHsubs; auto. }
  Qed.

  Lemma rm_highest_procs_trivial :
    forall i {n} (l : n_procs (S n)),
      i < n
      -> all_lower i l = true
      -> rm_highest_procs l = l.
  Proof.
    unfold rm_highest_procs.
    induction l; introv ltn h; simpl in *; auto.
    allrw andb_true; repnd.
    allrw Nat.leb_le.
    destruct a as [cn' p']; simpl in *.
    destruct p'; simpl in *; tcsp; rewrite IHl; auto; clear IHl.
    destruct n; simpl in *; try omega.
  Qed.

  Lemma keep_highest_procs_nil :
    forall i {n} (l : n_procs (S n)),
      i < n
      -> all_lower i l = true
      -> keep_highest_procs l = [].
  Proof.
    unfold keep_highest_procs.
    induction l; introv ltn h; simpl in *; auto.
    allrw andb_true; repnd.
    allrw Nat.leb_le.
    destruct a as [cn' p'].
    destruct p'; simpl in *; tcsp; rewrite IHl; auto; clear IHl.
    destruct n; simpl in *; try omega.
  Qed.

  Lemma split_as_rm_highest_keep_highest :
    forall {n} (subs : n_procs n),
      ordered_subs subs = true
      -> no_dup_subs subs = true
      -> subs = keep_highest_procs subs ++ rm_highest_procs subs.
  Proof.
    unfold no_dup_subs, rm_highest_procs, keep_highest_procs.
    induction subs; introv ord nodup; simpl in *; tcsp.

    destruct a as [cn p].
    destruct n; simpl in *; tcsp;[].
    destruct p; simpl in *;
      allrw andb_true; repnd;
        repeat (dest_cases w; simpl in *; tcsp);
        try (complete (rewrite <- IHsubs; auto)).

    pose proof (rm_highest_procs_trivial (sm2level b) subs) as h; repeat (autodimp h hyp); eauto 3 with comp;[].
    unfold rm_highest_procs in h; rewrite h; clear h; simpl.
    pose proof (keep_highest_procs_nil (sm2level b) subs) as h; repeat (autodimp h hyp); eauto 3 with comp;[].
    unfold keep_highest_procs in h; rewrite h; clear h; simpl; auto.
  Qed.

  Lemma remove_name_split_if_no_dup :
    forall a {n} (l k : n_procs n),
      no_dup_subs (l ++ k) = true
      -> remove_name (l ++ k) a
         = remove_name l a ++ remove_name k a.
  Proof.
    unfold no_dup_subs.
    induction l; introv nodep; simpl in *; auto.
    destruct a0 as [cn p]; simpl in *.
    repeat (dest_cases w; subst; simpl in *; tcsp).

    { rewrite remove_name_trivial; auto.
      intro i; destruct n0; apply in_map_iff.
      apply in_map_iff in i; exrepnd; subst; simpl in *.
      exists x; dands; auto.
      apply in_app_iff; tcsp. }

    f_equal.
    apply IHl; auto.
  Qed.

  Lemma remove_subs_split_if_no_dup :
    forall {m} (u : n_procs m) {n} (l k : n_procs n),
      no_dup_subs (l ++ k) = true
      -> remove_subs (l ++ k) u
         = remove_subs l u ++ remove_subs k u.
  Proof.
    unfold no_dup_subs, remove_subs.
    induction u; introv nodep; simpl in *; auto.
    rewrite remove_name_split_if_no_dup; auto.
    rewrite IHu; auto.
    rewrite <- remove_name_split_if_no_dup; auto.
    rewrite get_names_remove_name.
    apply implies_norepeatsb_remove_fst; auto.
  Qed.

  Lemma app_m_proc_some2 :
    forall {n} {cn}
           (sm : n_proc n cn)
           (i  : cio_I (fio cn))
           (subs : n_procs n)
           (nod  : no_dup_subs subs = true)
           (ord  : ordered_subs subs = true),
      app_m_proc sm i subs
      = match sm2update sm (sm2state sm) i (select_n_procs (sm2level sm) subs) with
        | (subs', (sop, out)) =>
          (remove_subs subs subs' ++ raise_to_n_procs n subs',
           (option_map (update_state_m sm) sop, out))
        end.
  Proof.
    induction n; introv nodup ord; simpl in *; tcsp.
    destruct sm as [sm|sm].

    { unfold n_proc in *.
      fold M_StateMachine in *.
      fold n_proc in *.
      remember (sm_update sm (sm_state sm) i (select_n_procs n subs)) as w; symmetry in Heqw.
      repnd.

      unfold lift_n_procs_eq; simpl; autorewrite with comp in *.
      unfold lift_M_1, M_on_decr, app_n_proc_at, bind_pair, bind; simpl.
      rewrite decr_n_procs_as_select_n_procs.
      rewrite Heqw; simpl; auto.
      rewrite raise_to_n_procs_as_incr_n_procs.
      destruct w1; simpl; tcsp. }

    { pose proof (IHn cn sm i (select_n_procs n subs)) as IHn.
      pose proof (sm2level_le_pred _ _ sm) as lvl.
      rewrite select_n_procs_select_n_procs_le in IHn; auto; eauto 3 with comp; try omega;[].

      remember (sm2update sm (sm2state sm) i (select_n_procs (sm2level sm) subs)) as w.
      symmetry in Heqw; repnd.

      unfold lift_M_2, M_on_decr, bind_pair, bind, M_on_pred.
      simpl in *.

      rewrite <- decr_n_procs_as_select_n_procs in IHn.
      applydup @no_dup_subs_decr_n_procs in nodup.
      rewrite IHn; simpl; auto; clear IHn; eauto 3 with comp;
        try (complete (apply (ordered_subs_decr_n_procs subs); auto));[].

      unfold update_subs.
      rewrite incr_n_procs_app.
      rewrite incr_n_procs_raise_to_n_procs; auto; try omega;[].
      f_equal;[|destruct w1; simpl; auto];[].
      rewrite app_assoc; f_equal.
      rewrite remove_subs_app.
      rewrite remove_subs_raise_to_n_procs; try omega;[].
      rewrite incr_n_procs_remove_subs.
      pose proof (incr_n_procs_decr_n_procs_as_rm_highest subs) as h;
        simpl in *; rewrite h; clear h; auto.
      rewrite remove_subs_nested; auto.
      pose proof (remove_subs_decr_n_procs_as_keep_highest_subs subs) as h;
        simpl in *; rewrite h; clear h; auto.
      pose proof (split_as_rm_highest_keep_highest subs) as h.
      repeat (autodimp h hyp).
      rewrite <- remove_subs_split_if_no_dup; rewrite <- h; auto. }
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
  Hint Resolve are_procs_n_procs_find_name : comp.

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

(*  Lemma similar_subs_replace_sub :
    forall n cn (p1 p2 : n_proc n cn) (subs1 subs2 : n_procs n),
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
  Qed.
  Hint Resolve similar_subs_replace_sub : comp.*)

(*  Lemma similar_subs_replace_subs :
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
  Hint Resolve similar_subs_replace_subs : comp.*)

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
    destruct n; [simpl in *; tcsp|].
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

  Definition wf_procs {n} (subs : n_procs n) : Prop :=
    no_dup_subs subs && ordered_subs subs = true.

  Lemma wf_procs_cons :
    forall n p (subs : n_procs n),
      wf_procs (p :: subs)
      <->
      (
        ~In (pp_name p) (get_names subs)
        /\ lower_head (sm2level (pp_proc p)) subs = true
        /\ wf_procs subs
      ).
  Proof.
    introv; unfold wf_procs, no_dup_subs; simpl.
    allrw andb_true.
    dest_cases w; split; intro h; tcsp.
  Qed.

(*  Lemma proc_names_replace_sub :
    forall n cn (subs : n_procs n) (p : n_proc n cn),
      get_names (replace_sub subs p) = get_names subs.
  Proof.
    induction subs; introv; simpl in *; tcsp.
    pose proof (IHsubs p) as IHsubs.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq cn c); simpl; subst; tcsp; try congruence.
  Qed.
  Hint Rewrite proc_names_replace_sub : comp.*)

(*  Lemma in_replace_sub_if_diff :
    forall cn n (subs : n_procs n) (p : n_proc n cn) q,
      pp_name q <> cn
      -> In q subs
      -> In q (replace_sub subs p).
  Proof.
    induction subs; introv d i; simpl in *; tcsp.
    destruct a as [c a].
    destruct (CompNameDeq cn c); subst; simpl in *; tcsp;[].
    repndors; subst; simpl in *; tcsp.
  Qed.
  Hint Resolve in_replace_sub_if_diff : comp.*)

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
      -> In (pp_name a) (get_names subs).
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

(*  Lemma in_replace_sub_if_in_names :
    forall n (p : n_nproc n) subs,
      In (pp_name p) (get_names subs)
      -> In p (replace_sub subs (pp_proc p)).
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [cn a]; simpl in *.
    destruct p as [c p]; simpl in *.
    destruct (CompNameDeq c cn); subst; simpl; tcsp.
  Qed.*)

(*  Lemma implies_similar_subs_replace_sub :
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
  Hint Resolve implies_similar_subs_replace_sub : comp.*)

(*  Lemma similar_subs_replace_subs_raise_select :
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
  Qed.*)

  Lemma similar_subs_preserves_get_names :
    forall n (subs1 subs2 : n_procs n),
      similar_subs subs1 subs2
      -> get_names subs1 = get_names subs2.
  Proof.
    introv sim; induction sim; introv; auto.
    unfold get_names in *; simpl.
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

  Lemma similar_subs_preserves_ordered_subs :
    forall n (subs1 subs2 : n_procs n),
      similar_subs subs1 subs2
      -> ordered_subs subs1 = ordered_subs subs2.
  Proof.
    introv sim; induction sim; introv; auto; simpl.
    f_equal; auto;[].
    inversion simp as [? ? ? ? sims]; subst.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.

    destruct ps1, ps2; simpl in *; tcsp;
      inversion sim as [|xx ? ? ? sim1 sim2]; subst.
    applydup similar_sms_implies_eq_sm2levels in sims.
    rewrite sims0.
    f_equal.

    destruct n0 as [c1 p1], n1 as [c2 p2]; simpl in *.
    inversion sim1 as [? ? ? ? sims']; subst.
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
    applydup similar_sms_implies_eq_sm2levels in sims'; auto.
  Qed.

  Lemma similar_subs_preserves_wf_procs :
    forall n (subs1 subs2 : n_procs n),
      similar_subs subs1 subs2
      -> wf_procs subs1
      -> wf_procs subs2.
  Proof.
    introv sim.
    applydup similar_subs_preserves_get_names in sim.
    applydup similar_subs_preserves_ordered_subs in sim.
    unfold wf_procs, no_dup_subs.
    allrw andb_true.
    rewrite sim0, sim1; auto.
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

  Lemma subset_get_names_select_n_procs :
    forall n i (subs : n_procs n),
      subset (get_names (select_n_procs i subs)) (get_names subs).
  Proof.
    induction subs; introv j; simpl in *; tcsp.
    autorewrite with comp in *.
    remember (select_n_nproc i a) as sel; symmetry in Heqsel.
    destruct sel; simpl in *; repndors; subst; tcsp.
    left; eauto 3 with comp.
  Qed.

  Lemma select_n_proc_implies_same_level :
    forall cn n j (a : n_proc n cn) b,
      select_n_proc j a = Some b
      -> sm2level a = sm2level b.
  Proof.
    induction n; introv sel; simpl in *; tcsp;[].
    destruct j; tcsp; destruct a; simpl in *; tcsp; ginv.

    { dest_cases w; ginv.
      inversion w; subst; simpl.
      rewrite (UIP_refl_nat (S j) w); simpl; auto. }

    { dest_cases w; ginv.

      { inversion w; subst; simpl.
        rewrite (UIP_refl_nat (S j) w); simpl; auto. }

      pose proof (IHn (S j) b0 b) as q; simpl in *; autodimp q hyp. }
  Qed.

  Lemma select_n_nproc_implies_same_level :
    forall n j (a : n_nproc n) b,
      select_n_nproc j a = Some b
      -> sm2level (pp_proc a) = sm2level (pp_proc b).
  Proof.
    introv sel.
    destruct a as [cn1 p1], b as [cn2 p2]; simpl in *.
    apply option_map_Some in sel; exrepnd.
    inversion sel0; subst; simpl in *.
    apply decomp_p_nproc in sel0; subst.
    apply select_n_proc_implies_same_level in sel1; auto.
  Qed.

  Lemma lower_head_select_n_procs :
    forall j {n} (subs : n_procs n) i,
      ordered_subs subs = true
      -> lower_head i subs = true
      -> lower_head i (select_n_procs j subs) = true.
  Proof.
    unfold select_n_procs.
    induction subs; introv ord h; simpl in *; tcsp.
    allrw Nat.leb_le.
    allrw andb_true; repnd.
    destruct a as [cn p]; simpl in *.
    remember (select_n_proc j p) as sel; symmetry in Heqsel; destruct sel; simpl; tcsp.
    { allrw Nat.leb_le.
      apply select_n_proc_implies_same_level in Heqsel; try omega. }
    apply IHsubs; auto; eauto 3 with comp.
  Qed.
  Hint Resolve lower_head_decr_n_procs : comp.

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
    applydup select_n_nproc_implies_same_level in Heqsel as lvl.
    apply wf_procs_cons; dands; auto; eauto 3 with comp;
      [|apply lower_head_select_n_procs;apply andb_true in wf;tcsp; try congruence];[].
    introv j.
    apply subset_get_names_select_n_procs in j; tcsp.
    apply name_of_select_n_nproc in Heqsel.
    rewrite Heqsel in wf0; tcsp.
  Qed.
  Hint Resolve wf_procs_select_n_procs : comp.

  Lemma wf_procs_decr_n_procs :
    forall {n} (subs : n_procs n),
      wf_procs subs
      -> wf_procs (decr_n_procs subs).
  Proof.
    introv wf.
    rewrite decr_n_procs_as_select_n_procs_pred; eauto 3 with comp.
  Qed.
  Hint Resolve wf_procs_decr_n_procs : comp.

(*  Lemma wf_procs_replace_sub :
    forall cn n (subs : n_procs n) (p : n_proc n cn),
      wf_procs subs
      -> wf_procs (replace_sub subs p).
  Proof.
    induction subs; introv wf; simpl in *; tcsp.
    rewrite wf_procs_cons in wf; repnd.
    pose proof (IHsubs p wf) as IHsubs.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq cn c); subst; apply wf_procs_cons; dands; tcsp; simpl in *;
      autorewrite with comp; auto.
  Qed.
  Hint Resolve wf_procs_replace_sub : comp.*)

(*  Lemma implies_wf_procs_replace_subs :
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
  Hint Resolve implies_wf_procs_replace_subs : comp.*)

  Lemma get_names_replace_name :
    forall n cn (p : n_proc n cn) (subs : n_procs n),
      get_names (replace_name p subs) = get_names subs.
  Proof.
    induction subs; introv; simpl; auto.
    destruct a as [c a].
    destruct (CompNameDeq c cn); subst; simpl in *; tcsp.
    rewrite IHsubs; auto.
  Qed.
  Hint Rewrite get_names_replace_name : comp.

  (*Lemma wf_procs_replace_name :
    forall n cn (p : n_proc n cn) (subs : n_procs n),
      wf_procs subs
      -> wf_procs (replace_name p subs).
  Proof.
    introv wf; unfold wf_procs, no_dup_subs in *; autorewrite with comp; auto.
  Qed.
  Hint Resolve wf_procs_replace_name : comp.*)

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

  Lemma subset_get_names_raise_to_n_procs :
    forall n i (subs : n_procs n),
      subset (get_names (raise_to_n_procs i subs)) (get_names subs).
  Proof.
    induction subs; introv j; simpl in *; tcsp.
    autorewrite with comp in *.
    remember (raise_to_n_nproc i a) as sel; symmetry in Heqsel.
    destruct sel; simpl in *; repndors; subst; tcsp.
    left; eauto 3 with comp.
  Qed.

  Lemma raise_to_n_proc_implies_same_level :
    forall cn j n (a : n_proc n cn) b,
      raise_to_n_proc j a = Some b
      -> sm2level a = sm2level b.
  Proof.
    induction j; introv sel; simpl in *; tcsp;[].
    dest_cases w.
    apply option_map_Some in sel; exrepnd; subst; simpl in *; tcsp.
  Qed.

  Lemma lower_head_raise_to_n_procs :
    forall j {n} (subs : n_procs n) i,
      ordered_subs subs = true
      -> lower_head i subs = true
      -> lower_head i (raise_to_n_procs j subs) = true.
  Proof.
    unfold raise_to_n_procs.
    induction subs; introv ord h; simpl in *; tcsp.
    allrw Nat.leb_le.
    allrw andb_true; repnd.
    destruct a as [cn p]; simpl in *.
    remember (raise_to_n_proc j p) as sel; symmetry in Heqsel; destruct sel; simpl; tcsp.
    { allrw Nat.leb_le.
      apply raise_to_n_proc_implies_same_level in Heqsel; try omega. }
    apply IHsubs; auto; eauto 3 with comp.
  Qed.
  Hint Resolve lower_head_decr_n_procs : comp.

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
    { intro i; apply subset_get_names_raise_to_n_procs in i.
      apply name_of_raise_to_n_nproc in Heqw; rewrite <- Heqw in i; tcsp. }
    { destruct a as [c1 p1]; simpl in *.
      apply option_map_Some in Heqw; exrepnd; subst; simpl in *.
      apply raise_to_n_proc_implies_same_level in Heqw1.
      rewrite <- Heqw1.
      apply lower_head_raise_to_n_procs; auto.
      apply andb_true in wf; tcsp. }
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

  Lemma wf_procs_implies_no_dup :
    forall {n} (subs : n_procs n),
      wf_procs subs
      -> no_dup_subs subs = true.
  Proof.
    introv wf.
    apply andb_true in wf; tcsp.
  Qed.
  Hint Resolve wf_procs_implies_no_dup : comp.

  Lemma wf_procs_implies_ordered :
    forall {n} (subs : n_procs n),
      wf_procs subs
      -> ordered_subs subs = true.
  Proof.
    introv wf.
    apply andb_true in wf; tcsp.
  Qed.
  Hint Resolve wf_procs_implies_ordered : comp.

  Lemma is_proc_n_nproc_select_n_nproc :
    forall n k (a : n_nproc n) b,
      is_proc_n_nproc a
      -> select_n_nproc k a = Some b
      -> is_proc_n_nproc b.
  Proof.
    introv isp sel.
    destruct a as [cn a].
    simpl in *.
    apply option_map_Some in sel; exrepnd; subst; simpl in *.
    unfold is_proc_n_proc in *; exrepnd.
    exists p.
    introv.
    pose proof (isp0 s i) as isp0.
    eapply select_n_proc_preserves_sm2update_eq_proc2upd; eauto.
  Qed.
  Hint Resolve is_proc_n_nproc_select_n_nproc : comp.

  Lemma are_procs_n_procs_select_n_procs :
    forall n k (subs : n_procs n),
      are_procs_n_procs subs
      -> are_procs_n_procs (select_n_procs k subs).
  Proof.
    induction subs; introv aps; simpl in *; tcsp.
    { introv i; simpl in *; tcsp. }
    allrw are_procs_n_procs_cons; repnd.
    unfold select_n_procs; simpl.
    remember (select_n_nproc k a) as q; symmetry in Heqq.
    destruct q; simpl; tcsp;[].
    allrw are_procs_n_procs_cons.
    dands; tcsp; eauto 3 with comp.
  Qed.
  Hint Resolve are_procs_n_procs_select_n_procs : comp.

  Lemma implies_similar_app_r :
    forall {n} (k l1 l2 : n_procs n),
      similar_subs l1 l2
      -> similar_subs (l1 ++ k) (l2 ++ k).
  Proof.
    introv sim; induction sim; simpl; auto; eauto 3 with comp.
  Qed.

  Lemma implies_similar_app :
    forall {n} (k1 k2 l1 l2 : n_procs n),
      similar_subs l1 l2
      -> similar_subs k1 k2
      -> similar_subs (l1 ++ k1) (l2 ++ k2).
  Proof.
    introv sim; induction sim; simpl; auto; eauto 3 with comp.
  Qed.

  Lemma find_name_app_r :
    forall cn {n} (l k : n_procs n),
      ~In cn (get_names l)
      -> find_name cn (l ++ k) = find_name cn k.
  Proof.
    induction l; introv ni; simpl in *; tcsp.
    apply not_or in ni; repnd.
    destruct a as [x p]; simpl in *; dest_cases w.
  Qed.

  Lemma find_name_app_l :
    forall cn {n} (l k : n_procs n),
      In cn (get_names l)
      -> find_name cn (l ++ k) = find_name cn l.
  Proof.
    induction l; introv i; simpl in *; tcsp.
    destruct a as [x p]; simpl in *; repndors; subst; tcsp; dest_cases w.
  Qed.

  Lemma find_name_remove_name :
    forall cn a {n} (l : n_procs n),
      cn <> a
      -> find_name cn (remove_name l a) = find_name cn l.
  Proof.
    induction l; introv d; simpl in *; tcsp.
    destruct a0 as [x p]; simpl in *;
      repeat (dest_cases w; simpl in *; subst; tcsp).
  Qed.

  Lemma find_name_remove_names :
    forall cn k {n} (l : n_procs n),
      ~In cn k
      -> find_name cn (remove_names l k) = find_name cn l.
  Proof.
    induction k; introv ni; simpl in *; tcsp.
    apply not_or in ni; repnd.
    rewrite IHk; auto.
    rewrite find_name_remove_name; auto.
  Qed.

  Lemma find_name_remove_subs :
    forall cn {m} (k : n_procs m) {n} (l : n_procs n),
      ~In cn (get_names k)
      -> find_name cn (remove_subs l k) = find_name cn l.
  Proof.
    introv ni.
    unfold remove_subs.
    rewrite find_name_remove_names; auto.
  Qed.

  Lemma select_n_proc_0 :
    forall {n} {cn} (p : n_proc n cn),
      select_n_proc 0 p = None.
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct p; simpl in *; tcsp.
  Qed.
  Hint Rewrite @select_n_proc_0 : comp.

  Lemma select_n_proc_sm2level :
      forall {n} {cn} k (p : n_proc n cn),
        k <= sm2level p
        -> select_n_proc k p = None.
  Proof.
    induction n; introv lek; simpl in *; tcsp.
    destruct p; simpl in *; tcsp.
    { destruct k; simpl in *; tcsp.
      dest_cases w; ginv.
      inversion w; subst; simpl; try omega. }
    { destruct k; simpl in *; tcsp; autorewrite with comp; auto.
      dest_cases w; ginv.
      { inversion w; subst; simpl; try omega.
        pose proof (sm2level_le_pred _ _ b) as ln0; try omega. }
      apply (IHn cn (S k) b); auto. }
  Qed.

  Lemma no_dup_find_name_implies_no_in_names_select :
    forall cn {n} p (l : n_procs n),
      no_dup_subs l = true
      -> find_name cn l = Some p
      -> ~ In cn (get_names (select_n_procs (sm2level p) l)).
  Proof.
    unfold no_dup_subs, select_n_procs.
    induction l; introv nodup fn i; simpl in *; tcsp.
    destruct a as [x q]; simpl in *.
    repeat (dest_cases w; repndors; subst; simpl in *; ginv; tcsp; rev_Some);
      try (complete (apply option_map_Some in Heqw; exrepnd; repeat (subst; simpl in * );
                     rewrite select_n_proc_sm2level in Heqw1; ginv)).
    symmetry in Heqw.
    apply option_map_None in Heqw.
    rewrite select_n_proc_sm2level in Heqw; auto; GC.
    apply in_map_iff in i; exrepnd; subst; simpl in *.
    apply in_mapOption in i0; exrepnd.
    destruct n0; apply in_map_iff; eexists; dands; eauto.
    destruct a as [c1 p1]; simpl in *.
    apply option_map_Some in i2; exrepnd; subst; simpl in *; auto.
  Qed.
  Hint Resolve no_dup_find_name_implies_no_in_names_select : comp.

  Definition rm_highest_proc_upto (k : nat) {n} {cn} (p : n_proc n cn) : option (n_proc n cn) :=
    if sm2level p <? k then Some p
    else None.

  Definition rm_highest_nproc_upto k {n} (np : n_nproc n) : option (n_nproc n) :=
    match np with
    | MkPProc m p =>
      match rm_highest_proc_upto k p with
      | Some q => Some (MkPProc m q)
      | None => None
      end
    end.

  Definition rm_highest_procs_upto k {n} (ps : n_procs n) : n_procs n :=
    mapOption (rm_highest_nproc_upto k) ps.

  Definition keep_highest_proc_upto k {n} {cn} (p : n_proc n cn) : option (n_proc n cn) :=
    if k <=? sm2level p then Some p
    else None.

  Definition keep_highest_nproc_upto k {n} (np : n_nproc n) : option (n_nproc n) :=
    match np with
    | MkPProc m p =>
      match keep_highest_proc_upto k p with
      | Some q => Some (MkPProc m q)
      | None => None
      end
    end.

  Definition keep_highest_procs_upto k {n} (ps : n_procs n) : n_procs n :=
    mapOption (keep_highest_nproc_upto k) ps.

  Lemma select_n_proc_some_implies_raise_rm_highest :
    forall {cn} {n} (p : n_proc n cn) k q,
      select_n_proc k p = Some q
      -> raise_to_n_proc n q = Some p
         /\ rm_highest_proc_upto k p = Some p.
  Proof.
    induction n; introv sel; simpl in *; tcsp;[].
    destruct k; simpl in *; tcsp;[].
    repeat (dest_cases w; simpl in *; ginv; tcsp).
    { inversion w; subst; simpl.
      rewrite (UIP_refl_nat (S k) w); simpl; auto.
      rewrite (UIP_refl_nat (S k) w0); simpl; auto.
      dands; auto.
      unfold rm_highest_proc_upto; dest_cases w.
      symmetry in Heqw1.
      apply Nat.ltb_ge in Heqw1.
      pose proof (sm2level_le_pred cn (S k) p) as z.
      simpl in *; try omega. }
    { destruct p; simpl in *; ginv.
      pose proof (IHn b (S k) q) as z.
      autodimp z hyp; repnd.
      allrw; simpl; dands; auto.
      unfold rm_highest_proc_upto in *; simpl in *.
      dest_cases w. }
  Qed.

  Lemma select_n_proc_some_implies_keep_highest :
    forall {cn} {n} (p : n_proc n cn) k q,
      select_n_proc k p = Some q
      -> keep_highest_proc_upto k p = None.
  Proof.
    introv sel.
    unfold keep_highest_proc_upto; dest_cases w.
    symmetry in Heqw.
    apply Nat.leb_le in Heqw.
    rewrite select_n_proc_sm2level in sel; auto; ginv.
  Qed.

  Lemma select_n_proc_none_implies_keep_highest :
    forall {cn} {n} (p : n_proc n cn) k,
      k <= n
      -> select_n_proc k p = None
      -> keep_highest_proc_upto k p = Some p.
  Proof.
    introv len sel.
    unfold keep_highest_proc_upto; dest_cases w.
    symmetry in Heqw.
    apply Nat.leb_gt in Heqw.
    apply select_n_proc_implies_lt in sel; auto; try omega.
  Qed.

  Lemma select_n_proc_none_implies_rm_highest :
    forall {cn} {n} (p : n_proc n cn) k,
      k <= n
      -> select_n_proc k p = None
      -> rm_highest_proc_upto k p = None.
  Proof.
    introv len sel.
    unfold rm_highest_proc_upto; simpl; dest_cases w.
    symmetry in Heqw.
    allrw Nat.ltb_lt; try omega.
    pose proof (select_n_proc_implies_lt cn _ k p) as z.
    repeat (autodimp z hyp).
    try omega.
  Qed.

  Lemma raise_to_n_procs_select_n_procs_as_rm_highest_procs_upto :
    forall {n} (l : n_procs n) k,
      k <= n
      -> raise_to_n_procs n (select_n_procs k l)
         = rm_highest_procs_upto k l.
  Proof.
    unfold select_n_procs, raise_to_n_procs, rm_highest_procs_upto.
    induction l; introv len; simpl in *; tcsp.
    destruct a as [cn p]; simpl in *.
    remember (select_n_proc k p) as sel; symmetry in Heqsel.
    destruct sel; simpl in *.
    { applydup (select_n_proc_some_implies_raise_rm_highest p) in Heqsel; repnd.
      allrw; simpl; auto. }
    { rewrite IHl; auto.
      applydup @select_n_proc_none_implies_rm_highest in Heqsel; auto.
      allrw; auto. }
  Qed.

  Lemma remove_subs_select_n_procs_as_rm_highest_procs_upto :
    forall {n} (l : n_procs n) k,
      k <= n
      -> no_dup_subs l = true
      -> remove_subs l (select_n_procs k l)
         = keep_highest_procs_upto k l.
  Proof.
    unfold no_dup_subs, select_n_procs, remove_subs, keep_highest_procs_upto.
    induction l; introv len nodup; simpl in *; tcsp.
    dest_cases w;[].
    rewrite remove_names_cons; simpl.
    destruct a as [cn p]; simpl in *.
    remember (select_n_proc k p) as sel; symmetry in Heqsel.
    destruct sel; simpl in *.
    { destruct (CompNameDeq cn cn); tcsp; GC.
      rewrite IHl; auto.
      apply select_n_proc_some_implies_keep_highest in Heqsel; allrw; auto. }
    { applydup @select_n_proc_none_implies_keep_highest in Heqsel; auto;[].
      allrw; auto.
      dest_cases w.

      apply in_map_iff in i; exrepnd.
      apply in_mapOption in i0; exrepnd.
      destruct n0.
      apply in_map_iff; eexists; dands; eauto.
      destruct a as [z q]; simpl in *.
      apply option_map_Some in i2; exrepnd; subst; simpl in *; auto. }
  Qed.

  Lemma rm_highest_procs_upto_trivial :
    forall i {n} (subs : n_procs n) k,
      i < k
      -> all_lower i subs = true
      -> rm_highest_procs_upto k subs = subs.
  Proof.
    unfold rm_highest_procs_upto.
    induction subs; introv ltk h; simpl in *; auto.
    allrw andb_true; repnd.
    allrw Nat.leb_le.
    rewrite IHsubs; auto.
    destruct a as [cn p]; simpl in *.
    unfold rm_highest_proc_upto.
    dest_cases w; symmetry in Heqw.
    allrw Nat.ltb_ge; try omega.
  Qed.

  Lemma keep_highest_procs_upto_nil :
    forall i {n} (l : n_procs n) k,
      i < k
      -> all_lower i l = true
      -> keep_highest_procs_upto k l = [].
  Proof.
    unfold keep_highest_procs_upto.
    induction l; introv ltk h; simpl in *; auto.
    allrw andb_true; repnd.
    allrw Nat.leb_le.
    destruct a as [cn' p']; simpl in *.
    rewrite IHl; auto.
    unfold keep_highest_proc_upto; dest_cases w; tcsp.
    symmetry in Heqw.
    allrw Nat.leb_le; try omega.
  Qed.

  Lemma split_as_rm_highest_keep_highest_upto :
    forall {n} (subs : n_procs n) k,
      ordered_subs subs = true
      -> no_dup_subs subs = true
      -> subs = keep_highest_procs_upto k subs ++ rm_highest_procs_upto k subs.
  Proof.
    unfold no_dup_subs, rm_highest_procs_upto, keep_highest_procs_upto.
    induction subs; introv ord nodup; simpl in *; tcsp.

    destruct a as [cn p]; simpl in *.
    allrw andb_true; repnd.
    dest_cases w;[].
    unfold rm_highest_proc_upto.
    unfold keep_highest_proc_upto.
    repeat (dest_cases w);
      symmetry in Heqw; symmetry in Heqw0;
        allrw Nat.ltb_lt; allrw Nat.leb_le;
          allrw Nat.leb_gt; allrw Nat.ltb_ge;
            try omega; GC;
              try (complete (simpl; rewrite <- (IHsubs k); auto)).

    pose proof (rm_highest_procs_upto_trivial (sm2level p) subs k) as h.
    unfold rm_highest_procs_upto in h; rewrite h; eauto 3 with comp; clear h; simpl;[].
    pose proof (keep_highest_procs_upto_nil (sm2level p) subs k) as h.
    unfold keep_highest_procs_upto in h; rewrite h; eauto 3 with comp.
  Qed.

  Lemma lower_head_replace_name :
    forall x n cn (p q : n_proc n cn) (subs : n_procs n),
      find_name cn subs = Some p
      -> sm2level p = sm2level q
      -> all_lower x subs = true
      -> all_lower x (replace_name q subs) = true.
  Proof.
    induction subs; introv fn eqlvl hd; simpl in *; tcsp.
    destruct a as [cn' p']; simpl in *.
    dest_cases w; simpl in *; allrw andb_true; repnd; tcsp.
  Qed.
  Hint Resolve lower_head_replace_name : comp.

  Lemma ordered_subs_replace_name :
    forall n cn (p q : n_proc n cn) (subs : n_procs n),
      find_name cn subs = Some p
      -> sm2level p = sm2level q
      -> ordered_subs subs = true
      -> ordered_subs (replace_name q subs) = true.
  Proof.
    induction subs; introv fn eqlvl pr; simpl in *; auto.
    allrw andb_true; repnd.
    destruct a as [cn' p']; simpl in *.
    dest_cases w; subst; simpl in *; allrw andb_true; tcsp; ginv.
    repeat (autodimp IHsubs hyp).
    dands; auto; eauto 4 with comp.
  Qed.
  Hint Resolve ordered_subs_replace_name : comp.

  Lemma wf_procs_replace_name :
    forall n cn (p q : n_proc n cn) (subs : n_procs n),
      find_name cn subs = Some p
      -> sm2level p = sm2level q
      -> wf_procs subs
      -> wf_procs (replace_name q subs).
  Proof.
    introv fn eqlvl wf; unfold wf_procs, no_dup_subs in *; autorewrite with comp; auto.
    allrw andb_true; repnd.
    dands; auto; eauto 3 with comp.
  Qed.
  Hint Resolve wf_procs_replace_name : comp.

  Lemma sm2level_update_state_m :
    forall {cn} {n} (p : n_proc n cn) s,
      sm2level (update_state_m p s) = sm2level p.
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct p; auto.
  Qed.
  Hint Rewrite @sm2level_update_state_m : comp.

  Lemma wf_procs_nil :
    forall {n : nat}, @wf_procs n [].
  Proof.
    introv; split.
  Qed.
  Hint Resolve wf_procs_nil : comp.

  Lemma wf_procs_app :
    forall {n} (l k : n_procs n),
      wf_procs (l ++ k)
      <->
      (
        wf_procs l
        /\ wf_procs k
        /\ (forall (p1 p2 : n_nproc n),
               In p1 l -> In p2 k -> pp_name p1 <> pp_name p2)
        /\ (forall (p : n_nproc n),
               In p l -> lower_head (sm2level (pp_proc p)) k = true)
      ).
  Proof.
    induction l; introv; simpl; allrw wf_procs_cons;
      try (rewrite IHl);
      allrw @get_names_app;
      allrw in_app_iff;
      split; intro h; repnd; dands; eauto 2 with comp.
    { apply not_or in h0; repnd; tcsp. }
    { destruct l; simpl in *; tcsp. }
    { introv w z xx; repndors; subst; simpl in *; tcsp.
      { apply not_or in h0; repnd.
        destruct h0.
        rewrite xx; apply in_map_iff; exists p2; dands; auto. }
      { apply h4 in xx; tcsp. } }
    { introv w; repndors; subst; tcsp.
      destruct l; simpl in *; tcsp.
      allrw Nat.leb_le.
      pose proof (h n0) as h; autodimp h hyp.
      eauto 3 with comp. }
    { intro xx; repndors; tcsp.
      apply in_map_iff in xx; exrepnd.
      pose proof (h2 a x) as h2; repeat (autodimp h2 hyp). }
    { destruct l; simpl in *; tcsp. }
    { introv w z; apply h2; tcsp. }
    { introv w; apply h; tcsp. }
  Qed.

  Lemma implies_wf_procs_remove_names :
    forall {n} (l : n_procs n) k,
      wf_procs l
      -> wf_procs (remove_names l k).
  Proof.
    introv wf; unfold wf_procs in *; allrw andb_true; repnd; dands; eauto 3 with comp.
  Qed.
  Hint Resolve implies_wf_procs_remove_names : comp.

  Lemma implies_wf_procs_remove_subs :
    forall {n} (l : n_procs n) {m} (k : n_procs m),
      wf_procs l
      -> wf_procs (remove_subs l k).
  Proof.
    introv h; apply implies_wf_procs_remove_names; auto.
  Qed.
  Hint Resolve implies_wf_procs_remove_subs : comp.

  Lemma implies_no_dub_subs_remove_name :
    forall {n} (subs : n_procs n) a,
      no_dup_subs subs = true
      -> no_dup_subs (remove_name subs a) = true.
  Proof.
    unfold no_dup_subs.
    induction subs; introv h; simpl in *; auto.
    repeat (dest_cases w; simpl in *; tcsp).
    rewrite get_names_remove_name in i.
    apply in_remove_fst_implies in i; tcsp.
  Qed.
  Hint Resolve implies_no_dub_subs_remove_name : comp.

  Lemma remove_trivial :
    forall {A} (deq : Deq A) a (l : list A),
      ~ In a l
      -> remove deq a l = l.
  Proof.
    induction l; introv i; simpl in *; tcsp.
    apply not_or in i; repnd.
    dest_cases w; rewrite IHl; auto.
  Qed.

  Lemma remove_fst_as_remove :
    forall {A} (deq : Deq A) a (l : list A),
      norepeatsb deq l = true
      -> remove_fst deq a l = remove deq a l.
  Proof.
    induction l; introv norep; simpl in *; tcsp.
    repeat (dest_cases w; subst; simpl in *; tcsp).
    { rewrite remove_trivial; auto. }
    { rewrite IHl; auto. }
  Qed.

  Lemma get_names_remove_subs :
    forall k {n} (l : n_procs n),
      no_dup_subs l = true
      -> get_names (remove_names l k)
         = diff CompNameDeq k (get_names l).
  Proof.
    induction k; introv h; simpl in *; tcsp.
    rewrite IHk; clear IHk; auto; eauto 3 with comp;[].
    rewrite get_names_remove_name.
    rewrite remove_fst_as_remove; auto.
  Qed.

  Lemma in_raise_to_n_procs_implies_sm2level :
    forall {n} (l : n_procs n) m p,
      In p (raise_to_n_procs m l)
      -> sm2level (pp_proc p) <= pred n.
  Proof.
    unfold raise_to_n_procs.
    induction l; introv i; simpl in *; tcsp.
    destruct a as [cn q]; simpl in *.
    dest_cases w; simpl in *; rev_Some.
    apply option_map_Some in Heqw; exrepnd; subst; simpl in *.
    repndors; subst; simpl in *; tcsp.
    applydup raise_to_n_proc_implies_same_level in Heqw1.
    pose proof (sm2level_le_pred _ _ q) as lvl; try omega.
  Qed.

  Definition all_lower_in (i : nat) {n} (l : n_procs n) :=
    forall p, In p l -> sm2level (pp_proc p) <= i.

  Lemma all_lower_as_in :
    forall i {n} (l : n_procs n),
      all_lower i l = true
      <-> all_lower_in i l.
  Proof.
    induction l; introv; split; intro h; simpl in *; tcsp.
    { introv w; simpl in *; tcsp. }
    { allrw andb_true; allrw Nat.leb_le; repnd.
      apply IHl in h.
      introv w; simpl in *; repndors; subst; tcsp. }
    { allrw andb_true; allrw Nat.leb_le.
      pose proof (h a) as q; simpl in q; autodimp q hyp.
      dands; tcsp.
      apply IHl; introv w; apply h; simpl; tcsp. }
  Qed.

  Lemma all_lower_in_implies_lower_head :
    forall i {n} (l : n_procs n),
      all_lower_in i l
      -> lower_head i l = true.
  Proof.
    introv h; apply all_lower_as_in in h; eauto 3 with comp.
  Qed.
  Hint Resolve all_lower_in_implies_lower_head : comp.

  Lemma in_remove_name_implies :
    forall {n} p a (l : n_procs n),
      no_dup_subs l = true
      -> In p (remove_name l a)
      -> In p l /\ pp_name p <> a.
  Proof.
    unfold no_dup_subs.
    induction l; introv nodup j; simpl in *; tcsp.
    repeat (dest_cases w; subst; simpl in *; tcsp).
    { dands; tcsp.
      introv xx; rewrite <- xx in n0; destruct n0.
      apply in_map_iff; exists p; dands; auto. }
    { repndors; subst; tcsp. }
  Qed.

  Lemma in_remove_names_implies :
    forall {n} p k (l : n_procs n),
      no_dup_subs l = true
      -> In p (remove_names l k)
      -> In p l /\ ~ In (pp_name p) k.
  Proof.
    unfold no_dup_subs.
    induction k; introv nodup j; simpl in *; tcsp.
    apply IHk in j; tcsp; clear IHk; repnd;
      [|rewrite get_names_remove_name;
        apply implies_norepeatsb_remove_fst;auto];[].
    apply in_remove_name_implies in j0; auto; repnd; dands; tcsp.
  Qed.

  Lemma not_in_get_names_select_n_procs_implies :
    forall {n} p k (l : n_procs n),
      k <= n
      -> In p l
      -> ~ In (pp_name p) (get_names (select_n_procs k l))
      -> Init.Nat.pred k <= sm2level (pp_proc p).
  Proof.
    unfold select_n_procs.
    induction l; introv lek j ni; simpl in *; tcsp.
    remember (select_n_nproc k a) as sel; symmetry in Heqsel.
    destruct sel; simpl in *; tcsp;
      repndors; subst; tcsp.
    { apply not_or in ni; repnd.
      destruct p as [cn p]; simpl in *.
      apply option_map_Some in Heqsel; exrepnd; subst; simpl in *; tcsp. }
    { apply select_n_nproc_implies_lt in Heqsel; auto; try omega. }
  Qed.

  Lemma implies_all_lower_in_raise_to_n_procs :
    forall i k {n} (l : n_procs n),
      pred n <= i
      -> n <= pred k
      -> no_dup_subs l = true
      -> all_lower_in i (raise_to_n_procs k l).
  Proof.
    introv lei lek nodup h.
    apply in_raise_to_n_procs_implies_sm2level in h; try omega.
  Qed.

  Lemma find_name_implies_in_get_names :
    forall cn n (subs : n_procs n) sm,
      find_name cn subs = Some sm
      -> In cn (get_names subs).
  Proof.
    induction subs; introv fd; simpl in *; ginv.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq c cn); subst; tcsp.
    apply IHsubs in fd; tcsp.
  Qed.
  Hint Resolve find_name_implies_in_get_names : comp.

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
      remember (app_m_proc p i subs1) as ap; symmetry in Heqap; repnd.
      rewrite (app_m_proc_some2 p i) in Heqap; eauto 3 with comp;[].
      remember (sm2update p (sm2state p) i (select_n_procs (sm2level p) subs1)) as w; symmetry in Heqw.
      repnd; ginv; simpl in *.
      inversion Heqap; subst; simpl in *; clear Heqap.

      pose proof (sm2level_le_pred _ _ p) as ln0.

      pose proof (are_procs_n_procs_find_name _ _ subs1 p) as isp; simpl in isp.
      repeat (autodimp isp hyp).

      applydup is_proc_n_proc_update_implies_some in Heqw; auto;[]; exrepnd; subst; simpl in *.

      pose proof (imp (sm2level p) _ (sm2at p) (sm2state p) i (select_n_procs (sm2level p) subs1)) as imp.
      repeat (autodimp imp hyp); try omega; eauto 3 with comp;
        try (complete (destruct n; simpl in *; tcsp; try omega)).
      autorewrite with comp in *.

      simpl in *.
      unfold M_break in imp.
      rewrite Heqw in imp; repnd.

      assert (find_name cn (remove_subs subs1 w0 ++ raise_to_n_procs n w0) = Some p) as fn.
      { rewrite find_name_app_l.
        { rewrite find_name_remove_subs; auto.
          apply similar_subs_preserves_get_names in imp0.
          rewrite <- imp0; eauto 3 with comp. }
        pose proof (no_dup_find_name_implies_no_in_names_select cn p subs1) as q.
        repeat (autodimp q hyp); eauto 3 with comp.
        apply similar_subs_preserves_get_names in imp0.
        rewrite imp0 in q.
        unfold remove_subs.
        rewrite get_names_remove_subs; eauto 3 with comp.
        apply in_diff; dands; eauto 3 with comp. }

      dup imp0 as simb.
      apply (raise_to_n_procs_similar_subs n) in imp0.
      apply (implies_similar_app
               _ _
               (remove_subs subs1 (select_n_procs (sm2level p) subs1))
               (remove_subs subs1 w0)) in imp0;
        [|apply similar_subs_preserves_get_names in simb;
          unfold remove_subs; allrw; eauto 2 with comp];[].

      dands.

      { apply similar_subs_sym.
        eapply similar_subs_trans;
          [apply similar_subs_replace_name_update_state_m_find_name;
           auto|];[].
        eapply similar_subs_trans;[apply similar_subs_sym;eauto|];[].
        rewrite raise_to_n_procs_select_n_procs_as_rm_highest_procs_upto; try omega;[].
        rewrite remove_subs_select_n_procs_as_rm_highest_procs_upto; try omega; eauto 3 with comp;[].
        rewrite <- split_as_rm_highest_keep_highest_upto; eauto 3 with comp. }

      apply (wf_procs_replace_name _ _ p); autorewrite with comp; auto.
      apply wf_procs_app; dands; eauto 3 with comp.

      { introv h1 h2 xx.
        assert (In (pp_name p1) (get_names (remove_subs subs1 w0))) as i1.
        { apply in_map_iff; exists p1; dands; eauto. }
        assert (In (pp_name p2) (get_names (raise_to_n_procs n w0))) as i2.
        { apply in_map_iff; exists p2; dands; eauto. }
        clear h1 h2.
        autorewrite with comp in *.
        rewrite get_names_raise_to_n_procs in i2; auto; try omega;[].
        unfold remove_subs in i1.
        rewrite get_names_remove_subs in i1; eauto 3 with comp;[].
        rewrite xx in i1.
        apply in_diff in i1; repnd; tcsp. }

      { introv i1.
        unfold remove_subs in i1.
        applydup similar_subs_preserves_get_names in simb.
        rewrite <- simb0 in i1.
        apply in_remove_names_implies in i1; eauto 3 with comp;[]; repnd.
        apply not_in_get_names_select_n_procs_implies in i1; auto; try omega.
        apply all_lower_in_implies_lower_head.
        apply implies_all_lower_in_raise_to_n_procs; eauto 3 with comp; try omega. } }
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

  Definition wf_sys {f} (sys : M_USystem f) :=
    forall n, wf_procs (sys n).

  Lemma are_procs_n_procs_decr_n_procs :
    forall {n} (subs : n_procs n),
      are_procs_n_procs subs
      -> are_procs_n_procs (decr_n_procs subs).
  Proof.
    unfold decr_n_procs.
    induction subs; introv aps; simpl in *; tcsp.
    { introv i; simpl in *; tcsp. }
    allrw are_procs_n_procs_cons; repnd.
    destruct a as [cn p]; simpl in *.
    remember (decr_n_proc p) as d; symmetry in Heqd.
    destruct d; simpl; tcsp;[].
    allrw are_procs_n_procs_cons; simpl.
    dands; eauto 3 with comp.
    destruct n; simpl in *; tcsp.
    destruct p; simpl in *; ginv.
    inversion Heqd; subst; auto.
  Qed.
  Hint Resolve are_procs_n_procs_decr_n_procs : comp.

  Lemma implies_similar_sms_incr_n_proc :
    forall {n} {cn} (p1 p2 : n_proc n cn),
      similar_sms p1 p2
      -> similar_sms (incr_n_proc p1) (incr_n_proc p2).
  Proof.
    induction n; introv sim; simpl in *; tcsp.
  Qed.
  Hint Resolve implies_similar_sms_incr_n_proc : comp.

  Lemma implies_similar_subs_incr_n_procs :
    forall {n} (l1 l2 : n_procs n),
      similar_subs l1 l2
      -> similar_subs (incr_n_procs l1) (incr_n_procs l2).
  Proof.
    unfold incr_n_procs.
    introv sim; induction sim; introv; simpl; auto.
    constructor; auto.
    inversion simp as [? ? ? ? sims]; subst.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
    simpl in *.
    constructor; eauto 3 with comp.
  Qed.
  Hint Resolve implies_similar_subs_incr_n_procs : comp.

  Lemma implies_similar_subs_app :
    forall {n} (l1 l2 : n_procs n) k1 k2,
      similar_subs l1 l2
      -> similar_subs k1 k2
      -> similar_subs (l1 ++ k1) (l2 ++ k2).
  Proof.
    introv sim; revert k1 k2; induction sim; introv simk; simpl in *; tcsp.
  Qed.

  Lemma implies_similar_subs_remove_name :
    forall {n} (l1 l2 : n_procs n) a,
      similar_subs l1 l2
      -> similar_subs (remove_name l1 a) (remove_name l2 a).
  Proof.
    introv sim; induction sim; simpl in *; tcsp.
    applydup @similar_procs_implies_same_name in simp.
    rewrite simp0.
    dest_cases w.
  Qed.
  Hint Resolve implies_similar_subs_remove_name : comp.

  Lemma implies_similar_subs_remove_names :
    forall k {n} (l1 l2 : n_procs n),
      similar_subs l1 l2
      -> similar_subs (remove_names l1 k) (remove_names l2 k).
  Proof.
    induction k; introv sim; simpl in *; tcsp.
    apply IHk; eauto 3 with comp.
  Qed.
  Hint Resolve implies_similar_subs_remove_names : comp.

  Lemma implies_similar_subs_remove_subs :
    forall {n} (l1 l2 : n_procs n) {m} (k1 k2 : n_procs m),
      similar_subs l1 l2
      -> similar_subs k1 k2
      -> similar_subs (remove_subs l1 k1) (remove_subs l2 k2).
  Proof.
    introv siml simk.
    unfold remove_subs.
    apply similar_subs_preserves_get_names in simk; rewrite simk; eauto 3 with comp.
  Qed.
  Hint Resolve implies_similar_subs_remove_subs : comp.

  Lemma implies_similar_subs_update_subs :
    forall {n} (l1 l2 : n_procs (S n)) k1 k2,
      similar_subs l1 l2
      -> similar_subs k1 k2
      -> similar_subs (update_subs l1 k1) (update_subs l2 k2).
  Proof.
    introv siml simk.
    unfold update_subs.
    apply implies_similar_subs_app; eauto 3 with comp.
  Qed.
  Hint Resolve implies_similar_subs_update_subs : comp.

  Lemma update_subs_decr_n_procs_eq :
    forall {n} (l : n_procs (S n)),
      no_dup_subs l = true
      -> ordered_subs l = true
      -> update_subs l (decr_n_procs l) = l.
  Proof.
    introv nodup ord; unfold update_subs.
    pose proof (incr_n_procs_decr_n_procs_as_rm_highest l) as q.
    simpl in *; rewrite q; clear q.
    pose proof (remove_subs_decr_n_procs_as_keep_highest_subs l) as q.
    simpl in *; rewrite q; clear q; auto.
    rewrite <- split_as_rm_highest_keep_highest; eauto 3 with comp.
  Qed.

  Lemma similar_subs_update_subs_decr_n_procs :
    forall {n} (l : n_procs (S n)),
      no_dup_subs l = true
      -> ordered_subs l = true
      -> similar_subs l (update_subs l (decr_n_procs l)).
  Proof.
    introv nodup ord; rewrite update_subs_decr_n_procs_eq; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_update_subs_decr_n_procs : comp.

  Lemma are_procs_implies_preserves_sub_M_run_sm_on_input :
    forall {n} {cn}
           (main  : n_proc n cn)
           (i     : cio_I (fio cn))
           (subs1 : n_procs n),
      is_proc_n_proc main
      -> are_procs_n_procs subs1
      -> wf_procs subs1
      -> M_break (M_run_sm_on_input main i)
                 subs1
                 (fun subs2 _ =>
                    similar_subs subs1 subs2
                    /\ wf_procs subs2).
  Proof.
    unfold M_run_sm_on_input.
    induction n; introv isp aps wf; simpl in *; tcsp.
    destruct main; simpl in *; tcsp.

    { unfold M_break, M_on_decr; simpl.
      remember (sm_update a (sm_state a) i (decr_n_procs subs1)) as w;
        symmetry in Heqw; repnd; simpl in *.
      pose proof (are_procs_implies_preserves_sub
                    a (sm_state a)
                    i
                    (decr_n_procs subs1)) as q.
      repeat (autodimp q hyp); eauto 3 with comp;
        try (complete (apply (wf_procs_decr_n_procs subs1); auto));
        try (complete (apply (are_procs_n_procs_decr_n_procs subs1); auto));[].
      unfold M_break in q.
      rewrite Heqw in q; repnd.
      pose proof (implies_similar_subs_update_subs
                    subs1 subs1
                    (decr_n_procs subs1) w0) as z.
      repeat (autodimp z hyp); eauto 3 with comp.
      rewrite update_subs_decr_n_procs_eq in z; eauto 3 with comp. }

    { unfold M_on_decr, M_break; simpl in *.
      pose proof (IHn cn b i (decr_n_procs subs1)) as IHn.
      repeat (autodimp IHn hyp);
        try (complete (apply (wf_procs_decr_n_procs subs1); auto));
        try (complete (apply (are_procs_n_procs_decr_n_procs subs1); auto));[].
      unfold M_break in IHn; simpl in *.
      remember (M_on_sm
                  b
                  (fun p => sm_update p (sm_state p) i)
                  (decr_n_procs subs1)) as z; symmetry in Heqz.
      simpl in *; rewrite Heqz; rewrite Heqz in IHn.
      repnd; simpl in *.
      pose proof (implies_similar_subs_update_subs
                    subs1 subs1
                    (decr_n_procs subs1) z0) as x.
      repeat (autodimp x hyp); eauto 3 with comp.
      rewrite update_subs_decr_n_procs_eq in x; eauto 3 with comp. }
  Qed.

  Lemma is_proc_n_proc_run_on_input_implies_some :
    forall {cn} {n} (p : n_proc n cn) (i : cio_I (fio cn))
           (subs1 subs2 : n_procs n)
           (sop : option (sf cn))
           (out : cio_O (fio cn)),
      is_proc_n_proc p
      -> M_run_sm_on_input p i subs1 = (subs2, (sop, out))
      -> exists s0, sop = Some s0.
  Proof.
    unfold M_run_sm_on_input.
    induction n; introv isp run; simpl in *; tcsp.
    destruct p; simpl in *; tcsp.
    { unfold M_on_decr in *; simpl in *.
      dest_cases w; symmetry in Heqw; repnd; simpl in *.
      unfold is_proc_n_proc in isp; simpl in *.
      exrepnd.
      rewrite isp0 in Heqw.
      unfold proc2upd in Heqw; simpl in *.
      unfold interp_s_proc, to_proc_some_state in Heqw; simpl in *.
      unfold bind_pair, bind in Heqw; simpl in *.
      remember (interp_proc (p (sm_state a) i) (decr_n_procs subs1)) as z.
      simpl in *; rewrite <- Heqz in Heqw.
      repnd; simpl in *; inversion Heqw; subst.
      inversion run; subst; eauto. }
    { unfold M_on_decr in run; simpl in *.
      dest_cases w; symmetry in Heqw; repnd; simpl in *.
      apply IHn in Heqw; auto; exrepnd; subst; simpl in *.
      inversion run; subst; eauto. }
  Qed.

  Lemma implies_similar_subs_replace_name :
    forall {n} (l1 l2 : n_procs n) {cn} (p : n_proc n cn),
      similar_subs l1 l2
      -> similar_subs (replace_name p l1) (replace_name p l2).
  Proof.
    introv sim; revert p; induction sim; introv; simpl in *; tcsp.
    inversion simp as [? ? ? ? sims]; subst.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
    simpl in *.
    dest_cases w; subst; simpl in *; GC.
    constructor; eauto 3 with comp.
  Qed.
  Hint Resolve implies_similar_subs_replace_name : comp.

  Lemma are_procs_n_procs_implies_ls_preserves_sub :
    forall {n} (ls : n_procs n),
      are_procs_n_procs ls
      -> wf_procs ls
      -> ls_preserves_subs ls.
  Proof.
    introv h wf sim.
    eapply similar_subs_preserves_are_procs_n_procs in h;[|eauto];[].
    eapply similar_subs_preserves_wf_procs in wf;[|simpl;eauto];[].

    unfold M_run_ls_on_input_ls.
    unfold M_run_ls_on_input.
    unfold on_comp.
    dest_cases w; rev_Some; simpl in *; tcsp; eauto 3 with comp;[].

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input
                  w i ls0) as z.
    repeat (autodimp z hyp); eauto 3 with comp;[].
    unfold M_break in *; simpl in *.
    dest_cases u; repnd; simpl in *; symmetry in Hequ.
    applydup @is_proc_n_proc_run_on_input_implies_some in Hequ; eauto 3 with comp;[].
    exrepnd; subst; simpl in *.
    pose proof (implies_similar_subs_replace_name
                  ls0 u0 (update_state_m w s0)) as q.
    simpl in *; autodimp q hyp.
    eapply similar_subs_trans;[|eauto].
    apply similar_subs_sym.
    apply similar_subs_replace_name_update_state_m_find_name; auto.
  Qed.
  Hint Resolve are_procs_n_procs_implies_ls_preserves_sub : comp.



  (* ================================================================ *)
  (* ====== TEST ====== *)

  Lemma are_procs_n_procs_TEST : are_procs_n_procs TESTls.
  Proof.
    introv i; simpl in *; repndors; subst; tcsp; simpl;
      eexists; introv; unfold proc2upd;  reflexivity.
  Qed.

  Lemma wf_procs_TEST : wf_procs TESTls.
  Proof.
    unfold wf_procs, wf_procs; simpl; auto.
  Qed.

  Lemma ls_preserves_subs_TEST : ls_preserves_subs TESTls.
  Proof.
    apply are_procs_n_procs_implies_ls_preserves_sub;
      try apply are_procs_n_procs_TEST;
      try apply wf_procs_TEST.
  Qed.

  (* ================================================================ *)

  Definition state_of_main_or_sub
             {n} {cn}
             (name : CompName)
             (s    : sf cn)
             (subs : n_procs n) : option (sf name) :=
    match CompNameDeq cn name with
    | left p => Some (eq_rect _ _ s _ p)
    | right q => state_of_component name subs
    end.

  Lemma find_name_not_in_get_names_implies :
    forall cn name n (subs : n_procs n) sm,
      find_name cn subs = Some sm
      -> ~ In name (get_names subs)
      -> cn <> name.
  Proof.
    introv fd ni.
    apply find_name_implies_in_get_names in fd.
    intro xx; subst; tcsp.
  Qed.

(*  Lemma find_sub_wf_procs_implies :
    forall cn {L} {S} (ls : LocalSystem L S) sm,
      find_sub cn ls = Some sm
      -> wf_procs ls
      -> cn <> S.
  Proof.
    introv fd ni.
    destruct ls as [main subs]; simpl in *.
    unfold find_sub in *; simpl in *.
    destruct ni as [ni1 ni2]; simpl in *.
    eapply find_name_not_in_get_names_implies; eauto.
  Qed.*)

(*  Lemma state_of_component_eq :
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
  Qed.*)

(*  Lemma M_byz_state_ls_before_event_as :
    forall {L S}
           (ls : LocalSystem L S)
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
  Qed.*)

  (*
  map_op_untrusted_op
      (M_byz_run_ls_before_event ls e)
      (state_of_component cn).

  Lemma M_byz_compose_step :
    forall {L S}
           (ls : LocalSystem L S)
           {eo : EventOrdering}
           (e  : Event),
      are_procs_n_procs ls
      -> find_sub cn ls = Some sm
      -> wf_procs ls
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

(*  Lemma in_replace_sub_implies :
    forall {n} {cn} (p : n_nproc n) (subs : n_procs n) (a : n_proc (pred n) cn),
      In p (replace_sub subs a)
      -> In p subs \/ p = MkPProc cn (incr_pred_n_proc a).
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [c a].
    destruct (CompNameDeq cn c); subst; simpl in *; repndors; tcsp.
    apply IHsubs in i; repndors; tcsp.
  Qed.*)

(*  Lemma in_replace_subs_implies :
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
  Qed.*)

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

(*  Lemma wf_procs_replace_subs :
    forall n l (subs : n_procs n),
      wf_procs subs
      -> wf_procs (replace_subs subs l).
  Proof.
    induction l; introv wf; simpl in *; auto.
    destruct a as [c a]; simpl in *.
    apply IHl; clear IHl; eauto 3 with comp.
  Qed.
  Hint Resolve wf_procs_replace_subs : comp.*)

  Lemma wf_procs_replace_name_implies :
    forall cn n (subs : n_procs n) (p : n_proc n cn),
      get_names (replace_name p subs) = get_names subs.
  Proof.
    induction subs; introv; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq c cn); subst; simpl in *; tcsp.
    rewrite IHsubs; auto.
  Qed.
  Hint Rewrite wf_procs_replace_name_implies : comp.

  Lemma are_procs_n_procs_and_wffst_interp_proc :
    forall {n} {A} (subs : n_procs n) (p : Proc A),
      wf_procs subs
      -> are_procs_n_procs subs
      ->
      (
        wf_procs (fst (interp_proc p subs))
        /\ similar_subs subs (fst (interp_proc p subs))
        /\ are_procs_n_procs (fst (interp_proc p subs))
      ).
  Proof.
    induction n as [? ind] using comp_ind; introv.
    introv wf aps.

    pose proof (interp_proc_preserves_subs p subs) as q.
    repeat (autodimp q hyp).
    { introv ltm isp' aps' wf'.
      unfold is_proc_n_proc_at in isp'; exrepnd.
      rewrite isp'0.
      unfold proc2upd, interp_s_proc, M_break.
      pose proof (ind m) as ind; autodimp ind hyp.
      pose proof (ind _ subs1 (to_proc_some_state (p0 s i))) as ind.
      repeat (autodimp ind hyp); repnd.
      split_pair; dands; auto. }

    unfold M_break in q; split_pair; repnd.
    dands; eauto 3 with comp.
  Qed.

  Lemma are_procs_n_procs_fst_interp_proc :
    forall {n} {A} (subs : n_procs n) (p : Proc A),
      wf_procs subs
      -> are_procs_n_procs subs
      -> are_procs_n_procs (fst (interp_proc p subs)).
  Proof.
    introv wf aps.
    apply are_procs_n_procs_and_wffst_interp_proc; auto.
  Qed.
  Hint Resolve are_procs_n_procs_fst_interp_proc : comp.

  Lemma wf_procs_fst_interp_proc :
    forall {n} {A} (subs : n_procs n) (p : Proc A),
      wf_procs subs
      -> are_procs_n_procs subs
      -> wf_procs (fst (interp_proc p subs)).
  Proof.
    introv wf.
    apply are_procs_n_procs_and_wffst_interp_proc; auto.
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
  Definition run_subs_leaves_direct {n} (subs1 subs2 : n_procs n) : Prop :=
    forall cn (p : n_proc n cn),
      sm2level p = 0
      -> In (MkPProc cn p) subs1
      ->
      exists (l : list (cio_I (fio cn))),
        In (MkPProc cn (snd (run_sm_on_inputs p l subs1))) subs2.

  Definition run_subs_leaves {n} (subs1 subs2 : n_procs n) : Prop :=
    forall cn (p : n_proc n cn),
      sm2level p = 0
      -> In (MkPProc cn p) subs1
      ->
      exists (l : list (cio_I (fio cn))) comp,
        M_comp_ls_on_op_inputs (sm2ls p) cn (map Some l) = Some comp
        /\ In (MkPProc cn comp) subs2.

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

  Lemma snd_M_run_sm_on_input_eq :
    forall {n} {cn} (p : n_proc n cn) i subs,
      snd (M_run_sm_on_input p i subs)
      = snd (sm2update p (sm2state p) i (select_n_procs (sm2level p) subs)).
  Proof.
    unfold M_run_sm_on_input.
    induction n; introv; simpl in *; tcsp;[].
    destruct p; simpl in *; tcsp.

    { unfold M_on_decr.
      rewrite decr_n_procs_as_select_n_procs_pred; simpl.
      split_pair; simpl; auto. }

    unfold M_on_decr; split_pair; simpl.
    rewrite IHn.
    fold (M_StateMachine n) in *; fold (n_proc n) in *.
    pose proof (select_n_procs_decr_n_procs (S n) (sm2level b) subs) as w; simpl in *.
    pose proof (sm2level_le_pred _ _ b) as u.
    rewrite w; auto; try omega.
  Qed.

  Lemma n_procs_0 :
    forall (l : n_procs 0), l = [].
  Proof.
    induction l; introv; simpl in *; tcsp.
    destruct a as [cn p]; simpl in *; tcsp.
  Qed.
  Hint Rewrite n_procs_0 : comp.

  Lemma implies_are_procs_n_procs_sm2ls :
    forall {n} {cn} (p : n_proc n cn),
      is_proc_n_proc p
      -> are_procs_n_procs (sm2ls p).
  Proof.
    introv h q; simpl in *; repndors; subst; tcsp.
  Qed.
  Hint Resolve implies_are_procs_n_procs_sm2ls : comp.

  Lemma implies_wf_procs_sm2ls :
    forall {n} {cn} (p : n_proc n cn),
      wf_procs (sm2ls p).
  Proof.
    tcsp.
  Qed.
  Hint Resolve implies_wf_procs_sm2ls : comp.

  Lemma similar_subs_sm2ls :
    forall {n} {cn} (p : n_proc n cn) (l : n_procs n),
      similar_subs (sm2ls p) l
      <-> (exists (q : n_proc n cn), l = (sm2ls q) /\ similar_sms p q).
  Proof.
    unfold sm2ls.
    introv; split; intro h; exrepnd; subst; eauto 2 with comp.

    { inversion h; subst; simpl in *; clear h.
      inversion sims; subst; simpl in *; clear sims.
      inversion simp as [? ? ? ? sims]; subst; GC.
      match goal with
      | [ H : context[p1] |- _ ] => rename H into h1
      end.
      match goal with
      | [ H : context[p2] |- _ ] => rename H into h2
      end.
      apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
      apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
      apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp. }

    constructor; eauto 3 with comp.
  Qed.

  Lemma M_comp_ls_on_op_inputs_sm2ls_as_run_sm_on_inputs :
    forall {cn} l {n} (p : n_proc n cn) subs comp,
      sm2level p = 0
      -> is_proc_n_proc p
      -> (M_comp_ls_on_op_inputs (sm2ls p) cn (map Some l) = Some comp
          <-> snd (run_sm_on_inputs p l subs) = comp).
  Proof.
    unfold M_comp_ls_on_op_inputs; simpl.
    induction l; introv lvl isp; simpl in *; tcsp.

    { dest_cases w.
      rewrite (UIP_refl_CompName _ w); simpl; auto; split; intro h; ginv; auto. }

    unfold M_run_ls_on_input_ls; simpl.
    unfold M_run_ls_on_input, on_comp; simpl.
    destruct (CompNameDeq cn cn) as [d|d]; tcsp; simpl.
    rewrite (UIP_refl_CompName _ d); simpl; auto; GC.
    unfold M_break.
    dest_cases w; repnd; simpl in *; symmetry in Heqw.
    applydup @is_proc_n_proc_run_on_input_implies_some in Heqw; auto.
    exrepnd; subst; simpl in *.
    pose proof (snd_M_run_sm_on_input_eq p a (sm2ls p)) as q.
    rewrite Heqw in q; simpl in q.

    assert (select_n_procs (sm2level p) subs = []) as eqn.
    { rewrite lvl; apply n_procs_0. }
    rewrite eqn; clear eqn.
    assert (select_n_procs (sm2level p) (sm2ls p) = []) as eqn.
    { rewrite lvl; apply n_procs_0. }
    rewrite eqn in q; clear eqn.

    split_pair; simpl in *; rewrite <- q; simpl.
    rewrite <- IHl; autorewrite with comp; eauto 3 with comp;[].

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input p a (sm2ls p)) as w.
    repeat (autodimp w hyp); eauto 3 with comp;[].
    unfold M_break in w.
    rewrite Heqw in w; repnd.
    apply similar_subs_sm2ls in w2; exrepnd; subst; simpl in *.
    dest_cases w.
  Qed.

  Lemma run_subs_leaves_eq_direct :
    forall {n} (subs1 subs2 : n_procs n),
      are_procs_n_procs subs1
      -> (run_subs_leaves subs1 subs2
          <-> run_subs_leaves_direct subs1 subs2).
  Proof.
    introv aps.
    introv; split; introv h lvl i; applydup h in i; clear h; auto; exrepnd; exists l.
    { applydup aps in i; simpl in *.
      pose proof (M_comp_ls_on_op_inputs_sm2ls_as_run_sm_on_inputs l p subs1 comp) as q.
      repeat (autodimp q hyp); eauto 3 with comp.
      apply q in i1; clear q; try congruence. }
    { applydup aps in i; simpl in *.
      pose proof (M_comp_ls_on_op_inputs_sm2ls_as_run_sm_on_inputs l p subs1 (snd (run_sm_on_inputs p l subs1))) as q.
      repeat (autodimp q hyp); eauto 3 with comp.
      destruct q as [q' q]; clear q'; autodimp q hyp.
      simpl in *; rewrite q; simpl.
      eexists; dands; eauto. }
  Qed.

  Lemma implies_run_subs_leaves_direct :
    forall {n} (subs1 subs2 : n_procs n),
      are_procs_n_procs subs1
      -> run_subs_leaves subs1 subs2
      -> run_subs_leaves_direct subs1 subs2.
  Proof.
    introv aps run; apply run_subs_leaves_eq_direct; auto.
  Qed.
  Hint Resolve implies_run_subs_leaves_direct : comp.

  Lemma if_run_subs_leaves_direct :
    forall {n} (subs1 subs2 : n_procs n),
      are_procs_n_procs subs1
      -> run_subs_leaves_direct subs1 subs2
      -> run_subs_leaves subs1 subs2.
  Proof.
    introv aps run; apply run_subs_leaves_eq_direct; auto.
  Qed.
  Hint Resolve if_run_subs_leaves_direct : comp.

  Lemma M_comp_ls_on_inputs_sm2ls :
    forall {n} {cn} (p : n_proc n cn),
      M_comp_ls_on_inputs (sm2ls p) cn [] = Some p.
  Proof.
    introv; unfold M_comp_ls_on_inputs; simpl; dest_cases w.
    rewrite (UIP_refl_CompName _ w); simpl; auto.
  Qed.
  Hint Rewrite @M_comp_ls_on_inputs_sm2ls : comp.

  Lemma M_comp_ls_on_op_inputs_sm2ls :
    forall {n} {cn} (p : n_proc n cn),
      M_comp_ls_on_op_inputs (sm2ls p) cn [] = Some p.
  Proof.
    introv; unfold M_comp_ls_on_op_inputs; simpl; dest_cases w.
    rewrite (UIP_refl_CompName _ w); simpl; auto.
  Qed.
  Hint Rewrite @M_comp_ls_on_op_inputs_sm2ls : comp.

  Lemma run_subs_leaves_refl :
    forall {n} (subs : n_procs n),
      run_subs_leaves subs subs.
  Proof.
    introv lvl i.
    exists ([] : list (cio_I (fio cn))); simpl; auto.
    autorewrite with comp; eauto.
  Qed.
  Hint Resolve run_subs_leaves_refl : comp.

  Lemma run_subs_leaves_direct_refl :
    forall {n} (subs : n_procs n),
      run_subs_leaves_direct subs subs.
  Proof.
    introv lvl i.
    exists ([] : list (cio_I (fio cn))); simpl; auto.
  Qed.
  Hint Resolve run_subs_leaves_direct_refl : comp.

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

  Lemma implies_in_replace_name :
    forall cn n (subs : n_procs n) p,
      In cn (get_names subs)
      -> In (MkPProc cn p) (replace_name p subs).
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    destruct (CompNameDeq c cn); tcsp.
  Qed.
  Hint Resolve implies_in_replace_name : comp.

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
      -> In cn (get_names (select_n_procs j subs)).
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
      -> In cn (get_names (select_n_procs j subs))
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

(*  Lemma implies_in_replace_sub_left :
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
  Hint Resolve implies_in_replace_sub_left : comp.*)

(*  Lemma implies_in_replace_subs_left :
    forall n (l : n_procs (pred n)) (subs : n_procs n) (p : n_nproc n),
      In p subs
      -> ~In (pp_name p) (get_names l)
      -> In p (replace_subs subs l).
  Proof.
    induction l; introv i ni; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    apply not_or in ni; repnd.
    apply IHl; auto; eauto 3 with comp.
  Qed.
  Hint Resolve implies_in_replace_subs_left : comp.*)

(*  Lemma implies_in_replace_subs_right :
    forall n (l : n_procs (pred n)) (subs : n_procs n) (p : n_nproc n),
      wf_procs l
      -> In p (incr_pred_n_procs l)
      -> In (pp_name p) (get_names subs)
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
  Hint Resolve implies_in_replace_subs_right : comp.*)

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

  Lemma in_replace_name_diff :
    forall {n} (l : n_procs n) p {cn} (q : n_proc n cn),
      cn <> pp_name p
      -> In p l
      -> In p (replace_name q l).
  Proof.
    induction l; introv d i; simpl in *; tcsp; repndors; subst; tcsp.
    { destruct p; simpl in *; tcsp; dest_cases w. }
    { destruct a as [cn' a]; simpl in *; dest_cases w. }
  Qed.

  Lemma implies_in_remove_name :
    forall {n} (l : n_procs n) p a,
      pp_name p <> a
      -> In p l
      -> In p (remove_name l a).
  Proof.
    induction l; introv d i; simpl in *; tcsp; repndors;
      subst; tcsp; dest_cases w.
  Qed.
  Hint Resolve implies_in_remove_name : comp.

  Lemma implies_in_remove_names :
    forall k {n} (l : n_procs n) p,
      ~ In (pp_name p) k
      -> In p l
      -> In p (remove_names l k).
  Proof.
    induction k; introv ni i; simpl in *; tcsp.
    apply not_or in ni; repnd.
    apply IHk; tcsp; eauto 3 with comp.
  Qed.
  Hint Resolve implies_in_remove_names : comp.

  Lemma remove_subs_nil_r :
    forall {n} {m} (l : n_procs n), remove_subs l ([] : n_procs m) = l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @remove_subs_nil_r : comp.

  Lemma interp_proc_run_subs_leaves_direct :
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
          -> run_subs_leaves_direct subs (fst (sm_update main s i subs)))
      -> are_procs_n_procs subs
      -> wf_procs subs
      -> run_subs_leaves_direct subs (fst (interp_proc p subs)).
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
      remember (app_m_proc p i subs) as ap; symmetry in Heqap; repnd.
      split_pairs; simpl.

      pose proof (sm2level_le_pred _ _ p) as ln0.

      rewrite (app_m_proc_some2 p i) in Heqap; simpl; eauto 3 with comp;[].
      remember (sm2update p (sm2state p) i (select_n_procs (sm2level p) subs)) as w; symmetry in Heqw.
      repnd; simpl.
      inversion Heqap; subst; simpl in *; clear Heqap.

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
        inversion q0; subst; clear q0; autorewrite with comp list.
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

      destruct (in_dec CompNameDeq cn0 (get_names (select_n_procs (sm2level p) subs))) as [d|d].

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
        apply in_replace_name_diff; simpl; tcsp;[].
        apply in_app_iff; right.
        rewrite lvl in eqs1; symmetry in eqs1.
        apply implies_in_raise_to_n_procs; try omega.
        eexists;dands;[|eauto];[].
        simpl.
        rewrite option_map_Some.
        eexists;dands;[|eauto];[].

        pose proof (sm2level_le_pred _ _ p) as lvln0.
        apply raise_to_n_proc_as_select_n_proc; try omega.
        apply select_n_proc_fst_run_sm_in_inputs; auto; try omega. }

      { applydup similar_subs_preserves_get_names in q0 as eqns.
        dup d as d'; rewrite eqns in d'.
        exists ([] : list (cio_I (fio cn0))); simpl.
        apply in_replace_name_diff; simpl; tcsp;[].
        apply in_app_iff; left; auto.
        apply implies_in_remove_names; simpl; auto. } }
  Qed.

  Lemma interp_s_proc_run_subs_leaves_direct :
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
          -> run_subs_leaves_direct subs (fst (sm_update main s i subs)))
      -> are_procs_n_procs subs
      -> wf_procs subs
      -> run_subs_leaves_direct subs (fst (interp_s_proc p subs)).
  Proof.
    introv imp aps wf.
    unfold interp_s_proc, to_M_n_some_state; simpl.
    unfold bind_pair, bind; simpl.
    rewrite (surjective_pairing (interp_proc p subs)); simpl.
    rewrite (surjective_pairing (snd (interp_proc p subs))); simpl.
    apply interp_proc_run_subs_leaves_direct; auto.
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
      -> run_subs_leaves_direct subs (fst (sm_update main s i subs)).
  Proof.
    induction n as [? ind] using comp_ind; introv ip ap wf;[].
    unfold is_proc_n_proc_at in ip; exrepnd.
    rewrite ip0.
    unfold proc2upd; simpl.
    apply interp_s_proc_run_subs_leaves_direct; auto.
  Qed.

  Lemma run_subs_leaves_direct_trans :
    forall n (subs1 subs2 subs3 : n_procs n),
      run_subs_leaves_direct subs1 subs2
      -> run_subs_leaves_direct subs2 subs3
      -> run_subs_leaves_direct subs1 subs3.
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
  Hint Resolve run_subs_leaves_direct_trans : comp.


  Lemma run_subs_leaves_trans :
    forall n (subs1 subs2 subs3 : n_procs n),
      are_procs_n_procs subs1
      -> similar_subs subs1 subs2
      -> run_subs_leaves subs1 subs2
      -> run_subs_leaves subs2 subs3
      -> run_subs_leaves subs1 subs3.
  Proof.
    introv aps sim runa runb.
    apply run_subs_leaves_eq_direct in runa; auto.
    apply run_subs_leaves_eq_direct in runb; eauto 3 with comp.
  Qed.
  Hint Resolve run_subs_leaves_trans : comp.

  Lemma similar_sms_at_update_state :
    forall n cn (p : n_proc_at n cn) a,
      similar_sms_at p (update_state p a).
  Proof.
    introv; split; simpl; auto.
  Qed.
  Hint Resolve similar_sms_at_update_state : comp.

  Lemma level_zero_implies_in_decr_n_procs :
    forall {n} (l : n_procs (S n)) (p : n_nproc (S n)),
      sm2level (pp_proc p) = 0
      -> In p l
      -> n = 0
         \/
         exists q,
           decr_n_nproc p = Some q
           /\ In q (decr_n_procs l).
  Proof.
    unfold decr_n_procs; induction l; introv lvl i; simpl in *; tcsp.
    repndors; subst; tcsp.
    { destruct p as [cn p]; simpl in *.
      destruct p; simpl in *; tcsp; subst; simpl in *; tcsp.
      right.
      eexists; dands; eauto. }
    { pose proof (IHl p) as IHl; repeat (autodimp IHl hyp).
      repndors; exrepnd; subst; tcsp.
      right.
      exists q; dands; auto.
      dest_cases w. }
  Qed.

  Lemma update_state_op_m_incr_n_proc :
    forall {n} {cn} (p : n_proc n cn) s,
      update_state_op_m (incr_n_proc p) s
      = incr_n_proc (update_state_op_m p s).
  Proof.
    introv.
    unfold incr_n_proc, update_state_op_m; destruct s; simpl; auto.
  Qed.

  Lemma decr_n_procs_raise_to_n_procs :
    forall {n} (subs : n_procs n) k,
      n <= k
      -> decr_n_procs (raise_to_n_procs (S k) subs)
         = raise_to_n_procs k subs.
  Proof.
    unfold decr_n_procs, raise_to_n_procs.
    induction subs; introv lek; simpl in *; tcsp.
    destruct a as [cn p]; simpl in *.
    dest_cases w; simpl in *; tcsp; symmetry in Heqw.
    { apply option_map_Some in Heqw; exrepnd; subst; simpl in *.
      dest_cases w; subst; try omega.
      apply option_map_Some in Heqw1; exrepnd; subst; simpl in *.
      allrw; simpl; auto. }
    { apply option_map_None in Heqw; dest_cases w.
      apply option_map_None in Heqw.
      allrw; auto. }
  Qed.

  Lemma snd_run_sm_on_inputs_incr_n_proc_eq :
    forall {n} {cn} l (p : n_proc n cn) subs,
      snd (run_sm_on_inputs (incr_n_proc p) l subs)
      = incr_n_proc (snd (run_sm_on_inputs p l (decr_n_procs subs))).
  Proof.
    induction l; introv; simpl in *; tcsp.
    pose proof (select_n_procs_decr_n_procs (S n) (sm2level p) subs) as z.
    simpl in *.
    pose proof (sm2level_le_pred _ _ p) as u.
    repeat (autodimp z hyp); try omega.
    rewrite z; clear z.
    dest_cases w; repnd; simpl in *; symmetry in Heqw.
    rewrite update_state_op_m_incr_n_proc.
    rewrite IHl; clear IHl.
    rewrite decr_n_procs_raise_to_n_procs; auto; try omega.
  Qed.

  Lemma update_subs_nil_r :
    forall {n} (l : n_procs (S n)), update_subs l [] = l.
  Proof.
    introv; unfold update_subs; simpl; autorewrite with comp list; auto.
  Qed.
  Hint Rewrite @update_subs_nil_r : comp.

  Lemma are_procs_implies_run_subs_direct2 :
    forall {n} {cn}
           (p    : n_proc n cn)
           (i    : cio_I (fio cn))
           (subs : n_procs n),
      is_proc_n_proc p
      -> are_procs_n_procs subs
      -> wf_procs subs
      -> run_subs_leaves_direct subs (fst (M_run_sm_on_input p i subs)).
  Proof.
    unfold M_run_sm_on_input.
    induction n as [? ind] using comp_ind; introv ip ap wf;[].
    destruct n; simpl in *; tcsp.
    destruct p; simpl in *; tcsp.

    { unfold M_on_decr; simpl; dest_cases w; symmetry in Heqw; repnd; simpl in *.
      pose proof (are_procs_implies_run_subs
                    a (sm_state a) i (decr_n_procs subs)) as q.
      repeat (autodimp q hyp); eauto 3 with comp;
        try (apply (are_procs_n_procs_decr_n_procs subs); auto);
        try (apply (wf_procs_decr_n_procs subs); auto);[].
      rewrite Heqw in q; simpl in q.

      introv lvl j.
      applydup @level_zero_implies_in_decr_n_procs in j;
        try (complete (simpl; destruct p; simpl in *; tcsp));[].
      repndors.

      { subst.
        pose proof (n_procs_0 w0); subst; autorewrite with comp.
        exists ([] : list (cio_I (fio cn0))); simpl; auto. }

      exrepnd.
      simpl in *.
      destruct p; simpl in *; tcsp; ginv; GC.

      inversion j0; subst; simpl in *; GC; clear j0.
      apply q in j1; exrepnd; auto;[].
      exists l.
      apply in_app_iff; right.
      pose proof (snd_run_sm_on_inputs_incr_n_proc_eq
                    l b subs) as z.
      unfold incr_n_proc in z; simpl in *.
      fold (M_StateMachine n) in *; fold (n_proc n) in *.
      rewrite z; clear z.
      simpl.
      apply in_map_iff; eexists; dands;[|eauto]; simpl; auto. }

    { unfold M_on_decr; split_pair; simpl.
      pose proof (ind n) as ind; autodimp ind hyp.
      pose proof (ind cn b i (decr_n_procs subs)) as ind.
      repeat (autodimp ind hyp); eauto 3 with comp;
        try (apply (are_procs_n_procs_decr_n_procs subs); auto);
        try (apply (wf_procs_decr_n_procs subs); auto);[].
      remember (fst (M_on_sm b (fun p => sm_update p (sm_state p) i) (decr_n_procs subs))) as subs'.
      simpl in *.
      rewrite <- Heqsubs' in ind; rewrite <- Heqsubs'.
      clear Heqsubs'.

      introv lvl j.
      applydup @level_zero_implies_in_decr_n_procs in j;
        try (complete (simpl; destruct p; simpl in *; tcsp));[].
      repndors.

      { subst.
        pose proof (n_procs_0 subs'); subst.
        unfold update_subs; simpl.
        unfold remove_subs; simpl.
        simpl in *; destruct p; simpl in *; tcsp; GC. }

      exrepnd.
      simpl in *.
      destruct p; simpl in *; tcsp; ginv; GC.

      inversion j0; subst; simpl in *; GC; clear j0.
      apply ind in j1; exrepnd; auto;[].
      exists l.
      apply in_app_iff; right.
      pose proof (snd_run_sm_on_inputs_incr_n_proc_eq
                    l b0 subs) as z.
      unfold incr_n_proc in z; simpl in *.
      fold (M_StateMachine n) in *; fold (n_proc n) in *.
      rewrite z; clear z.
      simpl.
      apply in_map_iff; eexists; dands;[|eauto]; simpl; auto. }
  Qed.

  Definition has_comp cn {n} (ls : n_procs n) :=
    exists comp, find_name cn ls = Some comp.

  Definition ls_run_subs cn {n} (ls : n_procs n) :=
    forall i,
      run_subs_leaves ls (M_run_ls_on_input_ls ls cn i).

  Lemma are_procs_n_procs_implies_ls_run_sub :
    forall cn {n} (ls : n_procs n),
      has_comp cn ls
      -> are_procs_n_procs ls
      -> wf_procs ls
      -> ls_run_subs cn ls.
  Proof.
    introv hm h wf; introv.
    unfold are_procs_n_procs, wf_procs  in *.
    unfold M_run_ls_on_input_ls.
    apply run_subs_leaves_eq_direct; auto.
    unfold M_run_ls_on_input, on_comp; simpl.
    unfold has_comp in hm; exrepnd; allrw.
    unfold M_break.
    remember (M_run_sm_on_input comp i ls) as run; symmetry in Heqrun.
    repnd; simpl in *.
    applydup @is_proc_n_proc_run_on_input_implies_some in Heqrun; eauto 3 with comp;[].
    exrepnd; subst; simpl in *.

    pose proof (are_procs_implies_run_subs_direct2 comp i ls) as q; repeat (autodimp q hyp); eauto 3 with comp;[].
    rewrite Heqrun in q; simpl in *.
    introv lvl j.
    destruct (CompNameDeq cn cn0); subst; simpl in *;
      [|apply q in j; auto; exrepnd; exists l; apply in_replace_name_right; simpl; auto];[].

    eapply find_name_in_implies_eq in j; eauto; subst; simpl in *.
    exists [i]; simpl.
    pose proof (snd_M_run_sm_on_input_eq p i ls) as z.
    rewrite Heqrun in z; simpl in z.
    split_pair.
    simpl in *; rewrite <- z; simpl.
    apply implies_in_replace_name.
    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input p i ls) as x.
    repeat (autodimp x hyp); eauto 3 with comp;[].
    unfold M_break in x; rewrite Heqrun in x; repnd.
    apply similar_subs_preserves_get_names in x0; rewrite <- x0; eauto 3 with comp.
  Qed.

(*  Lemma M_run_sm_on_input_implies :
    forall {n} {cn} (p : n_proc n cn) i subs,
      snd (sm2update p (sm2state p) i (select_n_procs (sm2level p) subs))
      = snd (M_run_sm_on_input p i subs).
  Proof.
    unfold M_run_sm_on_input.
    induction n; introv; simpl in *; tcsp.
    destruct p; simpl in *; tcsp.
    { unfold M_on_decr; dest_cases w; symmetry in Heqw.
      rewrite decr_n_procs_as_select_n_procs_pred in Heqw; simpl in *.
      fold (M_StateMachine n) in *; fold (n_proc n) in *.
      rewrite Heqw; simpl; auto. }
    { unfold M_on_decr.
      pose proof (sm2level_le_pred _ _ b) as u.
      rewrite <- select_n_procs_decr_n_procs; simpl; auto; try omega;[].
      rewrite IHn; clear IHn.
      dest_cases w; symmetry in Heqw; simpl; auto. }
  Qed.*)

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

  Lemma M_byz_run_ls_on_this_one_event_M_nt_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> isCorrect e
      -> M_byz_run_ls_on_this_one_event ls1 e = ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    introv wf aps cor run.
    unfold M_byz_run_ls_on_this_one_event in run; simpl in *.
    unfold M_byz_run_ls_on_one_event in run; simpl in *.
    remember (M_byz_run_ls_on_input ls1 (msg_comp_name S) (trigger e)) as h; repnd;
      simpl in *; subst; symmetry in Heqh.
    unfold isCorrect, trigger_op in *.
    remember (trigger e) as trig; clear Heqtrig.
    destruct trig; simpl in *; tcsp; GC.
    unfold M_run_ls_on_input, on_comp in Heqh.
    dest_cases w; symmetry in Heqw; simpl in *; tcsp;
      [|ginv; dands; eauto 3 with comp];[].

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input
                  w d ls1) as q.
    repeat (autodimp q hyp); eauto 3 with comp;[].
    pose proof (are_procs_implies_run_subs_direct2 w d ls1) as z.
    repeat (autodimp z hyp); eauto 3 with comp;[].
    unfold M_break in *.
    dest_cases u; symmetry in Hequ; repnd; simpl in *.
    applydup @is_proc_n_proc_run_on_input_implies_some in Hequ; eauto 3 with comp;[].
    exrepnd; subst; simpl in *.
    inversion Heqh; subst; simpl in *; clear Heqh.
    unfold wf_procs, are_procs_n_procs.
    dands; eauto 3 with comp.
    { eapply similar_subs_preserves_wf_procs;
        [apply implies_similar_subs_replace_name; eauto|];[].
      eapply wf_procs_replace_name; eauto; autorewrite with comp; auto. }
    { introv j.
      apply in_replace_name_update_state_m_implies_is_proc_n_proc in j; eauto 3 with comp. }
    { eapply similar_subs_trans;
        [|apply implies_similar_subs_replace_name;eauto].
      apply similar_subs_sym.
      apply similar_subs_replace_name_update_state_m_find; auto. }
    { apply run_subs_leaves_eq_direct; auto;[].
      introv lvl j; applydup z in j; auto; exrepnd.
      destruct (CompNameDeq cn (msg_comp_name S)); subst; tcsp;
        [|exists l; apply in_replace_name_right; auto];[].
      dup Heqw as fn; eapply find_name_in_implies_eq in Heqw; eauto; subst.
      exists [d]; simpl.
      dest_cases v; symmetry in Heqv; repnd; simpl in *.
      pose proof (snd_M_run_sm_on_input_eq p d ls1) as x.
      rewrite Hequ in x; rewrite Heqv in x; simpl in x; ginv; simpl in *.
      apply implies_in_replace_name; eauto 3 with comp.
      apply similar_subs_preserves_get_names in q0; rewrite <- q0.
      eapply find_name_implies_in_get_names; eauto. }
  Qed.


  Lemma M_byz_run_ls_on_event_M_nt_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> has_correct_trace_bounded e
      -> M_byz_run_ls_on_event ls1 e = ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv wf aps cor run.
    rewrite M_byz_run_ls_on_event_unroll in run.

    destruct (dec_isFirst e) as [d|d]; ginv; auto;[|].
    { apply M_byz_run_ls_on_this_one_event_M_nt_preserves_subs in run; tcsp; eauto 3 with eo. }

    remember (M_byz_run_ls_before_event ls1 e) as ls'; simpl in *; symmetry in Heqls'.
    rewrite M_byz_run_ls_before_event_as_M_byz_run_ls_on_event_pred in Heqls'; auto;[].
    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo;[].
    pose proof (ind L S ls1 ls') as ind.
    repeat (autodimp ind hyp); eauto 3 with eo; repnd.
    apply M_byz_run_ls_on_this_one_event_M_nt_preserves_subs in run; eauto 3 with eo; repnd.
    dands; eauto 3 with comp.
  Qed.

  Lemma M_byz_run_ls_before_event_M_nt_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> has_correct_trace_bounded_lt e
      -> M_byz_run_ls_before_event ls1 e = ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv wf aps cor run.
    rewrite M_byz_run_ls_before_event_unroll in run.

    destruct (dec_isFirst e) as [d|d]; ginv; auto;[|].
    { subst; dands; eauto 3 with comp. }

    remember (M_byz_run_ls_before_event ls1 (local_pred e)) as ls'; simpl in *; symmetry in Heqls'.
    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo;[].
    pose proof (ind L S ls1 ls') as ind.
    repeat (autodimp ind hyp); eauto 3 with eo; repnd;[].
    apply M_byz_run_ls_on_this_one_event_M_nt_preserves_subs in run; eauto 3 with eo; repnd;[].
    dands; eauto 3 with comp.
  Qed.

  Lemma M_run_ls_on_event_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_run_ls_on_event ls1 e = Some ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    introv wf aps run.
    applydup @M_run_ls_on_event_M_byz_run_ls_on_event in run.
    apply M_byz_run_ls_on_event_M_nt_preserves_subs in run0; tcsp; eauto 3 with eo comp.
  Qed.

  Lemma M_run_ls_before_event_preserves_subs :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_run_ls_before_event ls1 e = Some ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    introv wf aps run.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in run.
    apply M_byz_run_ls_before_event_M_nt_preserves_subs in run0; tcsp; eauto 2 with eo comp.
  Qed.

(*  Lemma are_procs_n_procs_implies_some :
    forall {L S} (ls : LocalSystem L S) s i subs subs' sop o,
      are_procs_n_procs ls
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
  Qed.*)

  Lemma reduces_option_map_some :
    forall {A B} (a : A) (f : A -> B),
      option_map f (Some a) = Some (f a).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduces_option_map_some : comp.

(*  Lemma reduce_map_op_untrusted_op_some :
    forall {T} {A} (x : M_trusted T) (F : T -> option A),
      map_op_untrusted_op (Some x) F
      = map_untrusted_op x F.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduce_map_op_untrusted_op_some : comp.*)

(*  Lemma reduce_map_op_untrusted_some :
    forall {T} {A} (x : M_trusted T) (F : T -> A),
      map_op_untrusted (Some x) F
      = Some (map_untrusted x F).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduce_map_op_untrusted_some : comp.*)

(*  Lemma reduce_map_untrusted_op_M_nt :
    forall {T} {A} (x : T) (F : T -> option A),
      map_untrusted_op (M_nt x) F = option_map M_nt (F x).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduce_map_untrusted_op_M_nt : comp.*)

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

  Lemma run_subs_leaves_direct_of_find_name :
    forall {L} {cn} (ls ls' : n_procs L) (sm : n_proc L cn),
      sm2level sm = 0
      -> wf_procs ls'
      -> find_name cn ls = Some sm
      -> run_subs_leaves_direct ls ls'
      -> exists l,
          find_name cn ls' = Some (snd (run_sm_on_inputs sm l ls)).
  Proof.
    introv lvl wf fs run.
    applydup @find_name_implies_in in fs.
    apply run in fs0; auto;[].
    exrepnd.
    exists l.
    apply in_implies_find_name; auto.
  Qed.

  Lemma run_subs_leaves_of_find_name :
    forall {L} {cn} (ls ls' : n_procs L) (sm : n_proc L cn),
      sm2level sm = 0
      -> wf_procs ls'
      -> find_name cn ls = Some sm
      -> run_subs_leaves ls ls'
      -> exists l comp,
          M_comp_ls_on_op_inputs (sm2ls sm) cn (map Some l) = Some comp
          /\ find_name cn ls' = Some comp.
  Proof.
    introv lvl wf fs run.
    applydup @find_name_implies_in in fs.
    apply run in fs0; auto;[].
    exrepnd.
    exists l comp; dands; auto.
    apply in_implies_find_name; auto.
  Qed.

  Lemma find_name_implies_state_of_component :
    forall {L} {cn} (ls : n_procs L) (sm : n_proc L cn),
      wf_procs ls
      -> find_name cn ls = Some sm
      -> state_of_component cn ls = Some (sm2state sm).
  Proof.
    introv wf fs.
    unfold state_of_component; allrw; simpl; auto.
  Qed.

(*Lemma state_of_components_upd_ls_main_state_and_subs_if_in :
    forall {cn L S} s (ls : LocalSystem L S) (p : n_proc L cn) (l : n_procs L),
      wf_procs ls
      -> wf_procs l
      -> In (MkPProc cn p) l
      -> In cn (get_names (ls_subs ls))
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
  Qed.*)

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

(*Lemma M_byz_run_update_on_list_update_state_m_eq :
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
  Qed.*)

(*Lemma M_byz_run_sm_on_list_as_run_sm_on_inputs :
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
  Qed.*)

  Fixpoint is_trusted_in {n:nat} (cn : CompName) (l : n_procs n) : bool :=
    match l with
    | [] => false
    | MkPProc cn' pr :: rest =>
      if CompNameDeq cn cn' then comp_name_trust cn'
      else is_trusted_in cn rest
    end.

(*  Lemma ls_subs_MkLocalSystem :
    forall L S (main : n_proc_at L (msg_comp_name S)) (subs : n_procs L),
      MkLocalSystem main subs = subs.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite ls_subs_MkLocalSystem : comp.*)

  Lemma is_trusted_implies_in_get_names :
    forall cn n (subs : n_procs n),
      is_trusted_in cn subs = true
      -> In cn (get_names subs).
  Proof.
    induction subs; introv ist; simpl in *; tcsp.
    destruct a as [c a]; simpl in *; dest_cases w.
  Qed.

(*  Lemma wf_is_trusted_implies_state_of_subcomponents :
    forall cn {L S} (ls : LocalSystem L S),
      wf_procs ls
      -> is_trusted_in cn ls = true
      -> state_of_component cn ls
         = state_of_subcomponents ls cn.
  Proof.
    tcsp.
  Qed.*)

(*  Lemma is_trusted_implies_find_trusted :
    forall cn n (subs : n_procs n),
      is_trusted_in cn subs = true
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
  Qed.*)

(*  Lemma M_byz_run_sm_on_list_as_run_sm_on_inputs_app :
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
  Qed.*)

  Lemma reduce_map_option_some :
    forall {A B} (f : A -> option B) (a : A),
      map_option f (Some a) = f a.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @reduce_map_option_some : comp.

(*  Lemma M_run_update_on_list_update_state_m_eq :
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
  Qed.*)

(*  Lemma M_run_sm_on_list_as_run_sm_on_inputs :
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
  Qed.*)

  Lemma decr_n_procs_0 :
    forall (l : n_procs 0), decr_n_procs l = [].
  Proof.
    introv; rewrite (n_procs_0 l); simpl; auto.
  Qed.
  Hint Rewrite decr_n_procs_0 : comp.

  Definition unit_update : M_Update 0 (msg_comp_name 1) unit :=
    fun s m => interp_s_proc ([R] (s,[])).

  Definition unit_sm : n_proc 1 (msg_comp_name 1) :=
    build_m_sm unit_update tt.

  Definition unit_ls : LocalSystem 1 1 :=
    [MkPProc (msg_comp_name 1) unit_sm].

  Definition empty_ls (Lv : nat) (Sp : CompNameState) : LocalSystem Lv Sp := [].

  Lemma are_procs_unit_ls : are_procs_n_procs unit_ls.
  Proof.
    introv i; simpl in *; repndors; subst; tcsp; simpl.
    eexists; introv; unfold proc2upd; reflexivity.
  Qed.
  Hint Resolve are_procs_unit_ls : comp.

  Lemma are_procs_empty_ls : forall l s, are_procs_n_procs (empty_ls l s).
  Proof.
    introv i; simpl in *; tcsp.
  Qed.
  Hint Resolve are_procs_empty_ls : comp.

  Lemma wf_unit_ls : wf_procs unit_ls.
  Proof.
    tcsp.
  Qed.
  Hint Resolve wf_unit_ls : comp.

  Lemma wf_empty_ls : forall l s, wf_procs (empty_ls l s).
  Proof.
    tcsp.
  Qed.
  Hint Resolve wf_empty_ls : comp.

  Lemma M_run_ls_before_event_unit_ls :
    forall {eo : EventOrdering} (e : Event) ls,
      M_run_ls_before_event unit_ls e = Some ls
      -> ls = unit_ls.
  Proof.
    intros eo e; induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_run_ls_before_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; ginv; auto.
    apply map_option_Some in h; exrepnd; rev_Some.
    apply ind in h1; clear ind; eauto 3 with eo; subst.
    apply map_option_Some in h0; exrepnd; rev_Some.
    inversion h1; subst; simpl in *; clear h1; tcsp.
  Qed.

  Lemma M_run_ls_before_event_empty_ls :
    forall {eo : EventOrdering} (e : Event) l s ls,
      M_run_ls_before_event (empty_ls l s) e = Some ls
      -> ls = empty_ls l s.
  Proof.
    intros eo e; induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_run_ls_before_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; ginv; auto.
    apply map_option_Some in h; exrepnd; rev_Some.
    apply ind in h1; eauto 3 with eo; subst.
    apply map_option_Some in h0; exrepnd; rev_Some.
    inversion h1; clear h1; simpl in *; subst; tcsp.
  Qed.

(*  Lemma sm_halted_update_state :
    forall {L S} (a : n_proc_at L S) x,
      sm_halted (update_state a x) = sm_halted a.
  Proof.
    introv; tcsp.
  Qed.
  Hint Rewrite @sm_halted_update_state : comp.*)

  Lemma M_byz_run_ls_on_this_one_event_empty_ls :
    forall {eo : EventOrdering} (e : Event) l  s ls,
      M_byz_run_ls_on_this_one_event (empty_ls l s) e = ls
      -> ls = empty_ls l s.
  Proof.
    introv h; subst.
    unfold M_byz_run_ls_on_this_one_event; simpl in *.
    unfold M_byz_run_ls_on_one_event; simpl in *.
    remember (M_byz_run_ls_on_input (empty_ls l s) (msg_comp_name s) (trigger e)) as run.
    symmetry in Heqrun; repnd; simpl in *.
    remember (trigger e) as trig; destruct trig; simpl in *; tcsp; ginv;
      unfold M_run_ls_on_trusted,  M_run_ls_on_input, on_comp in *; simpl in *; ginv.
  Qed.

  Lemma M_byz_run_ls_before_event_empty_ls :
    forall {eo : EventOrdering} (e : Event) l s ls,
      M_byz_run_ls_before_event (empty_ls l s) e = ls
      -> ls = empty_ls l s.
  Proof.
    intros eo e; induction e as [e ind] using predHappenedBeforeInd;[]; introv h.
    rewrite M_byz_run_ls_before_event_unroll in h.
    destruct (dec_isFirst e) as [d|d]; ginv.
    remember (M_byz_run_ls_before_event (empty_ls l s) (local_pred e)) as run; symmetry in Heqrun; simpl in *.
    apply ind in Heqrun; eauto 3 with eo; subst run.
    apply M_byz_run_ls_on_this_one_event_empty_ls in h; auto.
  Qed.

  Lemma M_byz_run_ls_on_event_empty_ls :
    forall {eo : EventOrdering} (e : Event) l s ls,
      M_byz_run_ls_on_event (empty_ls l s) e = ls
      -> ls = empty_ls l s.
  Proof.
    introv run.
    rewrite M_byz_run_ls_on_event_unroll2 in run.
    remember (M_byz_run_ls_before_event (empty_ls l s) e) as h; simpl in *; symmetry in Heqh.
    apply M_byz_run_ls_before_event_empty_ls in Heqh; simpl in *; subst h.
    eapply M_byz_run_ls_on_this_one_event_empty_ls; eauto.
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
    inversion run1; subst; tcsp.
  Qed.

  Lemma find_name_implies_has_comp :
    forall {n} (ls : n_procs n) cn p,
      find_name cn ls = Some p
      -> has_comp cn ls.
  Proof.
    introv fn; exists p; auto.
  Qed.
  Hint Resolve find_name_implies_has_comp : comp.

  Lemma similar_subs_preserves_has_comp :
    forall cn {n} (ls1 ls2 : n_procs n),
      similar_subs ls1 ls2
      -> has_comp cn ls1
      -> has_comp cn ls2.
  Proof.
    introv sim hc.
    unfold has_comp in *; exrepnd.
    eapply similar_subs_preserves_find_name in sim; eauto.
    exrepnd; eauto.
  Qed.
  Hint Resolve similar_subs_preserves_has_comp : comp.

  Lemma M_run_sm_on_input_implies_M_run_sm2ls_on_input :
    forall {n} {cn} (p : n_proc n cn) i ls1 ls2 s out,
      is_proc_n_proc p
      -> sm2level p = 0
      -> M_run_sm_on_input p i ls1 = (ls2, (Some s, out))
      -> M_run_ls_on_input (sm2ls p) cn i = (sm2ls (update_state_m p s), Some out).
  Proof.
    introv isp lvl run.
    unfold M_run_ls_on_input, M_break, on_comp; simpl.
    destruct (CompNameDeq cn cn) as [d|d]; tcsp.
    rewrite (UIP_refl_CompName _ d); simpl; auto; GC.
    remember (M_run_sm_on_input p i (sm2ls p)) as q; symmetry in Heqq; repnd; simpl in *.
    applydup @is_proc_n_proc_run_on_input_implies_some in Heqq; auto; exrepnd; subst; simpl in *.

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input p i (sm2ls p)) as z.
    repeat (autodimp z hyp); eauto 3 with comp;[].
    unfold M_break in z.
    rewrite Heqq in z; repnd.
    apply similar_subs_sm2ls in z0; exrepnd; subst; simpl in *.
    dest_cases w; GC.

    pose proof (snd_M_run_sm_on_input_eq p i (sm2ls p)) as x1.
    pose proof (snd_M_run_sm_on_input_eq p i ls1) as x2.
    rewrite Heqq in x1.
    rewrite run in x2.
    simpl in *.

    assert (select_n_procs (sm2level p) (sm2ls p) = []) as xx.
    { rewrite lvl; apply n_procs_0. }
    rewrite xx in x1; clear xx.
    assert (select_n_procs (sm2level p) ls1 = []) as xx.
    { rewrite lvl; apply n_procs_0. }
    rewrite xx in x2; clear xx.
    rewrite <- x1 in x2; ginv.
  Qed.

  Lemma M_run_sm2ls_on_op_inputs_some_implies_sm2ls :
    forall {cn} l {n} (p : n_proc n cn) (ls : n_procs n),
      is_proc_n_proc p
      -> M_run_ls_on_op_inputs (sm2ls p) cn l = Some ls
      -> exists (q : n_proc n cn), ls = sm2ls q /\ similar_sms p q.
  Proof.
    induction l; introv isp run; simpl in *; ginv.
    { exists p; dands; eauto 3 with comp. }

    apply map_option_Some in run; exrepnd; subst; simpl in *; rev_Some.
    unfold M_run_ls_on_input_ls in *.
    remember (M_run_ls_on_input (sm2ls p) cn a0) as z; symmetry in Heqz; repnd; simpl in *.
    unfold M_run_ls_on_input, on_comp in Heqz; simpl in *.
    destruct (CompNameDeq cn cn) as [d|d]; tcsp; simpl in *.
    rewrite (UIP_refl_CompName _ d) in Heqz; simpl in *; GC.
    unfold M_break in Heqz; simpl in *.
    remember (M_run_sm_on_input p a0 (sm2ls p)) as x; symmetry in Heqx; repnd; simpl in *.
    applydup @is_proc_n_proc_run_on_input_implies_some in Heqx; auto; exrepnd; subst; simpl in *.
    inversion Heqz; subst; simpl in *; clear Heqz.

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input p a0 (sm2ls p)) as u.
    repeat (autodimp u hyp); eauto 3 with comp.
    unfold M_break in u.
    rewrite Heqx in u; repnd.
    apply similar_subs_sm2ls in u0; exrepnd; subst; simpl in *.
    destruct (CompNameDeq cn cn); tcsp.
    apply IHl in run0; eauto 3 with comp;[].
    exrepnd; subst; simpl in *.
    exists q0; dands; auto.
    eapply similar_sms_trans;[eauto|].
    eapply similar_sms_trans;[|eauto].
    eauto 3 with comp.
  Qed.

  Lemma M_run_sm2ls_on_inputs_some_implies_sm2ls :
    forall {cn} l {n} (p : n_proc n cn),
      is_proc_n_proc p
      -> exists (q : n_proc n cn), M_run_ls_on_inputs (sm2ls p) cn l = sm2ls q /\ similar_sms p q.
  Proof.
    induction l; introv isp; simpl in *; ginv.
    { exists p; dands; eauto 3 with comp. }

    unfold M_run_ls_on_input_ls in *.
    remember (M_run_ls_on_input (sm2ls p) cn a) as z; symmetry in Heqz; repnd; simpl in *.
    unfold M_run_ls_on_input, on_comp in Heqz; simpl in *.
    destruct (CompNameDeq cn cn) as [d|d]; tcsp; simpl in *.
    rewrite (UIP_refl_CompName _ d) in Heqz; simpl in *; GC.
    unfold M_break in Heqz; simpl in *.
    remember (M_run_sm_on_input p a (sm2ls p)) as x; symmetry in Heqx; repnd; simpl in *.
    applydup @is_proc_n_proc_run_on_input_implies_some in Heqx; auto; exrepnd; subst; simpl in *.
    inversion Heqz; subst; simpl in *; clear Heqz.

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input p a (sm2ls p)) as u.
    repeat (autodimp u hyp); eauto 3 with comp.
    unfold M_break in u.
    rewrite Heqx in u; repnd.
    apply similar_subs_sm2ls in u0; exrepnd; subst; simpl in *.
    destruct (CompNameDeq cn cn); tcsp; GC.
    pose proof (IHl _ (update_state_m p s0)) as IHl; autodimp IHl hyp; eauto 3 with comp;[].
    exrepnd; simpl in *.
    exists q0; dands; simpl in *; auto.
    eapply similar_sms_trans;[eauto|].
    eapply similar_sms_trans;[|eauto].
    eauto 3 with comp.
  Qed.

  Lemma M_comp_sm2ls_on_op_inputs_implies_similar_sms :
    forall {n} {cn} (p : n_proc n cn) l q,
      is_proc_n_proc p
      -> M_comp_ls_on_op_inputs (sm2ls p) cn l = Some q
      -> similar_sms p q.
  Proof.
    introv isp h.
    apply map_option_Some in h; exrepnd; rev_Some.
    apply M_run_sm2ls_on_op_inputs_some_implies_sm2ls in h1; auto; exrepnd; subst; simpl in *.
    dest_cases w; ginv.
    rewrite (UIP_refl_CompName _ w); simpl; auto.
  Qed.

  Lemma M_comp_sm2ls_on_inputs_implies_similar_sms :
    forall {n} {cn} (p : n_proc n cn) l q,
      is_proc_n_proc p
      -> M_comp_ls_on_inputs (sm2ls p) cn l = Some q
      -> similar_sms p q.
  Proof.
    introv isp h.
    pose proof (M_run_sm2ls_on_inputs_some_implies_sm2ls l p) as z.
    autodimp z hyp; exrepnd.
    unfold M_comp_ls_on_inputs in h; rewrite z1 in h; simpl in *; dest_cases w.
    rewrite (UIP_refl_CompName _ w) in h; simpl in *; ginv.
  Qed.

  Lemma implies_M_comp_sm2ls_on_op_inputs_app :
    forall {cn} l k {n} (p : n_proc n cn) q r,
      is_proc_n_proc p
      -> M_comp_ls_on_op_inputs (sm2ls p) cn l = Some q
      -> M_comp_ls_on_op_inputs (sm2ls q) cn k = Some r
      -> M_comp_ls_on_op_inputs (sm2ls p) cn (l ++ k) = Some r.
  Proof.
    unfold M_comp_ls_on_op_inputs.
    induction l; introv isp runa runb; simpl in *; tcsp.

    { dest_cases w. }

    apply map_option_Some in runa; exrepnd; rev_Some.
    apply map_option_Some in runb; exrepnd; rev_Some.
    apply map_option_Some in runa1; exrepnd; subst; rev_Some.

    unfold M_run_ls_on_input_ls in *; simpl in *.
    remember (M_run_ls_on_input (sm2ls p) cn a2) as z; symmetry in Heqz; repnd; simpl in *.
    unfold M_run_ls_on_input, on_comp in Heqz; simpl in *.
    destruct (CompNameDeq cn cn) as [d|d]; tcsp; simpl in *.
    rewrite (UIP_refl_CompName _ d) in Heqz; simpl in *; GC.
    unfold M_break in Heqz; simpl in *.
    remember (M_run_sm_on_input p a2 (sm2ls p)) as x; symmetry in Heqx; repnd; simpl in *.
    applydup @is_proc_n_proc_run_on_input_implies_some in Heqx; auto; exrepnd; subst; simpl in *.
    inversion Heqz; subst; simpl in *; clear Heqz.

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input p a2 (sm2ls p)) as u.
    repeat (autodimp u hyp); eauto 3 with comp.
    unfold M_break in u.
    rewrite Heqx in u; repnd.
    apply similar_subs_sm2ls in u0; exrepnd; subst; simpl in *.
    destruct (CompNameDeq cn cn); tcsp.

    pose proof (IHl k n (update_state_m p s0) q r) as IHl.
    repeat (autodimp IHl hyp); eauto 3 with comp;
      unfold sm2ls in *; allrw; simpl; auto.
  Qed.
  Hint Resolve implies_M_comp_sm2ls_on_op_inputs_app : comp.

  Lemma M_run_ls_on_input_preserves_subs :
    forall cn i {n} (ls1 ls2 : n_procs n) o,
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_run_ls_on_input ls1 cn i = (ls2, o)
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    introv wf aps run.
    unfold M_run_ls_on_input, on_comp, M_break in run.
    dest_cases w; rev_Some;[|ginv; dands; tcsp; eauto 3 with comp];[].
    dest_cases z; symmetry in Heqz; repnd; simpl in *.
    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input w i ls1) as h.
    repeat (autodimp h hyp); eauto 3 with comp;[].
    unfold M_break in h.
    rewrite Heqz in h; repnd.
    applydup @is_proc_n_proc_run_on_input_implies_some in Heqz; eauto 3 with comp;[].
    exrepnd; subst; simpl in *.
    inversion run; subst; simpl in *; clear run.

    pose proof (are_procs_implies_run_subs_direct2 w i ls1) as q.
    repeat (autodimp q hyp); eauto 3 with comp;[].
    apply run_subs_leaves_eq_direct in q; auto;[].
    rewrite Heqz in q; simpl in q.

    unfold wf_procs, are_procs_n_procs in *.
    dands; eauto 3 with comp.

    { eapply similar_subs_preserves_wf_procs;
        [apply implies_similar_subs_replace_name; eauto|];[].
      eapply wf_procs_replace_name; eauto; autorewrite with comp; auto. }

    { introv j.
      apply in_replace_name_update_state_m_implies_is_proc_n_proc in j; eauto 3 with comp. }

    { apply similar_subs_sym.
      eapply similar_subs_trans;
        [|eapply similar_subs_replace_name_update_state_m_find_name;eauto];
        apply implies_similar_subs_replace_name; eauto 3 with comp. }

    { introv lvl j.
      applydup q in j; auto; exrepnd.
      destruct (CompNameDeq cn0 cn) as [d|d]; subst; simpl in *.
      { eapply find_name_in_implies_eq in j; eauto; subst; GC.
        pose proof (implies_in_replace_name cn n z0 (update_state_m p s0)) as x.
        repeat (autodimp x hyp); eauto 3 with comp.
        exists [i] (update_state_m p s0); dands; auto.
        unfold M_comp_ls_on_op_inputs, on_some; simpl.
        unfold M_run_ls_on_input_ls.
        pose proof (M_run_sm_on_input_implies_M_run_sm2ls_on_input p i ls1 z0 s0 z1) as w.
        repeat (autodimp w hyp); eauto 3 with comp;[].
        rewrite w; clear w; simpl; dest_cases z.
        rewrite (UIP_refl_CompName _ z); tcsp. }

      pose proof (in_replace_name_right cn n (MkPProc cn0 comp) z0 (update_state_m w s0)) as x.
      simpl in x; repeat (autodimp x hyp).
      applydup @M_comp_sm2ls_on_op_inputs_implies_similar_sms in j1; eauto 3 with comp;[].
      applydup similar_sms_implies_eq_sm2levels in j2.
      exrepnd.
      exists l comp; dands; auto. }
  Qed.

  Lemma M_run_ls_on_op_inputs_preserves_subs :
    forall cn l {n} (ls1 ls2 : n_procs n),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_run_ls_on_op_inputs ls1 cn l = Some ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    induction l; introv wf aps run; simpl in *; ginv; tcsp.
    { dands; eauto 2 with comp. }
    apply map_option_Some in run; exrepnd; subst; simpl in *; rev_Some.

    unfold M_run_ls_on_input_ls in run0.
    remember (M_run_ls_on_input ls1 cn a0) as run; symmetry in Heqrun; repnd; simpl in *.
    pose proof (M_run_ls_on_input_preserves_subs cn a0 ls1 run1 run) as z.
    repeat (autodimp z hyp); repnd.
    apply IHl in run0; auto; repnd.
    dands; eauto 3 with comp.
  Qed.

  Lemma M_run_ls_on_inputs_preserves_subs :
    forall cn l {n} (ls1 ls2 : n_procs n),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_run_ls_on_inputs ls1 cn l = ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    induction l; introv wf aps run; simpl in *; ginv; tcsp.
    { subst; dands; eauto 2 with comp. }

    unfold M_run_ls_on_input_ls in run.
    remember (M_run_ls_on_input ls1 cn a) as run'; symmetry in Heqrun'; repnd; simpl in *.
    pose proof (M_run_ls_on_input_preserves_subs cn a ls1 run'0 run') as z.
    repeat (autodimp z hyp); repnd.
    apply IHl in run; auto; repnd.
    dands; eauto 3 with comp.
  Qed.

  Definition M_comp_ls_on_input {n}
             (ls : n_procs n)
             cn
             (i : cio_I (fio cn)) : option (n_proc n cn) :=
    find_name cn (M_run_ls_on_input_ls ls cn i).

  Lemma implies_M_comp_sm2ls_on_op_inputs_snoc :
    forall {cn} l i {n} (p : n_proc n cn) q r,
      is_proc_n_proc p
      -> M_comp_ls_on_op_inputs (sm2ls p) cn l = Some q
      -> M_comp_ls_on_input (sm2ls q) cn i = Some r
      -> M_comp_ls_on_op_inputs (sm2ls p) cn (snoc l (Some i)) = Some r.
  Proof.
    introv isp runa runb.
    rewrite snoc_as_app.
    eapply implies_M_comp_sm2ls_on_op_inputs_app;eauto.
  Qed.

  Lemma state_of_component_replace_name_same :
    forall {n} {cn} (p : n_proc n cn) (l : n_procs n),
      In cn (get_names l)
      -> state_of_component cn (replace_name p l) = Some (sm2state p).
  Proof.
    unfold state_of_component.
    induction l; introv i; simpl in *; tcsp.
    destruct a as [cn' p']; simpl in *; dest_cases w; repndors; subst; tcsp; GC;
      simpl in *; dest_cases z; simpl in *; tcsp;
        rewrite (UIP_refl_CompName _ z); simpl; tcsp.
  Qed.

  Lemma state_of_component_replace_name_diff :
    forall {n} cn {cn'} (p : n_proc n cn') (l : n_procs n),
      cn <> cn'
      -> state_of_component cn (replace_name p l) = state_of_component cn l.
  Proof.
    unfold state_of_component.
    induction l; introv i; simpl in *; tcsp.
    destruct a as [cn'' p']; simpl in *; dest_cases w; repndors; subst; tcsp; GC;
      simpl in *; dest_cases z; simpl in *; tcsp;
        rewrite (UIP_refl_CompName _ z); simpl; tcsp.
  Qed.

  Lemma if_in_replace_name_diff :
    forall {n} (l : n_procs n) p {cn} (q : n_proc n cn),
      cn <> pp_name p
      -> In p (replace_name q l)
      -> In p l.
  Proof.
    induction l; introv d i; simpl in *; tcsp.
    destruct a as [cn' p']; dest_cases w; subst;
      repeat (simpl in *; repndors; subst; tcsp).
    apply IHl in i; tcsp.
  Qed.

  Lemma M_non_byz_compose_gen :
    forall cn0
           (k : oplist (cio_I (fio cn0)))
           {n}
           (ls : n_procs n)
           {cn}
           (sm : n_proc n cn),
      are_procs_n_procs ls
      -> find_name cn ls = Some sm
      -> wf_procs ls
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      ->
      exists (l : oplist (cio_I (fio cn))),
        M_state_ls_on_op_inputs (sm2ls sm) cn l
        (*snd (M_run_sm_on_list sm l (select_n_procs (sm2level sm) (ls_subs ls)))*)
        = map_option (state_of_component cn) (M_run_ls_on_op_inputs ls cn0 k).
  Proof.
    introv aps fs wf lvl.

    remember (M_run_ls_on_op_inputs ls cn0 k) as run; symmetry in Heqrun.
    destruct run; simpl in *; eauto;
      [|exists [None : option (cio_I (fio cn))]; simpl; auto].

    rename n0 into ls'.

    applydup M_run_ls_on_op_inputs_preserves_subs in Heqrun as prp; auto; repnd;[].

    pose proof (run_subs_leaves_of_find_name ls ls' sm) as z.
    repeat (autodimp z hyp); eauto 3 with comp;[].
    exrepnd.
    exists (map Some l).
    rewrite M_state_ls_on_op_inputs_as_comp.
    unfold state_of_component.
    allrw; simpl; auto.
  Qed.

  Lemma M_non_byz_compose :
    forall {eo : EventOrdering} (e : Event)
           {L S}
           (ls : LocalSystem L S)
           {cn}
           (sm : n_proc L cn),
      are_procs_n_procs ls
      -> find_name cn ls = Some sm
      -> wf_procs ls
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      ->
      exists (l : oplist (cio_I (fio cn))),
        M_state_ls_on_op_inputs (sm2ls sm) cn l
        (*snd (M_run_sm_on_list sm l (select_n_procs (sm2level sm) (ls_subs ls)))*)
        = M_state_ls_before_event ls e cn.
  Proof.
    introv aps fs wf lvl.
    apply M_non_byz_compose_gen; auto.
  Qed.

  Fixpoint run_sm_on_op_inputs {n} {cn}
           (p : n_proc n cn)
           (l : oplist (cio_I (fio cn)))
           (subs : n_procs n) : n_procs n * option (n_proc n cn) :=
    match l with
    | [] => (subs, Some p)
    | Some i :: l =>
      match sm2update p (sm2state p) i (select_n_procs (sm2level p) subs) with
      | (subs', (sop, o)) =>
        run_sm_on_op_inputs
          (update_state_op_m p sop)
          l
          (raise_to_n_procs n subs')
      end
    | None :: l => (subs, None)
    end.

  Lemma M_comp_ls_on_op_inputs_sm2ls_as_run_sm_on_op_inputs :
    forall {cn} l {n} (p : n_proc n cn) subs,
      sm2level p = 0
      -> is_proc_n_proc p
      -> M_comp_ls_on_op_inputs (sm2ls p) cn l
         = snd (run_sm_on_op_inputs p l subs).
  Proof.
    unfold M_comp_ls_on_op_inputs; simpl.
    induction l; introv lvl isp; simpl in *; tcsp.

    { dest_cases w.
      rewrite (UIP_refl_CompName _ w); simpl; auto; split; intro h; ginv; auto. }

    unfold M_run_ls_on_input_ls; simpl.
    unfold M_run_ls_on_input, on_comp; simpl.
    destruct (CompNameDeq cn cn) as [d|d]; tcsp; simpl.
    rewrite (UIP_refl_CompName _ d); simpl; auto; GC.
    unfold M_break.
    dest_cases i; repnd; simpl in *; symmetry in Heqi; subst; simpl in *; tcsp.
    dest_cases w; repnd; simpl in *; symmetry in Heqw.
    applydup @is_proc_n_proc_run_on_input_implies_some in Heqw; auto.
    exrepnd; subst; simpl in *.
    pose proof (snd_M_run_sm_on_input_eq p i (sm2ls p)) as q.
    rewrite Heqw in q; simpl in q.

    assert (select_n_procs (sm2level p) subs = []) as eqn.
    { rewrite lvl; apply n_procs_0. }
    rewrite eqn; clear eqn.
    assert (select_n_procs (sm2level p) (sm2ls p) = []) as eqn.
    { rewrite lvl; apply n_procs_0. }
    rewrite eqn in q; clear eqn.

    split_pair; simpl in *; rewrite <- q; simpl.
    rewrite <- IHl; autorewrite with comp; eauto 3 with comp;[].

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input p i (sm2ls p)) as w.
    repeat (autodimp w hyp); eauto 3 with comp;[].
    unfold M_break in w.
    rewrite Heqw in w; repnd.
    apply similar_subs_sm2ls in w2; exrepnd; subst; simpl in *.
    dest_cases w.
  Qed.

  Lemma M_non_byz_compose2 :
    forall {eo : EventOrdering} (e : Event)
           {L S}
           (ls : LocalSystem L S)
           {cn}
           (sm : n_proc L cn),
      are_procs_n_procs ls
      -> find_name cn ls = Some sm
      -> wf_procs ls
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      ->
      exists (l : oplist (cio_I (fio cn))),
        option_map sm2state (snd (run_sm_on_op_inputs sm l []))
        (*snd (M_run_sm_on_list sm l (select_n_procs (sm2level sm) (ls_subs ls)))*)
        = M_state_ls_before_event ls e cn.
  Proof.
    introv aps fn wf lvl.
    pose proof (M_non_byz_compose e ls sm) as q.
    repeat (autodimp q hyp); exrepnd.
    rewrite M_state_ls_on_op_inputs_as_comp in q0.
    rewrite <- q0.
    exists l.
    erewrite M_comp_ls_on_op_inputs_sm2ls_as_run_sm_on_op_inputs; eauto 3 with comp.
  Qed.

  Definition is_trusted_ls {n} cn (ls : n_procs n) : Prop :=
    is_trusted_in cn ls = true.

(*  Definition to_trusted {n:nat} {cn : CompName} : n_proc n cn -> option trustedSM :=
    match cn with
    | MkCompName k s true =>
      fun pr => Some (MktrustedSM (sm2level pr) k s (sm2at pr))
    | _ => fun _ => None
    end.*)

(*  (* Byzantine mode, where we also react to Byzantine events *)
  Definition byz_run_sm_on_byz_inputs {n} {cn}
             (p : n_proc n cn)
             (l : list (trigger_info (cio_I (fio cn))))
             (subs : n_procs n) : n_procs n * M_trusted (n_proc n cn) :=
    match to_trusted p with
    | Some tsm => ([], M_t (run_trustedSM_on_trigger_info_list tsm l))
    | None => (subs, M_nt p)
    end.*)

(*  (* If we encounter a byzantine events, we switch to the Byzantine mode *)
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
    end.*)

  Lemma implies_is_proc_n_proc_update_state_op_m :
    forall n cn (p : n_proc n cn) sop,
      is_proc_n_proc p
      -> is_proc_n_proc (update_state_op_m p sop).
  Proof.
    introv i.
    destruct sop; simpl; auto; eauto 3 with comp.
  Qed.
  Hint Resolve implies_is_proc_n_proc_update_state_op_m : comp.

(*  Lemma run_sm_on_byz_inputs_as_run_sm_on_inputs :
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
  Qed.*)

  Lemma similar_subs_preserves_is_trusted :
    forall n cn (subs1 subs2 : n_procs n),
      similar_subs subs1 subs2
      -> is_trusted_in cn subs2 = is_trusted_in cn subs1.
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
    dest_cases w.
  Qed.

(*  Lemma run_sm_on_byz_inputs_as_run_sm_on_inputs_app :
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
  Qed.*)

(*  Lemma is_trusted_implies_find_trusted2 :
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
  Qed.*)

  (*Lemma to_trusted_eq :
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
  Qed.*)

  (*Lemma map_untrusted_op_Some_M_t_implies :
    forall {T} {A} (x : M_trusted T) (F : T -> option A) (a : trustedSM),
      map_untrusted_op x F = Some (M_t a)
      -> x = M_t a.
  Proof.
    introv h.
    destruct x; simpl in *; ginv; tcsp;[].
    apply option_map_Some in h; exrepnd; ginv.
  Qed.*)

  (*Lemma trusted_rn_sm_on_byz_inputs_throws_away_subs :
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
  Qed.*)

  (*Lemma run_trustedSM_on_trigger_info_list_snoc :
    forall {D} (l k : list (trigger_info D)) (tsm : trustedSM),
      run_trustedSM_on_trigger_info_list tsm (l ++ k)
      = run_trustedSM_on_trigger_info_list
          (run_trustedSM_on_trigger_info_list tsm l)
          k.
  Proof.
    induction l; introv; simpl; auto.
  Qed.*)

  (*Lemma run_sm_on_byz_inputs_as_run_sm_on_inputs_app_trusted :
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
  Qed.*)



  Definition M_byz_comp_ls_on_inputs {n}
             (ls : n_procs n)
             cn
             (l : list (trigger_info (cio_I (fio cn))))
    : option (n_proc n cn) :=
    find_name cn (M_byz_run_ls_on_inputs ls cn l).

  Definition M_byz_state_ls_on_inputs {n}
             (ls : n_procs n)
             cn
             (l : list (trigger_info (cio_I (fio cn))))
    : option (sf cn) :=
    state_of_component cn (M_byz_run_ls_on_inputs ls cn l).

  Lemma M_byz_state_ls_on_inputs_as_comp :
    forall {n}
           (ls : n_procs n)
           cn
           (l : list (trigger_info (cio_I (fio cn)))),
      M_byz_state_ls_on_inputs ls cn l
      = option_map
          sm2state
          (M_byz_comp_ls_on_inputs ls cn l).
  Proof.
    introv; unfold M_byz_state_ls_on_inputs, M_byz_comp_ls_on_inputs.
    remember (M_byz_run_ls_on_inputs ls cn l) as x; destruct x; simpl; auto.
  Qed.

  Inductive byz_input :=
  | byz_input_arbitrary
  | byz_input_trusted (d : ITrusted).

  Definition byz2trigger {A} (b : byz_input) : trigger_info A :=
    match b with
    | byz_input_arbitrary => trigger_info_arbitrary
    | byz_input_trusted d => trigger_info_trusted d
    end.

  Definition all_trusted {n} (l : n_procs n) :=
    forall p, In p l -> is_trusted p = true.

  Lemma all_trusted_procs2byz :
    forall {n} (ls : n_procs n),
      all_trusted (procs2byz ls).
  Proof.
    introv i; simpl in *; induction ls; simpl in *; tcsp.
    dest_cases w; simpl in *; repndors; subst; tcsp.
  Qed.
  Hint Resolve all_trusted_procs2byz : comp.

  Lemma wf_procs_M_run_ls_on_input :
    forall {n} (ls : n_procs n) cn i,
      wf_procs ls
      -> are_procs_n_procs ls
      -> wf_procs (fst (M_run_ls_on_input ls cn i)).
  Proof.
    introv wf aps.
    remember (M_run_ls_on_input ls cn i) as z; symmetry in Heqz; repnd; simpl in *.
    eapply M_run_ls_on_input_preserves_subs; eauto.
  Qed.
  Hint Resolve wf_procs_M_run_ls_on_input : comp.

  Lemma are_procs_n_procs_M_run_ls_on_input :
    forall {n} (ls : n_procs n) cn i,
      wf_procs ls
      -> are_procs_n_procs ls
      -> are_procs_n_procs (fst (M_run_ls_on_input ls cn i)).
  Proof.
    introv wf aps.
    remember (M_run_ls_on_input ls cn i) as z; symmetry in Heqz; repnd; simpl in *.
    eapply M_run_ls_on_input_preserves_subs; eauto.
  Qed.
  Hint Resolve are_procs_n_procs_M_run_ls_on_input : comp.

  Lemma get_names_procs2byz_subset :
    forall {n} (ls : n_procs n),
      subset (get_names (procs2byz ls)) (get_names ls).
  Proof.
    induction ls; introv i; simpl in *; tcsp.
    dest_cases w.
  Qed.

  Lemma implies_all_lower_procs2byz :
    forall i {n} (ls : n_procs n),
      all_lower i ls = true
      -> all_lower i (procs2byz ls) = true.
  Proof.
    induction ls; introv h; simpl in *; tcsp.
    allrw andb_true; repnd; autodimp IHls hyp;[].
    dest_cases w; simpl in *; allrw andb_true; dands; tcsp.
  Qed.
  Hint Resolve implies_all_lower_procs2byz : comp.

  Lemma implies_wf_procs_procs2byz :
    forall {n} (ls : n_procs n),
      wf_procs ls
      -> wf_procs (procs2byz ls).
  Proof.
    unfold wf_procs, wf_procs, no_dup_subs.
    induction ls; simpl in *; introv h; tcsp.
    allrw andb_true; repnd.
    repeat (dest_cases w; simpl in *; tcsp);
      repeat (autodimp IHls hyp);
      repnd; allrw andb_true; dands; tcsp;
        eauto 4 with comp;[].
    apply get_names_procs2byz_subset in i; tcsp.
  Qed.
  Hint Resolve implies_wf_procs_procs2byz : comp.

  Lemma in_procs2byz :
    forall {n} (ls : n_procs n) p,
      In p (procs2byz ls) <-> (In p ls /\ is_trusted p = true).
  Proof.
    induction ls; introv; split; intro h; simpl in *; repnd; dands; tcsp;
      dest_cases w; simpl in *; repndors; subst; tcsp;
        try (complete (apply IHls in h; tcsp));
        try (complete (rewrite IHls; tcsp));
        try (complete (rewrite h in *; ginv)).
  Qed.

  Lemma implies_are_procs_n_procs_procs2byz :
    forall {n} (ls : n_procs n),
      are_procs_n_procs ls
      -> are_procs_n_procs (procs2byz ls).
  Proof.
    unfold are_procs_n_procs; introv h i.
    apply in_procs2byz in i; repnd.
    apply h in i0; auto.
  Qed.
  Hint Resolve implies_are_procs_n_procs_procs2byz : comp.

  Lemma in_similar_subs_implies :
    forall {n} (ls1 ls2 : n_procs n) p,
      similar_subs ls1 ls2
      -> In p ls1
      -> exists q, In q ls2 /\ similar_procs p q.
  Proof.
    introv sim; induction sim; introv i; simpl in *; tcsp.
    repndors; subst; tcsp.
    { exists p2; dands; tcsp. }
    { autodimp IHsim hyp; exrepnd; exists q; dands; tcsp. }
  Qed.

  Lemma similar_procs_preserves_is_trusted :
    forall {n} (p q : n_nproc n),
      similar_procs p q
      -> is_trusted p = true
      -> is_trusted q = true.
  Proof.
    introv sim; inversion sim; subst; simpl in *.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
  Qed.
  Hint Resolve similar_procs_preserves_is_trusted : comp.

  Lemma similar_subs_preserves_all_trusted :
    forall {n} (ls1 ls2 : n_procs n),
      similar_subs ls1 ls2
      -> all_trusted ls1
      -> all_trusted ls2.
  Proof.
    introv sim h i.
    apply similar_subs_sym in sim.
    eapply in_similar_subs_implies in sim; eauto; exrepnd.
    applydup h in sim1; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_preserves_all_trusted : comp.

  Lemma procs2byz_procs2byz :
    forall {n} (ls : n_procs n),
      procs2byz (procs2byz ls) = procs2byz ls.
  Proof.
    induction ls; introv; simpl in *; tcsp.
    repeat (dest_cases w; simpl in *; tcsp); try congruence.
  Qed.
  Hint Rewrite @procs2byz_procs2byz : comp.

  Lemma split_M_byz_run_ls_on_op_inputs :
    forall cn (k : list (trigger_info (cio_I (fio cn)))) {n} (ls : n_procs n),
      wf_procs ls
      -> are_procs_n_procs ls
      ->
      (
        (exists (k' : list (cio_I (fio cn))),
            M_run_ls_on_op_inputs ls cn (map Some k') = Some (M_byz_run_ls_on_inputs ls cn k)
            /\ k = map (fun x => trigger_info_data x)  k'
        )
        \/
        (exists (k1  : list (cio_I (fio cn)))
                (ls1 : n_procs n)
                (ls2 : n_procs n)
                (i   : byz_input)
                (k2  : list (trigger_info (cio_I (fio cn)))),
            (* correct initial segment of the run *)
            M_run_ls_on_op_inputs ls cn (map Some k1) = Some ls1
            (* 1st byz event *)
            /\ fst (M_byz_run_ls_on_input (procs2byz ls1) cn (byz2trigger i)) = ls2
            (* the rest of the run  *)
            /\ M_byz_run_ls_on_inputs ls2 cn k2 = M_byz_run_ls_on_inputs ls cn k
            /\ k = (map (fun x => trigger_info_data x) k1) ++ (byz2trigger i) :: k2
        )
      ).
  Proof.
    induction k; introv wf aps; simpl in *.
    { left; exists ([] : list (cio_I (fio cn))); simpl; tcsp. }

    destruct a; simpl in *;[| |].

    { pose proof (IHk _ (fst (M_run_ls_on_input ls cn d))) as IHk.
      repeat (autodimp IHk hyp); eauto 3 with comp;[].
      repndors; exrepnd; subst; simpl in *;[|].

      { left.
        exists (d :: k'); simpl.
        unfold M_run_ls_on_input_ls; simpl in *.
        rewrite IHk1; simple; dands; auto. }

      { right.
        exists (d :: k1) ls1 (fst (M_byz_run_ls_on_input (procs2byz ls1) cn (byz2trigger i))) i k2.
        simpl.
        dands; tcsp. } }

    { right.
      exists ([] : list (cio_I (fio cn)))
             ls
             (fst (M_byz_run_ls_on_input (procs2byz ls) cn trigger_info_arbitrary))
             byz_input_arbitrary
             k; simpl; dands; tcsp; autorewrite with comp; eauto 3 with comp. }

    { right.
      exists ([] : list (cio_I (fio cn)))
             ls
             (fst (M_byz_run_ls_on_input (procs2byz ls) cn (trigger_info_trusted i)))
             (byz_input_trusted i)
             k; simpl; dands; tcsp; eauto 3 with comp.
      unfold M_run_ls_on_trusted; simpl.
      autorewrite with comp.

      remember (M_run_ls_on_input (procs2byz ls) (pre2trusted (it_name i)) (it_input i)) as run;
        symmetry in Heqrun; repnd; simpl in *.

      pose proof (M_run_ls_on_input_preserves_subs
                    (pre2trusted (it_name i))
                    (it_input i)
                    (procs2byz ls)
                    run0 run) as q.
      repeat (autodimp q hyp); repnd; eauto 4 with comp. }
  Qed.

  Lemma implies_eq_map_trigger_op :
    forall {eo : EventOrdering} (l : list Event) k,
      map trigger l = map (fun x => trigger_info_data x) k
      -> map Some k = map trigger_op l.
  Proof.
    induction l; introv h; simpl in *; destruct k; simpl in *; ginv.
    unfold trigger_op.
    remember (trigger a) as trig; clear Heqtrig.
    destruct trig; ginv.
    inversion h; subst; simpl in *.
    f_equal; tcsp.
  Qed.

  Lemma M_run_ls_on_op_inputs_some_implies_some :
    forall {cn} l {n} (ls : n_procs n) x,
      M_run_ls_on_op_inputs ls cn l = Some x
      -> exists k, l = map Some k.
  Proof.
    induction l; introv run; simpl in *; ginv.
    { exists ([] : list (cio_I (fio cn))); simpl; auto. }
    apply map_option_Some in run; exrepnd; subst; simpl in *; rev_Some.
    apply IHl in run0; exrepnd; subst.
    exists (a0 :: k); simpl; tcsp.
  Qed.

  Lemma M_run_ls_on_op_inputs_some_implies_byz :
    forall cn l {n} (ls1 : n_procs n) ls2,
      M_run_ls_on_op_inputs ls1 cn (map Some l) = Some ls2
      -> M_byz_run_ls_on_inputs ls1 cn (map (fun x => trigger_info_data x) l) = ls2.
  Proof.
    induction l; introv run; simpl in *; ginv; auto.
  Qed.

  Lemma M_run_ls_on_inputs_some_implies_or_find_name :
    forall cn l {n} (ls1 ls2 : n_procs n),
      M_run_ls_on_op_inputs ls1 cn l = Some ls2
      -> ls2 = ls1
         \/ exists comp, find_name cn ls1 = Some comp.
  Proof.
    induction l; introv run; simpl in *; ginv; tcsp.
    apply map_option_Some in run; exrepnd; subst; rev_Some.
    unfold M_run_ls_on_input_ls in run0.
    remember (M_run_ls_on_input ls1 cn a0) as run'; symmetry in Heqrun'; repnd; simpl in *.
    apply IHl in run0; clear IHl.
    unfold M_run_ls_on_input, on_comp in *.
    dest_cases w; rev_Some.
    right; eauto.
  Qed.

  Lemma procs2byz_eq_if_all_trusted :
    forall {n} (ls : n_procs n),
      all_trusted ls
      -> procs2byz ls = ls.
  Proof.
    induction ls; introv allt; simpl in *; tcsp.
    unfold all_trusted in *; simpl in *.
    rewrite IHls; tcsp.
    dest_cases w; symmetry in Heqw.
    rewrite allt in Heqw; tcsp.
  Qed.

  Lemma M_byz_run_ls_on_input_preserves_subs :
    forall cn i {n} (ls1 ls2 : n_procs n) o,
      all_trusted ls1
      -> wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_byz_run_ls_on_input ls1 cn i = (ls2, o)
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    introv allt wf aps run.
    unfold M_byz_run_ls_on_input in run.
    destruct i.

    { eapply M_run_ls_on_input_preserves_subs; eauto. }

    { ginv.
      rewrite (procs2byz_eq_if_all_trusted ls1); auto.
      dands; eauto 3 with comp. }

    { ginv.
      unfold M_run_ls_on_trusted in run.
      pose proof (M_run_ls_on_input_preserves_subs
                    (pre2trusted (it_name i))
                    (it_input i)
                    (procs2byz ls1) ls2 o) as q.
      repeat (autodimp q hyp); eauto 3 with comp.
      rewrite (procs2byz_eq_if_all_trusted ls1) in q; auto. }
  Qed.

  Lemma M_byz_run_ls_on_inputs_preserves_subs :
    forall cn l {n} (ls1 ls2 : n_procs n),
      all_trusted ls1
      -> wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_byz_run_ls_on_inputs ls1 cn l = ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs ls1 ls2
          /\ run_subs_leaves ls1 ls2).
  Proof.
    induction l; introv allt wf aps run; simpl in *; ginv; tcsp.
    { subst; dands; eauto 2 with comp. }

    remember (M_byz_run_ls_on_input ls1 cn a) as z; symmetry in Heqz; repnd; simpl in *.
    pose proof (M_byz_run_ls_on_input_preserves_subs cn a ls1 z0 z) as w.
    repeat (autodimp w hyp); repnd.
    apply IHl in run; auto; repnd; eauto 3 with comp.
    dands; eauto 3 with comp.
  Qed.

  Lemma M_run_ls_on_op_inputs_as_M_run_ls_on_inputs :
    forall cn l {n} (ls : n_procs n),
      M_run_ls_on_op_inputs ls cn (map Some l)
      = Some (M_run_ls_on_inputs ls cn l).
  Proof.
    induction l; introv; simpl in *; tcsp.
  Qed.

  Lemma M_comp_ls_on_op_inputs_as_M_comp_ls_on_inputs :
    forall {n} (ls : n_procs n) cn l,
      M_comp_ls_on_op_inputs ls cn (map Some l)
      = M_comp_ls_on_inputs ls cn l.
  Proof.
    introv.
    unfold M_comp_ls_on_op_inputs,  M_comp_ls_on_inputs.
    rewrite M_run_ls_on_op_inputs_as_M_run_ls_on_inputs; auto.
  Qed.

  Lemma M_byz_compose_gen_all_trusted :
    forall cn0
           (k : list (trigger_info (cio_I (fio cn0))))
           {n}
           (ls : n_procs n)
           {cn}
           (sm : n_proc n cn),
      all_trusted ls
      -> are_procs_n_procs ls
      -> find_name cn ls = Some sm
      -> wf_procs ls
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      ->
      exists (l : list (cio_I (fio cn))),
        M_state_ls_on_inputs (sm2ls sm) cn l
        (*snd (M_run_sm_on_list sm l (select_n_procs (sm2level sm) (ls_subs ls)))*)
        = state_of_component cn (M_byz_run_ls_on_inputs ls cn0 k).
  Proof.
    introv allt aps fs wf lvl.

    remember (M_byz_run_ls_on_inputs ls cn0 k) as ls'; symmetry in Heqls'.

    applydup M_byz_run_ls_on_inputs_preserves_subs in Heqls' as prp; auto; repnd;[].

    pose proof (run_subs_leaves_of_find_name ls ls' sm) as z.
    repeat (autodimp z hyp); eauto 3 with comp;[].
    exrepnd.
    rewrite M_comp_ls_on_op_inputs_as_M_comp_ls_on_inputs in z0.

    exists l.
    rewrite M_state_ls_on_inputs_as_comp.
    unfold state_of_component.
    rewrite z0, z1; simpl; auto.
  Qed.

  Lemma find_name_sm2ls :
    forall cn {n} (p : n_proc n cn),
      find_name cn (sm2ls p) = Some p.
  Proof.
    introv; unfold find_name; simpl; dest_cases w.
    rewrite (UIP_refl_CompName _ w); auto.
  Qed.
  Hint Rewrite find_name_sm2ls : comp.

  Lemma similar_sms_implies_eq :
    forall {n} {cn} (p q : n_proc n cn),
      similar_sms p q
      -> sm2state p = sm2state q
      -> p = q.
  Proof.
    induction n; introv sim eqs; simpl in *; tcsp.
    destruct p, q; simpl in *; tcsp.
    { unfold similar_sms_at in *.
      destruct a, a0; simpl in *; subst; auto. }
    { apply IHn in sim; subst; auto. }
  Qed.

  Lemma find_name_procs2byz_if_trusted :
    forall cn {n} (ls : n_procs n),
      comp_name_trust cn = true
      -> find_name cn (procs2byz ls) = find_name cn ls.
  Proof.
    induction ls; introv h; simpl in *; tcsp.
    dest_cases w; simpl in *; tcsp; destruct a; simpl in *; dest_cases w.
    unfold is_trusted in *; simpl in *; subst.
    rewrite h in *; ginv.
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

  Lemma M_byz_compose_gen :
    forall cn0
           (k : list (trigger_info (cio_I (fio cn0))))
           {n}
           (ls : n_procs n)
           {cn}
           (sm : n_proc n cn),
      are_procs_n_procs ls
      -> wf_procs ls
      -> find_name cn ls = Some sm
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      -> comp_name_trust cn = true
      ->
      exists (l : list (cio_I (fio cn))),
        M_state_ls_on_inputs (sm2ls sm) cn l
        = state_of_component cn (M_byz_run_ls_on_inputs ls cn0 k).
  Proof.
    introv aps wf fs lvl trust.

    remember (M_byz_run_ls_on_inputs ls cn0 k) as run; symmetry in Heqrun; simpl.

    pose proof (split_M_byz_run_ls_on_op_inputs cn0 k ls) as q.
    rewrite Heqrun in q; clear Heqrun.
    repeat (autodimp q hyp);[].

    repndors; exrepnd.

    { clear dependent k.
      pose proof (M_non_byz_compose_gen cn0 (map Some k') ls sm) as z.
      repeat (autodimp z hyp); exrepnd.
      rewrite q1 in z0; simpl in z0.

      applydup M_run_ls_on_op_inputs_preserves_subs in q1; auto; repnd;[].

      rename_hyp_with @similar_subs sim; eapply similar_subs_preserves_find_name in sim; eauto; exrepnd.
      unfold state_of_component in *.
      rewrite sim1 in *; simpl in *.

      apply map_option_Some in z0; exrepnd; rev_Some.
      apply map_option_Some in z1; exrepnd.
      rewrite z2; clear z2.
      unfold M_state_ls_on_inputs.

      applydup @M_run_ls_on_op_inputs_some_implies_some in z0; exrepnd; subst l.
      rewrite M_run_ls_on_op_inputs_as_M_run_ls_on_inputs in z0; ginv.
      exists k.
      unfold state_of_component; repeat (allrw; simpl; auto). }

    { clear dependent k.
      pose proof (M_non_byz_compose_gen cn0 (map Some k1) ls sm) as z.
      repeat (autodimp z hyp); exrepnd.
      rewrite q1 in z0; simpl in z0.

      applydup M_run_ls_on_op_inputs_preserves_subs in q1; auto; repnd;[].

      rename_hyp_with @similar_subs sim; dup sim as sim'.
      eapply similar_subs_preserves_find_name in sim'; eauto; exrepnd.
      unfold state_of_component in *.
      rewrite sim'1 in *; simpl in *.

      apply map_option_Some in z0; exrepnd; rev_Some.
      apply map_option_Some in z1; exrepnd.
      inversion z2; clear z2.

      applydup @M_run_ls_on_op_inputs_some_implies_some in z0; exrepnd; subst l.
      rewrite M_run_ls_on_op_inputs_as_M_run_ls_on_inputs in z0; ginv.

      remember (M_byz_run_ls_on_input (procs2byz ls1) cn0 (byz2trigger i)) as runo; symmetry in Heqruno; repnd.
      simpl in *; rewrite Heqruno; simpl in *.

      pose proof (M_run_sm2ls_on_inputs_some_implies_sm2ls k sm) as xx.
      autodimp xx hyp; eauto 3 with comp;[]; exrepnd.
      rewrite xx1 in *; autorewrite with comp in *; ginv.
      assert (a0 = s');[|subst a0;GC].
      { apply similar_sms_implies_eq; eauto 3 with comp. }
      applydup similar_sms_implies_eq_sm2levels in sim'0.

      pose proof (M_byz_compose_gen_all_trusted cn0 [byz2trigger i] (procs2byz ls1) s') as v.
      rewrite find_name_procs2byz_if_trusted in v; auto.
      simpl in *; rewrite Heqruno in v; simpl in v.
      repeat (autodimp v hyp); eauto 3 with comp; try congruence;[].
      exrepnd.

      pose proof (M_byz_run_ls_on_input_preserves_subs cn0 (byz2trigger i) (procs2byz ls1) runo0 runo) as v.
      simpl in *; rewrite Heqruno in v.
      repeat (autodimp v hyp); eauto 3 with comp; repnd.

      dup v3 as sim''.
      eapply similar_subs_preserves_find_name in sim'';
        [|rewrite find_name_procs2byz_if_trusted;eauto].
      exrepnd.
      unfold state_of_component in v0.
      rewrite sim''1 in *; simpl in *.

      apply map_option_Some in v0; exrepnd; rev_Some.
      inversion v4; clear v4.

      pose proof (M_run_sm2ls_on_inputs_some_implies_sm2ls l s') as zz.
      autodimp zz hyp; eauto 3 with comp; exrepnd;[].
      rewrite zz1 in *; autorewrite with comp in *; ginv.
      assert (s'0 = a);[|subst a;GC].
      { apply similar_sms_implies_eq; eauto 3 with comp. }
      applydup similar_sms_implies_eq_sm2levels in sim''0.

      pose proof (M_byz_compose_gen_all_trusted cn0 k2 runo0 s'0) as u.
      repeat (autodimp u hyp); eauto 3 with comp; try congruence;[].
      exrepnd.
      unfold state_of_component in u0.
      simpl in *; rewrite <- u0; clear u0.
      exists (k ++ l ++ l0).

      unfold M_state_ls_on_inputs; f_equal.

      rewrite app_assoc.
      rewrite @M_run_ls_on_inputs_app.
      rewrite @M_run_ls_on_inputs_app.
      rewrite xx1; simpl.
      rewrite zz1; simpl; auto. }
  Qed.

  Lemma M_byz_compose :
    forall {eo : EventOrdering} (e : Event)
           {n s}
           (ls : LocalSystem n s)
           {cn}
           (sm : n_proc n cn),
      are_procs_n_procs ls
      -> wf_procs ls
      -> find_name cn ls = Some sm
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      -> comp_name_trust cn = true
      ->
      exists (l : list (cio_I (fio cn))),
        M_state_ls_on_inputs (sm2ls sm) cn l
        (*map_untrusted_op
          (snd (run_sm_on_byz_inputs sm l (ls_subs ls)))
          (fun p => Some (sm2state p))*)
        = M_byz_state_ls_before_event ls e cn.
  Proof.
    introv aps wf fs lvl trust.
    apply M_byz_compose_gen; auto.
  Qed.

  (*Lemma M_byz_run_ls_on_this_one_event_M_nt_implies_similar_sms_at :
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
  Qed.*)

  (*Lemma M_byz_run_ls_before_event_M_nt_implies_similar_sms_at :
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
  Qed.*)

  (*Lemma M_run_ls_before_event_implies_similar_sms_at :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : MLocalSystem L S),
      M_run_ls_before_event ls1 e = Some ls2
      -> similar_sms_at (ls_main ls1) (ls_main ls2).
  Proof.
    introv run.
    apply M_run_ls_before_event_M_byz_run_ls_before_event in run.
    apply M_byz_run_ls_before_event_M_nt_implies_similar_sms_at in run; tcsp.
  Qed.*)

  Definition procs_non_trusted {n} (subs : n_procs n) : Prop :=
    forallb (fun p => negb (is_trusted p)) subs = true.

  Definition sys_non_trusted {f} (sys : M_USystem f) :=
    forall n, procs_non_trusted (sys n).

  Lemma procs2byz_if_non_trusted :
    forall {L S} (ls : LocalSystem L S),
      procs_non_trusted ls
      -> procs2byz ls = empty_ls L S.
  Proof.
    induction ls; introv h; simpl in *; tcsp.
    unfold procs_non_trusted in *; simpl in *.
    allrw andb_true; repnd.
    unfold negb in h0; dest_cases w.
  Qed.

  Lemma M_run_ls_on_trusted_empty_ls_implies :
    forall {L S} i ls o,
      M_run_ls_on_trusted (empty_ls L S) i = (ls, o)
      -> ls = empty_ls L S /\ o = None.
  Proof.
    introv h.
    unfold M_run_ls_on_trusted in *; simpl in *.
    unfold M_run_ls_on_input, on_comp in h; simpl in *; ginv; auto.
  Qed.

  Lemma procs_non_trusted_replace_name :
    forall {n cn} (p : n_proc n cn) ls,
      procs_non_trusted ls
      -> procs_non_trusted (replace_name p ls).
  Proof.
    unfold procs_non_trusted; induction ls; introv h; simpl in *; auto.
    rewrite andb_true in *; repnd.
    destruct a as [cn' p']; simpl in *; dest_cases w; simpl in *;
      allrw andb_true; subst; dands; tcsp.
  Qed.
  Hint Resolve procs_non_trusted_replace_name : comp.

  Lemma similar_subs_preserves_non_trusted :
    forall {n} (ls1 ls2 : n_procs n),
      similar_subs ls1 ls2
      -> procs_non_trusted ls1
      -> procs_non_trusted ls2.
  Proof.
    unfold procs_non_trusted; introv sim; induction sim; introv h; simpl in *; tcsp.
    allrw andb_true; repnd; dands; tcsp.
    apply similar_procs_sym in simp.
    remember (is_trusted p2) as b; destruct b; simpl in *; tcsp.
    eapply similar_procs_preserves_is_trusted in simp;
      try rewrite simp in *; simpl in *; tcsp.
  Qed.
  Hint Resolve similar_subs_preserves_non_trusted : comp.

  Lemma has_correct_trace_bounded_lt_local_pred_implies :
    forall {eo : EventOrdering} (e : Event),
      isCorrect (local_pred e)
      -> has_correct_trace_bounded_lt (local_pred e)
      -> has_correct_trace_bounded_lt e.
  Proof.
    introv iscor cor h.
    apply local_implies_pred_or_local in h; repndors; exrepnd.
    { unfold local_pred in *; rewrite h in *; auto. }
    unfold local_pred in *; rewrite h1 in *; tcsp.
  Qed.
  Hint Resolve has_correct_trace_bounded_lt_local_pred_implies : eo.

  Lemma M_byz_run_ls_on_one_event_if_non_trusted :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S) o,
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> procs_non_trusted ls1
      -> M_byz_run_ls_on_one_event ls1 e = (ls2, o)
      ->
      (
        (wf_procs ls2
         /\ are_procs_n_procs ls2
         /\ similar_subs ls1 ls2
         /\ run_subs_leaves ls1 ls2
         /\ procs_non_trusted ls2
         /\ ((exists x, isCorrect e /\ o = Some x)
             \/ (find_name (msg_comp_name S) ls1 = None /\ o = None)))
        \/
        (ls2 = empty_ls L S /\ o = None)
      ).
  Proof.
    introv wf aps nontr run.
    unfold M_byz_run_ls_on_this_one_event in run; simpl in *.
    unfold M_byz_run_ls_on_one_event in run; simpl in *.
    remember (M_byz_run_ls_on_input ls1 (msg_comp_name S) (trigger e)) as h; repnd;
      simpl in *; subst; symmetry in Heqh.
    inversion run; subst; clear run.

    unfold isCorrect, event2out, trigger_op in *.
    remember (trigger e) as trig; clear Heqtrig.
    destruct trig; simpl in *; tcsp; GC;
      try (complete (ginv; rewrite procs2byz_if_non_trusted; auto));
      try (complete (rewrite procs2byz_if_non_trusted in Heqh; auto; simpl in *;
                     apply M_run_ls_on_trusted_empty_ls_implies in Heqh;
                     repnd; subst; eauto));[].

    unfold M_run_ls_on_input, on_comp in Heqh.
    dest_cases w; symmetry in Heqw; simpl in *; tcsp;
      [|ginv; left; dands; eauto 3 with comp];[].

    pose proof (are_procs_implies_preserves_sub_M_run_sm_on_input
                  w d ls1) as q.
    repeat (autodimp q hyp); eauto 3 with comp;[].
    pose proof (are_procs_implies_run_subs_direct2 w d ls1) as z.
    repeat (autodimp z hyp); eauto 3 with comp;[].
    unfold M_break in *.
    dest_cases u; symmetry in Hequ; repnd; simpl in *.
    applydup @is_proc_n_proc_run_on_input_implies_some in Hequ; eauto 3 with comp;[].
    exrepnd; subst; simpl in *.
    inversion Heqh; subst; simpl in *; clear Heqh.
    unfold wf_procs, are_procs_n_procs.
    left; dands; eauto 3 with comp; eauto.
    { eapply similar_subs_preserves_wf_procs;
        [apply implies_similar_subs_replace_name; eauto|];[].
      eapply wf_procs_replace_name; eauto; autorewrite with comp; auto. }
    { introv j.
      apply in_replace_name_update_state_m_implies_is_proc_n_proc in j; eauto 3 with comp. }
    { eapply similar_subs_trans;
        [|apply implies_similar_subs_replace_name;eauto].
      apply similar_subs_sym.
      apply similar_subs_replace_name_update_state_m_find; auto. }
    { apply run_subs_leaves_eq_direct; auto;[].
      introv lvl j; applydup z in j; auto; exrepnd.
      destruct (CompNameDeq cn (msg_comp_name S)); subst; tcsp;
        [|exists l; apply in_replace_name_right; auto];[].
      dup Heqw as fn; eapply find_name_in_implies_eq in Heqw; eauto; subst.
      exists [d]; simpl.
      dest_cases v; symmetry in Heqv; repnd; simpl in *.
      pose proof (snd_M_run_sm_on_input_eq p d ls1) as x.
      rewrite Hequ in x; rewrite Heqv in x; simpl in x; ginv; simpl in *.
      apply implies_in_replace_name; eauto 3 with comp. }
  Qed.

  Lemma similar_subs_preserves_find_name_none :
    forall {n} cn (ls1 ls2 : n_procs n),
      similar_subs ls1 ls2
      -> find_name cn ls1 = None
      -> find_name cn ls2 = None.
  Proof.
    introv sim fn.
    remember (find_name cn ls2) as q; destruct q; auto; rev_Some.
    apply similar_subs_sym in sim.
    eapply similar_subs_preserves_find_name in Heqq; eauto.
    exrepnd.
    rewrite Heqq1 in *; ginv.
  Qed.
  Hint Resolve similar_subs_preserves_find_name_none : comp.

  Lemma M_byz_run_ls_before_event_if_non_trusted :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> procs_non_trusted ls1
      -> M_byz_run_ls_before_event ls1 e = ls2
      ->
      (
        (wf_procs ls2
         /\ are_procs_n_procs ls2
         /\ similar_subs ls1 ls2
         /\ run_subs_leaves ls1 ls2
         /\ procs_non_trusted ls1
         /\ (has_correct_trace_bounded_lt e
             \/ find_name (msg_comp_name S) ls1 = None))
        \/
        ls2 = empty_ls L S
      ).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv wf aps nontr run.
    rewrite M_byz_run_ls_before_event_unroll in run.

    destruct (dec_isFirst e) as [d|d]; ginv; auto;[|].
    { subst; dands; eauto 3 with comp.
      left; dands; eauto 3 with comp eo. }

    remember (M_byz_run_ls_before_event ls1 (local_pred e)) as ls'; simpl in *; symmetry in Heqls'.
    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo;[].
    pose proof (ind L S ls1 ls') as ind.
    repeat (autodimp ind hyp); eauto 3 with eo; repndors; repnd;
      [|rewrite ind in *;
        apply M_byz_run_ls_on_this_one_event_empty_ls in run; rewrite run in *;
        dands; eauto 3 with comp];[].

    unfold M_byz_run_ls_on_this_one_event in *.
    remember (M_byz_run_ls_on_one_event ls' (local_pred e)) as run'; symmetry in Heqrun'.
    repnd; simpl in *; subst run'0.

    apply M_byz_run_ls_on_one_event_if_non_trusted in Heqrun'; eauto 3 with eo comp.
    repndors; repnd; tcsp; try (complete (left; dands; eauto 3 with comp eo));[].
    left; dands; eauto 3 with comp eo.
    repndors; exrepnd; tcsp; eauto 3 with comp eo;[].
    remember (find_name (msg_comp_name S) ls1) as fn; symmetry in Heqfn.
    destruct fn; tcsp.
    eapply similar_subs_preserves_find_name in Heqfn; eauto.
    exrepnd; rewrite Heqfn1 in *; ginv.
  Qed.

  Lemma M_byz_run_ls_on_one_event_empty_ls :
    forall {L S} {eo : EventOrdering} (e : Event),
      M_byz_run_ls_on_one_event (empty_ls L S) e = (empty_ls L S, None).
  Proof.
    introv.
    unfold M_byz_run_ls_on_one_event; simpl.
    unfold M_byz_run_ls_on_input; simpl.
    unfold event2out.
    remember (trigger e) as trig; destruct trig; simpl; tcsp.
  Qed.
  Hint Rewrite @M_byz_run_ls_on_one_event_empty_ls : comp.

  Lemma M_byz_output_sys_on_event_implies_M_output_sys_on_event :
    forall {eo : EventOrdering} (e : Event) {F} (sys : M_USystem F) o,
      sys_non_trusted sys
      -> wf_sys sys
      -> are_procs_sys sys
      -> M_byz_output_sys_on_event sys e = Some o
      -> forall m, dmsg_is_in_out m o -> m ∈ sys ⇝ e.
  Proof.
    introv nontr wf aps out inout.
    unfold M_byz_output_sys_on_event in *; simpl in *.
    unfold M_byz_output_ls_on_event in *.
    unfold M_output_sys_on_event, sys_non_trusted in *.
    unfold M_output_ls_on_event; simpl.
    remember (M_byz_run_ls_before_event (sys (loc e)) e) as run; symmetry in Heqrun.
    pose proof (M_byz_run_ls_before_event_if_non_trusted e (sys (loc e)) run) as q.
    repeat (autodimp q hyp); tcsp.
    repeat (repndors; repnd);
      try (complete (rewrite q in *; simpl in *; autorewrite with comp in *;
                     simpl in *; ginv)).

    { pose proof (M_byz_run_ls_before_event_as_M_run_ls_before_event e (sys (loc e))) as w.
      repeat (autodimp w hyp).
      repeat (allrw; simpl).
      unfold M_output_ls_on_this_one_event; simpl.

      remember (M_byz_run_ls_on_one_event run e) as run'; symmetry in Heqrun'.
      repnd; simpl in *; subst run'.
      pose proof (M_byz_run_ls_on_one_event_if_non_trusted e run run'0 (Some o)) as z.
      repeat (autodimp z hyp); eauto 3 with comp.
      repeat (repndors; exrepnd); ginv.

      { clear z0 z1 z2 z3 z4.
        unfold M_run_ls_on_input_out.
        unfold M_byz_run_ls_on_one_event, isCorrect, event2out, dmsg_is_in_out, trigger_op in *.
        remember (trigger e) as trig; destruct trig; simpl in *; tcsp; GC.
        unfold LocalSystem in *; rewrite Heqrun'; simpl; auto. }
    }

    { unfold M_byz_run_ls_on_one_event in out; simpl in *.
      unfold M_byz_run_ls_on_input in out.
      unfold M_byz_run_ls_on_one_event, isCorrect, event2out, dmsg_is_in_out, trigger_op in *.
      remember (trigger e) as trig; destruct trig; simpl in *; tcsp; GC.
      unfold M_run_ls_on_input, on_comp in out; simpl in *.
      eapply similar_subs_preserves_find_name_none in q; eauto.
      rewrite q in *; simpl in *; ginv. }
  Qed.


End ComponentSM2.


Hint Resolve has_correct_trace_bounded_lt_local_pred_implies : eo.


Hint Resolve similar_procs_preserves_is_proc_n_nproc : comp.
Hint Resolve similar_subs_preserves_are_procs_n_procs : comp.
Hint Resolve is_proc_n_nproc_select_n_nproc_decr_n_nproc : comp.
Hint Resolve are_procs_n_procs_select_n_procs_decr_n_procs : comp.
Hint Resolve sm2level_le_pred : comp.
Hint Resolve implies_is_proc_n_proc_at_sm2at : comp.
Hint Resolve similar_sms_incr_pred_n_proc : comp.
(*Hint Resolve similar_subs_replace_sub : comp.*)
(*Hint Resolve similar_subs_replace_subs : comp.*)
Hint Resolve similar_sms_update_state_m : comp.
Hint Resolve similar_subs_replace_name_update_state_m_find : comp.
(*Hint Resolve wf_procs_replace_sub : comp.*)
(*Hint Resolve in_replace_sub_if_diff : comp.*)
Hint Resolve in_implies_in_proc_names : comp.
(*Hint Resolve implies_similar_subs_replace_sub : comp.*)
Hint Resolve similar_subs_preserves_wf_procs : comp.
Hint Resolve name_of_select_n_nproc : comp.
Hint Resolve wf_procs_select_n_procs : comp.
Hint Resolve wf_procs_decr_n_procs : comp.
(*Hint Resolve implies_wf_procs_replace_subs : comp.*)
Hint Resolve wf_procs_replace_name : comp.
Hint Resolve name_of_raise_to_n_nproc : comp.
Hint Resolve implies_wf_procs_raise_to_n_procs : comp.
Hint Resolve are_procs_n_procs_implies_ls_preserves_sub : comp.
Hint Resolve find_name_implies_in_get_names : comp.
Hint Resolve implies_is_proc_n_proc_update_state_m : comp.
Hint Resolve in_replace_name_update_state_m_implies_is_proc_n_proc : comp.
Hint Resolve raise_to_n_proc_preserves_is_proc_n_proc : comp.
Hint Resolve raise_to_n_nproc_preserves_is_proc_n_nproc : comp.
Hint Resolve raise_to_n_procs_preserves_proc : comp.
Hint Resolve are_procs_n_procs_fst_interp_proc : comp.
(*Hint Resolve wf_procs_replace_subs : comp.*)
Hint Resolve wf_procs_fst_interp_proc : comp.
Hint Resolve run_subs_leaves_refl : comp.
Hint Resolve are_procs_n_procs_nil : comp.
Hint Resolve wf_procs_nil : comp.
Hint Resolve implies_in_replace_name : comp.
Hint Resolve select_n_nproc_preserves_is_proc_n_nproc : comp.
Hint Resolve select_n_procs_preserves_are_procs_n_procs : comp.
Hint Resolve select_n_proc_S_incr_implies_level : comp.
(*Hint Resolve implies_in_replace_sub_left : comp.*)
(*Hint Resolve implies_in_replace_subs_left : comp.*)
(*Hint Resolve implies_in_replace_subs_right : comp.*)
Hint Resolve implies_select_n_proc_update_state_m : comp.
Hint Resolve implies_select_n_proc_update_state_op_m : comp.
Hint Resolve run_subs_leaves_trans : comp.
Hint Resolve similar_sms_at_update_state : comp.
Hint Resolve find_name_implies_in : comp.
Hint Resolve in_implies_find_name : comp.
(*Hint Resolve are_procs_n_procs_find_sub : comp.*)
Hint Resolve implies_is_proc_n_proc_update_state_op_m : comp.
Hint Resolve are_procs_unit_ls : comp.
Hint Resolve wf_unit_ls : comp.
Hint Resolve implies_wf_procs_sm2ls : comp.
Hint Resolve implies_are_procs_n_procs_sm2ls : comp.
Hint Resolve are_procs_n_procs_find_name : comp.
Hint Resolve procs_non_trusted_replace_name : comp.
Hint Resolve similar_subs_preserves_non_trusted : comp.
Hint Resolve similar_subs_preserves_find_name_none : comp.


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
(*Hint Rewrite @proc_names_replace_sub : comp.*)
Hint Rewrite @wf_procs_replace_name_implies : comp.
Hint Rewrite @sm2level_update_state_m : comp.
Hint Rewrite @sm2level_update_state_op_m : comp.
Hint Rewrite @run_sm_on_inputs_preserves_sm2level : comp.
Hint Rewrite @select_n_proc_0 : comp.
Hint Rewrite @select_n_procs_0 : comp.
Hint Rewrite @reduces_option_map_some : comp.
(*Hint Rewrite @reduce_map_op_untrusted_op_some : comp.*)
(*Hint Rewrite @reduce_map_op_untrusted_some : comp.*)
(*Hint Rewrite @reduce_map_untrusted_op_M_nt : comp.*)
Hint Rewrite @sm2state_update_state_m : comp.
(*Hint Rewrite @ls_subs_MkLocalSystem : comp.*)
Hint Rewrite @reduce_map_option_some : comp.
Hint Rewrite @get_names_replace_name : comp.
(*Hint Rewrite @sm_halted_update_state : comp.*)
Hint Rewrite @decr_n_procs_0 : comp.
Hint Rewrite @M_byz_run_ls_on_one_event_empty_ls : comp.


Notation "a [>>=] f" := (PROC_BIND a f) (at level 80).
Notation "[R] a" := (PROC_RET a) (at level 80).
Notation "a [C] b" := (PROC_CALL a b) (at level 80).
Notation "a [>>>=] f" := (proc_bind_pair a f) (at level 80).
