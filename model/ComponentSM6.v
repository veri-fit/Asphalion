Require Export ComponentSM3.
Require Export ComponentSM4.


Section ComponentSM6.

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


  Fixpoint sm2update_p {n} {cn}
    : forall (sm : n_proc n cn), M_Update (pred n) cn (sf cn) :=
    match n with
    | 0 => fun sm => match sm with end
    | S m => fun sm =>
               match sm with
               | sm_or_at q => sm_update q
               | sm_or_sm q => fun s t i => M_on_pred (sm2update_p q s t i)
               end
    end.

  (* [k] is meant to be <= than [n] *)
  Definition M_to {n} k {O} (m : M_n n O) : M_n k O :=
    fun (ps : n_procs k) =>
      let (ps', o') := m (raise_to_n_procs _ ps)
      in (select_n_procs _ ps', o').

  (* [n] is meant to be <= than [k] *)
  Definition M_from {n} k {O} (m : M_n n O) : M_n k O :=
    fun (ps : n_procs k) =>
      let (ps', o') := m (select_n_procs _ ps)
      in (raise_to_n_procs _ ps', o').

  Lemma M_to_same :
    forall {n} {O} (m : M_n n O),
      M_to n m = m.
  Proof.
    introv.
    apply functional_extensionality; introv; simpl.
    unfold M_to; autorewrite with comp.
    dest_cases w; autorewrite with comp; auto.
  Qed.
  Hint Rewrite @M_to_same : comp.

  Lemma M_from_same :
    forall {n} {O} (m : M_n n O),
      M_from n m = m.
  Proof.
    introv.
    apply functional_extensionality; introv; simpl.
    unfold M_from; autorewrite with comp.
    dest_cases w; autorewrite with comp; auto.
  Qed.
  Hint Rewrite @M_from_same : comp.

  Lemma select_n_proc_incr_pred_n_proc :
    forall {cn} {k} n (sm : n_proc (pred k) cn),
      n <= pred k
      -> select_n_proc n (incr_pred_n_proc sm)
         = select_n_proc n sm.
  Proof.
    induction k; introv lek; simpl in *; tcsp;[].
    destruct n; auto;[].
    destruct (deq_nat k n); subst; auto;[].
    simpl; try omega.
  Qed.

  Lemma select_n_procs_incr_pred_n_procs :
    forall n k (l : n_procs (pred k)),
      n <= pred k
      -> select_n_procs n (incr_pred_n_procs l)
         = select_n_procs n l.
  Proof.
    induction l; introv len; simpl; tcsp;[].
    repeat (autodimp IHl hyp).
    unfold select_n_procs in *; simpl in *.
    destruct a as [cn p]; simpl.
    rewrite select_n_proc_incr_pred_n_proc; auto;[].
    remember (select_n_proc n p) as w; symmetry in Heqw.
    rewrite IHl; auto.
  Qed.

  Lemma M_to_M_on_pred :
    forall {n} {O} k (m : M_n (pred n) O),
      k <= pred n
      -> M_to k (M_on_pred m) = M_to k m.
  Proof.
    introv le.
    apply functional_extensionality; introv; simpl.
    unfold M_to, M_on_pred; simpl.
    autorewrite with comp.
    rewrite decr_n_procs_as_select_n_procs_pred.
    rewrite raise_to_n_procs_select_n_procs; try omega;[].
    remember (m (raise_to_n_procs (Init.Nat.pred n) x)) as p; repnd.
    rewrite select_n_procs_incr_pred_n_procs; auto.
  Qed.

  Lemma sm2update_as_sm2update_p :
    forall {n} {cn}
           (sm : n_proc n cn) s t i,
      sm2update sm s t i = M_to (sm2level sm) (sm2update_p sm s t i).
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct sm as [sm|sm]; simpl in *; auto; autorewrite with comp; auto;[].
    rewrite IHn.
    pose proof (sm2level_le_pred _ _ sm) as q.
    rewrite M_to_M_on_pred; auto.
  Qed.

  Lemma sm2update_p_as_sm2update :
    forall {n} {cn}
           (sm : n_proc n cn) s t i,
      sm2update_p sm s t i = M_from (pred n) (sm2update sm s t i).
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct sm as [sm|sm]; simpl in *; auto; autorewrite with comp; auto;[].
    rewrite IHn.
    pose proof (sm2level_le_pred _ _ sm) as q.

    apply functional_extensionality; introv; simpl.
    unfold M_on_pred, M_from.
    rewrite select_n_procs_decr_n_procs; auto.
    remember (sm2update sm s t i (select_n_procs (sm2level sm) x)) as w; repnd; f_equal.
    rewrite incr_pred_n_procs_raise_to_n_procs; auto.
  Qed.

(*  Lemma app_m_proc_as_sm2update :
    forall {n} {cn}
           (sm : n_proc n cn)
           (i  : cio_I (fio cn)),
      app_m_proc sm i
      = ((sm2update_p sm (sm2state sm) i)
           >>>= fun s o => ret _ (update_state_or_halt_m sm s, o)).
  Proof.
    induction n; introv; simpl in *; tcsp.
    destruct sm as [sm|sm].

    { f_equal.
      apply functional_extensionality; introv; simpl.
      unfold lift_M_O, app_n_proc_at, bind_pair, bind; simpl.
      fold M_StateMachine in *.
      fold n_proc in *.
      remember (sm_update sm (sm_state sm) i x) as q; symmetry in Heqq; simpl in *; repnd; simpl.
      destruct q1; simpl; auto. }

    { rewrite IHn; simpl.
      f_equal.
      apply functional_extensionality; introv; simpl.
      unfold lift_M_O2, M_on_pred, bind_pair, bind; simpl.
      fold M_StateMachine in *.
      fold n_proc in *.
      remember (sm2update_p sm (sm2state sm) i (decr_n_procs x)) as q; repnd; simpl; auto.
      unfold update_state_or_halt_m; destruct q1; simpl; auto. }
  Qed.*)

  Lemma select_n_proc_raise :
    forall {n} {cn} i j (a : n_proc n cn) b,
      j <= i <= n
      -> select_n_proc j a = Some b
      -> select_n_proc i a = raise_to_n_proc i b.
  Proof.
    induction n; introv len sel; simpl in *; tcsp;[].
    destruct j; simpl in *; tcsp;[].
    destruct (deq_nat n j); subst; ginv.

    { assert (i = S j) by omega; subst.
      destruct (deq_nat j j); subst; simpl in *; tcsp.
      destruct (deq_nat j j); subst; simpl in *; tcsp.
      pose proof (UIP_refl_nat _ e) as z; subst; simpl in *.
      pose proof (UIP_refl_nat _ e0) as z; subst; simpl in *; auto. }

    destruct i; auto; simpl in *; auto; try omega;[].

    destruct (deq_nat n i); subst; simpl in *; try omega.

    { destruct (deq_nat j i); subst; simpl in *; auto;
        destruct a as [a|a]; ginv;[].

      pose proof (raise_to_n_proc_as_select_n_proc _ (S j) i a b) as q.
      autodimp q hyp; try omega.
      apply q in sel; clear q.
      rewrite sel; simpl; auto. }

    destruct (deq_nat j i); subst; try omega;
      destruct a as [a|a]; ginv;[].

    pose proof (IHn _ (S i) (S j) a b) as IHn.
    repeat (autodimp IHn hyp); try omega;[].
    rewrite IHn; simpl.
    destruct (deq_nat j i); subst; try omega; auto.
  Qed.

  Lemma select_n_nproc_raise :
    forall {n} i j (a : n_nproc n) b,
      j <= i <= n
      -> select_n_nproc j a = Some b
      -> select_n_nproc i a = raise_to_n_nproc i b.
  Proof.
    introv len sel.
    destruct a; simpl in *.
    apply option_map_Some in sel; exrepnd; subst; simpl in *.
    apply (select_n_proc_raise i) in sel1; auto.
    rewrite sel1; auto.
  Qed.

(*  Definition M_run_smat_on_inputs {n} {cn}
             (sm : n_proc_at n cn)
             (l  : list (cio_I (fio cn)))
             (i  : cio_I (fio cn))
    : M_n n (op_st_o cn) :=
    M_run_update_on_inputs (sm_state sm) (sm_update sm) l i.*)

(*  Definition halt_main_ls {L S} (ls : LocalSystem L S) : LocalSystem L S :=
    LocalSystem
      (halt_machine (ls_main ls))
      (ls_subs ls).*)

(*  Definition upd_ls_main_op_state_and_subs
             {L} {S}
             (ls : LocalSystem L S)
             (o  : option (sf _))
             (ss : n_procs _) : LocalSystem _ _ :=
    match o with
    | Some s => upd_ls_main_state_and_subs ls s ss
    | None => halt_main_ls (upd_ls_subs ls ss)
    end.*)

(*  Definition M_output_ls_on_input
             {Lv cn}
             (ls : LocalSystem Lv cn)
             (i  : cio_I (fio cn)) : LocalSystem _ _ * cio_O (fio cn) :=
    M_break
      (M_run_smat_on_inputs (ls_main ls) [] i)
      (ls_subs ls)
      (fun subs op =>
         match op with
         | Some (ops, o) => (upd_ls_main_op_state_and_subs ls ops subs, o)
         | None => (halt_main_ls (upd_ls_subs ls subs), cio_default_O (fio cn))
         end).*)

  Definition raise_to_n_proc_def {n} {cn} m (p : n_proc n cn) (d : n_proc m cn) : n_proc m cn :=
    opt_val (raise_to_n_proc m p) d.

  Lemma at2sm_update_state :
    forall n cn (p : n_proc_at n cn) s,
      at2sm (update_state p s)
      = update_state_m (at2sm p) s.
  Proof.
    tcsp.
  Qed.

(*  Lemma at2sm_halt_machine :
    forall n cn (p : n_proc_at n cn),
      at2sm (halt_machine p)
      = halt_machine_m (at2sm p).
  Proof.
    tcsp.
  Qed.*)

  Lemma raise_to_n_proc_update_state_m :
    forall m n cn (p : n_proc n cn) s,
      raise_to_n_proc m (update_state_m p s)
      = option_map
          (fun q => update_state_m q s)
          (raise_to_n_proc m p).
  Proof.
    induction m; introv; simpl in *; tcsp.

    { destruct (deq_nat n 0); subst; simpl in *; tcsp. }

    destruct (deq_nat n (S m)); subst; simpl in *; tcsp.
    rewrite IHm; clear IHm.
    repeat (rewrite option_map_option_map; unfold compose; simpl); auto.
  Qed.

(*  Lemma raise_to_n_proc_halt_machine_m :
    forall m n cn (p : n_proc n cn),
      raise_to_n_proc m (halt_machine_m p)
      = option_map halt_machine_m (raise_to_n_proc m p).
  Proof.
    induction m; introv; simpl in *; tcsp.

    { destruct (deq_nat n 0); subst; simpl in *; tcsp. }

    destruct (deq_nat n (S m)); subst; simpl in *; tcsp.
    rewrite IHm; clear IHm.
    repeat (rewrite option_map_option_map; unfold compose; simpl); auto.
  Qed.*)

  Lemma at2sm_sm2at :
    forall n cn (p : n_proc n cn),
      raise_to_n_proc n (at2sm (sm2at p)) = Some p.
  Proof.
    induction n; introv; simpl in *; tcsp;[].
    destruct p as [p|p]; simpl in *.

    { destruct (deq_nat n n); tcsp.
      pose proof (UIP_refl_nat _ e) as q; subst; simpl in *; auto. }

    destruct (deq_nat (sm2level p) n); subst; simpl in *; tcsp.

    { pose proof (sm2level_le_pred _ _ p) as q.
      rewrite e in q.
      destruct n; simpl in *; try omega. }

    rewrite IHn; simpl; auto.
  Qed.
  Hint Rewrite at2sm_sm2at : comp.

(*  Definition update_subs_with_sub_ls
             {n} {L} {cn}
             (subs : n_procs n)
             (sm   : n_proc n cn)
             (ls   : LocalSystem L cn) : n_procs n :=
    replace_subs
      (replace_name (raise_to_n_proc_def _ (at2sm (ls_main ls)) sm) subs)
      (raise_to_n_procs (pred n) (ls_subs ls)).*)

(*  Lemma M_break_call_comp :
    forall (cn : CompName) n O
           (i    : cio_I (fio cn))
           (subs : n_procs n)
           (F    : n_procs n -> cio_O (fio cn) -> O),
      M_break (call_proc cn i) subs F
      = match find_name cn subs with
        | Some sm =>

          let ls1 := MkLocalSystem (sm2at sm) (select_n_procs _ subs) in
          let (ls2, o) := M_output_ls_on_input ls1 i in
          F (update_subs_with_sub_ls subs sm ls2) o

        | None => F subs (cio_default_O (fio cn))
        end.
  Proof.
    introv.
    unfold M_break, call_proc, M_output_ls_on_input, M_output_sm_on_inputs; simpl.
    unfold update_subs_with_sub_ls.
    unfold M_run_smat_on_inputs, M_run_update_on_inputs; simpl.
    remember (find_name cn subs) as find; symmetry in Heqfind; destruct find; auto;[].
    rename n0 into p.

    autorewrite with comp.
    unfold M_break; simpl.
    rewrite app_m_proc_as_sm2update.
    rewrite sm2update_p_as_sm2update.
    unfold M_from, bind_pair, bind; simpl.
    rewrite select_n_procs_decr_n_procs; eauto 3 with comp;[].

    remember (sm2update p (sm2state p) i (select_n_procs (sm2level p) subs)) as w; repnd; simpl in *.
    f_equal.

    destruct w1; simpl; f_equal; f_equal.

    { rewrite at2sm_update_state.
      unfold raise_to_n_proc_def.
      rewrite raise_to_n_proc_update_state_m.
      autorewrite with comp; simpl; auto. }

    { rewrite at2sm_halt_machine.
      unfold raise_to_n_proc_def.
      rewrite raise_to_n_proc_halt_machine_m.
      autorewrite with comp; simpl; auto. }
  Qed.*)

(*  Lemma ls_subs_upd_ls_main_op_state_and_subs :
    forall {L S} (ls : LocalSystem L S) ops subs,
      ls_subs (upd_ls_main_op_state_and_subs ls ops subs) = subs.
  Proof.
    introv.
    destruct ops; simpl; auto.
  Qed.
  Hint Rewrite @ls_subs_upd_ls_main_op_state_and_subs : comp.*)

(*  Lemma is_proc_n_proc_at_upd_ls_main_op_state_and_subs :
    forall {L S} (ls : LocalSystem L S) ops subs,
      is_proc_n_proc_at (ls_main ls)
      -> is_proc_n_proc_at (upd_ls_main_op_state_and_subs ls ops subs).
  Proof.
    introv; destruct ops; simpl; auto.
  Qed.
  Hint Resolve is_proc_n_proc_at_upd_ls_main_op_state_and_subs : comp.*)

  Lemma is_proc_n_proc_at_update_implies_some :
    forall cn n (p : n_proc_at n cn) s t i subs1 subs2 sop out,
      is_proc_n_proc_at p
      -> sm_update p s t i subs1 = (subs2, (sop, out))
      -> exists s, sop = hsome s.
  Proof.
    introv isp e.
    unfold is_proc_n_proc_at in isp; exrepnd.
    rewrite isp0 in e; clear isp0.
    unfold proc2upd in *; simpl in *.
    unfold interp_s_proc, to_proc_some_state in *; simpl in *.
    unfold bind_pair, bind in *; simpl in *.
    remember (interp_proc (p0 s t i) subs1) as w; repnd; simpl in *; ginv; eauto.
    inversion e; subst; eauto.
  Qed.

(*  Lemma M_output_ls_on_input_preserves :
    forall {L S} (ls1 ls2 : LocalSystem L S) i o,
      wf_ls ls1
      -> are_procs_ls ls1
      -> M_output_ls_on_input ls1 i = (ls2, o)
      -> wf_ls ls2
         /\ are_procs_ls ls2
         /\ similar_sms_at (ls_main ls1) (ls_main ls2)
         /\ similar_subs (ls_subs ls1) (ls_subs ls2).
  Proof.
    introv wf aps out.
    unfold M_output_ls_on_input, M_break in out; simpl in *.
    dest_cases w; symmetry in Heqw.
    unfold M_run_smat_on_inputs in Heqw; simpl in *.
    unfold M_run_update_on_inputs, bind_some, bind in Heqw; simpl in *.
    unfold bind in Heqw; simpl in *.
    repeat (dest_cases w; repnd); ginv.
    inversion Heqw; subst; simpl in *; GC.
    clear Heqw.
    symmetry in Heqw1.
    destruct aps as [aps1 aps2].
    destruct wf as [wf1 wf2].
    pose proof (are_procs_implies_preserves_sub
                  (ls_main ls1)
                  (sm_state (ls_main ls1))
                  i
                  (ls_subs ls1)) as q.
    repeat (autodimp q hyp).
    unfold M_break in q.
    rewrite Heqw1 in q; simpl in *.
    repnd.
    unfold wf_ls, are_procs_ls; simpl.
    autorewrite with comp.
    applydup is_proc_n_proc_at_update_implies_some in Heqw1; auto;[].
    exrepd; subst; simpl in *.
    dands; eauto 3 with comp;[].
    apply similar_subs_preserves_procs_names in q0.
    rewrite <- q0; auto.
  Qed.*)

  Lemma M_break_snd_eq :
    forall {n} {A} {B}
           (m : M_n n (A * B))
           (subs : n_procs n),
      M_break m subs (fun _ out => snd out)
      = snd (M_break m subs (fun _ out => out)).
  Proof.
    introv.
    unfold M_break.
    destruct (m subs); auto.
  Qed.

  Lemma M_break_fst_eq :
    forall {n} {A} {B}
           (m : M_n n (A * B))
           (subs : n_procs n),
      M_break m subs (fun _ out => fst out)
      = fst (M_break m subs (fun _ out => out)).
  Proof.
    introv.
    unfold M_break.
    destruct (m subs); auto.
  Qed.

  Lemma M_break_fst_eq2 :
    forall {n} {A} {B}
           (m : M_n n (A * B))
           (subs : n_procs n),
      M_break m subs (fun _ out => fst out)
      = fst (snd (M_break m subs (fun subs out => (subs, out)))).
  Proof.
    introv.
    unfold M_break.
    destruct (m subs); auto.
  Qed.

  Lemma M_break_snd_eq2 :
    forall {n} {A} {B}
           (m : M_n n (A * B))
           (subs : n_procs n),
      M_break m subs (fun _ out => snd out)
      = snd (snd (M_break m subs (fun subs out => (subs, out)))).
  Proof.
    introv.
    unfold M_break.
    destruct (m subs); auto.
  Qed.

  Lemma M_break_option_map_fst_eq :
    forall {n} {A} {B} {O}
           (m : M_n n (option A * B))
           (subs : n_procs n) (F : n_procs n -> A -> O),
      M_break m subs (fun subs' out => option_map (F subs') (fst out))
      = let (subs',out) := M_break m subs (fun subs' out => (subs', out)) in
        option_map (F subs') (fst out).
  Proof.
    introv.
    unfold M_break.
    destruct (m subs); auto.
  Qed.

  Lemma similar_subs_nil_l :
    forall {n} (subs : n_procs n),
      similar_subs ([] : n_procs n) subs <-> subs = [].
  Proof.
    introv; split; intro q; subst; auto.
    inversion q; auto.
  Qed.
  Hint Rewrite @similar_subs_nil_l : comp.

  Definition sm2p0 {cn} (sm : MP_StateMachine (fun _ => False) cn) : n_proc_at 0 cn := sm.

  Lemma fold_build_m_sm :
    forall {n} {nm} (upd : M_Update n nm (sf nm)) (s : sf nm),
      at2sm (build_mp_sm upd s) = build_m_sm upd s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @fold_build_m_sm : comp.

  Lemma update_state_m_sm_or_at_build_mp_sm :
    forall {cn} (upd : M_Update 0 cn (sf cn)) (s s' : sf cn),
      @update_state_m _ _ _ _ _ _ _ _ 1 cn (@sm_or_at _ False (build_mp_sm upd s)) s'
      = build_m_sm upd s'.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @update_state_m_sm_or_at_build_mp_sm : comp.

  Lemma lower_head_incr_n_procs :
    forall i {n} (l : n_procs n),
      lower_head i (incr_n_procs l)
      = lower_head i l.
  Proof.
    destruct l; simpl; auto.
    destruct n0; simpl in *; tcsp.
  Qed.
  Hint Rewrite lower_head_incr_n_procs : comp.

  Lemma ordered_subs_incr_n_procs :
    forall {n} (l : n_procs n),
      ordered_subs (incr_n_procs l)
      = ordered_subs l.
  Proof.
    unfold incr_n_procs; induction l; introv; simpl in *; tcsp.
    rewrite IHl; f_equal.
    destruct a; simpl.
    fold (incr_n_procs l); autorewrite with comp; auto.
  Qed.
  Hint Rewrite @ordered_subs_incr_n_procs : comp.

  Lemma get_names_incr_n_procs :
    forall {n} (l : n_procs n),
      get_names (incr_n_procs l)
      = get_names l.
  Proof.
    induction l; introv; simpl in *; tcsp.
    rewrite IHl.
    destruct a; simpl in *; tcsp.
  Qed.
  Hint Rewrite @get_names_incr_n_procs : comp.

  Lemma are_procs_n_procs_incr_n_procs :
    forall {n} (l : n_procs n),
      are_procs_n_procs l
      -> are_procs_n_procs (incr_n_procs l).
  Proof.
    introv aps i; apply in_map_iff in i; exrepnd; subst; simpl in *.
    apply aps in i0.
    destruct x; simpl in *; tcsp.
  Qed.
  Hint Resolve are_procs_n_procs_incr_n_procs : comp.

  Lemma similar_procs_incr_n_nproc_left_implies :
    forall {n} (p : n_nproc n) (k : n_nproc (S n)),
      similar_procs (incr_n_nproc p) k
      -> exists j, k = incr_n_nproc j /\ similar_procs p j.
  Proof.
    introv sim.
    inversion sim as [? ? ? ? sims]; clear sim; subst.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
    simpl in *.
    destruct p, p1, p2; simpl in *; tcsp; inversion h1; subst; simpl in *.
    match goal with
    | [ H : context[b] |- _ ] => rename H into h3
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h3; subst; eauto 3 with comp.
    exists (MkPProc pp_name b0); simpl; tcsp.
  Qed.

  Lemma similar_subs_incr_n_procs_left_implies :
    forall {n} (l : n_procs n) (k : n_procs (S n)),
      similar_subs (incr_n_procs l) k
      -> exists j, k = incr_n_procs j /\ similar_subs l j.
  Proof.
    induction l; destruct k; introv sim; simpl in *; tcsp;
      inversion sim; subst; clear sim.
    { exists ([] : n_procs n); simpl; tcsp. }
    apply IHl in sims; clear IHl; exrepnd; subst; simpl in *.
    apply similar_procs_incr_n_nproc_left_implies in simp; exrepnd; subst.
    exists (j0 :: j); simpl; tcsp.
  Qed.

End ComponentSM6.


Hint Rewrite @M_to_same : comp.
Hint Rewrite @M_from_same : comp.
Hint Rewrite @at2sm_sm2at : comp.
(*Hint Rewrite @ls_subs_upd_ls_main_op_state_and_subs : comp.*)
Hint Rewrite @similar_subs_nil_l : comp.
Hint Rewrite @fold_build_m_sm : comp.
Hint Rewrite @update_state_m_sm_or_at_build_mp_sm : comp.
Hint Rewrite @lower_head_incr_n_procs : comp.
Hint Rewrite @ordered_subs_incr_n_procs : comp.
Hint Rewrite @get_names_incr_n_procs : comp.

Hint Resolve are_procs_n_procs_incr_n_procs : comp.


(*Hint Resolve is_proc_n_proc_at_upd_ls_main_op_state_and_subs : comp.*)


Ltac prove_wf :=
  match goal with
  | [ |- wf_procs _ ] =>
    repeat constructor; simpl; tcsp
  end.

Ltac prove_are_procs :=
  match goal with
  | [ |- are_procs_n_procs _ ] =>
    repeat constructor;
    [unfold is_proc_n_proc_at; eexists; introv; reflexivity
    |introv xx; simpl in *; tcsp]
  end.

(*Ltac m_output_ls_on_input_preserves H out :=
  match type of H with
  | M_output_ls_on_input ?ls1 ?i = (?ls2, ?o) =>
    let wf   := fresh "wf"   in
    let wf1  := fresh "wf1"  in
    let wf2  := fresh "wf2"  in
    let wf3  := fresh "wf3"  in
    let wf4  := fresh "wf4"  in
    let main := fresh "main" in
    let subs := fresh "subs" in
    autorewrite with comp minbft in H;
    applydup @M_output_ls_on_input_preserves in H as wf;
    try prove_wf;
    try prove_are_procs;
    destruct ls2 as [main subs]; simpl in *;
    simpl in wf;
    autorewrite with comp minbft in wf;
    destruct wf as [wf1 [wf2 [wf3 wf4]]];
    exrepnd; subst; simpl in *;
    rename o into out
  end.*)

(*Ltac abstract_m_output_ls_on_input H out :=
  match type of H with
  | context[M_output_ls_on_input ?ls ?i] =>
    let o := fresh "out" in
    remember (M_output_ls_on_input ls i) as o;
    repnd;
    match goal with
    | [ G : (_,_) = M_output_ls_on_input _ _ |- _ ] =>
      symmetry in G;
      simpl in H;
      m_output_ls_on_input_preserves G out
    end
  end.*)

(*Ltac use_m_break_call_comp out :=
  match goal with
  | [ H : context[call_proc ?n ?i] |- _ ] =>
    let h  := fresh "h" in
    let xx := fresh "xx" in
    pose proof (M_break_call_comp n) as h;
    rewrite h in H; clear h;
    remember @M_output_ls_on_input as xx;
    simpl in H; subst xx;
    abstract_m_output_ls_on_input H out
  end.*)
