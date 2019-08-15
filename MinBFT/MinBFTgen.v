Require Export MinBFTprops0.
(*Require Export MinBFTsubs.*)
Require Export MinBFTbreak.
Require Export ComponentSM6.


Section MinBFTgen.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Definition M_break_mon {n} {S}
             (sm   : M_n n S)
             (subs : n_procs n) : n_procs n :=
    M_break sm subs (fun subs' _ => subs').

  Definition M_break_out {n} {S}
             (sm   : M_n n S)
             (subs : n_procs n) : S :=
    M_break sm subs (fun _ out => out).

  Lemma M_break_call_proc_USIGname :
    forall {O} i subs (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname i)
        subs
        F
      = match find_name USIGname subs with
        | Some a =>
          match a with
          | sm_or_at a =>
            let subs' := M_break_mon
                           (lift_M_O (app_n_proc_at (sm2p0 a) i))
                           (decr_n_procs subs) in
            let out := M_break_out
                         (lift_M_O (app_n_proc_at (sm2p0 a) i))
                         (decr_n_procs subs) in
            F (replace_subs (replace_name (fst out) subs) subs')
              (snd out)
          | sm_or_sm x => match x with end
          end
        | None => F subs verify_ui_out_def
        end.
  Proof.
    introv.
    simpl in *.
    unfold M_break_out, M_break_mon, M_break, call_proc; simpl; smash_minbft2.
    destruct x; simpl in *; tcsp.
    smash_minbft2.
    unfold sm2p0 in *; simpl in *.
    rewrite Heqx in *; ginv.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname : minbft2.

  Lemma M_break_call_proc_LOGname :
    forall {O} i subs (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname i)
        subs
        F
      = match find_name LOGname subs with
        | Some a =>
          match a with
          | sm_or_at a =>
            let subs' := M_break_mon
                           (lift_M_O (app_n_proc_at (sm2p0 a) i))
                           (decr_n_procs subs) in
            let out := M_break_out
                         (lift_M_O (app_n_proc_at (sm2p0 a) i))
                         (decr_n_procs subs) in
            F (replace_subs (replace_name (fst out) subs) subs')
              (snd out)
          | sm_or_sm x => match x with end
          end
        | None => F subs (log_out true)
        end.
  Proof.
    introv.
    simpl in *.
    unfold M_break_out, M_break_mon, M_break, call_proc; simpl; smash_minbft2.
    destruct x; simpl in *; tcsp.
    smash_minbft2.
    unfold sm2p0 in *; simpl in *.
    rewrite Heqx in *; ginv.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname : minbft2.

  Lemma unfold_on_create_ui_out :
    forall {A} (f : UI -> A) (d : unit -> A) (out : USIG_output_interface),
      on_create_ui_out f d out
      = match out with
        | create_ui_out (Some ui) => f ui
        | _ => d tt
        end.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @unfold_on_create_ui_out : minbft2.

  Lemma unfold_if_true_verify_ui_out :
    forall {A} (f d : unit -> A) (out : USIG_output_interface),
      if_true_verify_ui_out f d out
      = match out with
        | verify_ui_out b => if b then f tt else d tt
        | _ => d tt
        end.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @unfold_if_true_verify_ui_out : minbft2.

  Lemma unfold_on_log_out :
    forall {A} (d f : unit -> A) (out : LOG_output_interface),
      on_log_out d f out
      = match out with
        | log_out true  => d tt
        | log_out false => f tt
        end.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @unfold_on_log_out : minbft2.

  Lemma unfold_on_log_out_bool :
    forall {A} (f : bool -> A) (out : LOG_output_interface),
      on_log_out_bool f out
      = match out with
        | log_out b  => f b
        end.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @unfold_on_log_out_bool : minbft2.

  Definition is_M_break_mon {n} {S}
             (sm    : M_n n S)
             (subs  : n_procs n)
             (subs' : n_procs n) :=
    M_break_mon sm subs = subs'.

  Definition is_M_break_out {n} {S}
             (sm   : M_n n S)
             (subs : n_procs n)
             (s    : S) :=
    M_break_out sm subs = s.

  Lemma fold_is_M_break_mon :
    forall {n} {S}
           (sm    : M_n n S)
           (subs  : n_procs n)
           (subs' : n_procs n),
      M_break_mon sm subs = subs'
      <-> is_M_break_mon sm subs subs'.
  Proof.
    tcsp.
  Qed.

  Lemma fold_is_M_break_out :
    forall {n} {S}
           (sm   : M_n n S)
           (subs : n_procs n)
           (s    : S),
      M_break_out sm subs = s
      <-> is_M_break_out sm subs s.
  Proof.
    tcsp.
  Qed.

  Lemma ui2counter_commit2ui_i_as_commit2counter_i :
    forall c,
      ui2counter (commit2ui_i c) = commit2counter_i c.
  Proof.
    tcsp.
  Qed.

  Lemma similar_sms_at_minbft_replica :
    forall r (p : n_proc_at 1 _),
      similar_sms_at p (MAIN_comp r)
      -> exists s, p = MinBFT_replicaSM_new r s.
  Proof.
    introv sim.
    unfold similar_sms_at in *; repnd; simpl in *; subst.
    destruct p as [h upd st]; simpl in *; subst; simpl in *.
    exists st; auto.
  Qed.

  (* MOVE to MinBFTsubs *)
  Lemma M_run_ls_before_event_ls_is_minbftP :
    forall {eo   : EventOrdering}
           (e    : Event)
           (r    : Rep)
           (ls   : MinBFTls)
           (subs : n_procs _),
      M_run_ls_before_event (MinBFTlocalSysP r subs) e = Some ls
      ->
      exists (s : MAIN_state) (subs' : n_procs _),
        ls = MinBFTlocalSys_newP r s subs'.
  Proof.
    introv run.
    applydup M_run_ls_before_event_implies_similar_sms_at in run.
    destruct ls as [main subs']; simpl in *.

    apply similar_sms_at_sym in run0.
    apply similar_sms_at_minbft_replica in run0; exrepnd; subst.
    eexists; eexists; eexists; try reflexivity.
  Qed.

  Lemma upd_ls_main_state_and_subs_eq_MinBFTlocalSys_newP_implies :
    forall r s subs s1 subs1 s' subs',
      upd_ls_main_state_and_subs (MinBFTlocalSys_newP r s subs) s1 subs1
      = MinBFTlocalSys_newP r s' subs'
      -> s' = s1 /\ subs' = subs1.
  Proof.
    introv h.
    unfold upd_ls_main_state_and_subs in h.
    unfold MinBFTlocalSys_newP in h; inversion h; subst; tcsp.
  Qed.

End MinBFTgen.


Hint Rewrite @M_break_call_proc_USIGname : minbft2.
Hint Rewrite @M_break_call_proc_LOGname : minbft2.
Hint Rewrite @unfold_on_create_ui_out : minbft2.
Hint Rewrite @unfold_if_true_verify_ui_out : minbft2.
Hint Rewrite @unfold_on_log_out : minbft2.
Hint Rewrite @unfold_on_log_out_bool : minbft2.


(* ********* TACTICS ********* *)

Ltac gdest :=
  let x := fresh "x" in
  match goal with
  | [ H : context[ match ?c with _ => _  end ] |- _ ] =>
    remember c as x; destruct x; simpl in H
  end.

Ltac hide_break :=
  match goal with
  | [ H : context[M_break_mon ?sm ?subs] |- _ ] =>
    let m := fresh "mon" in
    remember (M_break_mon sm subs) as m;
    match goal with
    | [ J : m = M_break_mon sm subs |- _ ] =>
      symmetry in J;
      simpl in J;
      try (rewrite J in H);
      rewrite fold_is_M_break_mon in J
    end

  | [ H : context[M_break_out ?sm ?subs] |- _ ] =>
    let m := fresh "out" in
    remember (M_break_out sm subs) as m;
    match goal with
    | [ J : m = M_break_out sm subs |- _ ] =>
      symmetry in J;
      simpl in J;
      try (rewrite J in H);
      rewrite fold_is_M_break_out in J
    end
  end.

Ltac minbft_rw_in H :=
  progress rewrite_strat try outermost (choice
                                          (choice
                                             M_break_call_proc_LOGname
                                             M_break_call_proc_USIGname)
                                          (choice
                                             (hints minbft)
                                             (choice
                                                (hints minbft2)
                                                (choice
                                                   (hints comp)
                                                   (choice
                                                      (hints kn)
                                                      (choice
                                                         (hints eo)
                                                         (hints proc))))))) in H.

Ltac minbft_rw :=
  progress rewrite_strat try outermost (choice
                                          (choice
                                             M_break_call_proc_LOGname
                                             M_break_call_proc_USIGname)
                                          (choice
                                             (hints minbft)
                                             (choice
                                                (hints minbft2)
                                                (choice
                                                   (hints comp)
                                                   (choice
                                                      (hints kn)
                                                      (choice
                                                         (hints eo)
                                                         (hints proc))))))).

Ltac smash_minbft1_at_ H :=
  let atac := fun _ => (eauto 1  with minbft) in
  let stac := fun _ => minbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  let rtac := fun _ => repeat (minbft_rw_in H;simpl in H) in
  let x := fresh "x" in
  simpl in *;
  dest_all x stac ftac;
  rtac ();
  simplifier stac;
  atac ().

Ltac rw_is_M_break :=
  match goal with
  | [ H : is_M_break_out ?a ?b ?c |- context[M_break_out ?a ?b] ] =>
    rewrite H; simpl
  | [ H : is_M_break_mon ?a ?b ?c |- context[M_break_mon ?a ?b] ] =>
    rewrite H; simpl
  end.
