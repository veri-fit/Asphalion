Require Export MinBFTprops0.
(*Require Export MinBFTsubs.*)
Require Export MinBFTbreak.
Require Export MinBFTsim1.
Require Export ComponentSM6.
Require Export ComponentSM9.


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


  Lemma M_break_call_proc_USIGname :
    forall {O} t i subs (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname t i)
        subs
        F
      = match find_name USIGname subs with
        | Some a =>
          match a with
          | sm_or_at a =>
            let subs' := M_break_mon (lift_M_1 (app_n_proc_at (sm2p0 a) t i)) subs in
            let out := M_break_out (lift_M_1 (app_n_proc_at (sm2p0 a) t i)) subs in
            F (replace_name_op (fst out) subs') (snd out)
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
    forall {O} t i subs (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname t i)
        subs
        F
      = match find_name LOGname subs with
        | Some a =>
          match a with
          | sm_or_at a =>
            let subs' := M_break_mon (lift_M_1 (app_n_proc_at (sm2p0 a) t i)) subs in
            let out := M_break_out (lift_M_1 (app_n_proc_at (sm2p0 a) t i)) subs in
            F (replace_name_op (fst out) subs') (snd out)
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

  Lemma ui2counter_commit2ui_i_as_commit2counter_i :
    forall c,
      ui2counter (commit2ui_i c) = commit2counter_i c.
  Proof.
    tcsp.
  Qed.

(*  Lemma similar_sms_at_minbft_replica :
    forall r (p : n_proc_at 1 _),
      similar_sms_at p (MAIN_comp r)
      -> exists s, p = MinBFT_replicaSM_new r s.
  Proof.
    introv sim.
    unfold similar_sms_at in *; repnd; simpl in *; subst.
    destruct p as [h upd st]; simpl in *; subst; simpl in *.
    exists st; auto.
  Qed.*)

(*  Lemma upd_ls_main_state_and_subs_eq_MinBFTlocalSys_newP_implies :
    forall r s subs s1 subs1 s' subs',
      upd_ls_main_state_and_subs (MinBFTlocalSys_newP r s subs) s1 subs1
      = MinBFTlocalSys_newP r s' subs'
      -> s' = s1 /\ subs' = subs1.
  Proof.
    introv h.
    unfold upd_ls_main_state_and_subs in h.
    unfold MinBFTlocalSys_newP in h; inversion h; subst; tcsp.
  Qed.*)

  Lemma is_M_break_mon_0_implies_eq :
    forall {cn} (p : n_proc_at 0 cn) t (i : cio_I (fio cn)) (l k : n_procs 1),
      is_proc_n_proc_at p
      -> is_M_break_mon (lift_M_1 (app_n_proc_at p t i)) l k
      -> k = l.
  Proof.
    introv isp h.
    unfold is_M_break_mon, M_break_mon, M_break, lift_M_1, M_on_decr, app_n_proc_at, bind_pair, bind in h;
      simpl in *; subst.
    rewrite (n_procs_0 (decr_n_procs l)).

    pose proof (are_procs_implies_preserves_sub p (sm_state p) t i []) as q.
    repeat (autodimp q hyp); eauto 3 with comp;[].
    unfold M_break in q.

    remember (sm_update p (sm_state p) t i []) as w; symmetry in Heqw; simpl in *.
    unfold n_nproc in *; simpl in *; rewrite Heqw; rewrite Heqw in q.
    repnd; simpl in *.
    unfold update_subs_decr.
    inversion q0; subst.
    autorewrite with comp; simpl.
    rewrite update_subs_nil_r; auto.
  Qed.

  (* Move to some ComponentSM file*)
  Definition is_proc_n_proc_op {n} {cn} (o : hoption (n_proc n cn)) :=
    match o with
    | hsome p => is_proc_n_proc p
    | halt_local => True
    | halt_global => True
    end.

  (* Move to some ComponentSM file*)
  Lemma in_remove_name_implies_in :
    forall {n} cn (p : n_nproc n) l,
      In p (remove_name l cn)
      -> In p l.
  Proof.
    induction l; introv i; simpl in *; tcsp; dest_cases w.
  Qed.
  Hint Resolve in_remove_name_implies_in : comp.

  (* Move to some ComponentSM file*)
  Lemma are_procs_n_procs_replace_name_op :
    forall {n} {cn} (o : hoption (n_proc n cn)) l,
      is_proc_n_proc_op o
      -> are_procs_n_procs l
      -> are_procs_n_procs (replace_name_op o l).
  Proof.
    introv ips aps i.
    destruct o; simpl in *;tcsp.
    { apply in_replace_name_implies in i; repndors; subst; tcsp. }
    { apply in_remove_name_implies_in in i; tcsp. }
  Qed.
  Hint Resolve are_procs_n_procs_replace_name_op : comp.

  (* Move to some ComponentSM file*)
  Lemma is_M_break_out_preserves_is_proc_n_proc_op :
    forall {n} {cn} (p : n_proc_at n cn) l t i o b,
      is_proc_n_proc_at p
      -> is_M_break_out (lift_M_1 (app_n_proc_at p t i)) l (o, b)
      -> is_proc_n_proc_op o.
  Proof.
    introv isp brk.
    apply is_M_break_out_preserves_subs in brk; auto; exrepnd; subst; simpl in *.
    destruct q; simpl in *; tcsp.
    pose proof (similar_sms_preserves_is_proc_n_proc _ _ (at2sm p) (at2sm a)) as q.
    simpl in q; apply q; auto.
  Qed.
  Hint Resolve is_M_break_out_preserves_is_proc_n_proc_op : comp.

  Lemma is_M_break_out_preserves_subs_sm2p0 :
    forall {cn} (p : n_proc_at 0 cn) l t i o b,
      is_proc_n_proc_at p
      -> is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) t i)) l (o, b)
      -> exists q, o = hsome (at2sm q) /\ similar_sms_at p q.
  Proof.
    introv j h.
    apply is_M_break_out_preserves_subs in h; auto; exrepnd; simpl in *.
    destruct q; simpl in *; tcsp; eauto.
  Qed.

End MinBFTgen.


Hint Rewrite @M_break_call_proc_USIGname : minbft2.
Hint Rewrite @M_break_call_proc_LOGname : minbft2.
Hint Rewrite @unfold_on_create_ui_out : minbft2.
Hint Rewrite @unfold_if_true_verify_ui_out : minbft2.
Hint Rewrite @unfold_on_log_out : minbft2.
Hint Rewrite @unfold_on_log_out_bool : minbft2.


Hint Resolve in_remove_name_implies_in : comp.
Hint Resolve are_procs_n_procs_replace_name_op : comp.
Hint Resolve is_M_break_out_preserves_is_proc_n_proc_op : comp.


(* ********* TACTICS ********* *)

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



Ltac smash_minbft1_ :=
  let atac := fun _ => (eauto 1  with minbft) in
  let stac := fun _ => minbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  let rtac := fun _ => repeat (minbft_rw;simpl) in
  let x := fresh "x" in
  simpl in *;
  dest_all x stac ftac;
  rtac ();
  simplifier stac;
  atac ().

Ltac sp_minbft_rw :=
  progress rewrite_strat try outermost (choice
                                          (choice
                                             (choice
                                                (choice
                                                   M_break_call_proc_LOGname
                                                   M_break_call_proc_USIGname)
                                                M_break_MinBFT_state_update)
                                             M_break_bind)
                                          (choice
                                             (hints minbft)
                                             (hints comp))).

Ltac invalid_prep_imp_count h :=
  match goal with
  | [ H : invalid_prepare _ _ _ _ _ = false |- _ ] =>
    applydup invalid_prepare_false_implies_prepare2counter_eq in H as h
  | [ H : invalid_commit2 _ _ _ _ _ _ = false |- _ ] =>
    applydup invalid_commit2_false_implies_commit2counter_i_eq in H as h
  end.

Ltac prove_has_comp :=
  match goal with
  | [ H : find_name ?cn ?l = Some _ |- has_comp ?cn ?l ] =>
    eapply find_name_implies_has_comp; exact H
  | [ |- has_comp _ (replace_name _ _) ] =>
    apply implies_has_comp_replace_name
  | [ H : similar_subs _ ?l |- has_comp _ ?l ] =>
    eapply similar_subs_preserves_has_comp;[exact H|]
  end.

Ltac rw_find_name_replace_name :=
  match goal with
  | [ H : find_name _ (replace_name _ _) = Some _ |- _ ] =>
    let xx := fresh "xx" in
    first [rewrite find_name_replace_name_diff in H;[|intro xx; inversion xx; fail]
          |rewrite find_name_replace_name_same in H;[|complete (repeat prove_has_comp)];
           try apply eq_Some in H;
           try apply at2sm_eq_sm_or_at_implies in H;
           try subst
          ]
  end.

Ltac pwf_step :=
  match goal with
  | [ H : ?x |- ?x ] => auto

  (* wf_procs *)
  | [ H : find_name _ ?l = Some _ |- wf_procs (replace_name _ ?l) ] =>
    eapply wf_procs_replace_name;[exact H| |]

  | [ |- wf_procs (replace_name _ (replace_name _ _)) ] =>
    apply implies_wf_procs_replace_name_twice

  | [ H : similar_subs _ ?l |- wf_procs (replace_name _ ?l) ] =>
    eapply similar_subs_preserves_wf_procs;
    [apply implies_similar_subs_replace_name;eauto|];
    auto

  (* is_proc_n_proc_at *)
  | [ H : find_name _ _ = Some (sm_or_at ?p) |- is_proc_n_proc_at (sm2p0 ?p) ] =>
    eapply implies_is_proc_n_proc_at_0;[|exact H];auto

  | [ H : find_name _ _ = Some (sm_or_at ?p) |- is_proc_n_proc_at ?p ] =>
    eapply implies_is_proc_n_proc_at_0;[|exact H];auto

  (* is_proc_n_proc *)
  | [ H : find_name _ _ = Some (sm_or_at ?p) |- is_proc_n_proc (at2sm ?p) ] =>
    eapply implies_is_proc_n_proc_at_0;[|exact H];auto

  | [ H : similar_sms_at _ ?b |- is_proc_n_proc (sm_or_at ?b) ] =>
    eapply similar_sms_preserves_is_proc_n_proc;
    [apply implies_similar_sms_sm_or_at;eauto|];
    simpl; auto

  | [ H : similar_sms_at _ ?b |- is_proc_n_proc (at2sm ?b) ] =>
    eapply similar_sms_preserves_is_proc_n_proc;
    [apply implies_similar_sms_sm_or_at;eauto|];
    simpl; auto

  (* is_proc_n_proc_op *)
  | [ H : is_M_break_out (lift_M_1 (app_n_proc_at _ _)) _ (?o,_) |- is_proc_n_proc_op ?o ] =>
    eapply is_M_break_out_preserves_is_proc_n_proc_op;[|exact H]

  (* are_procs_n_procs *)
  | [ |- are_procs_n_procs (replace_name _ _) ] =>
    apply implies_are_procs_n_procs_replace_name; auto

  | [ |- are_procs_n_procs (replace_name_op _ _) ] =>
    apply are_procs_n_procs_replace_name_op; auto

  | [ H : similar_subs _ ?l |- are_procs_n_procs ?l ] =>
    eapply similar_subs_preserves_are_procs_n_procs;[eauto|];auto

  (* similar_subs *)
  | [ |- similar_subs ?l (replace_name _ ?k) ] =>
    apply similar_subs_replace_name_right; auto

  | [ H : similar_subs _ ?b |- similar_subs _ ?b ] =>
    eapply similar_subs_trans;[|eauto]

  (* has_sim_comp *)
  | [ H : find_name _ ?l = Some (sm_or_at ?a) |- has_sim_comp (at2sm ?a) ?l ] =>
    apply find_name_implies_has_sim_comp_at2sm; auto

  | [ H : similar_subs _ ?k |- has_sim_comp _ ?k ] =>
    eapply similar_subs_preserves_has_sim_comp;[eauto|]

  | [ H : similar_sms_at _ ?b |- has_sim_comp (at2sm ?b) _ ] =>
    eapply similar_sms_at_preserves_has_sim_comp;[eauto|]

  | [ |- has_sim_comp _ (replace_name _ _) ] =>
    let xx := fresh "xx" in
    first [apply implies_has_simp_comp_replace_name_same
          |apply implies_has_simp_comp_replace_name_diff;[intro xx; inversion xx; fail|]
          ]
  end.

Ltac pwf := repeat (pwf_step; eauto 2 with comp minbft).

Ltac break2sim :=
  match goal with
  | [ H : is_M_break_mon _ _ _ |- _ ] =>
    apply @is_M_break_mon_preserves_subs in H;
    simpl; eauto 3 with comp minbft; pwf;[]

  | [ H : is_M_break_out _ _ _ |- _ ] =>
    let q  := fresh "q" in
    let h1 := fresh H in
    let h2 := fresh H in
    apply @is_M_break_out_preserves_subs in H;
    eauto 3 with comp minbft;
    destruct H as [q [h1 h2] ]; repnd; subst; simpl in *;pwf;[];
    try (apply similar_sms_at2sm_sm2p0 in h2; exrepnd; subst);
    simpl in *; tcsp;[]
  end.

Ltac break2sims := repeat break2sim.

Ltac rm_is_M_break_mon :=
  match goal with
  | [ H : is_M_break_mon _ _ _ |- _ ] =>
    apply @is_M_break_mon_0_implies_eq in H;[|pwf];[];subst
  end.

Ltac sp_find_name_twice :=
  match goal with
  | [ H : find_name ?a ?b = Some _ , K : find_name ?a ?b = Some _ |- _ ] =>
    rewrite H in K;
    try apply eq_Some in K;
    try apply at2sm_eq_sm_or_at_implies in K;
    try subst
  end.

Ltac sp_sm_or_at :=
  match goal with
  | [ H : sm_or_at _ = at2sm _    |- _ ] => apply at2sm_eq_sm_or_at_implies in H; subst
  | [ H : at2sm _    = sm_or_at _ |- _ ] => apply at2sm_eq_sm_or_at_implies in H; subst
  | [ H : sm_or_at _ = sm_or_at _ |- _ ] => apply at2sm_eq_sm_or_at_implies in H; subst
  | [ H : at2sm _    = at2sm _    |- _ ] => apply at2sm_eq_sm_or_at_implies in H; subst
  end.

Ltac is_M_break_out_some :=
  match goal with
  | [ H : is_M_break_out _ _ (?a, _) |- _ ] =>
    match a with
    | Some _ => fail 1
    | _ =>
      applydup @is_M_break_out_preserves_subs_sm2p0 in H;[|pwf];[];
      exrepnd; subst; simpl in *
    end
  end.


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

Ltac sp_break :=
  match goal with
  | [ H : is_M_break_out ?x ?y _, J : is_M_break_out ?x ?y _ |- _ ] =>
    unfold is_M_break_out in H, J; rewrite H in J; repeat hide_break; subst; ginv; GC
  | [ H : is_M_break_mon ?x ?y _, J : is_M_break_mon ?x ?y _ |- _ ] =>
    unfold is_M_break_mon in H, J; rewrite H in J; repeat hide_break; subst; ginv; GC
  end.

Ltac rw_is_M_break :=
  match goal with
  | [ H : is_M_break_out ?a ?b ?c |- context[M_break_out ?a ?b] ] =>
    rewrite H; simpl
  | [ H : is_M_break_mon ?a ?b ?c |- context[M_break_mon ?a ?b] ] =>
    rewrite H; simpl
  end.
