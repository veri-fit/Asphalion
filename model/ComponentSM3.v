Require Export ComponentSM2.


Section ComponentSM3.

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


  (* As opposed to [M_byz_compose], this one shows that the machine doesn't terminate.
     TODO: We could have a separate lemma that shows that.  We have in addition to
     assume that there is at least one trusted component.
   *)
  Lemma M_byz_compose2 :
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
      exists (s : M_trusted (sf cn)) (l : list (trigger_info (cio_I (fio cn)))),
        map_untrusted_op
          (snd (run_sm_on_byz_inputs sm l (ls_subs ls)))
          (fun p => Some (sm2state p)) = Some s
        /\ M_byz_state_ls_before_event ls e cn = Some s.
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
      eexists; exists ([] : list (trigger_info (cio_I (fio cn)))); dands;[|eauto]; simpl; auto. }

    pose proof (ind (local_pred e)) as ind.
    autodimp ind hyp; eauto 3 with eo.
    pose proof (ind L S ls cn sm) as ind.
    repeat (autodimp ind hyp).
    exrepnd.

    unfold M_byz_state_ls_before_event in ind1.

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
      rewrite z1 in ind1; simpl in ind1; ginv.
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

        eexists; exists (map (fun x => trigger_info_data x) (l0 ++ l1)).
        dands;[|eauto].

        pose proof (run_sm_on_byz_inputs_as_run_sm_on_inputs
                      cn L (l0 ++ l1) sm (ls_subs ls)) as xx.
        autodimp xx hyp; eauto 3 with comp;[].

        remember (run_sm_on_inputs sm (l0 ++ l1) (ls_subs ls)) as rn.
        symmetry in Heqrn; repnd; simpl.
        simpl in xx; rewrite xx; clear xx; simpl; auto. }

      { dup trust as trust'.
        unfold is_trusted_ls in trust'.
        erewrite <- (similar_subs_preserves_is_trusted L cn) in trust';[|eauto].

        pose proof (run_sm_on_byz_inputs_as_run_sm_on_inputs_app
                      cn L l0 [trigger_info_arbitrary] sm (ls_subs ls)) as h.
        remember (run_sm_on_inputs sm l0 (ls_subs ls)) as rn; symmetry in Heqrn.
        repnd; simpl in *.
        rewrite <- snoc_as_app in h.

        applydup is_trusted_implies_find_trusted2 in trust'; exrepnd.
        unfold find_sub in z0.
        rewrite trust'0 in z0.
        inversion z0; subst sm0.

        eexists.
        exists (snoc (map (fun x => trigger_info_data x) l0) trigger_info_arbitrary).

        rewrite h; clear h.
        unfold byz_run_sm_on_byz_inputs; simpl.
        rewrite trust'1; simpl.
        rewrite (to_trusted_eq _ eqn); simpl; dands; eauto. }

      { dup trust as trust'.
        unfold is_trusted_ls in trust'.
        erewrite <- (similar_subs_preserves_is_trusted L cn) in trust';[|eauto].

        pose proof (run_sm_on_byz_inputs_as_run_sm_on_inputs_app
                      cn L l0 [trigger_info_trusted i] sm (ls_subs ls)) as h.
        remember (run_sm_on_inputs sm l0 (ls_subs ls)) as rn; symmetry in Heqrn.
        repnd; simpl in *.
        rewrite <- snoc_as_app in h.

        applydup is_trusted_implies_find_trusted2 in trust'; exrepnd.
        unfold find_sub in z0.
        rewrite trust'0 in z0.
        inversion z0; subst sm0.

        eexists.
        exists (snoc (map (fun x => trigger_info_data x) l0) (trigger_info_trusted i)).

        rewrite h; clear h.
        unfold byz_run_sm_on_byz_inputs; simpl.
        rewrite trust'1; simpl.
        rewrite (to_trusted_eq _ eqn); simpl; dands; eauto. } }

    { simpl in *; ginv.
      remember (trigger (local_pred e)) as trig.
      destruct trig; simpl;[| |];
        try (complete (eexists; exists l; rewrite ind0; simpl; auto));[].

      remember (sm_update (tsm_sm t) (state_of_trusted t) i []) as z; symmetry in Heqz.
      simpl in *; repnd.
      apply map_untrusted_op_Some_M_t_implies in ind0.

      eexists.
      exists (snoc l (trigger_info_trusted i)).

      rewrite snoc_as_app.
      remember (run_sm_on_byz_inputs sm l (ls_subs ls)) as w; symmetry in Heqw; repnd; simpl in *; subst.
      applydup (run_sm_on_byz_inputs_as_run_sm_on_inputs_app_trusted
                  l [trigger_info_trusted i] sm) in Heqw; simpl in *.
      rewrite Heqw0; clear Heqw0.
      rewrite Heqz; simpl; dands; eauto. }
  Qed.

  Definition trusted_run_sm_on_byz_inputs {n} {cn}
             (p    : n_proc n cn)
             (mt   : M_trusted (sf cn))
             (l    : list (trigger_info (cio_I (fio cn))))
             (subs : n_procs n) : n_procs n * M_trusted (n_proc n cn) :=
    match mt with
    | inl s => run_sm_on_byz_inputs (update_state_m p s) l subs
    | inr t => ([], M_t (run_trustedSM_on_trigger_info_list t l))
    end.

  Lemma map_untrusted_op_Some_M_nt_implies :
    forall {T} {A} (x : M_trusted T) (F : T -> option A) (a : A),
      map_untrusted_op x F = Some (M_nt a)
      -> exists t, x = M_nt t /\ F t = Some a.
  Proof.
    introv h.
    destruct x; simpl in *; ginv; tcsp;[].
    apply option_map_Some in h; exrepnd; ginv.
    exists t; dands; auto.
  Qed.

  Lemma similar_sms_implies_eq_update_state_m_sm2state :
    forall n cn (sm1 sm2 : n_proc n cn),
      similar_sms sm1 sm2
      -> sm2 = update_state_m sm1 (sm2state sm2).
  Proof.
    induction n; introv sim; simpl in *; tcsp;[].
    destruct sm1, sm2; simpl in *; tcsp.

    { unfold similar_sms_at in sim; repnd; subst.
      destruct a as [h1 u1 s1], a0 as [h2 u2 s2]; simpl in *; subst; auto. }

    { apply IHn in sim.
      rewrite sim at 1; auto. }
  Qed.

  Lemma similar_subs_preserves_find_name :
    forall n cn (subs1 subs2 : n_procs n) (sm1 sm2 : n_proc n cn),
      similar_subs subs1 subs2
      -> find_name cn subs1 = Some sm1
      -> find_name cn subs2 = Some sm2
      -> sm2 = update_state_m sm1 (sm2state sm2).
  Proof.
    introv sim.
    induction sim; introv fn1 fn2; simpl in *; tcsp.
    destruct p1 as [n1 p1], p2 as [n2 p2].
    applydup @similar_procs_implies_same_name in simp; simpl in *; subst.
    apply similar_procs_implies_same_proc in simp.
    destruct (CompNameDeq n2 cn); subst; simpl in *; ginv; tcsp.
    apply similar_sms_implies_eq_update_state_m_sm2state; auto.
  Qed.

  Lemma similar_subs_preserves_find_sub :
    forall {L S cn} (ls ls' : LocalSystem L S) (sm : n_proc L cn) (s : sf cn),
      wf_ls ls
      -> find_sub cn ls = Some sm
      -> similar_subs (ls_subs ls) (ls_subs ls')
      -> state_of_component cn ls' = Some s
      -> find_sub cn ls' = Some (update_state_m sm s).
  Proof.
    introv wf fs sim comp.
    unfold find_sub in *.
    unfold state_of_component in comp.
    destruct wf as [wf1 wf2].
    destruct ls as [main1 subs1], ls' as [main2 subs2].
    autorewrite with comp in *.
    destruct (CompNameDeq S cn); subst.

    { apply find_name_implies_in_procs_names in fs; tcsp. }

    unfold state_of_subcomponents in comp.
    apply option_map_Some in comp; exrepnd; subst.
    erewrite <- similar_subs_preserves_find_name; eauto.
  Qed.
  Hint Resolve similar_subs_preserves_find_sub : comp.

  Lemma similar_subs_preserves_is_trusted_ls :
    forall {L S} cn (ls1 ls2 : LocalSystem L S),
      similar_subs (ls_subs ls1) (ls_subs ls2)
      -> is_trusted_ls cn ls1
      -> is_trusted_ls cn ls2.
  Proof.
    introv sim ist.
    unfold is_trusted_ls in *.
    destruct ls1 as [main1 subs1], ls2 as [main2 subs2]; simpl in *.
    apply (similar_subs_preserves_is_trusted _ cn) in sim; congruence.
  Qed.
  Hint Resolve similar_subs_preserves_is_trusted_ls : comp.

  (* TODO: use this one to prove the other M_byz_compose lemmas *)
  Lemma M_byz_compose_step :
    forall {eo : EventOrdering} (e : Event)
           {L S} {cn}
           (ls : MLocalSystem L S)
           (sm : n_proc L cn),
      are_procs_ls ls
      -> wf_ls ls
      -> find_sub cn ls = Some sm
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      -> is_trusted_ls cn ls
      ->
      exists (s : M_trusted (sf cn)) (l : list (trigger_info (cio_I (fio cn)))),
        map_op_untrusted_op
          (M_byz_run_ls_on_this_one_event ls e)
          (state_of_component cn) = Some s
        /\ map_untrusted_op
             (snd (run_sm_on_byz_inputs sm l []))
             (fun p => Some (sm2state p)) = Some s.
  Proof.
    introv aps wf fs lvl trust.
    unfold M_byz_run_ls_on_this_one_event, M_break.

    pose proof (are_procs_ls_implies_ls_run_sub ls) as lsr; repeat (autodimp lsr hyp).
    pose proof (are_procs_ls_implies_ls_preserves_sub ls) as lps; repeat (autodimp lps hyp).

    applydup @find_sub_implies_state_of_component in fs; auto.
    applydup @find_sub_implies_in in fs.

    remember (trigger e) as trig; clear Heqtrig.
    destruct trig; simpl;[| |].

    { remember (sm_update (ls_main ls) (sm_state (ls_main ls)) d (ls_subs ls)) as w; symmetry in Heqw.
      repnd; simpl.
      applydup @are_procs_ls_implies_some in Heqw; auto;[].
      exrepnd; subst.
      autorewrite with comp.

      pose proof (lsr (sm_state (ls_main ls)) d) as lsr.
      pose proof (lps (sm_state (ls_main ls)) d (ls_subs ls)) as lps.
      autodimp lps hyp; eauto 3 with comp.
      unfold M_break in lps; split_pair.
      rewrite Heqw in lsr; simpl in lsr.
      rewrite Heqw in lps; simpl in lps.

      apply lsr in fs1; auto; exrepnd;[].

      dup fs2 as v.
      apply (state_of_components_upd_ls_main_state_and_subs_if_in s ls) in v; eauto; eauto 3 with comp;[].
      rewrite v; simpl.

      rewrite (eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf l sm (ls_subs ls) []); auto;[].

      pose proof (run_sm_on_byz_inputs_as_run_sm_on_inputs cn L l sm []) as xx.
      autodimp xx hyp; eauto 3 with comp;[].
      remember (run_sm_on_inputs sm l []) as rn.
      symmetry in Heqrn; repnd; simpl.

      eexists.
      exists (map (fun x => trigger_info_data x) l).
      dands; try reflexivity.
      simpl; simpl in xx; rewrite xx; auto. }

    { dup trust as trust'.
      unfold is_trusted_ls in trust'.

      applydup is_trusted_implies_find_trusted2 in trust'; exrepnd.
      unfold find_sub in fs.
      rewrite trust'0 in fs.
      inversion fs; subst sm0.
      rewrite trust'1; simpl.

      eexists.
      exists [trigger_info_arbitrary : trigger_info (cio_I (fio cn))]; simpl.
      dands; eauto.
      unfold byz_run_sm_on_byz_inputs; simpl.
      rewrite (to_trusted_eq _ eqn); simpl; auto. }

    { dup trust as trust'.
      unfold is_trusted_ls in trust'.

      applydup is_trusted_implies_find_trusted2 in trust'; exrepnd.
      unfold find_sub in fs.
      rewrite trust'0 in fs.
      inversion fs; subst sm0.
      rewrite trust'1; simpl.

      eexists.
      exists [trigger_info_trusted i : trigger_info (cio_I (fio cn))]; simpl.
      dands; dands; eauto;[].
      unfold byz_run_sm_on_byz_inputs; simpl.
      rewrite (to_trusted_eq _ eqn); simpl; auto. }
  Qed.

  Lemma M_byz_compose_step2 :
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
      exists (s1 s2 : M_trusted (sf cn)) (l : list (trigger_info (cio_I (fio cn)))),
        M_byz_state_ls_before_event ls e cn = Some s1
        /\ M_byz_state_ls_on_event ls e cn = Some s2
        /\ map_untrusted_op
             (snd (trusted_run_sm_on_byz_inputs sm s1 l []))
             (fun p => Some (sm2state p)) = Some s2.
  Proof.
    introv aps wf fs lvl ist.
    pose proof (M_byz_compose2 e ls sm) as q.
    repeat (autodimp q hyp); exrepnd.
    clear dependent l.
    exists s.
    unfold M_byz_state_ls_on_event, M_byz_state_ls_before_event in *.
    rewrite M_byz_run_ls_on_event_unroll2.
    rewrite q1.

    remember (M_byz_run_ls_before_event ls e) as run; symmetry in Heqrun.
    destruct run; simpl in *; ginv;[].

    destruct s as [s|t]; simpl in *.

    { apply map_untrusted_op_Some_M_nt_implies in q1; exrepnd.
      subst; simpl in *.
      rename t into ls'.
      applydup M_byz_run_ls_before_event_M_nt_preserves_subs in Heqrun; auto; repnd.

      assert (find_sub cn ls' = Some (update_state_m sm s)) as fs' by eauto 3 with comp.
      assert (is_trusted_ls cn ls') as ist' by eauto 3 with comp.
      assert (sm2level (update_state_m sm s) = 0) as lvl' by (autorewrite with comp; auto).

      clear dependent ls.
      pose proof (M_byz_compose_step e ls' (update_state_m sm s)) as q.
      repeat (autodimp q hyp).
      exrepnd.
      exists s0 l; dands; auto. }

    { apply map_untrusted_op_Some_M_t_implies in q1; exrepnd; subst; simpl in *.
      remember (trigger e) as trig.
      destruct trig; simpl;[| |];
        try (complete (exists (M_t t : M_trusted (sf cn)) ([] : list (trigger_info (cio_I (fio cn))));
                              simpl; dands; auto));[].

      eexists.
      exists [trigger_info_trusted i : trigger_info (cio_I (fio cn))].
      dands; try reflexivity. }
  Qed.

  (*Definition to_trusted_state {cn} : sf cn -> option tsf :=
    match cn with
    | MkCompName k s true => fun s => Some s
    | _ => fun _ => None
    end.*)

  (*Definition run_sm_on_inputs_trusted {n} {cn}
             (sm   : n_proc n cn)
             (l    : list (cio_I (fio cn)))
             (subs : n_procs n) : option tsf :=
    let (subs', sm') := run_sm_on_inputs sm l subs in
    to_trusted_state (sm2state sm').*)

  Definition run_sm_on_inputs_trusted
             {n} {k} {s}
             (sm : n_proc n (MkCN k s true))
             (l  : list (cio_I (fio (MkCN k s true)))) : tsf :=
    sm2state (snd (run_sm_on_inputs sm l [])).

  Definition trusted_run_sm_on_inputs {n} {cn} (t : tsf)
    : n_proc n cn -> list (cio_I (fio cn)) -> option tsf :=
    match cn with
    | MkCompName k s true =>
      fun sm l => Some (run_sm_on_inputs_trusted (update_state_m sm t) l)
    | _ => fun sm l => None
    end.

  Definition is_trusted_comp_name (cn : CompName) :=
    comp_name_trust cn = true.

  Lemma is_trusted_comp_name_implies_to_trusted_some :
    forall {cn} {n} (sm : n_proc n cn),
      is_trusted_comp_name cn
      -> exists t, to_trusted sm = Some t.
  Proof.
    introv ist.
    destruct cn as [s k t]; simpl in *.
    unfold is_trusted_comp_name in ist; simpl in *; subst; simpl in *; eauto.
  Qed.

  Lemma run_sm_on_byz_inputs_M_nt_implies :
    forall n cn l (sm1 sm2 : n_proc n cn) (subs1 subs2 : n_procs n),
      is_trusted_comp_name cn
      -> run_sm_on_byz_inputs sm1 l subs1 = (subs2, M_nt sm2)
      ->
      exists k,
        l = map (fun x => trigger_info_data x) k
        /\ run_sm_on_inputs sm1 k subs1 = (subs2, sm2).
  Proof.
    induction l; introv istcn run; simpl in *; tcsp; ginv.
    { exists ([] : list (cio_I (fio cn))); simpl; dands; auto. }

    destruct a; simpl in *; ginv.

    { dest_cases w; repnd; simpl in *.
      symmetry in Heqw.
      apply IHl in run; exrepnd; subst; auto;[].
      exists (d :: k); simpl; dands; auto.
      rewrite Heqw; auto. }

    { unfold byz_run_sm_on_byz_inputs in run; simpl in *.
      pose proof (is_trusted_comp_name_implies_to_trusted_some sm1) as k.
      autodimp k hyp; exrepnd.
      rewrite k0 in run; ginv. }

    { unfold byz_run_sm_on_byz_inputs in run; simpl in *.
      pose proof (is_trusted_comp_name_implies_to_trusted_some sm1) as k.
      autodimp k hyp; exrepnd.
      rewrite k0 in run; ginv. }
  Qed.

  Lemma sm_state_sm2at :
    forall {cn} {n} (sm : n_proc n cn),
      sm_state (sm2at sm) = sm2state sm.
  Proof.
    induction n; introv; simpl in *; tcsp; destruct sm as [sm|sm]; tcsp.
  Qed.
  Hint Rewrite @sm_state_sm2at : comp.

  Lemma is_proc_n_proc_to_trusted_implies_update_some :
    forall {n} {cn} (sm : n_proc n cn) (tsm : trustedSM) i subs1 subs2 sop out,
      is_proc_n_proc sm
      -> to_trusted sm = Some tsm
      -> sm_update (tsm_sm tsm) (state_of_trusted tsm) i subs1
         = (subs2, (sop, out))
      -> exists s, sop = Some s.
  Proof.
    introv isp trust upd.
    destruct cn as [k s t]; simpl in *.
    destruct t; ginv; simpl in *;[].
    unfold state_of_trusted in upd; simpl in upd.
    autorewrite with comp in *.
    apply @is_proc_n_proc_update_implies_some in upd; auto.
  Qed.

  Lemma implies_equal_trustedSM :
    forall lvl1 lvl2 k s
           (sm1 : n_proc_at lvl1 (MkCN k s true))
           (sm2 : n_proc_at lvl2 (MkCN k s true))
           (e : lvl1 = lvl2),
      (eq_rect _ (fun n => n_proc_at n _) sm1 _ e) = sm2
      -> MktrustedSM lvl1 k s sm1 = MktrustedSM lvl2 k s sm2.
  Proof.
    introv eqsm.
    subst; simpl in *; auto.
  Qed.

  Lemma sm2at_update_state_m_as_update_state_sm2at :
    forall n cn (sm : n_proc n cn) s
           (e : sm2level (update_state_m sm s) = sm2level sm),
      (eq_rect
         _ (fun n => n_proc_at n cn)
         (sm2at (update_state_m sm s))
         _ e)
      = update_state (sm2at sm) s.
  Proof.
    induction n; introv; simpl in *; tcsp;[].
    destruct sm as [sm|sm]; simpl in *; tcsp.
    pose proof (UIP_refl_nat _ e) as xx; subst; simpl in *; auto.
  Qed.

  Lemma run_trustedSM_on_trigger_info_list_implies_run_sm_on_inputs :
    forall {D} (l : list (trigger_info D))
           (tsm1 tsm2 : trustedSM)
           {n} {cn}
           (sm : n_proc n cn),
      sm2level sm = 0
      -> is_proc_n_proc sm
      -> to_trusted sm = Some tsm1
      -> run_trustedSM_on_trigger_info_list tsm1 l = tsm2
      ->
      exists (l' : list (cio_I (fio cn))) (sm' : n_proc n cn),
        run_sm_on_inputs sm l' [] = ([], sm')
        /\ to_trusted sm' = Some tsm2.
  Proof.
    induction l; introv lvl isp trust run; simpl in *; subst; tcsp.

    { exists ([] : list (cio_I (fio cn))) sm; simpl; auto. }

    destruct a; simpl in *.

    { pose proof (IHl tsm1 (run_trustedSM_on_trigger_info_list tsm1 l) n cn sm) as IHl.
      repeat (autodimp IHl hyp). }

    { pose proof (IHl tsm1 (run_trustedSM_on_trigger_info_list tsm1 l) n cn sm) as IHl.
      repeat (autodimp IHl hyp). }

    { remember (sm_update (tsm_sm tsm1) (state_of_trusted tsm1) i []) as w; symmetry in Heqw; repnd; simpl in *.
      applydup (is_proc_n_proc_to_trusted_implies_update_some sm) in Heqw; auto;[].
      exrepnd; subst; simpl in *.

      destruct cn as [k sp t]; simpl in *.
      destruct t; simpl in *; ginv;[].
      unfold tsm_sm, state_of_trusted in Heqw; simpl in *.

      pose proof (IHl (MktrustedSM (sm2level sm) k sp (update_state (sm2at sm) s))
                      (run_trustedSM_on_trigger_info_list (MktrustedSM (sm2level sm) k sp (update_state (sm2at sm) s)) l)
                      n (MkCN k sp true)
                      (update_state_m sm s)) as IHl.
      simpl in *; autorewrite with comp in *.

      repeat (autodimp IHl hyp); autorewrite with comp; eauto 3 with comp;[|].

      { f_equal.
        assert (sm2level (update_state_m sm s) = sm2level sm) as e by (autorewrite with comp; auto).
        apply (implies_equal_trustedSM _ _ _ _ _ _ e).
        apply sm2at_update_state_m_as_update_state_sm2at. }

      exrepnd.
      exists (i :: l') sm'; simpl.
      rewrite select_n_procs_nil_if_leaf; auto; simpl in *.
      unfold n_nproc;rewrite Heqw ;simpl.
      dands; auto.
      pose proof (are_procs_implies_preserves_sub (sm2at sm) (sm2state sm) i []) as q.
      repeat (autodimp q hyp); eauto 3 with comp;[].
      autorewrite with comp in q; simpl in q.
      unfold M_break in q; simpl in q.
      unfold n_nproc in q; rewrite Heqw in q; repnd.
      inversion q0; clear q0; subst; simpl in *.
      autorewrite with comp; auto. }
  Qed.

  Lemma run_sm_on_byz_inputs_M_t_implies :
    forall n k s l (sm : n_proc n (MkCN k s true)) (tsm : trustedSM) (subs1 subs2 : n_procs n),
      sm2level sm = 0
      -> is_proc_n_proc sm
      -> run_sm_on_byz_inputs sm l subs1 = (subs2, M_t tsm)
      ->
      exists (sm' : n_proc n (MkCN k s true)) (l' : list (cio_I (fio (MkCN k s true)))) (subs : n_procs n),
        run_sm_on_inputs sm l' subs1 = (subs, sm')
        /\ to_trusted sm' = Some tsm.
  Proof.
    induction l; introv lvl isp run; simpl in *; tcsp; ginv;[].

    destruct a; simpl in *; ginv.

    { dest_cases w; repnd; simpl in *.
      symmetry in Heqw.
      apply IHl in run; exrepnd; subst; autorewrite with comp; eauto 3 with comp; auto;[].
      ginv; subst; simpl in *.
      exists sm' (d :: l') subs; simpl; dands; auto.
      rewrite Heqw; auto. }

    { unfold byz_run_sm_on_byz_inputs in run; simpl in *.
      inversion run; subst; simpl in *; clear run.
      clear IHl.
      pose proof (run_trustedSM_on_trigger_info_list_implies_run_sm_on_inputs
                    l
                    (MktrustedSM (sm2level sm) k s (sm2at sm))
                    (run_trustedSM_on_trigger_info_list (MktrustedSM (sm2level sm) k s (sm2at sm)) l)
                    sm) as xx.
      repeat (autodimp xx hyp);[].
      exrepnd; simpl in *.

      pose proof (@eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf
                    _ _ _ _ _ _ _ _ (MkCN k s true) n
                    l' sm subs1 []) as xx; autodimp xx hyp.
      rewrite xx0 in xx; simpl in *.
      remember (run_sm_on_inputs sm l' subs1) as zz; symmetry in Heqzz; repnd; simpl in *; subst.

      exists sm' l' zz0.
      dands; auto. }

    { unfold byz_run_sm_on_byz_inputs in run; simpl in *.
      inversion run; subst; simpl in *; clear run.
      clear IHl.
      unfold MkCN, state_of_trusted; simpl.

      remember (sm_update (sm2at sm) (sm_state (sm2at sm)) i []) as upd; symmetry in Hequpd; repnd.
      autorewrite with comp in *.
      applydup is_proc_n_proc_update_implies_some in Hequpd; auto;[].
      exrepnd; subst; simpl in *.

      pose proof (run_trustedSM_on_trigger_info_list_implies_run_sm_on_inputs
                    l
                    (MktrustedSM (sm2level sm) k s (update_state (sm2at sm) s0))
                    (run_trustedSM_on_trigger_info_list (MktrustedSM (sm2level sm) k s (update_state (sm2at sm) s0)) l)
                    (update_state_m sm s0)) as xx.
      repeat (autodimp xx hyp); autorewrite with comp; eauto 3 with comp;[|].

      { simpl; f_equal.
        assert (sm2level (update_state_m sm s0) = sm2level sm) as e by (autorewrite with comp; auto).
        apply (implies_equal_trustedSM _ _ _ _ _ _ e).
        apply sm2at_update_state_m_as_update_state_sm2at. }

      exrepnd; simpl in *.

      pose proof (@eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf
                    _ _ _ _ _ _ _ _ (MkCN k s true) n
                    l' (update_state_m sm s0) subs1 []) as xx.
      autodimp xx hyp; autorewrite with comp; auto;[].
      rewrite xx0 in xx; simpl in *.
      remember (run_sm_on_inputs (update_state_m sm s0) l' subs1) as zz; symmetry in Heqzz; repnd; simpl in *; subst.

      exists sm' (i :: l'); simpl.
      rewrite select_n_procs_nil_if_leaf; auto; simpl in *;[].
      unfold n_nproc, MkCN in *; rewrite Hequpd; repnd; simpl.

      pose proof (@eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf
                    _ _ _ _ _ _ _ _ (MkCN k s true) n
                    l' (update_state_m sm s0) subs1 (raise_to_n_procs n upd0)) as eqrun.
      autorewrite with comp in eqrun; autodimp eqrun hyp; auto;[].
      unfold MkCN in *; rewrite Heqzz in eqrun; simpl in eqrun.
      remember (run_sm_on_inputs (update_state_m sm s0) l' (raise_to_n_procs n upd0)) as r; symmetry in Heqr.
      repnd; simpl in *; subst.
      exists r0; dands; auto. }
  Qed.

  Lemma is_trusted_ls_implies_is_trusted_comp_name :
    forall cn {L S} (ls : LocalSystem L S),
      is_trusted_ls cn ls
      -> is_trusted_comp_name cn.
  Proof.
    introv trust.
    unfold is_trusted_ls in trust.
    destruct ls as [main subs]; simpl in *.
    induction subs; simpl in *; tcsp.
    destruct a as [c a]; simpl in *.
    destruct c as [k n t]; simpl in *.
    destruct t; simpl in *; tcsp.

    destruct (CompNameDeq cn (MkCN k n true)); subst; simpl in *; tcsp.
  Qed.
  Hint Resolve is_trusted_ls_implies_is_trusted_comp_name : comp.

  Lemma sm2at_as_update_state_sm2at_sm2state :
    forall n cn (p1 p2 : n_proc n cn)
           (e : sm2level p2 = sm2level p1),
      similar_sms p1 p2
      -> (eq_rect
            _ (fun n => n_proc_at n cn)
            (sm2at p2)
            _ e)
         = update_state (sm2at p1) (sm2state p2).
  Proof.
    induction n; introv sim; simpl in *; tcsp;[].
    destruct p1 as [p1|p1], p2 as [p2|p2]; simpl in *; tcsp;[].
    pose proof (UIP_refl_nat _ e) as xx; subst; simpl in *; auto.
    unfold similar_sms_at in sim; repnd.
    destruct p1 as [h1 upd1 s1], p2 as [h2 upd2 s2]; simpl in *; subst.
    unfold update_state; simpl; auto.
  Qed.

  Lemma similar_subs_preserves_find_trusted :
    forall n (subs1 subs2 : n_procs n) tsm,
      similar_subs subs1 subs2
      -> find_trusted subs1 = Some tsm
      -> exists s,
          find_trusted subs2 = Some (updateTrustedSM tsm s).
  Proof.
    introv sim; induction sim; introv find; simpl in *; tcsp.
    destruct p1 as [n1 p1], p2 as [n2 p2].
    applydup @similar_procs_implies_same_name in simp; simpl in *; subst.
    apply similar_procs_implies_same_proc in simp.
    destruct n2 as [k2 s2 t2]; simpl in *.
    destruct t2; ginv; simpl in *;[].
    exists (sm2state p2).
    f_equal.
    apply similar_sms_implies_eq_sm2levels in simp as e; symmetry in e.
    apply (implies_equal_trustedSM _ _ _ _ _ _ e).
    apply sm2at_as_update_state_sm2at_sm2state; auto.
  Qed.

  Lemma update_state_sm_state :
    forall n cn (sm : n_proc_at n cn),
      update_state sm (sm_state sm) = sm.
  Proof.
    destruct sm as [h upd s]; simpl; tcsp.
  Qed.
  Hint Rewrite update_state_sm_state : comp.

  Lemma updateTrustedSM_state_of_trusted :
    forall (t : trustedSM),
      updateTrustedSM t (state_of_trusted t) = t.
  Proof.
    destruct t as [lvl k s sm]; simpl.
    unfold state_of_trusted; simpl.
    f_equal.
    autorewrite with comp; auto.
  Qed.
  Hint Rewrite updateTrustedSM_state_of_trusted : comp.

  Lemma find_trusted_implies_find_name :
    forall n (subs : n_procs n) (t : trustedSM),
      find_trusted subs = Some t
      ->
      exists sm,
        find_name (MkCN (tsm_kind t) (tsm_space t) true) subs = Some sm
        /\ to_trusted sm = Some t.
  Proof.
    induction subs; introv find; simpl in *; tcsp.
    destruct a as [c a].
    destruct c as [k s tr]; simpl in *.
    destruct tr; simpl in *; ginv; simpl in *.

    { destruct (CompNameKindDeq k k); subst; tcsp.
      destruct (CompNameSpaceDeq s s); subst; tcsp.
      pose proof (UIP_refl_CompNameKind _ e) as xx; subst; simpl in *.
      pose proof (UIP_refl_CompNameSpace _ e0) as xx; subst; simpl in *.
      exists a; dands; auto. }

    { destruct (CompNameKindDeq k (tsm_kind t)); subst; tcsp;
        destruct (CompNameSpaceDeq s (tsm_space t)); subst; tcsp;
          destruct (CompNameStateDeq x (tsm_state t)); subst; tcsp. }
  Qed.

  Lemma state_of_trusted_updateTrustedSM :
    forall (tsm : trustedSM) s,
      state_of_trusted (updateTrustedSM tsm s) = s.
  Proof.
    introv.
    destruct tsm; simpl; tcsp.
  Qed.
  Hint Rewrite state_of_trusted_updateTrustedSM : comp.

  Lemma updateTrustedSM_updateTrustedSM :
    forall tsm s1 s2,
      updateTrustedSM (updateTrustedSM tsm s1) s2
      = updateTrustedSM tsm s2.
  Proof.
    destruct tsm; introv; simpl; tcsp.
  Qed.
  Hint Rewrite updateTrustedSM_updateTrustedSM : comp.

  Lemma M_byz_run_ls_on_this_one_event_M_t_preserves_trusted :
    forall {eo : EventOrdering} e {L S} (ls : MLocalSystem L S) (tsm t : trustedSM),
      are_procs_ls ls
      -> find_trusted (ls_subs ls) = Some tsm
      -> M_byz_run_ls_on_this_one_event ls e = Some (M_t t)
      -> t = updateTrustedSM tsm (state_of_trusted t).
  Proof.
    introv aps find run.
    unfold M_byz_run_ls_on_this_one_event in run; simpl in *.
    remember (trigger e) as trig; clear Heqtrig.
    destruct trig; simpl in *;[| |];
      try (complete (apply option_map_Some in run; exrepnd; ginv;
                     rewrite find in run1; ginv; autorewrite with comp; auto)).

    { unfold M_break in run.
      dest_cases w; symmetry in Heqw; repnd; simpl in *.
      apply option_map_Some in run; exrepnd; subst; simpl in *.
      rename_hyp_with @M_nt mnt.
      inversion mnt; subst; simpl in *; clear mnt. }

    { rewrite find in run; simpl in *; ginv.
      dest_cases w; symmetry in Heqw; repnd; simpl in *.
      applydup find_trusted_implies_find_name in find; exrepnd.
      pose proof (is_proc_n_proc_to_trusted_implies_update_some sm tsm i [] w0 w2 w1) as q.
      repeat (autodimp q hyp); eauto 3 with comp;[]; exrepnd; subst; simpl in *.
      autorewrite with comp; auto. }
  Qed.

  Lemma is_proc_n_proc_at_implies_update_some :
    forall (tsm : trustedSM) i subs1 subs2 sop out,
      is_proc_n_proc_at (tsm_sm tsm)
      -> sm_update (tsm_sm tsm) (state_of_trusted tsm) i subs1
         = (subs2, (sop, out))
      -> exists s, sop = Some s.
  Proof.
    introv isp upd.
    unfold state_of_trusted in upd; simpl in upd.
    autorewrite with comp in *.
    unfold is_proc_n_proc_at in isp; exrepnd; simpl in *.
    rewrite isp0 in upd.
    unfold proc2upd in *; simpl in *.
    unfold interp_s_proc, to_M_n_some_state in *; simpl in *.
    unfold bind_pair, bind in *; simpl in *.
    remember (interp_proc (p (sm_state (tsm_sm tsm)) i) subs1) as w; repnd; simpl in *.
    inversion upd; subst; eauto.
  Qed.

  Lemma implies_is_proc_n_proc_at :
    forall n cn (sm : n_proc_at n cn) s,
      is_proc_n_proc_at sm
      -> is_proc_n_proc_at (update_state sm s).
  Proof.
    introv isp.
    unfold is_proc_n_proc_at in *; exrepnd; exists p; introv; simpl; auto.
  Qed.
  Hint Resolve implies_is_proc_n_proc_at : comp.

  Lemma M_byz_run_ls_on_this_one_event_M_t_implies_is_proc :
    forall {eo : EventOrdering} e {L S} (ls : MLocalSystem L S) (t : trustedSM),
      are_procs_ls ls
      -> M_byz_run_ls_on_this_one_event ls e = Some (M_t t)
      -> is_proc_n_proc_at (tsm_sm t).
  Proof.
    introv aps run.
    unfold M_byz_run_ls_on_this_one_event in run; simpl in *.
    remember (trigger e) as trig; clear Heqtrig.
    destruct trig; simpl in *;[| |];
      try (complete (apply option_map_Some in run; exrepnd; ginv;
                     rewrite find in run1; ginv; autorewrite with comp; auto)).

    { unfold M_break in run.
      dest_cases w; symmetry in Heqw; repnd; simpl in *.
      apply option_map_Some in run; exrepnd; subst; simpl in *.
      rename_hyp_with @M_nt mnt.
      inversion mnt; subst; simpl in *; clear mnt. }

    { apply option_map_Some in run; exrepnd; ginv.
      applydup find_trusted_implies_find_name in run1; exrepnd.
      destruct aps as [aps1 aps2]; simpl in *.
      apply are_procs_n_procs_find_name in run0; auto.
      inversion run2; subst; simpl in *; eauto 3 with comp. }

    { apply option_map_Some in run; exrepnd; ginv; simpl in *.
      dest_cases w; symmetry in Heqw; repnd; simpl in *.
      applydup find_trusted_implies_find_name in run1; exrepnd.
      pose proof (is_proc_n_proc_to_trusted_implies_update_some sm a i [] w0 w2 w1) as q.
      repeat (autodimp q hyp); eauto 3 with comp;[]; exrepnd; subst; simpl in *.
      inversion run2; simpl.
      destruct aps as [aps1 aps2]; simpl in *.
      apply are_procs_n_procs_find_name in run0; auto; eauto 3 with comp. }
  Qed.

  Lemma find_trusted_implies_is_proc :
    forall {L S} (ls : LocalSystem L S) (t : trustedSM),
      are_procs_ls ls
      -> find_trusted (ls_subs ls) = Some t
      -> is_proc_n_proc_at (tsm_sm t).
  Proof.
    introv aps run.
    destruct aps as [aps1 aps2]; simpl in *.
    destruct ls as [main subs]; simpl in *.
    applydup find_trusted_implies_find_name in run; exrepnd.
    apply are_procs_n_procs_find_name in run0; auto.
    simpl in *; inversion run1; subst; simpl in *; eauto 3 with comp.
  Qed.
  Hint Resolve find_trusted_implies_is_proc : comp.

  Lemma M_byz_run_ls_before_event_some_M_t_implies :
    forall {eo : EventOrdering} (e : Event)
           {L S} (ls : MLocalSystem L S)
           (t tsm : trustedSM),
      wf_ls ls
      -> are_procs_ls ls
      -> M_byz_run_ls_before_event ls e = Some (M_t t)
      -> find_trusted (ls_subs ls) = Some tsm
      -> t = updateTrustedSM tsm (state_of_trusted t)
         /\ is_proc_n_proc_at (tsm_sm t).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv wf aps run find.
    rewrite M_byz_run_ls_before_event_unroll in run.
    destruct (dec_isFirst e) as [d|d]; ginv;[].
    apply map_option_Some in run; exrepnd.
    symmetry in run0.

    destruct a as [ls'|t']; simpl in *; ginv.

    { clear ind.
      applydup M_byz_run_ls_before_event_M_nt_preserves_subs in run1; auto; repnd;[].
      applydup @M_byz_run_ls_on_this_one_event_M_t_implies_is_proc in run0; eauto 3 with comp;[].
      applydup (similar_subs_preserves_find_trusted L (ls_subs ls) (ls_subs ls') tsm) in run6; auto; exrepnd.
      pose proof (M_byz_run_ls_on_this_one_event_M_t_preserves_trusted
                    (local_pred e) ls' (updateTrustedSM tsm s) t) as q.
      repeat (autodimp q hyp).
      autorewrite with comp in q; auto. }

    { pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo;[].
      pose proof (ind L S ls t' tsm) as ind.
      repeat (autodimp ind hyp);[].
      remember (trigger (local_pred e)) as trig; clear Heqtrig.
      destruct trig; simpl; tcsp;[].
      dest_cases w; symmetry in Heqw; repnd; simpl in *.
      applydup is_proc_n_proc_at_implies_update_some in Heqw; auto;[].
      exrepnd; subst; simpl in *; autorewrite with comp.
      applydup @find_trusted_implies_is_proc in find; auto;[].

      rewrite ind0.
      autorewrite with comp; dands; auto; eauto 3 with comp.
      destruct tsm as [lvl k sp sm]; simpl in *; eauto 3 with comp. }
  Qed.

  Lemma M_byz_compose_step_trusted :
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
      exists (s1 s2 : tsf) (l : list (cio_I (fio cn))),
        M_byz_state_ls_before_event_of_trusted ls e = Some s1
        /\ M_byz_state_ls_on_event_of_trusted ls e = Some s2
        /\ trusted_run_sm_on_inputs s1 sm l = Some s2.
  Proof.
    introv aps wf fs lvl trust.
    unfold M_byz_state_ls_before_event_of_trusted.
    unfold M_byz_state_ls_on_event_of_trusted.

    pose proof (M_byz_compose_step2 e ls sm) as h.
    repeat (autodimp h hyp).
    exrepnd.

    unfold M_byz_state_ls_before_event in *.
    unfold M_byz_state_ls_on_event in *.

    remember (M_byz_run_ls_before_event ls e) as runa; symmetry in Heqruna.
    remember (M_byz_run_ls_on_event ls e) as runb; symmetry in Heqrunb.

    destruct runa; simpl in *; ginv.
    destruct runb; simpl in *; ginv.

    destruct m; simpl in *.

    { apply option_map_Some in h1; exrepnd; subst; simpl in *.
      applydup M_byz_run_ls_before_event_M_nt_preserves_subs in Heqruna; auto; repnd;[].
      dup Heqruna4 as ist.
      apply (similar_subs_preserves_is_trusted_ls cn) in ist; auto.
      applydup is_trusted_implies_find_trusted2 in ist; exrepnd.
      rewrite wf_is_trusted_implies_state_of_subcomponents in h1; auto;[].
      unfold state_of_subcomponents in h1.
      rewrite ist0 in h1; simpl in *; ginv.
      unfold state_of_trusted_in_ls, find_trusted_sub; rewrite ist1; simpl.
      unfold state_of_trusted; simpl.

      destruct m0; simpl in *.

      { apply option_map_Some in h2; exrepnd; subst; simpl in *.
        applydup M_byz_run_ls_on_event_M_nt_preserves_subs in Heqrunb; auto; repnd;[].
        dup Heqrunb4 as ist'.
        apply (similar_subs_preserves_is_trusted_ls cn) in ist'; auto.
        applydup is_trusted_implies_find_trusted2 in ist'; exrepnd.
        rewrite wf_is_trusted_implies_state_of_subcomponents in h2; auto;[].
        unfold state_of_subcomponents in h2.
        rewrite ist'0 in h2; simpl in *; ginv.
        unfold find_trusted_sub; rewrite ist'1; simpl.
        assert (eqn0 = eqn) by (apply UIP_dec; apply CompNameDeq); subst.

        destruct cn as [k s t]; simpl in *; ginv;[].
        inversion eqn; subst; simpl in *;[].
        pose proof (UIP_refl_CompName _ eqn) as xx; subst; simpl in *;[].

        apply map_untrusted_op_Some_M_nt_implies in h0; exrepnd.
        inversion h1 as [xx].
        rewrite xx in *; clear h1.

        autorewrite with comp in *.
        exists (sm2state sm0) (sm2state sm1); simpl.

        pose proof (run_sm_on_byz_inputs_M_nt_implies
                      L (MkCN k s true) l
                      (update_state_m sm (sm2state sm0))
                      t []) as q.
        remember (run_sm_on_byz_inputs (update_state_m sm (sm2state sm0)) l []) as w; symmetry in Heqw; repnd.
        simpl in *; subst; simpl in *.
        unfold is_trusted_comp_name in q; simpl in q.
        pose proof (q w0) as q; repeat (autodimp q hyp);[].
        exrepnd; subst; simpl in *.
        exists k0; simpl in *.
        unfold run_sm_on_inputs_trusted; simpl.
        rewrite q0; simpl; dands; auto;[].
        unfold MkCN in *; rewrite xx; auto. }

      { ginv.
        apply map_untrusted_op_Some_M_t_implies in h0.
        destruct cn as [k s tr]; simpl in *.
        inversion eqn; subst; simpl in *.
        pose proof (UIP_refl_CompName _ eqn) as xx; subst; simpl in *;[].

        autorewrite with comp in *.
        exists (sm2state sm0) (sm_state (tsm_sm t)).

        remember (run_sm_on_byz_inputs (update_state_m sm (sm2state sm0)) l []) as r; symmetry in Heqr; repnd; simpl in *; subst.
        applydup run_sm_on_byz_inputs_M_t_implies in Heqr; exrepnd; autorewrite with comp; eauto 3 with comp;[].

        exists l'.
        unfold run_sm_on_inputs_trusted; simpl.
        rewrite Heqr0; simpl in *; ginv; simpl in *.
        autorewrite with comp; auto. } }

    { ginv.
      apply map_untrusted_op_Some_M_t_implies in h2; subst; simpl in *.
      applydup is_trusted_ls_implies_is_trusted_comp_name in trust.

      exists (state_of_trusted t) (state_of_trusted (run_trustedSM_on_trigger_info_list t l)).

      destruct cn as [k s tr]; simpl in *.
      unfold is_trusted_comp_name in *; simpl in *; subst; simpl in *.

      remember (run_trustedSM_on_trigger_info_list t l) as tsm.

      pose proof (run_trustedSM_on_trigger_info_list_implies_run_sm_on_inputs
                    l t tsm
                    (update_state_m sm (state_of_trusted t))) as xx.
      autorewrite with comp in xx.
      repeat (autodimp xx hyp); eauto 3 with comp.

      { simpl; f_equal.
        unfold is_trusted_ls in trust.
        applydup is_trusted_implies_find_trusted2 in trust; simpl in *.
        exrepnd; ginv.
        pose proof (UIP_refl_CompName _ eqn) as xx; subst; simpl in *.
        unfold find_sub in fs; rewrite trust0 in fs.
        inversion fs; subst; simpl in *; clear fs.

        eapply M_byz_run_ls_before_event_some_M_t_implies in Heqruna; eauto.
        simpl in *; repnd.
        rewrite Heqruna0 at 3; simpl.
        assert (sm2level (update_state_m sm (state_of_trusted t)) = sm2level sm) as ee by (autorewrite with comp; auto).
        apply (implies_equal_trustedSM _ _ _ _ _ _ ee).
        apply sm2at_update_state_m_as_update_state_sm2at. }

      { exrepnd; simpl in *.
        exists l'.
        dands; auto;[].
        unfold run_sm_on_inputs_trusted; simpl.
        unfold MkCN in *; rewrite xx0; simpl.
        clear Heqtsm.
        ginv; unfold state_of_trusted; simpl; autorewrite with comp; auto. } }
  Qed.

  Lemma run_sm_on_inputs_trusted_cons :
    forall n k s
           (sm : n_proc n (MkCN k s true))
           i (l  : list (cio_I (fio (MkCN k s true)))),
      sm2level sm = 0
      -> run_sm_on_inputs_trusted sm (i :: l)
         = run_sm_on_inputs_trusted
             (update_state_op_m sm (fst (snd (sm2update sm (sm2state sm) i []))))
             l.
  Proof.
    introv lvl.
    unfold run_sm_on_inputs_trusted; simpl.
    autorewrite with comp.
    dest_cases w; symmetry in Heqw; repnd; simpl in *.
    erewrite (eq_snd_run_sm_on_inputs_on_diff_subs_if_leaf _ _ _ []); autorewrite with comp; auto.
  Qed.

  Lemma run_sm_on_inputs_trusted_nil :
    forall n k s
           (sm : n_proc n (MkCN k s true)),
      run_sm_on_inputs_trusted sm [] = sm2state sm.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite run_sm_on_inputs_trusted_nil : minbft.

  Lemma M_byz_run_ls_on_event_some_M_t_implies :
    forall {eo : EventOrdering} (e : Event)
           {L S} (ls : MLocalSystem L S)
           (t tsm : trustedSM),
      wf_ls ls
      -> are_procs_ls ls
      -> M_byz_run_ls_on_event ls e = Some (M_t t)
      -> find_trusted (ls_subs ls) = Some tsm
      -> t = updateTrustedSM tsm (state_of_trusted t)
         /\ is_proc_n_proc_at (tsm_sm t).
  Proof.
    introv wf aps run find.
    rewrite M_byz_run_ls_on_event_unroll2 in run.
    apply map_option_Some in run; exrepnd; rev_Some.
    destruct a; simpl in *; ginv.

    { apply M_byz_run_ls_before_event_M_nt_preserves_subs in run1; auto; repnd.
      eapply similar_subs_preserves_find_trusted in find; eauto.
      exrepnd.
      eapply M_byz_run_ls_on_this_one_event_M_t_preserves_trusted in run0; eauto.
      autorewrite with comp in *.
      dands; auto.
      rewrite run0.
      apply find_trusted_implies_is_proc in find0; auto.
      destruct tsm; simpl in *; auto. }

    eapply M_byz_run_ls_before_event_some_M_t_implies in run1; eauto; repnd.
    remember (trigger e) as trig; symmetry in Heqtrig.
    destruct trig; simpl; tcsp;[].
    dest_cases w; repnd; simpl in *.
    symmetry in Heqw.
    applydup is_proc_n_proc_at_implies_update_some in Heqw; auto.
    exrepnd; subst; simpl in *; autorewrite with comp.
    revert run1.
    rewrite run0; autorewrite with comp; dands; auto.
    destruct tsm; simpl in *; auto.
  Qed.

End ComponentSM3.


Hint Resolve similar_subs_preserves_find_sub : comp.
Hint Resolve similar_subs_preserves_is_trusted_ls : comp.
Hint Resolve is_trusted_ls_implies_is_trusted_comp_name : comp.
Hint Resolve implies_is_proc_n_proc_at : comp.
Hint Resolve find_trusted_implies_is_proc : comp.


Hint Rewrite @sm_state_sm2at : comp.
Hint Rewrite @update_state_sm_state : comp.
Hint Rewrite @updateTrustedSM_state_of_trusted : comp.
Hint Rewrite @state_of_trusted_updateTrustedSM : comp.
Hint Rewrite @updateTrustedSM_updateTrustedSM : comp.
Hint Rewrite @run_sm_on_inputs_trusted_nil : minbft.
