Require Export ComponentSM6.


Hint Resolve implies_wf_procs_procs2byz : comp.
Hint Resolve implies_are_procs_n_procs_procs2byz : comp.
Hint Rewrite @procs2byz_procs2byz : comp.
Hint Resolve wf_procs_implies_no_dup : comp.
Hint Resolve wf_procs_implies_ordered : comp.


Section ComponentSM9.

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

  Lemma incr_n_proc_update_state_m :
    forall {n} {cn} (p : n_proc n cn) s,
      incr_n_proc (update_state_m p s)
      = update_state_m (incr_n_proc p) s.
  Proof.
    induction n; introv; simpl; tcsp.
  Qed.

  Lemma trusted_run_sm_on_inputs_incr_n_proc :
    forall {n} cn s (p : n_proc n (pre2trusted cn)) l,
      trusted_run_sm_on_inputs s (incr_n_proc p) l
      = trusted_run_sm_on_inputs s p l.
  Proof.
    introv.
    unfold trusted_run_sm_on_inputs.
    pose proof (snd_run_sm_on_inputs_incr_n_proc_eq l (update_state_m p s) []) as w.
    unfold decr_n_procs in w; simpl in w.
    rewrite incr_n_proc_update_state_m in w.
    simpl in *; rewrite w; clear w; tcsp.
  Qed.
  Hint Rewrite @trusted_run_sm_on_inputs_incr_n_proc : comp.

  Lemma implies_similar_subs_procs2byz :
    forall {n} (l k : n_procs n),
      similar_subs l k
      -> similar_subs (procs2byz l) (procs2byz k).
  Proof.
    introv sim; induction sim; simpl in *; tcsp.
    inversion simp; subst; simpl in *; GC.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
    unfold is_trusted in *; simpl in *; dest_cases w.
  Qed.
  Hint Resolve implies_similar_subs_procs2byz : comp.

  Lemma M_byz_run_ls_on_this_one_event_preserves_subs_byz :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_byz_run_ls_on_this_one_event ls1 e = ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs (procs2byz ls1) (procs2byz ls2)).
  Proof.
    introv wf aps run.
    unfold M_byz_run_ls_on_this_one_event in run; simpl in *.
    unfold M_byz_run_ls_on_one_event in run; simpl in *.
    remember (M_byz_run_ls_on_input ls1 (msg_comp_name S) (time e) (trigger e)) as h; repnd;
      simpl in *; subst; symmetry in Heqh.
    remember (trigger e) as trig.
    destruct trig; simpl in *; tcsp; GC.

    { pose proof (M_byz_run_ls_on_this_one_event_M_nt_preserves_subs e ls1 ls2) as q.
      repeat (autodimp q hyp).
      { unfold isCorrect, trigger_op; allrw <-; simpl; auto. }
      { unfold M_byz_run_ls_on_this_one_event, M_byz_run_ls_on_one_event.
        remember (M_byz_run_ls_on_input ls1 (msg_comp_name S) (time e) (trigger e)) as run; repnd; simpl in *.
        revert dependent run.
        rewrite <- Heqtrig; simpl; introv q.
        rewrite Heqh in q; ginv. }
      { repnd.
        dands; eauto 2 with comp. } }

    { destruct h; tcsp; ginv; dands; autorewrite with comp in *; eauto 3 with comp. }

    { unfold M_run_ls_on_trusted in Heqh.
      pose proof (M_run_ls_on_input_preserves_subs
                    (pre2trusted (it_name i))
                    (time e)
                    (it_input i)
                    (procs2byz ls1)
                    ls2 h) as q.
      repeat (autodimp q hyp); eauto 3 with comp; repnd.
      apply implies_similar_subs_procs2byz in q2; autorewrite with comp in *.
      dands; auto; eauto 3 with comp. }
  Qed.

  Lemma M_byz_run_ls_before_event_preserves_subs_byz :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_byz_run_ls_before_event ls1 e = ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ similar_subs (procs2byz ls1) (procs2byz ls2)).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv wf aps run.
    rewrite M_byz_run_ls_before_event_unroll in run.

    destruct (dec_isFirst e) as [d|d]; ginv; auto;[|].
    { subst; dands; eauto 3 with comp. }

    remember (M_byz_run_ls_before_event ls1 (local_pred e)) as ls'; simpl in *; symmetry in Heqls'.
    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo;[].
    pose proof (ind L S ls1 ls') as ind.
    repeat (autodimp ind hyp); eauto 3 with eo; repnd;[].
    clear Heqls'.

    apply M_byz_run_ls_on_this_one_event_preserves_subs_byz in run; auto.
    repnd; dands; eauto 3 with comp.
  Qed.

  Lemma M_byz_run_ls_on_this_one_event_preserves_subs_byz2 :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_byz_run_ls_on_this_one_event ls1 e = ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ (similar_subs ls1 ls2 \/ similar_subs (procs2byz ls1) ls2)).
  Proof.
    introv wf aps run.
    unfold M_byz_run_ls_on_this_one_event in run; simpl in *.
    unfold M_byz_run_ls_on_one_event in run; simpl in *.
    remember (M_byz_run_ls_on_input ls1 (msg_comp_name S) (time e) (trigger e)) as h; repnd;
      simpl in *; subst; symmetry in Heqh.
    remember (trigger e) as trig.
    destruct trig; simpl in *; tcsp; GC.

    { pose proof (M_byz_run_ls_on_this_one_event_M_nt_preserves_subs e ls1 ls2) as q.
      repeat (autodimp q hyp).
      { unfold isCorrect, trigger_op; allrw <-; simpl; auto. }
      { unfold M_byz_run_ls_on_this_one_event, M_byz_run_ls_on_one_event.
        remember (M_byz_run_ls_on_input ls1 (msg_comp_name S) (time e) (trigger e)) as run; repnd; simpl in *.
        revert dependent run.
        rewrite <- Heqtrig; simpl; introv q.
        rewrite Heqh in q; ginv. }
      { repnd.
        dands; eauto 2 with comp. } }

    { destruct h; tcsp; ginv; dands; autorewrite with comp in *; eauto 3 with comp. }

    { unfold M_run_ls_on_trusted in Heqh.
      pose proof (M_run_ls_on_input_preserves_subs
                    (pre2trusted (it_name i))
                    (time e)
                    (it_input i)
                    (procs2byz ls1)
                    ls2 h) as q.
      repeat (autodimp q hyp); eauto 3 with comp; repnd.
      applydup @implies_similar_subs_procs2byz in q2; autorewrite with comp in *.
      dands; auto; eauto 3 with comp. }
  Qed.

  Lemma M_byz_run_ls_before_event_preserves_subs_byz2 :
    forall {eo : EventOrdering} e {L S} (ls1 ls2 : LocalSystem L S),
      wf_procs ls1
      -> are_procs_n_procs ls1
      -> M_byz_run_ls_before_event ls1 e = ls2
      -> (wf_procs ls2
          /\ are_procs_n_procs ls2
          /\ (similar_subs ls1 ls2 \/ similar_subs (procs2byz ls1) ls2)).
  Proof.
    intros eo e.
    induction e as [e ind] using predHappenedBeforeInd; introv wf aps run.
    rewrite M_byz_run_ls_before_event_unroll in run.

    destruct (dec_isFirst e) as [d|d]; ginv; auto;[|].
    { subst; dands; eauto 3 with comp. }

    remember (M_byz_run_ls_before_event ls1 (local_pred e)) as ls'; simpl in *; symmetry in Heqls'.
    pose proof (ind (local_pred e)) as ind; autodimp ind hyp; eauto 3 with eo;[].
    pose proof (ind L S ls1 ls') as ind.
    repeat (autodimp ind hyp); eauto 3 with eo; repnd;[].
    clear Heqls'.

    apply M_byz_run_ls_on_this_one_event_preserves_subs_byz2 in run; auto.
    repnd; dands; eauto 3 with comp;[].

    repndors; tcsp; eauto 4 with comp.
    apply implies_similar_subs_procs2byz in ind; autorewrite with comp in *; eauto 3 with comp.
  Qed.

  Definition M_break_mon {n} {S}
             (sm   : M_n n S)
             (subs : n_procs n) : n_procs n :=
    M_break sm subs (fun subs' _ => subs').

  Definition M_break_out {n} {S}
             (sm   : M_n n S)
             (subs : n_procs n) : S :=
    M_break sm subs (fun _ out => out).

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

  Lemma is_M_break_mon_preserves_subs :
    forall {n} {cn} (p : n_proc_at n cn) (l k : n_procs (S n)) t i,
      wf_procs l
      -> is_proc_n_proc_at p
      -> are_procs_n_procs l
      -> is_M_break_mon (lift_M_1 (app_n_proc_at p t i)) l k
      -> similar_subs l k.
  Proof.
    introv wf isp aps h.
    unfold is_M_break_mon, M_break_mon, M_break in h; simpl in h.

    pose proof (app_m_proc_some2 (at2sm p) t i l) as q.
    simpl in q; repeat (autodimp q hyp); eauto 3 with comp.
    rewrite q in h; clear q.

    remember (sm_update p (sm_state p) t i (select_n_procs n l)) as z;
      symmetry in Heqz; repnd; simpl in *; subst; simpl in *.
    fold (M_StateMachine n) in *; fold (n_proc n) in *; rewrite Heqz.

    pose proof (are_procs_implies_preserves_sub p (sm_state p) t i (select_n_procs n l)) as h.
    repeat (autodimp h hyp); eauto 3 with comp;[].
    unfold M_break in h.
    rewrite Heqz in h; repnd.

    applydup similar_subs_preserves_get_names in h0 as eqn; rewrite eqn.

    rewrite raise_to_n_procs_as_incr_n_procs.
    rewrite <- decr_n_procs_as_select_n_procs in h0.
    eapply similar_subs_trans;
      [|apply implies_similar_subs_app;
        [apply implies_similar_subs_remove_subs;[apply similar_subs_refl|eauto]
        |apply implies_similar_subs_incr_n_procs;eauto]
      ].
    rewrite @remove_subs_decr_n_procs_as_keep_highest_subs; eauto 3 with comp.
    pose proof (incr_n_procs_decr_n_procs_as_rm_highest l) as rm; simpl in *; rewrite rm; clear rm.
    rewrite <- split_as_rm_highest_keep_highest; eauto 3 with comp.
  Qed.

  Lemma implies_is_proc_n_proc_at_0 :
    forall (l : n_procs 1) {cn} (p : n_proc_at 0 cn),
      are_procs_n_procs l
      -> find_name cn l = Some (sm_or_at p)
      -> is_proc_n_proc_at (sm2p0 p).
  Proof.
    introv aps fn.
    apply @are_procs_n_procs_find_name in fn; auto.
  Qed.
  Hint Resolve implies_is_proc_n_proc_at_0 : comp.

  Lemma is_M_break_out_preserves_subs :
    forall {n} {cn} (p : n_proc_at n cn) (l : n_procs (S n)) t i a b,
      is_proc_n_proc_at p
      -> is_M_break_out (lift_M_1 (app_n_proc_at p t i)) l (a,b)
      -> exists q, a = hsome q /\ similar_sms (at2sm p) q.
  Proof.
    introv isp h.
    unfold is_M_break_out, M_break_out, M_break in h; simpl in h.

    unfold lift_M_1, M_on_decr, app_n_proc_at, bind_pair, bind in h; simpl in h.
    remember (sm_update p (sm_state p) t i (decr_n_procs l)) as z; symmetry in Heqz; repnd; simpl in *; ginv.

    unfold is_proc_n_proc_at in isp; exrepnd.
    rewrite isp0 in Heqz; simpl in *.
    unfold proc2upd in Heqz.
    rewrite interp_s_proc_as in Heqz.
    unfold bind_pair, bind in Heqz; simpl in *.

    remember (interp_proc (p0 (sm_state p) t i) (decr_n_procs l)) as w; symmetry in Heqw; repnd; simpl in *.
    rewrite Heqw in Heqz; simpl in *; ginv.
    inversion Heqz; subst; simpl in *; tcsp.
    eexists; dands; eauto; simpl; tcsp.
  Qed.

  Lemma in_replace_name_implies :
    forall {n} {cn} (p : n_proc n cn) subs q,
      In q (replace_name p subs)
      -> q = MkPProc cn p \/ In q subs.
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a; simpl in *; tcsp; dest_cases w; simpl in *; repndors; ginv; tcsp.
    apply IHsubs in i; repndors; subst; tcsp.
  Qed.

  Lemma implies_are_procs_n_procs_replace_name :
    forall {n} {cn} (subs : n_procs n) (p : n_proc n cn),
      are_procs_n_procs subs
      -> is_proc_n_proc p
      -> are_procs_n_procs (replace_name p subs).
  Proof.
    introv aps ips i.
    apply in_replace_name_implies in i; repndors; subst; tcsp.
  Qed.
  Hint Resolve implies_are_procs_n_procs_replace_name : comp.

  Lemma implies_similar_sms_sm_or_at :
    forall {cn} (p q : n_proc_at 0 cn),
      similar_sms_at p q
      -> similar_sms (at2sm p) (at2sm q).
  Proof.
    tcsp.
  Qed.

  Lemma similar_sms_at2sm_sm2p0 :
    forall {cn} (a : n_proc_at 0 cn) q,
      similar_sms (at2sm (sm2p0 a)) q
      -> exists b, q = at2sm b /\ similar_sms_at a b.
  Proof.
    introv h; simpl in *; destruct q; simpl in *; tcsp.
    exists a0; dands; auto.
  Qed.

  Definition has_sim_comp {cn} {n} (p : n_proc n cn) (ls : n_procs n) :=
    exists comp, find_name cn ls = Some comp /\ similar_sms comp p.

  Lemma similar_subs_replace_name_right :
    forall {n} {cn} (p : n_proc n cn) (subs1 subs2 : n_procs n),
      has_sim_comp p subs2
      -> similar_subs subs1 subs2
      -> similar_subs subs1 (replace_name p subs2).
  Proof.
    induction subs1; introv hc sim; destruct subs2; simpl in *; tcsp;
      inversion sim; subst; tcsp; clear sim.
    destruct n0 as [cn' p']; simpl in *; dest_cases w; subst; tcsp.

    { constructor; auto.
      unfold has_sim_comp in *; exrepnd; simpl in *; dest_cases w.
      rewrite (UIP_refl_CompName _ w) in hc1; simpl in *; ginv.
      eapply similar_procs_trans;eauto. }

    { constructor; auto.
      apply IHsubs1; auto.
      unfold has_sim_comp in *; exrepnd; simpl in *; dest_cases w; eauto. }
  Qed.

  Lemma similar_subs_preserves_has_sim_comp :
    forall {n} {cn} (p : n_proc n cn) (l k : n_procs n),
      similar_subs l k
      -> has_sim_comp p l
      -> has_sim_comp p k.
  Proof.
    introv sim h.
    unfold has_sim_comp in *; exrepnd.
    eapply ComponentSM.similar_subs_preserves_find_name in h1; eauto; exrepnd.
    exists s'; dands; eauto 3 with comp.
  Qed.
  Hint Resolve similar_subs_preserves_has_sim_comp : comp.

  Lemma similar_sms_at_preserves_has_sim_comp :
    forall {n} {cn} (a b : n_proc_at n cn) subs,
      similar_sms_at a b
      -> has_sim_comp (at2sm a) subs
      -> has_sim_comp (at2sm b) subs.
  Proof.
    introv sim h; unfold has_sim_comp in *; exrepnd.
    destruct comp; simpl in *; tcsp.
    eexists; dands; eauto; simpl; eauto 3 with comp.
  Qed.
  Hint Resolve similar_sms_at_preserves_has_sim_comp : comp.

  Lemma find_name_implies_has_sim_comp_at2sm :
    forall {cn} (a : n_proc_at 0 cn) (l : n_procs 1),
      find_name cn l = Some (sm_or_at a)
      -> has_sim_comp (at2sm a) l.
  Proof.
    introv h; eexists; dands; eauto; eauto 3 with comp.
  Qed.
  Hint Resolve find_name_implies_has_sim_comp_at2sm : comp.

  Lemma find_name_replace_name_diff :
    forall {cn1} {cn2} {n} (p : n_proc n cn2) l,
      cn1 <> cn2
      -> find_name cn1 (replace_name p l) = find_name cn1 l.
  Proof.
    induction l; introv d; simpl in *; tcsp.
    destruct a; simpl in *; tcsp; repeat (dest_cases w; subst; simpl in *; tcsp).
  Qed.
  Hint Resolve find_name_replace_name_diff : comp.

  Lemma implies_has_name_replace_name_same :
    forall {cn} {n} (p : n_proc n cn) l x,
      find_name cn l = Some x
      -> find_name cn (replace_name p l) = Some p.
  Proof.
    induction l; introv h; simpl in *; tcsp.
    destruct a; simpl in *; repeat (dest_cases w; subst; simpl in *; tcsp).
    { rewrite (UIP_refl_CompName _ w); tcsp. }
    eapply IHl; eauto.
  Qed.
  Hint Resolve implies_has_name_replace_name_same : comp.

  Lemma implies_has_simp_comp_replace_name_same :
    forall {cn} {n} (a b : n_proc n cn) l,
      has_sim_comp a l
      -> has_sim_comp b l
      -> has_sim_comp a (replace_name b l).
  Proof.
    introv h q.
    unfold has_sim_comp in *; exrepnd.
    rewrite h1 in q1; ginv.
    exists b; dands; eauto 3 with comp.
  Qed.
  Hint Resolve implies_has_simp_comp_replace_name_same : comp.

  Lemma implies_has_name_replace_name_diff :
    forall cn1 {cn2} {n} (p : n_proc n cn2) l x,
      cn1 <> cn2
      -> find_name cn1 l = Some x
      -> find_name cn1 (replace_name p l) = Some x.
  Proof.
    induction l; introv d h; simpl in *; tcsp.
    destruct a; simpl in *; repeat (dest_cases w; subst; simpl in *; tcsp).
    rewrite (UIP_refl_CompName _ w); tcsp.
  Qed.
  Hint Resolve implies_has_name_replace_name_diff : comp.

  Lemma implies_has_simp_comp_replace_name_diff :
    forall {cn1} {cn2} {n} (a : n_proc n cn1) (b : n_proc n cn2) l,
      cn1 <> cn2
      -> has_sim_comp a l
      -> has_sim_comp a (replace_name b l).
  Proof.
    introv h q.
    unfold has_sim_comp in *; exrepnd.
    exists comp; dands; eauto 3 with comp.
  Qed.
  Hint Resolve implies_has_simp_comp_replace_name_diff : comp.

  Lemma find_name_replace_name_same :
    forall {n} {cn} (p : n_proc n cn) l,
      has_comp cn l
      -> find_name cn (replace_name p l) = Some p.
  Proof.
    induction l; introv h; simpl in *; tcsp; unfold has_comp in *; exrepnd; simpl in *; tcsp.
    destruct a; simpl in *; tcsp; repeat (dest_cases w; subst; simpl in *; tcsp).
    { rewrite (UIP_refl_CompName _ w); tcsp. }
    apply IHl; eauto.
  Qed.
  Hint Resolve find_name_replace_name_same : comp.

  Lemma implies_has_comp_replace_name :
    forall cn' {n} {cn} (p : n_proc n cn) l,
      has_comp cn' l
      -> has_comp cn' (replace_name p l).
  Proof.
    induction l; introv h; unfold has_comp in *; exrepnd; simpl in *; tcsp.
    destruct a; simpl in *; repeat (dest_cases w; subst; simpl in *; tcsp; ginv); eauto.
  Qed.
  Hint Resolve implies_has_comp_replace_name : comp.

  Lemma at2sm_eq_sm_or_at_implies :
    forall {cn} (a b : n_proc_at 0 cn),
      at2sm a = sm_or_at b -> a = b.
  Proof.
    introv h; inversion h; auto.
  Qed.

  Lemma replace_name_twice :
    forall {n} {cn} (p q : n_proc n cn) l,
      replace_name p (replace_name q l) = replace_name p l.
  Proof.
    induction l; introv; simpl in *; tcsp.
    destruct a; simpl in *; tcsp; repeat (dest_cases w; subst; simpl in *; tcsp).
  Qed.
  Hint Rewrite @replace_name_twice : comp.

  Lemma lower_head_replace_name_twice :
    forall n {m} {cn} (p q : n_proc m cn) l,
      lower_head n (replace_name p (replace_name q l))
      = lower_head n (replace_name p l).
  Proof.
    introv; autorewrite with comp; auto.
  Qed.
  Hint Rewrite lower_head_replace_name_twice : comp.

  Lemma implies_wf_procs_replace_name_twice :
    forall {n} {cn} (p q : n_proc n cn) l,
      wf_procs (replace_name p l)
      -> wf_procs (replace_name p (replace_name q l)).
  Proof.
    introv; autorewrite with comp; auto.
  Qed.
  Hint Resolve implies_wf_procs_replace_name_twice : comp.

End ComponentSM9.


Hint Rewrite @replace_name_twice : comp.
Hint Rewrite @trusted_run_sm_on_inputs_incr_n_proc : comp.
Hint Rewrite @lower_head_replace_name_twice : comp.


Hint Resolve implies_similar_subs_procs2byz : comp.
Hint Resolve implies_is_proc_n_proc_at_0 : comp.
Hint Resolve implies_are_procs_n_procs_replace_name : comp.
Hint Resolve similar_subs_preserves_has_sim_comp : comp.
Hint Resolve similar_sms_at_preserves_has_sim_comp : comp.
Hint Resolve find_name_implies_has_sim_comp_at2sm : comp.
Hint Resolve find_name_replace_name_diff : comp.
Hint Resolve implies_has_name_replace_name_same : comp.
Hint Resolve implies_has_simp_comp_replace_name_same : comp.
Hint Resolve implies_has_name_replace_name_diff : comp.
Hint Resolve implies_has_simp_comp_replace_name_diff : comp.
Hint Resolve find_name_replace_name_same : comp.
Hint Resolve implies_has_comp_replace_name : comp.
Hint Resolve implies_wf_procs_replace_name_twice : comp.
