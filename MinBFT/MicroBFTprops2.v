Require Export MicroBFTprops1.


Section MicroBFTprops2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Definition MkMicroBFTtrustedSM (u : USIG_state) : trustedSM :=
    MktrustedSM
      _ _ _
      (build_mp_sm USIG_update u).

  Lemma ex_M_byz_run_ls_on_event_MicroBFTlocalSys :
    forall {eo : EventOrdering} (e : Event) n,
      (exists u, M_byz_run_ls_on_event (MicroBFTlocalSys n) e = Some (M_t (MkMicroBFTtrustedSM u)))
      \/ (exists s u l, M_byz_run_ls_on_event (MicroBFTlocalSys n) e = Some (M_nt (MicroBFTlocalSys_new n s u l))).
  Proof.
    introv.
    remember (M_byz_run_ls_on_event (MicroBFTlocalSys n) e) as run; symmetry in Heqrun.

    pose proof (M_byz_compose_step2 e (MicroBFTlocalSys n) (USIG_comp n)) as q.
    repeat (autodimp q hyp); eauto 3 with microbft comp;[].
    exrepnd.
    clear l q1 q0.
    unfold M_byz_state_ls_on_event in *.
    rewrite Heqrun in q2; simpl in *.
    apply map_option_Some in q2; exrepnd; subst; simpl in *.
    symmetry in q0.
    rewrite q1.

    destruct a; simpl in *; ginv.

    { right.
      apply option_map_Some in q0; exrepnd; subst; simpl in *.
      apply M_byz_run_ls_on_event_M_run_ls_on_event in q1.
      apply M_run_ls_on_event_ls_is_microbft in q1.
      exrepnd; subst.
      eexists; eexists; eexists; reflexivity. }

    { left.
      eapply M_byz_run_ls_on_event_some_M_t_implies in q1; simpl; eauto; eauto 3 with microbft.
      simpl in *; repnd.
      rewrite q0.
      exists (state_of_trusted t); auto. }
  Qed.

  (* FIX this one if need
  Lemma ex_M_byz_state_sys_on_event_of_trusted_MicroBFT :
    forall {eo : EventOrdering} (e : Event),
      ex_node_e e
      ->
      exists (u : USIG_state),
        M_byz_state_sys_on_event_of_trusted MicroBFTsys e = Some u.
  Proof.
    introv exe.
    unfold M_byz_state_sys_on_event_of_trusted; simpl.
    dup exe as exeb.
    unfold ex_node_e in exe; exrepnd; simpl in *.
    assert ((loc e = MicroBFT_backup1) \/ (loc e = MicroBFT_backup2) \/ (loc e = MicroBFT_primary)) as eqloc by
          (destruct (loc e); simpl in *; subst;  ginv; tcsp;
           try (complete (inversion exe0; allrw; reflexivity))).

    destruct eqloc as [eqloc| [eqloc | eqloc]].
    {
      rewrite eqloc in *; simpl in *.
      inversion exe0. rewrite H0 in *.
      unfold M_byz_state_ls_on_event_oMinf_trusted; simpl.

      pose proof (ex_M_byz_run_ls_on_event_MicroBFTlocalSys e n) as q.
      repndors; exrepnd.
      Focus 2.
      {
        rewrite <- H0 in *.
        rewrite q0; simpl; eauto.
      unfold state_of_trusted_in_ls; simpl; eauto.

Admitted.
*)


  Lemma ex_M_byz_run_ls_before_event_MicroBFTlocalSys :
    forall {eo : EventOrdering} (e : Event) n,
      (exists (u : USIG_state),
          M_byz_run_ls_before_event (MicroBFTlocalSys n) e = Some (M_t (MkMicroBFTtrustedSM u)))
      \/
      (exists s u l,
          M_byz_run_ls_before_event (MicroBFTlocalSys n) e = Some (M_nt (MicroBFTlocalSys_new n s u l))).
  Proof.
    introv.
    rewrite M_byz_run_ls_before_event_unroll_on.
    destruct (dec_isFirst e) as [d|d].

    { right.
      rewrite MicroBFTlocalSys_as_new.
      eexists; eexists; eexists; eauto. }

    apply ex_M_byz_run_ls_on_event_MicroBFTlocalSys.
  Qed.

  Lemma MicroBFT_M_byz_run_ls_on_event_unroll_sp :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : MicroBFT_node),
      (exists s u l,
          M_byz_run_ls_on_event (MicroBFTlocalSys r) e
          = M_byz_run_ls_on_this_one_event (MicroBFTlocalSys_new r s u l) e
          /\ M_byz_run_ls_before_event (MicroBFTlocalSys r) e
             = Some (M_nt ((MicroBFTlocalSys_new r s u l))))
      \/
      (exists u,
          M_byz_run_ls_on_event (MicroBFTlocalSys r) e
          = Some (M_t (fst (run_trustedSM_on_trigger_info (MkMicroBFTtrustedSM u) (trigger e))))
          /\ M_byz_run_ls_before_event (MicroBFTlocalSys r) e
             = Some (M_t (MkMicroBFTtrustedSM u))).
  Proof.
    introv.
    rewrite M_byz_run_ls_on_event_unroll.
    destruct (dec_isFirst e) as [d|d]; simpl.

    { left.
      rewrite MicroBFTlocalSys_as_new.
      eexists; eexists; eexists; dands; eauto.
      rewrite M_byz_run_ls_before_event_unroll_on.
      destruct (dec_isFirst e); tcsp. }

    pose proof (ex_M_byz_run_ls_before_event_MicroBFTlocalSys e r) as w.
    repndors; exrepnd; allrw; simpl.

    { right; eexists; eauto. }

    left.
    eexists; eexists; eexists; eauto.
  Qed.


  Lemma USIG_preserves_id :
    forall {eo : EventOrdering} (e : Event) n l s1 s2,
      loc e = MicroBFTheader.node2name n
      -> usig_id s1 = n
      -> run_sm_on_inputs_trusted (USIG_sm_new s1) l = s2
      -> usig_id s2 = n.
  Proof.
    induction l; introv eqloc eqid run; simpl in *; tcsp.

    { autorewrite with microbft in *; simpl in *; subst; tcsp. }

    pose proof (run_sm_on_inputs_trusted_cons
                  _ _ _ (USIG_sm_new s1) a l) as w.
    simpl in *; rewrite w in run; auto; clear w;[].

    unfold USIG_update in run; destruct a; repnd; simpl in *;
      [|apply IHl in run; auto];[].
    apply IHl in run; auto.
  Qed.


  Lemma preserves_usig_id :
    forall {eo : EventOrdering} (e : Event) n u,
      loc e = MicroBFTheader.node2name n
      -> M_byz_state_ls_on_event_of_trusted (MicroBFTlocalSys n) e = Some u
      -> usig_id u = n.
  Proof.
    intros eo; induction e as [e ind] using predHappenedBeforeInd;[]; introv eqloc eqst.

    pose proof (M_byz_compose_step_trusted e (MicroBFTlocalSys n) (USIG_comp n)) as h.
    repeat (autodimp h hyp); eauto 3 with comp microbft;[].
    exrepnd.
    rewrite eqst in h2; ginv; simpl.

    pose proof (USIG_preserves_id
                  e n l s1
                  (run_sm_on_inputs_trusted (USIG_sm_new s1) l)) as q.
    repeat (autodimp q hyp).

    rewrite unroll_M_byz_state_ls_before_event_of_trusted in h1.
    destruct (dec_isFirst e) as [d|d].

    { apply option_map_Some in h1; exrepnd; subst; simpl in *.
      unfold find_trusted_sub in h1; simpl in h1; ginv. }

    apply ind in h1; autorewrite with eo; eauto 2 with eo.
  Qed.


  Lemma preserves_usig_id2 :
    forall {eo : EventOrdering} (e : Event) n ls u,
      loc e = MicroBFTheader.node2name n
      -> M_run_ls_on_event (MicroBFTlocalSys n) e = Some ls
      -> state_of_component USIGname ls = Some u
      -> usig_id u = n.
  Proof.
    introv eqloc run eqst.
    apply (preserves_usig_id e n u); auto.
    unfold M_byz_state_ls_on_event_of_trusted; simpl.
    applydup @M_run_ls_on_event_M_byz_run_ls_on_event in run as z; rewrite z; simpl.
    apply M_run_ls_on_event_ls_is_microbft in run; exrepnd; subst; simpl in *; tcsp.
  Qed.


(* FIX if needed
  Lemma implies_learns_prepare2ui :
    forall {eo : EventOrdering} (e : Event) r n s u l,
      loc e = MicroBFTheader.node2name n
      -> trigger_op e = Some (MicroBFT_request r)
      -> M_run_ls_before_event (MicroBFTlocalSys n) e = Some (MicroBFTlocalSys_new n s u l)
      -> verify_UI (request_n r) (request_ui r) u = true
      -> learns_data e (microbft_data_ui (request_ui r)).
  Proof.
    introv eqloc eqtrig runBef verif.
    exists n (request2auth_data r).
    simpl; allrw; simpl; dands; eauto 3 with microbft;[].
    unfold MicroBFT_ca_verify.
    rewrite request2auth_data_eq.
    unfold M_byz_state_sys_before_event_of_trusted; simpl.
    allrw; simpl.
    unfold M_byz_state_ls_before_event_of_trusted.
    applydup @M_run_ls_before_event_M_byz_run_ls_before_event in runBef as byzRunBef.
    allrw; simpl.
    unfold state_of_trusted; simpl.
    autorewrite with microbft; smash_microbft.
    admit.

  Abort.
  Hint Resolve implies_learns_prepare2ui : microbft.
 *)

End MicroBFTprops2.


(*Hint Resolve implies_learns_prepare2ui : microbft.
Hint Resolve implies_learns_commit2ui_i : microbft.
Hint Resolve implies_learns_commit2ui_j : microbft. *)
