Require Export ComponentSM3.
Require Export MinBFTprops2.


Section MinBFTass_mon.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.



  Lemma USIG_sm_mon :
    forall {eo : EventOrdering} (e : Event) n l s1 s2,
      loc e = MinBFT_replica n
      -> usig_id s1 = n
      -> run_sm_on_inputs_trusted (USIG_sm_new s1) l = s2
      -> usig_counter s1 = usig_counter s2
         \/
         usig_counter s1 < usig_counter s2.
  Proof.
    induction l; introv eqloc eqid run; simpl in *; tcsp.

    { autorewrite with minbft in *; simpl in *; subst; tcsp. }

    pose proof (run_sm_on_inputs_trusted_cons
                  _ _ _ (USIG_sm_new s1) a l) as w.
    simpl in *; rewrite w in run; auto; clear w;[].

    unfold USIG_update in run; destruct a; repnd; simpl in *;
      [|apply IHl in run; auto];[].

    right.
    applydup IHl in run; simpl; auto;[].
    simpl in *.
    repndors; exrepnd; try omega.
  Qed.

  Lemma ASSUMPTION_monotonicity_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_monotonicity.
  Proof.
    repeat introv; apply assume_eo_ASSUMPTION_monotonicity_iff_monotonicity.
    clear e.
    introv.
    unfold no_trusted_generation, generates_trusted.
    unfold id_before, id_after; simpl.
    unfold trusted_state_before, trusted_state_after; simpl.
    unfold M_byz_state_sys_on_event_of_trusted.
    unfold M_byz_state_sys_before_event_of_trusted.

    assert (ex_node_e e) as exe by (destruct e; auto).

    unfold ex_node_e in exe; simpl in *; exrepnd.
    apply node_cond2 in exe0.
    unfold MinBFTsys; rewrite <- exe0.

    pose proof (M_byz_compose_step_trusted e (MinBFTlocalSys n) (USIG_comp n)) as h.
    repeat (autodimp h hyp); eauto 3 with comp minbft;[].
    exrepnd.
    rewrite h1, h2.

    (* TODO: use something else? *)
    applydup preserves_usig_id in h2; auto.
    rewrite trusted_run_sm_on_inputs_usig in h0; inversion h0 as [run]; clear h0.
    rewrite run.
    pose proof (run_sm_on_inputs_trusted_usig_preserves_id l s1) as eqid.
    rewrite run in eqid.

    assert (usig_counter s1 = usig_counter s2
            \/
            usig_counter s1 < usig_counter s2) as h.
    { eapply USIG_sm_mon; eauto; try congruence. }
    repndors; exrepnd;
      [left; exists (usig_counter s1); dands; eauto
      |right; exists (usig_counter s1) (usig_counter s2); dands; eauto; rewrite interp_towns; auto].
  Qed.
  Hint Resolve ASSUMPTION_monotonicity_true : minbft.

End MinBFTass_mon.


Hint Resolve ASSUMPTION_monotonicity_true : minbft.
