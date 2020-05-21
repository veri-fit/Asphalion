(* TRINC instance *)

Require Export ComponentSM3.
Require Export TrIncprops2.
Require Export TrIncsm_mon.


Section TrIncass_mon.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma ASSUMPTION_monotonicity_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_monotonicity.
  Proof.
    repeat introv; apply assume_eo_ASSUMPTION_monotonicity_iff_monotonicity.
    clear e.
    introv.
    unfold no_trusted_generation, generates_trusted.
    unfold id_before, id_after; simpl.
    unfold trusted_state_before, trusted_state_after; simpl.
    unfold M_byz_state_sys_on_event.
    unfold M_byz_state_sys_before_event.

    assert (ex_node_e e) as exe by (destruct e; auto).

    unfold ex_node_e in exe; simpl in *; exrepnd.
    apply node_cond2 in exe0.
    unfold MinBFTsys; rewrite <- exe0.

    pose proof (M_byz_compose_step_trusted e (MinBFTlocalSys n) (incr_n_proc (USIG_comp n))) as h.
    repeat (autodimp h hyp); eauto 3 with comp minbft;[].
    exrepnd; simpl in *.

    unfold TCN, pre2trusted in *; simpl in *.
    unfold preUSIGname in *; simpl in *.
    rewrite h1, h2.

    pose proof (trusted_run_sm_on_inputs_incr_n_proc preUSIGname s1 (USIG_comp n) l) as z; simpl in z.
    repeat (unfold TCN, USIGname, preUSIGname, MkCN, pre2trusted in *; simpl in *); rewrite z in h0; clear z.

    (* TODO: use something else? *)
    assert (trinc_counters s1 = trinc_counters s2
            \/
            lts (trinc_counters s1) (trinc_counters s2)) as h.
    { eapply USIG_sm_mon; eauto; try congruence. }
    repndors; exrepnd.

    { left; exists (trinc_counters s1); dands; eauto. }

    { right; exists (trinc_counters s1) (trinc_counters s2); dands; eauto; rewrite interp_towns; auto. }
  Qed.
  Hint Resolve ASSUMPTION_monotonicity_true : minbft.

End TrIncass_mon.


Hint Resolve ASSUMPTION_monotonicity_true : minbft.
