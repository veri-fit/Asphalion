Require Export ComponentSM3.
Require Export MicroBFTprops2.


Section MicroBFTass_mon.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.



  Lemma USIG_sm_mon :
    forall n l s1 s2,
      trusted_run_sm_on_inputs s1 (USIG_comp n) l = s2
      -> usig_counter s1 = usig_counter s2
         \/
         usig_counter s1 < usig_counter s2.
  Proof.
    unfold trusted_run_sm_on_inputs.
    induction l; introv run; simpl in *; tcsp; subst; tcsp;[].
    destruct a; repnd; simpl in *; tcsp;[].
    unfold update_state in *; simpl in *.
    autorewrite with comp in *.
    match goal with
    | [ |- _ \/ usig_counter ?a < usig_counter ?b ] =>
      pose proof (IHl (increment_USIG s1) b) as IHl
    end; repeat (autodimp IHl hyp); simpl in *; repndors; tcsp; try omega.
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
    unfold M_byz_state_sys_on_event.
    unfold M_byz_state_sys_before_event.

    assert (ex_node_e e) as exe by (destruct e; auto).

    unfold ex_node_e in exe; simpl in *; exrepnd.
    apply node_cond2 in exe0.
    unfold MicroBFTsys; rewrite <- exe0.

    pose proof (M_byz_compose_step_trusted e (MicroBFTlocalSys n) (incr_n_proc (USIG_comp n))) as h.
    repeat (autodimp h hyp); eauto 3 with comp microbft;[].
    exrepnd; simpl in *; autorewrite with microbft in *.
    pose proof (trusted_run_sm_on_inputs_incr_n_proc preUSIGname s1 (USIG_comp n) l) as z; simpl in z.
    repeat (unfold TCN, USIGname, preUSIGname, MkCN, pre2trusted in *; simpl in *); rewrite z in h0; clear z.
    unfold node2name; simpl; rewrite h1, h2.

    (* TODO: use something else? *)
    assert (usig_counter s1 = usig_counter s2
            \/
            usig_counter s1 < usig_counter s2) as h.
    { eapply USIG_sm_mon; eauto; try congruence. }
    repndors; exrepnd;
      [left; exists (usig_counter s1); dands; eauto
      |right; exists (usig_counter s1) (usig_counter s2); dands; eauto; rewrite interp_towns; auto].
  Qed.
  Hint Resolve ASSUMPTION_monotonicity_true : microbft.

End MicroBFTass_mon.


Hint Resolve ASSUMPTION_monotonicity_true : microbft.
