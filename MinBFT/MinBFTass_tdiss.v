Require Export CalculusSM_derived2.
Require Export MinBFTprops2.
Require Export MinBFTtacts2.


Section MinBFTass_tdiss.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma ASSUMPTION_diss_own_gen_for_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_diss_own_gen_for.
  Proof.
    introv diss; simpl in *; exrepnd.
    exists (MinBFT_data2ui c); simpl.
    unfold disseminate_data in *; simpl in *.
    unfold data_is_owned_by in *.
    unfold M_byz_output_sys_on_event in *; simpl in *.
    rewrite M_byz_output_ls_on_event_as_run in diss0.
    rewrite M_byz_output_ls_on_event_as_run.
    rewrite diss2 in *; simpl in *.

    pose proof (ex_M_byz_run_ls_before_event_MinBFTlocalSys e c0) as run.
    repndors; exrepnd; rewrite run0 in *; simpl in *.

    { remember (trigger e) as trig; symmetry in Heqtrig.
      destruct trig; simpl in *; ginv; tcsp;[].
      unfold state_of_trusted in *; simpl in *.
      unfold USIG_update in *; destruct i; simpl in *;
        repeat (simpl in *; autorewrite with minbft in *; smash_minbft2).

      1:{ inversion Heqx; clear Heqx; subst; simpl in *.
          repndors; tcsp; subst; simpl in *; tcsp.
          smash_minbft1.
          dands; tcsp; eauto.
          unfold generated_for; simpl.


}
  Qed.

End MinBFTass_tdiss.

Hint Resolve ASSUMPTION_diss_own_gen_for_true : minbft.
