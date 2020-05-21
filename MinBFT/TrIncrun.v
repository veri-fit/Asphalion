(* TRINC instance *)

Require Export TrIncprops1.
Require Export ComponentSM10.


Section TrIncrun.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma M_byz_run_ls_before_event_ls_is_minbft :
    forall {eo : EventOrdering}
           (e  : Event)
           (r  : Rep)
           (ls : MinBFTls),
      M_byz_run_ls_before_event (MinBFTlocalSys r) e = ls
      ->
      (
        (exists (s : MAIN_state) (u : TRINC_state) (l : LOG_state),
            ls = MinBFTlocalSys_new r s u l)
        \/
        (exists (u : TRINC_state),
            ls = [MkPProc USIGname (incr_n_proc (build_m_sm USIG_update u))])
      ).
  Proof.
    introv run.
    apply M_byz_run_ls_before_event_preserves_subs_byz2 in run; eauto 3 with minbft comp;[].
    repnd; autorewrite with minbft in *.
    repndors.

    { apply similar_subs_MinBFTlocalSys_implies in run; exrepnd; subst; eauto. }

    { inversion run; subst; clear run.
      inversion sims; subst; clear sims.
      applydup @similar_procs_implies_same_name in simp; simpl in *.
      destruct p2; simpl in *; subst; simpl in *.
      apply @similar_procs_implies_same_proc in simp.
      destruct pp_proc; simpl in *; tcsp;[].
      destruct b; simpl in *; subst; simpl in *; tcsp;[].
      unfold similar_sms_at in *; repnd; simpl in *; subst; tcsp.
      destruct a; simpl in *; subst; tcsp.
      right.
      exists sm_state; auto. }
  Qed.

  Lemma rw_M_run_ls_on_trusted_USIGlocalSys :
    forall (s : TRINC_state) (i : ITrusted),
      M_run_ls_on_trusted (USIGlocalSys s) i
      = match i with
        | MkITrusted pre j =>
          match PreCompNameDeq pre preUSIGname with
          | left x => M_run_ls_on_input
                        (USIGlocalSys s)
                        USIGname
                        (eq_rect _ (fun pcn => iot_input (iot_fun pcn)) j _ x)
          | right _ => (USIGlocalSys s, None)
          end
        end.
  Proof.
    introv.
    unfold M_run_ls_on_trusted; simpl.
    destruct i as [cn i]; simpl; dest_cases w; subst; tcsp;[].
    apply (M_run_ls_on_input_not_in (USIGlocalSys s) (pre2trusted cn)).
    simpl; introv xx; repndors; subst; tcsp.
    inversion xx; subst; tcsp.
  Qed.

End TrIncrun.
