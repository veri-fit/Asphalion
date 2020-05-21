(* GENERIC *)

Require Export MinBFTcount_gen4_request.
Require Export MinBFTcount_gen4_reply.
Require Export MinBFTcount_gen4_prepare.
Require Export MinBFTcount_gen4_commit.
Require Export MinBFTcount_gen4_accept.
Require Export MinBFTcount_gen4_debug.


Section MinBFTcount_gen4.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma wf_procs_MinBFTlocalSys_newP_implies_wf_procs_subs :
    forall r s l,
      ~In MAINname (get_names l)
      -> wf_procs (MinBFTlocalSys_newP r s l)
      -> wf_procs l.
  Proof.
    introv ni wf; unfold wf_procs, no_dup_subs in *; simpl in *; allrw andb_true; repnd.
    autorewrite with comp in *; dest_cases w.
  Qed.
  Hint Resolve wf_procs_MinBFTlocalSys_newP_implies_wf_procs_subs : minbft.

  Lemma wf_procs_MinBFTlocalSys_newP_implies_lower_head_subs :
    forall r s l,
      ~In MAINname (get_names l)
      -> wf_procs (MinBFTlocalSys_newP r s l)
      -> lower_head 1 l = true.
  Proof.
    introv ni wf; unfold wf_procs, no_dup_subs in *; simpl in *; allrw andb_true; repnd.
    autorewrite with comp in *; auto.
  Qed.
  Hint Resolve wf_procs_MinBFTlocalSys_newP_implies_lower_head_subs : minbft.

  Lemma are_procs_n_procs_MinBFTlocalSys_newP_implies_are_procs_n_procs_subs :
    forall r s l,
      are_procs_n_procs (MinBFTlocalSys_newP r s l)
      -> are_procs_n_procs l.
  Proof.
    introv ps i.
    pose proof (ps (incr_n_nproc p)) as ps; simpl in *.
    autodimp ps hyp; tcsp.
    { right; apply in_map_iff; eauto. }
    unfold is_proc_n_nproc in *; destruct p; simpl in *; tcsp.
  Qed.
  Hint Resolve are_procs_n_procs_MinBFTlocalSys_newP_implies_are_procs_n_procs_subs : minbft.

  Lemma M_run_ls_before_event_minbft_preserves_cond_LOGname :
    forall {eo : EventOrdering} (e : Event) R s subs subs',
      ~ In MAINname (get_names subs)
      -> lower_head 1 subs = true
      -> wf_procs subs
      -> are_procs_n_procs subs
      -> M_run_ls_before_event (MinBFTlocalSysP R subs) e
         = Some (MinBFTlocalSys_newP R s subs')
      -> in_subs LOGname subs = true
      -> in_subs USIGname subs = true
      -> cond_LOGname_ex_entry subs
      -> cond_LOGname_ex_entry subs'.
  Proof.
    intros eo.
    induction e as [e ind] using predHappenedBeforeInd;
      introv ni low wf aps eqls insL insU cond.
    rewrite M_run_ls_before_event_unroll in eqls.
    destruct (dec_isFirst e) as [d|d]; ginv; minbft_simp.

    { inversion eqls as [xx]; apply incr_n_procs_inj in xx; subst; auto. }

    apply map_option_Some in eqls; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbftP in eqls1; exrepnd; subst; auto;[].
    apply (M_run_ls_before_event_minbft_preserves_in_subs LOGname) in eqls1 as insL'; auto;[].
    apply (M_run_ls_before_event_minbft_preserves_in_subs USIGname) in eqls1 as insU'; auto;[].
    applydup M_run_ls_before_event_preserves_subs in eqls1; eauto 3 with minbft; repnd;[].

    apply ind in eqls1; clear ind; auto; eauto 3 with eo; repnd.
    applydup @similar_subs_preserves_get_names in eqls2 as eqn.
    rewrite eqn in ni.

    clear dependent subs.

    remember (trigger (local_pred e)) as trig; symmetry in Heqtrig; destruct trig;
      try (complete (apply map_option_Some in eqls0; exrepnd; rev_Some; minbft_simp;
                     unfold trigger_op in *; rewrite Heqtrig in *; simpl in *; ginv));[].
    destruct d0; simpl in *.
    { eapply M_run_ls_on_this_one_event_minbft_preserves_cond_LOGname_request; eauto 3 with minbft. }
    { eapply M_run_ls_on_this_one_event_minbft_preserves_cond_LOGname_reply; eauto 3 with minbft. }
    { eapply M_run_ls_on_this_one_event_minbft_preserves_cond_LOGname_prepare; eauto 3 with minbft. }
    { eapply M_run_ls_on_this_one_event_minbft_preserves_cond_LOGname_commit; eauto 3 with minbft. }
    { eapply M_run_ls_on_this_one_event_minbft_preserves_cond_LOGname_accept; eauto 3 with minbft. }
    { eapply M_run_ls_on_this_one_event_minbft_preserves_cond_LOGname_debug; eauto 3 with minbft. }
  Qed.
  Hint Resolve M_run_ls_before_event_minbft_preserves_cond_LOGname : minbft.

End MinBFTcount_gen4.


Hint Resolve M_run_ls_before_event_minbft_preserves_cond_LOGname : minbft.
