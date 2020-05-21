(* GENERIC *)

Require Export MinBFTg.
Require Export ComponentSM6.


Section MinBFTsim1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.

  Lemma wf_procs_MinBFTlocalSysP :
    forall r subs,
      ~In MAINname (get_names subs)
      -> lower_head 1 subs = true
      -> wf_procs subs
      -> wf_procs (MinBFTlocalSysP r subs).
  Proof.
    introv ni.
    unfold wf_procs, no_dup_subs; simpl; allrw andb_true.
    autorewrite with comp.
    dest_cases w; dands; tcsp.
  Qed.
  Hint Resolve wf_procs_MinBFTlocalSysP : minbft.

  Lemma is_proc_n_proc_MAIN_comp :
    forall r, is_proc_n_proc (MAIN_comp r).
  Proof.
    introv; eexists; introv; try reflexivity.
  Qed.
  Hint Resolve is_proc_n_proc_MAIN_comp : minbft.

  Lemma are_procs_n_procs_MinBFTlocalSysP :
    forall r subs,
      are_procs_n_procs subs
      -> are_procs_n_procs (MinBFTlocalSysP r subs).
  Proof.
    introv aps i; simpl in *; repndors; subst; tcsp; simpl in *; tcsp; eauto 3 with minbft comp.
    apply are_procs_n_procs_incr_n_procs in i; auto.
  Qed.
  Hint Resolve are_procs_n_procs_MinBFTlocalSysP : minbft.

  Lemma similar_sms_at_minbft_replica :
    forall r (p : n_proc 2 _),
      similar_sms p (MAIN_comp r)
      -> exists s, p = MinBFT_replicaSM_new r s.
  Proof.
    introv sim; simpl in *.
    destruct p; simpl in *; tcsp.
    unfold similar_sms_at in sim.
    destruct a as [upd st]; simpl in *; subst; simpl in *.
    exists st; auto.
  Qed.

  Lemma similar_procs_MAIN :
    forall r p,
      similar_procs (MkPProc MAINname (MAIN_comp r)) p
      -> exists s, p = MkPProc MAINname (MinBFT_replicaSM_new r s).
  Proof.
    introv sim.
    inversion sim as [? ? ? ? sims]; clear sim; subst.
    match goal with
    | [ H : context[p1] |- _ ] => rename H into h1
    end.
    match goal with
    | [ H : context[p2] |- _ ] => rename H into h2
    end.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h1; subst; eauto 3 with comp.
    apply Eqdep.EqdepTheory.inj_pair2 in h2; subst; eauto 3 with comp.
    apply similar_sms_sym in sims.
    apply similar_sms_at_minbft_replica in sims; exrepnd; subst; eauto.
  Qed.

  Lemma similar_subs_MinBFTlocalSysP :
    forall r subs ls,
      similar_subs (MinBFTlocalSysP r subs) ls
      -> exists (s : MAIN_state) (subs' : n_procs _),
        ls = MinBFTlocalSys_newP r s subs'
        /\ similar_subs subs subs'.
  Proof.
    introv sim.
    inversion sim; subst; simpl in *.
    apply similar_procs_MAIN in simp; exrepnd; subst; simpl in *.
    apply similar_subs_incr_n_procs_left_implies in sims; exrepnd; subst.
    exists s j; dands; tcsp.
  Qed.

  (* MOVE to MinBFTsubs *)
  Lemma M_run_ls_before_event_ls_is_minbftP :
    forall {eo   : EventOrdering}
           (e    : Event)
           (r    : Rep)
           (ls   : LocalSystem 2 0)
           (subs : n_procs _),
      ~In MAINname (get_names subs)
      -> lower_head 1 subs = true
      -> wf_procs subs
      -> are_procs_n_procs subs
      -> M_run_ls_before_event (MinBFTlocalSysP r subs) e = Some ls
      ->
      exists (s : MAIN_state) (subs' : n_procs _),
        ls = MinBFTlocalSys_newP r s subs'
        /\ similar_subs subs subs'.
  Proof.
    introv ni low wf aps run.
    applydup M_run_ls_before_event_preserves_subs in run; eauto 3 with minbft.
    repnd.
    apply similar_subs_MinBFTlocalSysP in run3; exrepnd; subst.
    exists s subs'; dands; auto.
  Qed.

End MinBFTsim1.


Hint Resolve wf_procs_MinBFTlocalSysP : minbft.
Hint Resolve is_proc_n_proc_MAIN_comp : minbft.
Hint Resolve are_procs_n_procs_MinBFTlocalSysP : minbft.
