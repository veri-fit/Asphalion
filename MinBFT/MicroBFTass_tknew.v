Require Export MicroBFTass_knew.


Section MicroBFTass_tknew.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Lemma implies_learns_prepare2ui :
    forall {eo : EventOrdering} (e : Event) r n s u l,
      loc e = MicroBFTheader.node2name n
      -> trigger_op e = Some (MicroBFT_commit r)
      -> M_run_ls_before_event (MicroBFTlocalSys n) e = Some (MicroBFTlocalSys_new n s u l)
      -> verify_UI (commit_n r) (commit_ui r) u = true
      -> learns_data e (microbft_data_ui (commit_ui r)).
  Proof.
    introv eqloc eqtrig runBef verif.
    exists n (commit2auth_data r).
    simpl; allrw; simpl; dands; eauto 3 with microbft.
  Qed.
  Hint Resolve implies_learns_prepare2ui : microbft.

  Lemma ASSUMPTION_trusted_knew_or_learns_or_gen_true :
    forall (eo : EventOrdering), assume_eo eo (KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen).
  Proof.
    repeat introv; apply ASSUMPTION_knew_or_learns_or_gen_true; auto.
  Qed.
  Hint Resolve ASSUMPTION_trusted_knew_or_learns_or_gen_true : microbft.

End MicroBFTass_tknew.


Hint Resolve implies_learns_prepare2ui : microbft.
Hint Resolve ASSUMPTION_trusted_knew_or_learns_or_gen_true : microbft.
