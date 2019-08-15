Require Export MinBFTprops0.
Require Export MinBFTkn.


Section MinBFTstate.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma const_opTrust :
    forall {t a},
      In (minbft_data_ui t) (MinBFT_auth2data a)
      -> opTrust a.
  Proof.
    introv i.
    exists (Some t); simpl.
    pose proof (kc_auth2trust_correct a t) as q; apply q.
    exists (minbft_data_ui t); simpl; tcsp.
  Defined.
  Hint Resolve const_opTrust : minbft.

  Lemma upd_ls_main_state_and_subs_MinBFTlocalSys_new :
    forall n s u l s' u' l',
      upd_ls_main_state_and_subs (MinBFTlocalSys_new n s u l) s' (MinBFTsubs_new u' l')
      = MinBFTlocalSys_new n s' u' l'.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite upd_ls_main_state_and_subs_MinBFTlocalSys_new : minbft.

  Lemma state_of_subcomponents_MinBFTsubs_USIGname :
    forall r,
      state_of_subcomponents (MinBFTsubs r) USIGname
      = Some (USIG_initial r).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MinBFTsubs_USIGname : minbft.

  Lemma state_of_subcomponents_MinBFTsubs_new_USIGname :
    forall s l,
      state_of_subcomponents (MinBFTsubs_new s l) USIGname
      = Some s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MinBFTsubs_new_USIGname : minbft.

  Lemma state_of_subcomponents_MinBFTsubs_LOGname :
    forall r,
      state_of_subcomponents (MinBFTsubs r) LOGname
      = Some LOG_initial.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MinBFTsubs_LOGname : minbft.

  Lemma state_of_subcomponents_MinBFTsubs_new_LOGname :
    forall s l,
      state_of_subcomponents (MinBFTsubs_new s l) LOGname
      = Some l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MinBFTsubs_new_LOGname : minbft.

  Lemma state_of_subcomponents_MinBFTsubs_new_u_LOGname :
    forall u,
      state_of_subcomponents (MinBFTsubs_new_u u) LOGname
      = Some LOG_initial.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MinBFTsubs_new_u_LOGname : minbft.

  Lemma state_of_subcomponents_MinBFTsubs_new_u_USIGname :
    forall u,
      state_of_subcomponents (MinBFTsubs_new_u u) USIGname
      = Some u.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_subcomponents_MinBFTsubs_new_u_USIGname : minbft.

  Lemma upd_ls_main_state_and_subs_MinBFTlocalSys :
    forall n s u l,
      upd_ls_main_state_and_subs (MinBFTlocalSys n) s (MinBFTsubs_new u l)
      = MinBFTlocalSys_new n s u l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite upd_ls_main_state_and_subs_MinBFTlocalSys : minbft.

  Lemma state_of_component_MinBFTlocalSys_new_LOGname :
    forall n s u l,
      state_of_component LOGname (MinBFTlocalSys_new n s u l)
      = Some l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_component_MinBFTlocalSys_new_LOGname : minbft.

  Lemma state_of_component_MinBFTlocalSys_new_USIGname :
    forall n s u l,
      state_of_component USIGname (MinBFTlocalSys_new n s u l)
      = Some u.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_component_MinBFTlocalSys_new_USIGname : minbft.

End MinBFTstate.


Hint Resolve const_opTrust : minbft.
Hint Rewrite @upd_ls_main_state_and_subs_MinBFTlocalSys_new : minbft.
Hint Rewrite @state_of_subcomponents_MinBFTsubs_USIGname : minbft.
Hint Rewrite @state_of_subcomponents_MinBFTsubs_new_USIGname : minbft.
Hint Rewrite @state_of_subcomponents_MinBFTsubs_LOGname : minbft.
Hint Rewrite @state_of_subcomponents_MinBFTsubs_new_LOGname : minbft.
Hint Rewrite @state_of_subcomponents_MinBFTsubs_new_u_LOGname : minbft.
Hint Rewrite @state_of_subcomponents_MinBFTsubs_new_u_USIGname : minbft.
Hint Rewrite @upd_ls_main_state_and_subs_MinBFTlocalSys : minbft.
Hint Rewrite @state_of_component_MinBFTlocalSys_new_LOGname : minbft.
Hint Rewrite @state_of_component_MinBFTlocalSys_new_USIGname : minbft.