Require Export MinBFTprops1.


Section MinBFTinv.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma invalid_prepare_false_implies_diff_prepare2sender :
    forall R ks v p s,
      invalid_prepare R ks v p s = false
      -> R <> MinBFTprimary v.
  Proof.
    introv inv.
    unfold invalid_prepare, valid_prepare, is_primary in inv; smash_minbft2.
  Qed.

  Lemma data_is_owned_by_invalid_prepare_implies_false :
    forall r ks v p s,
      data_is_owned_by r (minbft_data_ui (prepare2ui p))
      -> invalid_prepare r ks v p s = false
      -> False.
  Proof.
    introv own inv.
    unfold data_is_owned_by in *; simpl in *.
    unfold ui2rep in *; simpl in *.
    applydup invalid_prepare_false_implies_eq_prepare2sender in inv.
    applydup invalid_prepare_false_implies_diff_prepare2sender in inv.
    autorewrite with minbft in *; try congruence.
  Qed.

  Lemma data_is_owned_by_invalid_commit_not_pil_implies_false :
    forall r ks v c s,
      invalid_commit r ks v c false s = false
      -> data_is_owned_by r (minbft_data_ui (commit2ui_i c))
      -> False.
  Proof.
    introv h q.
    unfold invalid_commit, valid_commit, data_is_owned_by, primary_has_logged_its_prepare in *.
    smash_minbft2.
  Qed.

  Lemma commit2ui_i_mk_my_commit :
    forall c ui,
      commit2ui_i (mk_my_commit c ui) = commit2ui_i c.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite commit2ui_i_mk_my_commit : minbft.

End MinBFTinv.


Hint Rewrite @commit2ui_i_mk_my_commit : minbft.
