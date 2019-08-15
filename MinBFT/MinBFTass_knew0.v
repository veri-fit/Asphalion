Require Export CalculusSM_derived2.
Require Export MinBFTprops2.
Require Export MinBFTtacts2.


Section MinBFTass_knew0.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  (* MOVE *)
  Hint Rewrite ui_in_log_log_new_prepare : minbft.
  Hint Rewrite ui_in_log_log_new_commit : minbft.

  Lemma invalid_prepare_false_implies_equal_views :
    forall i keys v p s,
      invalid_prepare i keys v p s = false
      -> prepare2view p = v.
  Proof.
    introv h; unfold invalid_prepare, valid_prepare in *; smash_minbft.
  Qed.
  Hint Resolve invalid_prepare_false_implies_equal_views : minbft.

  Lemma invalid_commit_false_implies_equal_views :
    forall i keys v c pil s,
      invalid_commit i keys v c pil s = false
      -> commit2view c = v.
  Proof.
    introv h; unfold invalid_commit, valid_commit in *; smash_minbft.
  Qed.
  Hint Resolve invalid_commit_false_implies_equal_views : minbft.

  Definition msg2request (m : MinBFT_msg) : option Request :=
    match m with
    | MinBFT_request r => Some r
    | MinBFT_reply r   => Some (bare_reply_r (reply_b r))
    | MinBFT_prepare p => Some (prepare2request p)
    | MinBFT_commit  c => Some (commit2request c)
    | MinBFT_accept  _ => None
    | MinBFT_debug   _ => None
    end.

End MinBFTass_knew0.


Hint Rewrite @ui_in_log_log_new_prepare : minbft.
Hint Rewrite @ui_in_log_log_new_commit : minbft.

Hint Resolve invalid_prepare_false_implies_equal_views : minbft.
Hint Resolve invalid_commit_false_implies_equal_views : minbft.
