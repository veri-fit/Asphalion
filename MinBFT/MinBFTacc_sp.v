Require Export MinBFTprops0.


Section MinBFTacc_sp.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma commit2bare_request_mk_auth_commit :
    forall v r ui1 ui2,
      commit2bare_request (mk_auth_commit v r ui1 ui2) = request_b r.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite commit2bare_request_mk_auth_commit : minbft.

  Lemma commit2client_mk_auth_commit :
    forall v r ui1 ui2,
      commit2client (mk_auth_commit v r ui1 ui2) = request2sender r.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite commit2client_mk_auth_commit : minbft.

  Lemma commit2msg_mk_auth_commit :
    forall v r ui1 ui2,
      commit2msg (mk_auth_commit v r ui1 ui2) = request2msg r.
  Proof.
    introv; destruct r; simpl; auto.
  Qed.
  Hint Rewrite commit2msg_mk_auth_commit : minbft.

  Lemma request_b_prepare2request :
    forall p, request_b (prepare2request p) = prepare2bare_request p.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite request_b_prepare2request : minbft.

  Lemma new_bare_request_prep_as_new_request_prep :
    forall (p : Prepare) (l : latest_executed_request),
      new_request (prepare2request p) l = new_bare_request (prepare2bare_request p) l.
  Proof.
    unfold prepare2bare_request, prepare2request; simpl.
    induction l; simpl; tcsp; repnd; simpl in *; smash_minbft.
  Qed.

End MinBFTacc_sp.


Hint Rewrite @commit2bare_request_mk_auth_commit : minbft.
Hint Rewrite @commit2client_mk_auth_commit : minbft.
Hint Rewrite @commit2msg_mk_auth_commit : minbft.
Hint Rewrite @request_b_prepare2request : minbft.
