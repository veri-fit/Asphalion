(* GENERIC *)

Require Export MinBFTg.


Section MinBFTrw1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  (* Move to Components *)
  Lemma decr_n_procs_incr_n_procs :
    forall {n} (subs : n_procs n),
      decr_n_procs (incr_n_procs subs) = subs.
  Proof.
    induction subs; introv; simpl; tcsp.
    unfold decr_n_procs in *; simpl in *.
    rewrite IHsubs.
    destruct a; simpl in *; tcsp.
  Qed.
  Hint Rewrite @decr_n_procs_incr_n_procs : comp.

  (* Move to Components *)
  Lemma decr_n_procs_cons :
    forall {n} p (subs : n_procs n),
      decr_n_procs (p :: subs)
      = match decr_n_nproc p with
        | Some q => q :: decr_n_procs subs
        | None => decr_n_procs subs
        end.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @decr_n_procs_cons : comp.

  (* Move to Components *)
  Lemma remove_names_get_names_nil :
    forall {n} (l : n_procs n),
      remove_names l (get_names l) = [].
  Proof.
    induction l; introv; simpl in *; tcsp.
    dest_cases w.
  Qed.
  Hint Rewrite @remove_names_get_names_nil : comp.

  (* Move to Components *)
  Lemma remove_names_incr_n_procs :
    forall k {n} (l : n_procs n),
      remove_names (incr_n_procs l) k
      = incr_n_procs (remove_names l k).
  Proof.
    induction k; introv; simpl; tcsp.
    repeat rewrite remove_names_remove_name_swap.
    rewrite IHk.
    rewrite incr_n_procs_remove_name; auto.
  Qed.

  (* Move to ComponentSM *)
  Lemma update_state_build_mp_sm_same :
    forall {cn} (u : M_Update 0 cn (sf cn)) (s : sf cn),
      update_state (build_mp_sm u s) s = build_mp_sm u s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @update_state_build_mp_sm_same : comp.


  Lemma eq_MinBFT_replicaSM_new :
    forall r s,
      sm_or_at (build_mp_sm (MAIN_update r) s)
      =  MinBFT_replicaSM_new r s.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite eq_MinBFT_replicaSM_new : minbft.

  Lemma replace_name_in_MinBFTlocalSys_newP_same :
    forall r s r' s' subs,
      replace_name
        (MinBFT_replicaSM_new r s)
        (MinBFTlocalSys_newP r' s' subs)
      = MinBFTlocalSys_newP r s subs.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite replace_name_in_MinBFTlocalSys_newP_same : minbft.

  Lemma update_subs_MinBFTlocalSys_newP_same :
    forall r s subs,
      ~ In MAINname (get_names subs)
      -> update_subs
           (MinBFTlocalSys_newP r s subs)
           (decr_n_procs (MinBFTlocalSys_newP r s subs))
         = MinBFTlocalSys_newP r s subs.
  Proof.
    introv ni; unfold update_subs, remove_subs, MinBFTlocalSys_newP; simpl.
    autorewrite with comp; simpl.
    rewrite (remove_names_cons
               (get_names subs)
               (MkPProc MAINname (MinBFT_replicaSM_new r s))
               (incr_n_procs subs)); simpl.
    dest_cases w.
    rewrite remove_names_incr_n_procs.
    autorewrite with comp; simpl; tcsp.
  Qed.

  Lemma update_subs_MinBFTlocalSys_newP_same2 :
    forall r s (subs : n_procs 1),
      ~ In MAINname (get_names subs)
      -> update_subs (MinBFTlocalSys_newP r s subs) subs
         = MinBFTlocalSys_newP r s subs.
  Proof.
    introv ni; unfold update_subs, remove_subs, MinBFTlocalSys_newP; simpl.
    autorewrite with comp; simpl.
    rewrite (remove_names_cons
               (get_names subs)
               (MkPProc MAINname (MinBFT_replicaSM_new r s))
               (incr_n_procs subs)); simpl.
    dest_cases w.
    rewrite remove_names_incr_n_procs.
    autorewrite with comp; simpl; tcsp.
  Qed.

  Lemma eq_MinBFTlocalSys_newP_implies :
    forall r s1 s2 l1 l2,
      MinBFTlocalSys_newP r s1 l1 = MinBFTlocalSys_newP r s2 l2
      -> s1 = s2 /\ l1 = l2.
  Proof.
    introv h.
    apply eq_cons in h; repnd.
    apply incr_n_procs_inj in h; subst.
    apply decomp_p_nproc in h0.
    inversion h0; subst; auto.
  Qed.

  Lemma invalid_commit2_false_implies :
    forall slf km v c pil s,
      invalid_commit2 slf km v c pil s = false
      -> valid_commit2 slf km v c pil s = 0.
  Proof.
    introv h.
    unfold invalid_commit2 in *; dest_cases w.
  Qed.
  Hint Resolve invalid_commit2_false_implies : minbft.

  Lemma commit2request_mk_auth_commit :
    forall v r ui1 ui2,
      commit2request (mk_auth_commit v r ui1 ui2) = r.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite commit2request_mk_auth_commit : minbft.

  Lemma decr_n_procs_MinBFTlocalSys_newP :
    forall r s l,
      decr_n_procs (MinBFTlocalSys_newP r s l) = l.
  Proof.
    introv.
    unfold MinBFTlocalSys_newP.
    rewrite @decr_n_procs_cons; simpl.
    autorewrite with comp; auto.
  Qed.
  Hint Rewrite decr_n_procs_MinBFTlocalSys_newP : minbft.

  Lemma update_state_build_mp_sm_MAIN_update :
    forall r s1 s2,
      sm_or_at (update_state (build_mp_sm (MAIN_update r) s1) s2)
      = MinBFT_replicaSM_new r s2.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite update_state_build_mp_sm_MAIN_update : minbft.

  (* Move to some MinBFTrw1 *)
  Lemma update_subs_MinBFTlocalSys_newP :
    forall r s subs subs',
      ~ In MAINname (get_names subs)
      -> similar_subs subs subs'
      -> update_subs
           (MinBFTlocalSys_newP r s subs)
           subs'
         = MinBFTlocalSys_newP r s subs'.
  Proof.
    introv ni sim; unfold update_subs, remove_subs, MinBFTlocalSys_newP; simpl.
    autorewrite with comp; simpl.
    applydup similar_subs_preserves_get_names in sim as eqn.
    rewrite (remove_names_cons
               (get_names subs')
               (MkPProc MAINname (MinBFT_replicaSM_new r s))
               (incr_n_procs subs)); simpl.
    rewrite <- eqn.
    dest_cases w;[].
    rewrite remove_names_incr_n_procs.
    autorewrite with comp; simpl; tcsp.
  Qed.

  Lemma replace_name_in_replace_subs_MinBFTlocalSys_newP :
    forall r s r' s' subs subs',
      ~ In MAINname (get_names subs)
      -> similar_subs subs subs'
      -> replace_name (MinBFT_replicaSM_new r s) (update_subs (MinBFTlocalSys_newP r' s' subs) subs')
         = MinBFTlocalSys_newP r s subs'.
  Proof.
    introv ni sim.
    rewrite update_subs_MinBFTlocalSys_newP; auto.
  Qed.

End MinBFTrw1.


Hint Resolve invalid_commit2_false_implies : minbft.


Hint Rewrite @decr_n_procs_incr_n_procs : comp.
Hint Rewrite @decr_n_procs_cons : comp.
Hint Rewrite @remove_names_get_names_nil : comp.
Hint Rewrite @update_state_build_mp_sm_same : comp.


Hint Rewrite @eq_MinBFT_replicaSM_new : minbft.
Hint Rewrite @replace_name_in_MinBFTlocalSys_newP_same : minbft.
Hint Rewrite @commit2request_mk_auth_commit : minbft.
Hint Rewrite @decr_n_procs_MinBFTlocalSys_newP : minbft.
Hint Rewrite @update_state_build_mp_sm_MAIN_update : minbft.
