Require Export MinBFTcount_gen4.


Section MinBFTcount_gen5_aux.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma state_of_component_replace_name_diff :
    forall {n} {cn} cn' (p : n_proc n cn) subs,
      cn <> cn'
      -> state_of_component cn' (replace_name p subs)
         = state_of_component cn' subs.
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [cm q]; simpl in *; dest_cases w; subst; GC;
      unfold state_of_component; simpl; dest_cases w.
  Qed.

  Lemma in_subs_implies_state_of_sub_components :
    forall cn {n} (subs : n_procs n),
      in_subs cn subs = true
      -> exists x, state_of_component cn subs = Some x.
  Proof.
    induction subs; introv h; simpl in *; tcsp.
    destruct a as [cn' p]; simpl in *; dest_cases w; ginv; subst;
      unfold state_of_component; simpl; dest_cases z.
    rewrite (compname_proof_irrelevance z eq_refl); simpl; eauto.
  Qed.

  Lemma in_subs_find_name_none_implies :
    forall cn {n} (subs : n_procs n),
      in_subs cn subs = true
      -> find_name cn subs = None
      -> False.
  Proof.
    induction subs; introv h q; simpl in *; tcsp.
    destruct a as [k p]; dest_cases w.
  Qed.

  (* Move to TrIncprops0 *)
  Lemma invalid_commit_implies_ui2cui_0 :
    forall r ks v c b s,
      invalid_commit r ks v c b s = false
      -> ui2cid (commit2ui_i c) = cid0.
  Proof.
    introv h.
    unfold invalid_commit, valid_commit in *; smash_minbft1.
    unfold is_counter0 in *; smash_minbft1.
  Qed.
  Hint Resolve invalid_commit_implies_ui2cui_0 : minbft.

  Lemma invalid_prepare_implies_ui2cui_0:
    forall (r : Rep) (ks : local_key_map) (v : View) (p : Prepare) (s : MAIN_state),
      invalid_prepare r ks v p s = false
      -> ui2cid (prepare2ui p) = cid0.
  Proof.
    introv h.
    unfold invalid_prepare, valid_prepare in *; smash_minbft1.
    unfold is_counter0 in *; smash_minbft1.
  Qed.
  Hint Resolve invalid_prepare_implies_ui2cui_0 : minbft.

  Lemma invalid_prepare_false_implies_eq_prepare2view :
    forall R ks v p s,
      invalid_prepare R ks v p s = false
      -> prepare2view p = v.
  Proof.
    introv h.
    unfold invalid_prepare, valid_prepare in h.
    smash_minbft2.
  Qed.
  Hint Resolve invalid_prepare_false_implies_eq_prepare2view : minbft.

  Lemma ui2counter_prepare2ui_as_prepare2counter :
    forall p,
      ui2counter (prepare2ui p) = prepare2counter p.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite ui2counter_prepare2ui_as_prepare2counter : minbft.

  Lemma invalid_prepare_false_implies_eq_prepare2sender :
    forall R ks v p s,
      invalid_prepare R ks v p s = false
      -> prepare2sender p = MinBFTprimary v.
  Proof.
    introv h.
    unfold invalid_prepare, valid_prepare, is_primary in h.
    smash_minbft2.
  Qed.
  Hint Resolve invalid_prepare_false_implies_eq_prepare2sender : minbft.

  Lemma implies_ex_entry_request_data :
    forall ui' v r ui s,
      ex_entry (commit2request_data_i (mk_auth_commit v r ui ui')) s
      -> ex_entry (request_data v r ui) s.
  Proof.
    tcsp.
  Qed.

  Lemma wf_procs_MinBFTlocalSys_newP :
    forall r s subs,
      ~In MAINname (get_names subs)
      -> lower_head 1 subs = true
      -> wf_procs subs
      -> wf_procs (MinBFTlocalSys_newP r s subs).
  Proof.
    introv ni.
    unfold wf_procs, no_dup_subs; simpl; allrw andb_true.
    autorewrite with comp.
    dest_cases w; dands; tcsp.
  Qed.
  Hint Resolve wf_procs_MinBFTlocalSys_newP : minbft.

  Lemma is_proc_n_proc_MinBFT_replicaSM_new :
    forall r s, is_proc_n_proc (MinBFT_replicaSM_new r s).
  Proof.
    introv; eexists; introv; try reflexivity.
  Qed.
  Hint Resolve is_proc_n_proc_MinBFT_replicaSM_new : minbft.

  Lemma are_procs_n_procs_MinBFTlocalSys_newP :
    forall r s subs,
      are_procs_n_procs subs
      -> are_procs_n_procs (MinBFTlocalSys_newP r s subs).
  Proof.
    introv aps i; simpl in *; repndors; subst; tcsp; simpl in *; tcsp; eauto 3 with minbft comp.
    apply are_procs_n_procs_incr_n_procs in i; auto.
  Qed.
  Hint Resolve are_procs_n_procs_MinBFTlocalSys_newP : minbft.

  Lemma similar_procs_MinBFT_replicaSM_new :
    forall r s p,
      similar_procs (MkPProc MAINname (MinBFT_replicaSM_new r s)) p
      -> exists s', p = MkPProc MAINname (MinBFT_replicaSM_new r s').
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

  Lemma similar_subs_MinBFTlocalSys_newP :
    forall r s subs ls,
      similar_subs (MinBFTlocalSys_newP r s subs) ls
      -> exists (s' : MAIN_state) (subs' : n_procs _),
        ls = MinBFTlocalSys_newP r s' subs'
        /\ similar_subs subs subs'.
  Proof.
    introv sim.
    inversion sim; subst; simpl in *.
    apply similar_procs_MinBFT_replicaSM_new in simp; exrepnd; subst; simpl in *.
    apply similar_subs_incr_n_procs_left_implies in sims; exrepnd; subst.
    exists s' j; dands; tcsp.
  Qed.

  (* MOVE to MinBFTsubs *)
  Lemma M_run_ls_on_input_ls_is_minbft_newP :
    forall cn i o s
           (r    : Rep)
           (ls   : LocalSystem 2 0)
           (subs : n_procs _),
      ~In MAINname (get_names subs)
      -> lower_head 1 subs = true
      -> wf_procs subs
      -> are_procs_n_procs subs
      -> M_run_ls_on_input (MinBFTlocalSys_newP r s subs) cn i = (ls, o)
      ->
      exists (s' : MAIN_state) (subs' : n_procs _),
        ls = MinBFTlocalSys_newP r s' subs'
        /\ similar_subs subs subs'.
  Proof.
    introv ni low wf aps run.
    apply M_run_ls_on_input_preserves_subs in run; eauto 3 with minbft; repnd.
    apply similar_subs_MinBFTlocalSys_newP in run2; exrepnd; subst.
    exists s' subs'; dands; auto.
  Qed.

  Lemma preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry2 :
    forall (p : n_proc_at 0 LOGname) c q l,
      is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) (is_committed_in c))) l (Some (at2sm q), log_out true)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> ex_entry (commit2request_data_i c) (sm_state q).
  Proof.
    introv h w.
    pose proof (w 0 c (at2sm q) l) as w; simpl in w; tcsp.
  Qed.
  Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry2 : minbft.

  (* MOVE to some ComponentSM file *)
  Lemma similar_sms_at_preserves_is_proc_n_proc_at :
    forall cn n (p1 p2 : n_proc_at n cn),
      similar_sms_at p1 p2
      -> is_proc_n_proc_at p1
      -> is_proc_n_proc_at p2.
  Proof.
    introv sim isp.
    unfold is_proc_n_proc_at in *; exrepnd.
    exists p.
    introv.
    rewrite <- sim; auto.
  Qed.
  Hint Resolve similar_sms_at_preserves_is_proc_n_proc_at : comp.

End MinBFTcount_gen5_aux.


Hint Resolve invalid_commit_implies_ui2cui_0 : minbft.
Hint Resolve invalid_prepare_implies_ui2cui_0 : minbft.
Hint Resolve invalid_prepare_false_implies_eq_prepare2view : minbft.
Hint Resolve invalid_prepare_false_implies_eq_prepare2sender : minbft.
Hint Resolve wf_procs_MinBFTlocalSys_newP : minbft.
Hint Resolve is_proc_n_proc_MinBFT_replicaSM_new : minbft.
Hint Resolve are_procs_n_procs_MinBFTlocalSys_newP : minbft.
Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry2 : minbft.


Hint Resolve similar_sms_at_preserves_is_proc_n_proc_at : comp.


Hint Rewrite @ui2counter_prepare2ui_as_prepare2counter : minbft.


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* REPLACE in MinBFTgen *)
Ltac pwf_step :=
  match goal with
  | [ H : ?x |- ?x ] => auto

  (* wf_procs *)
  | [ H : find_name _ ?l = Some _ |- wf_procs (replace_name _ ?l) ] =>
    eapply wf_procs_replace_name;[exact H| |]

  | [ |- wf_procs (replace_name _ (replace_name _ _)) ] =>
    apply implies_wf_procs_replace_name_twice

  | [ H : similar_subs _ ?l |- wf_procs (replace_name _ ?l) ] =>
    eapply similar_subs_preserves_wf_procs;
    [apply implies_similar_subs_replace_name;eauto|];
    auto

  (* is_proc_n_proc_at *)
  | [ H : find_name _ _ = Some (sm_or_at ?p) |- is_proc_n_proc_at (sm2p0 ?p) ] =>
    eapply implies_is_proc_n_proc_at_0;[|exact H];auto

  | [ H : find_name _ _ = Some (sm_or_at ?p) |- is_proc_n_proc_at ?p ] =>
    eapply implies_is_proc_n_proc_at_0;[|exact H];auto

  | [ H : similar_sms_at _ ?b |- is_proc_n_proc_at (sm2p0 ?b) ] =>
    eapply similar_sms_at_preserves_is_proc_n_proc_at; [exact H|];
    simpl; auto

  | [ H : similar_sms_at _ ?b |- is_proc_n_proc_at ?b ] =>
    eapply similar_sms_at_preserves_is_proc_n_proc_at; [exact H|];
    simpl; auto

  (* is_proc_n_proc *)
  | [ H : find_name _ _ = Some (sm_or_at ?p) |- is_proc_n_proc (at2sm ?p) ] =>
    eapply implies_is_proc_n_proc_at_0;[|exact H];auto

  | [ H : similar_sms_at _ ?b |- is_proc_n_proc (sm_or_at ?b) ] =>
    eapply similar_sms_preserves_is_proc_n_proc;
    [apply implies_similar_sms_sm_or_at;eauto|];
    simpl; auto

  | [ H : similar_sms_at _ ?b |- is_proc_n_proc (at2sm ?b) ] =>
    eapply similar_sms_preserves_is_proc_n_proc;
    [apply implies_similar_sms_sm_or_at;eauto|];
    simpl; auto

  (* is_proc_n_proc_op *)
  | [ H : is_M_break_out (lift_M_1 (app_n_proc_at _ _)) _ (?o,_) |- is_proc_n_proc_op ?o ] =>
    eapply is_M_break_out_preserves_is_proc_n_proc_op;[|exact H]

  (* are_procs_n_procs *)
  | [ |- are_procs_n_procs (replace_name _ _) ] =>
    apply implies_are_procs_n_procs_replace_name; auto

  | [ |- are_procs_n_procs (replace_name_op _ _) ] =>
    apply are_procs_n_procs_replace_name_op; auto

  | [ H : similar_subs _ ?l |- are_procs_n_procs ?l ] =>
    eapply similar_subs_preserves_are_procs_n_procs;[eauto|];auto

  (* similar_subs *)
  | [ |- similar_subs ?l (replace_name _ ?k) ] =>
    apply similar_subs_replace_name_right; auto

  | [ H : similar_subs _ ?b |- similar_subs _ ?b ] =>
    eapply similar_subs_trans;[|eauto]

  (* has_sim_comp *)
  | [ H : find_name _ ?l = Some (sm_or_at ?a) |- has_sim_comp (at2sm ?a) ?l ] =>
    apply find_name_implies_has_sim_comp_at2sm; auto

  | [ H : similar_subs _ ?k |- has_sim_comp _ ?k ] =>
    eapply similar_subs_preserves_has_sim_comp;[eauto|]

  | [ H : similar_sms_at _ ?b |- has_sim_comp (at2sm ?b) _ ] =>
    eapply similar_sms_at_preserves_has_sim_comp;[eauto|]

  | [ H : similar_sms_at _ ?b |- has_sim_comp (sm_or_at ?b) _ ] =>
    eapply similar_sms_at_preserves_has_sim_comp;[eauto|]

  | [ |- has_sim_comp _ (replace_name _ _) ] =>
    let xx := fresh "xx" in
    first [apply implies_has_simp_comp_replace_name_same
          |apply implies_has_simp_comp_replace_name_diff;[intro xx; inversion xx; fail|]
          ]
  end.

Ltac pwf := repeat (pwf_step; eauto 2 with comp minbft).

Ltac rm_is_M_break_mon :=
  match goal with
  | [ H : is_M_break_mon _ _ _ |- _ ] =>
    apply @is_M_break_mon_0_implies_eq in H;[|pwf];[];subst
  end.

Ltac is_M_break_out_some :=
  match goal with
  | [ H : is_M_break_out _ _ (?a, _) |- _ ] =>
    match a with
    | Some _ => fail 1
    | _ =>
      applydup @is_M_break_out_preserves_subs_sm2p0 in H;[|pwf];[];
      exrepnd; subst; simpl in *
    end
  end.
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
