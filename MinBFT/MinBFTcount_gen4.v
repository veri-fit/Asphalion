Require Export MinBFTcount_gen3.


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


  (* old definition *)
  Inductive pres_is_M_break_out {n} {cn} (P : n_proc_at n cn -> Prop) :
    nat -> n_proc_at n cn -> Prop :=
  | pres_cond1 :
      forall p, P p -> pres_is_M_break_out P 0 p
  | pres_cond2 :
      forall k p i q o,
        is_M_break_out (lift_M_O (app_n_proc_at p i)) [] (sm_or_at q, o)
        -> pres_is_M_break_out P k p
        -> pres_is_M_break_out P (S k) q.

  Fixpoint preserves_is_M_break_out
           {n} {cn}
           (k : nat)
           (P : n_proc_at n cn -> Prop)
           (p : n_proc_at n cn) : Prop :=
    match k with
    | 0 => P p
    | S k =>
      forall i q o,
        is_M_break_out (lift_M_O (app_n_proc_at p i)) [] (sm_or_at q, o)
        -> preserves_is_M_break_out k P q
    end.

  Definition ex_entry (rd : RequestData) (l : LOG_state) : Prop :=
    exists e, find_entry rd l = Some e.

  Definition is_M_break_out_LOGname_implies_ex_entry
             (p : n_proc_at 0 LOGname) :=
    forall c q,
      (is_M_break_out
         (lift_M_O (app_n_proc_at p (is_committed_in c))) []
         (q, log_out true)
       \/ (exists o,
              is_M_break_out
                 (lift_M_O (app_n_proc_at p (log_new_commit_log_in c))) []
                (q, o))
       \/ is_M_break_out
            (lift_M_O (app_n_proc_at p (prepare_already_in_log_in (commit2prepare c)))) []
            (q, log_out true)
       \/ (exists o ui,
              is_M_break_out
                (lift_M_O (app_n_proc_at p (log_new_commit_log_in (mk_my_commit c ui)))) []
                (q, o)))
      -> ex_entry (commit2request_data_i c) (sm2state q).

  Definition preserves_is_M_break_out_LOGname_implies_ex_entry
             (p : n_proc_at 0 LOGname) :=
    forall k,
      preserves_is_M_break_out
        k
        is_M_break_out_LOGname_implies_ex_entry
        p.

  Definition cond_LOGname_ex_entry
             (subs : n_procs 1) :=
    forall a,
      find_name LOGname subs = Some (sm_or_at a)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry a.

  Lemma implies_cond_LOGname_ex_entry_replace_name_diff :
    forall (p : n_proc 1 USIGname) (subs : n_procs 1),
      in_subs LOGname subs = true
      -> cond_LOGname_ex_entry subs
      -> cond_LOGname_ex_entry (replace_name p subs).
  Proof.
    introv i cond h.
    simplify_find_name_replace; tcsp.
  Qed.

  Lemma implies_cond_LOGname_ex_entry_replace_name_eq :
    forall (p : n_proc 1 LOGname) (subs : n_procs 1),
      in_subs LOGname subs = true
      -> preserves_is_M_break_out_LOGname_implies_ex_entry (proc2at0 p)
      -> cond_LOGname_ex_entry (replace_name p subs).
  Proof.
    introv i cond h.
    simplify_find_name_replace; tcsp.
  Qed.

  Lemma cond_implies_preserves_ex_entry :
    forall (subs : n_procs 1) (p : n_proc_at 0 LOGname) q i o,
      cond_LOGname_ex_entry subs
      -> find_name LOGname subs = Some (sm_or_at p)
      -> is_M_break_out (lift_M_O (app_n_proc_at (sm2p0 p) i)) [] (q, o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry (proc2at0 q).
  Proof.
    introv cond fn h; introv.
    apply cond in fn; clear cond.
    pose proof (fn (S k)) as fn.
    unfold preserves_is_M_break_out_LOGname_implies_ex_entry in *; simpl in *.
    unfold sm2p0 in *; simpl in *.
    destruct q; simpl in *; tcsp.
    pose proof (fn i a o) as fn; tcsp.
  Qed.

  Lemma is_M_break_out_preserves_ex_entry :
    forall (p : n_proc_at 0 LOGname) q i o,
      is_M_break_out (lift_M_O (app_n_proc_at (sm2p0 p) i)) [] (q, o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> preserves_is_M_break_out_LOGname_implies_ex_entry (proc2at0 q).
  Proof.
    introv h w.
    destruct q; simpl in *; tcsp.
    introv.
    pose proof (w (S k)) as w; simpl in *.
    apply w in h; auto.
  Qed.
  Hint Resolve is_M_break_out_preserves_ex_entry : minbft.

  Lemma is_M_break_out_preserves_ex_entry_2 :
    forall (p : n_proc_at 0 LOGname) q i o,
      is_M_break_out (lift_M_O (app_n_proc_at (sm2p0 p) i)) [] (sm_or_at q, o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> preserves_is_M_break_out_LOGname_implies_ex_entry q.
  Proof.
    introv h w.
    introv.
    pose proof (w (S k)) as w; simpl in *.
    apply w in h; auto.
  Qed.
  Hint Resolve is_M_break_out_preserves_ex_entry_2 : minbft.

  Lemma invalid_commit_false_implies_eq_commit2view :
    forall R ks v c b s,
      invalid_commit R ks v c b s = false
      -> commit2view c = v.
  Proof.
    introv h.
    unfold invalid_commit, valid_commit in h.
    repeat dest_cases w.
  Qed.
  Hint Resolve invalid_commit_false_implies_eq_commit2view : minbft.

  Hint Rewrite ui2counter_commit2ui_i_as_commit2counter_i : minbft.

  Lemma invalid_commit_false_implies_eq_commit2sender_i :
    forall R ks v c b s,
      invalid_commit R ks v c b s = false
      -> commit2sender_i c = MinBFTprimary v.
  Proof.
    introv h.
    unfold invalid_commit, valid_commit, is_primary in h.
    repeat dest_cases w.
  Qed.
  Hint Resolve invalid_commit_false_implies_eq_commit2sender_i : minbft.

  Lemma cond_LOGname_ex_entry_implies_preserves :
    forall (subs : n_procs 1) (p : n_proc_at 0 LOGname),
      cond_LOGname_ex_entry subs
      -> find_name LOGname subs = Some (sm_or_at p)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p.
  Proof.
    introv cond fn; introv; tcsp.
    apply cond in fn; clear cond; tcsp.
  Qed.
  Hint Resolve cond_LOGname_ex_entry_implies_preserves : minbft.

  Lemma preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry :
    forall (p : MP_StateMachine (fun _ => False) LOGname) c q,
      is_M_break_out (lift_M_O (app_n_proc_at (sm2p0 p) (is_committed_in c))) [] (q, log_out true)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> ex_entry (commit2request_data_i c) (sm2state q).
  Proof.
    introv h w.
    pose proof (w 0 c q) as w; simpl in w; tcsp.
  Qed.
  Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry : minbft.

  Lemma mk_my_commit_commit2ui_j :
    forall c,
      mk_my_commit c (commit2ui_j c) = c.
  Proof.
    introv.
    destruct c as [b uij], b as [v r uii]; simpl; tcsp.
  Qed.
  Hint Rewrite mk_my_commit_commit2ui_j : minbft.

  Lemma preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log :
    forall (p : MP_StateMachine (fun _ => False) LOGname) c q o,
      is_M_break_out (lift_M_O (app_n_proc_at (sm2p0 p) (log_new_commit_log_in c))) [] (q, o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> ex_entry (commit2request_data_i c) (sm2state q).
  Proof.
    introv h w.
    pose proof (w 0 c q) as w; simpl in w; tcsp.
    apply w; clear w.
    right; right; right; eauto.
    exists o (commit2ui_j c).
    autorewrite with minbft; auto.
  Qed.
  Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log : minbft.

  Lemma preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log_my :
    forall (p : MP_StateMachine (fun _ => False) LOGname) c q o ui,
      is_M_break_out (lift_M_O (app_n_proc_at (sm2p0 p) (log_new_commit_log_in (mk_my_commit c ui)))) [] (q, o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> ex_entry (commit2request_data_i c) (sm2state q).
  Proof.
    introv h w.
    pose proof (w 0 c q) as w; simpl in w; tcsp.
    apply w; right; eauto.
  Qed.
  Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log_my : minbft.

  Lemma preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_prep :
    forall (p : MP_StateMachine (fun _ => False) LOGname) c q,
      is_M_break_out (lift_M_O (app_n_proc_at (sm2p0 p) (prepare_already_in_log_in (commit2prepare c)))) [] (q, log_out true)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> ex_entry (commit2request_data_i c) (sm2state q).
  Proof.
    introv h w.
    pose proof (w 0 c q) as w; simpl in w; tcsp.
  Qed.
  Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_prep : minbft.

  Lemma M_run_ls_before_event_minbft_preserves_cond_LOGname :
    forall {eo : EventOrdering} (e : Event) R s subs subs',
      M_run_ls_before_event (MinBFTlocalSysP R subs) e
      = Some (MinBFTlocalSys_newP R s subs')
      -> in_subs LOGname subs = true
      -> in_subs USIGname subs = true
      -> cond_LOGname_ex_entry subs
      -> cond_LOGname_ex_entry subs'.
  Proof.
    intros eo.
    induction e as [e ind] using predHappenedBeforeInd;introv eqls insL insU cond.
    rewrite M_run_ls_before_event_unroll in eqls.
    destruct (dec_isFirst e) as [d|d]; ginv.

    { inversion eqls as [xx]; subst; auto. }

    apply map_option_Some in eqls; exrepnd; rev_Some.
    applydup M_run_ls_before_event_ls_is_minbftP in eqls1; exrepnd; subst.
    apply (M_run_ls_before_event_minbft_preserves_in_subs LOGname) in eqls1 as insL'; auto;[].
    apply (M_run_ls_before_event_minbft_preserves_in_subs USIGname) in eqls1 as insU'; auto;[].
    apply ind in eqls1; auto; eauto 3 with eo; repnd.

    clear dependent subs.
    apply map_option_Some in eqls0; exrepnd; simpl in *; rev_Some.
    autorewrite with minbft comp in *.
    Time minbft_dest_msg Case;
      repeat (autorewrite with minbft comp in *; simpl in *; smash_minbft2);
      try (complete (inversion eqls2; subst; auto));
      try (complete (repeat (gdest; smash_minbft1_at_ eqls2; repeat hide_break; repnd; simpl in *; repndors; ginv; tcsp; eauto 2 with minbft; minbft_simp);
                       inversion eqls2; subst; simpl in *; auto;
                         repeat simplify_find_name_replace;
                         autorewrite with minbft comp in *;
                         repeat (first [apply implies_cond_LOGname_ex_entry_replace_name_eq; in_subs_tac
                                       |apply implies_cond_LOGname_ex_entry_replace_name_diff; in_subs_tac]);
                         eauto 10 with minbft comp)).
  Qed.
  Hint Resolve M_run_ls_before_event_minbft_preserves_cond_LOGname : minbft.

End MinBFTcount_gen4.


Hint Resolve is_M_break_out_preserves_ex_entry : minbft.
Hint Resolve is_M_break_out_preserves_ex_entry_2 : minbft.
Hint Resolve invalid_commit_false_implies_eq_commit2view : minbft.
Hint Resolve invalid_commit_false_implies_eq_commit2sender_i : minbft.
Hint Resolve cond_LOGname_ex_entry_implies_preserves : minbft.
Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry : minbft.
Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log : minbft.
Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log_my : minbft.
Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_prep : minbft.
Hint Resolve M_run_ls_before_event_minbft_preserves_cond_LOGname : minbft.


Hint Rewrite @mk_my_commit_commit2ui_j : minbft.
Hint Rewrite @ui2counter_commit2ui_i_as_commit2counter_i : minbft.
