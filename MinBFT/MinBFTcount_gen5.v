Require Export MinBFTcount_gen4.


Section MinBFTcount_gen5.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma state_of_subcomponents_replace_name_diff :
    forall {n} {cn} cn' (p : n_proc n cn) subs,
      cn <> cn'
      -> state_of_subcomponents (replace_name p subs) cn'
         = state_of_subcomponents subs cn'.
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [cm q]; simpl in *; dest_cases w; subst; GC;
      unfold state_of_subcomponents; simpl; dest_cases w.
  Qed.

  Lemma in_subs_implies_state_of_sub_components :
    forall cn {n} (subs : n_procs n),
      in_subs cn subs = true
      -> exists x, state_of_subcomponents subs cn = Some x.
  Proof.
    induction subs; introv h; simpl in *; tcsp.
    destruct a as [cn' p]; simpl in *; dest_cases w; ginv; subst;
      unfold state_of_subcomponents; simpl; dest_cases z.
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

  (* This uses compositional reasoning, but using [LOG_comp]'s spec defined in
     [M_output_ls_on_input_is_committed_implies] *)
  Lemma accepted_counter_if_received_UI_primary :
    forall {eo   : EventOrdering}
           (e    : Event)
           (R    : Rep)
           (subs : n_procs _)
           (r    : Request)
           (i    : nat)
           (l    : list name),
      in_subs LOGname subs = true
      -> in_subs USIGname subs = true
      -> cond_LOGname_ex_entry subs
      -> In (send_accept (accept r i) l) (M_output_ls_on_event (MinBFTlocalSysP R subs) e)
      ->
      exists (s     : MAIN_state)
             (subs' : n_procs _)
             (log   : LOG_state)
             (rd    : RequestData)
             (ui    : UI),
        M_run_ls_on_event (MinBFTlocalSysP R subs) e = Some (MinBFTlocalSys_newP R s subs')
        /\ state_of_subcomponents subs' LOGname = Some log
        /\ ex_entry rd log
        /\ request_data2ui rd = ui
        /\ request_data2request rd = r
        /\ request_data2view rd = current_view s
        /\ ui2counter ui = i
        /\ ui2cid ui = cid0
        /\ ui2rep ui = MinBFTprimary (current_view s).
  Proof.
    introv logIN usigIN condL h.
    apply M_output_ls_on_event_as_run in h; exrepnd.
    rename ls' into ls.
    rewrite M_run_ls_on_event_unroll2; allrw; simpl.

    applydup M_run_ls_before_event_ls_is_minbftP in h1; exrepnd; subst.
    apply in_M_output_ls_on_this_one_event_implies in h0; exrepnd; simpl in *.
    unfold M_run_ls_on_this_one_event; simpl; allrw; simpl.

    rewrite M_break_snd_eq2 in h2.
    rewrite M_break_option_map_fst_eq.
    unfold statefund_nm in *; simpl in *.
    match goal with
    | [ H : context[M_break ?a ?b ?c] |- _ ] => remember (M_break a b c) as mb; symmetry in Heqmb
    end.
    simpl in *.
    rewrite Heqmb in h2; rewrite Heqmb.
    repnd; simpl in *.

    assert (in_subs LOGname subs' = true) as logIH' by eauto 3 with minbft.
    assert (in_subs USIGname subs' = true) as usigIH' by eauto 3 with minbft.
    applydup in_subs_implies_state_of_sub_components in logIH'; exrepnd.

    autorewrite with minbft comp in *.
    Time minbft_dest_msg Case; simpl in *; tcsp; ginv; repeat smash_minbft_2; ginv;
      repeat (use_m_break_call_comp out;
                destruct out; simpl in *; repeat smash_minbft_2;
                  repndors; ginv; tcsp);
      repeat (gdest; smash_minbft1_at_ Heqmb; repeat hide_break; repnd; simpl in *; repndors; ginv; tcsp; eauto 2 with minbft);
      repeat simplify_find_name_replace;
      autorewrite with minbft comp in *;
      eexists; eexists; eexists;
        first [exists (commit2request_data_i c)
              |exists (commit2request_data_i (mk_auth_commit (current_view s) (prepare2request p) (prepare2ui p) x0))];
        eexists;
        dands; try reflexivity; simpl;
          autorewrite with minbft in *; auto; eauto 2 with minbft;
            try (complete (repeat (rewrite state_of_subcomponents_replace_name_diff;[|intro xx; inversion xx; fail]);
                             eauto; rewrite state_of_subcomponents_replace_name; try reflexivity;
                               repeat apply implies_in_subs_replace_name; eauto 2 with comp minbft));
            try (complete (eapply in_subs_find_name_none_implies in logIH'; eauto; tcsp));
            try (complete (try (apply (implies_ex_entry_request_data x0));
                             repeat simplify_find_name_replace;
                             applydup M_run_ls_before_event_minbft_preserves_cond_LOGname in h1;
                             eauto 7 with minbft)).
  Qed.


End MinBFTcount_gen5.


Hint Resolve invalid_commit_implies_ui2cui_0 : minbft.
Hint Resolve invalid_prepare_implies_ui2cui_0 : minbft.
