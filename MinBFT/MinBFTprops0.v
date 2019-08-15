Require Export MinBFTtacts.
Require Export CalculusSM.
Require Export MinBFTkn0.


Hint Rewrite orb_false_r : bool.



Section MinBFTprops0.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma invalid_commit_false_implies :
    forall slf km v c pil s,
      invalid_commit slf km v c pil s = false
      -> valid_commit slf km v c pil s = 0.
  Proof.
    introv h.
    unfold invalid_commit in *; smash_minbft.
  Qed.
  Hint Resolve invalid_commit_false_implies : minbft.

  Lemma valid_commit2_implies_executed_prior :
    forall slf km v c pil s,
      valid_commit2 slf km v c pil s = 0
      -> executed_prior_counter (commit2ui_i c) s = true.
  Proof.
    introv h.
    unfold valid_commit2 in h; smash_minbft.
  Qed.
  Hint Resolve valid_commit2_implies_executed_prior : minbft.

  Lemma executed_prior_counter_implies_eq_S :
    forall c s,
      executed_prior_counter (commit2ui_i c) s = true
      -> commit2counter_i c = S (cexec s).
  Proof.
    introv h.
    destruct c as [b uij]; simpl in *.
    destruct b as [v r uii]; simpl in *.
    destruct uii as [puii d]; simpl in *.
    destruct puii as [i j c]; simpl in *.
    destruct c; unfold executed_prior_counter in *; simpl in *; smash_minbft.
  Qed.
  Hint Resolve executed_prior_counter_implies_eq_S : minbft.

  Lemma invalid_commit2_false_implies_commit2counter_i_eq :
    forall r ks v c b s,
      invalid_commit2 r ks v c b s = false
      -> commit2counter_i c = S (cexec s).
  Proof.
    introv h.
    unfold invalid_commit2, valid_commit2, executed_prior_counter in h; smash_minbft2.
  Qed.
  Hint Resolve invalid_commit2_false_implies_commit2counter_i_eq : minbft.

  Lemma executed_prior_counter_prep_implies_eq_S :
    forall (p : Prepare) (s : MAIN_state),
      executed_prior_counter (prepare2ui p) s = true
      -> prepare2counter p = S (cexec s).
  Proof.
    introv h.
    destruct p as [b ui]; simpl in *.
    destruct b as [v r]; simpl in *.
    destruct ui as [pui d]; simpl in *.
    destruct pui as [i j c]; simpl in *.
    destruct c; unfold executed_prior_counter in *; simpl in *; smash_minbft.
  Qed.
  Hint Resolve executed_prior_counter_prep_implies_eq_S : minbft.

  Lemma invalid_prepare_false_implies_prepare2counter_eq :
    forall (r : Rep) (ks : local_key_map) (v : View) (p : Prepare) (s : MAIN_state),
      invalid_prepare r ks v p s = false
      -> prepare2counter p = S (cexec s).
  Proof.
    introv h.
    unfold invalid_prepare, valid_prepare, executed_prior_counter in h; smash_minbft2.
  Qed.
  Hint Resolve invalid_prepare_false_implies_prepare2counter_eq : minbft.

  Lemma commit2counter_i_mk_auth_commit_prepare2ui :
    forall v r p x,
      commit2counter_i (mk_auth_commit v r (prepare2ui p) x)
      = prepare2counter p.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite commit2counter_i_mk_auth_commit_prepare2ui : minbft.

  Lemma is_committed_true_implies :
    forall c l,
      is_committed c l = true
      ->
      exists e,
        find_entry (commit2request_data_i c) l = Some e
        /\ F <= length (log_entry_commits e).
  Proof.
    introv i.
    unfold is_committed in i; smash_minbft.
    eexists; dands; eauto.
    unfold is_committed_entry in *.
    destruct x; simpl in *; smash_minbft.
  Qed.

  Lemma commit2rd2ui2counter_eq :
    forall c,
      ui2counter (request_data2ui (commit2request_data_i c))
      = commit2counter_i c.
  Proof.
    destruct c as [b a], b as [v m ui]; simpl; auto.
  Qed.
  Hint Rewrite commit2rd2ui2counter_eq : minbft.

  Lemma commit2rd2ui2rep_eq :
    forall c,
      ui2rep (request_data2ui (commit2request_data_i c))
      = commit2sender_i c.
  Proof.
    destruct c as [b a], b as [v m ui]; simpl; auto.
  Qed.
  Hint Rewrite commit2rd2ui2rep_eq : minbft.

  Lemma current_view_stop_processing :
    forall s,
      current_view (stop_processing s) = current_view s.
  Proof.
    destruct s; simpl; auto.
  Qed.
  Hint Rewrite current_view_stop_processing : minbft.

  Lemma current_view_increment_latest_executed_counter :
    forall s,
      current_view (increment_latest_executed_counter s)
      = current_view s.
  Proof.
    destruct s; simpl; auto.
  Qed.
  Hint Rewrite current_view_increment_latest_executed_counter : minbft.

  Lemma current_view_update_latest_executed :
    forall r s,
      current_view (update_latest_executed r s)
      = current_view s.
  Proof.
    destruct s; simpl; auto.
  Qed.
  Hint Rewrite current_view_update_latest_executed : minbft.

  Lemma current_view_update_highest_received_counter :
    forall ui s,
      current_view (update_highest_received_counter ui s)
      = current_view s.
  Proof.
    destruct s; simpl; auto.
  Qed.
  Hint Rewrite current_view_update_highest_received_counter : minbft.

  Lemma current_view_start_processing :
    forall r s,
      current_view (start_processing r s)
      = current_view s.
  Proof.
    introv; destruct s; simpl; auto.
  Qed.
  Hint Rewrite current_view_start_processing : minbft.

  Lemma valid_commit_implies_primary1 :
    forall slf km v c pil s,
      valid_commit slf km v c pil s = 0
      -> commit2sender_i c = MinBFTprimary v.
  Proof.
    introv h.
    unfold valid_commit, is_primary in h; smash_minbft.
  Qed.
  Hint Resolve valid_commit_implies_primary1 : minbft.

  Lemma valid_commit_implies_primary2 :
    forall slf km v c pil s,
      valid_commit slf km v c pil s = 0
      -> commit2sender_i c = MinBFTprimary (commit2view c).
  Proof.
    introv h.
    unfold valid_commit, is_primary in h; smash_minbft.
  Qed.
  Hint Resolve valid_commit_implies_primary2 : minbft.

  Lemma eq_commit2request_data :
    forall c,
      request_data (commit2view c) (commit2request c) (commit2ui_i c)
      = commit2request_data_i c.
  Proof.
    destruct c as [c ui], c; simpl; auto.
  Qed.
  Hint Rewrite eq_commit2request_data : minbft.

  Lemma commit2rd2rep_eq :
    forall c,
      request_data2rep (commit2request_data_i c) = commit2sender_i c.
  Proof.
    destruct c as [c ui], c; simpl; auto.
  Qed.
  Hint Rewrite commit2rd2rep_eq : minbft.

  Lemma same_RequestData_Deq :
    forall {T} rd (a b : T),
      (if RequestData_Deq rd rd then a else b) = a.
  Proof.
    introv; smash_minbft.
  Qed.
  Hint Rewrite @same_RequestData_Deq : minbft.

  Lemma request_data2ui_commit2request_data_i :
    forall c,
      request_data2ui (commit2request_data_i c)
      = commit2ui_i c.
  Proof.
    destruct c as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2ui_commit2request_data_i : minbft.

  Lemma request_data2view_commit2request_data_j_eq :
    forall c,
      request_data2view (commit2request_data_j c)
      = commit2view c.
  Proof.
    destruct c as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2view_commit2request_data_j_eq : minbft.

  Lemma request_data2view_commit2request_data_i_eq :
    forall c,
      request_data2view (commit2request_data_i c)
      = commit2view c.
  Proof.
    destruct c as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2view_commit2request_data_i_eq : minbft.

  Lemma request_data2data_message_commit2request_data_j_eq :
    forall c,
      request_data2data_message (commit2request_data_j c)
      = commit2bare_request c.
  Proof.
    destruct c as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2data_message_commit2request_data_j_eq : minbft.

  Lemma request_data2data_message_commit2request_data_i_eq :
    forall c,
      request_data2data_message (commit2request_data_i c)
      = commit2bare_request c.
  Proof.
    destruct c as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2data_message_commit2request_data_i_eq : minbft.

  Lemma ui2rep_commit2ui_j_eq :
    forall c,
      ui2rep (commit2ui_j c) = commit2sender_j c.
  Proof.
    destruct c as [b ui], ui as [x c], x; simpl; tcsp.
  Qed.
  Hint Rewrite ui2rep_commit2ui_j_eq : minbft.

  Lemma ui2rep_commit2ui_i_eq :
    forall c,
      ui2rep (commit2ui_i c) = commit2sender_i c.
  Proof.
    destruct c as [b ui], ui as [x c], x; simpl; tcsp.
  Qed.
  Hint Rewrite ui2rep_commit2ui_i_eq : minbft.

  Lemma valid_commit_implies_commit2view_eq :
    forall slf km v c pil s,
      valid_commit slf km v c pil s = 0
      -> commit2view c = v.
  Proof.
    introv h.
    unfold valid_commit in h; smash_minbft.
  Qed.
  Hint Resolve valid_commit_implies_commit2view_eq : minbft.

  Lemma find_ui_implies_ui_in_log :
    forall rd l e,
      find_entry rd l = Some e
      -> ui_in_log (request_data2ui rd) l = true.
  Proof.
    induction l; introv h; simpl in *; ginv; smash_minbft.
    clear IHl.
    left.
    destruct e as [rd comms], rd; simpl.
    unfold ui_in_log_entry; simpl; smash_minbft.
  Qed.
  Hint Resolve find_ui_implies_ui_in_log : minbft.

  Lemma request_data_eta :
    forall rd,
      request_data
        (request_data2view rd)
        (request_data2request rd)
        (request_data2ui rd) = rd.
  Proof.
    destruct rd; auto.
  Qed.
  Hint Rewrite request_data_eta : minbft.

  Lemma request_data2ui_prepare2request_data :
    forall p,
      request_data2ui (prepare2request_data p)
      = prepare2ui p.
  Proof.
    destruct p as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2ui_prepare2request_data : minbft.

  Lemma ui_in_log_log_new_prepare :
    forall (ui : UI) (p : Prepare) (l : LOG_state),
      ui_in_log ui (log_new_prepare p l)
      = if UI_dec ui (prepare2ui p) then true
        else ui_in_log ui l.
  Proof.
    induction l; simpl; autorewrite with bool; tcsp;[|].

    { unfold ui_in_log_entry, MkNewLogEntryFromPrepare; simpl.
      autorewrite with minbft; auto. }

    smash_minbft;[].

    destruct a as [rd comms], rd, p as [b pui], b; simpl.
    unfold ui_in_log_entry, log_entry_request_data, prepare2request_data in *;
      simpl in *; ginv; smash_minbft.
  Qed.

  Definition prepare2hash_data (p : Prepare) : HashData :=
    RequestData2HashData (prepare2request_data p).

  Definition commit2hash_data_i (c : Commit) : HashData :=
    RequestData2HashData (commit2request_data_i c).

  Definition commit2hash_data_j (c : Commit) : HashData :=
    RequestData2HashData (commit2request_data_j c).

  Lemma hash_data_in_log_log_new_prepare :
    forall (hd : HashData) (p : Prepare) (l : LOG_state),
      hash_data_in_log hd (log_new_prepare p l)
      = if HashData_Deq hd (prepare2hash_data p) then true
        else hash_data_in_log hd l.
  Proof.
    induction l; simpl; autorewrite with bool; tcsp.
    smash_minbft.
    unfold prepare2hash_data.
    rewrite <- e.
    destruct a as [rd comms], rd; simpl.
    unfold hash_data_in_log_entry; simpl; smash_minbft.
  Qed.

  Lemma request_data2ui_commit2request_data_j :
    forall c,
      request_data2ui (commit2request_data_j c)
      = commit2ui_j c.
  Proof.
    destruct c as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2ui_commit2request_data_j : minbft.

  Definition log_state_entry2rep (e : LOG_state_entry) : Rep :=
    request_data2rep (log_entry_request_data e).

  Definition log_state_entry2reps (e : LOG_state_entry) : list Rep :=
    log_state_entry2rep e :: map ui2rep (log_entry_commits e).

  Definition commit_ui_j_rep_not_in_log (c : Commit) (l : LOG_state) : bool :=
    match find_entry (commit2request_data_i c) l with
    | Some e =>
      if in_dec rep_deq (commit2sender_j c) (log_state_entry2reps e)
      then false
      else true
    | None => true
    end.

  Lemma in_add_commit2commits_implies :
    forall ui c comms,
      In ui (add_commit2commits c comms)
      -> ui = c \/ In ui comms.
  Proof.
    introv h.
    unfold add_commit2commits in h; smash_minbft; repndors; tcsp.
  Qed.

  Lemma not_over_or: forall a b : Prop, ~ (a \/ b) <-> ~ a /\ ~ b.
  Proof.
    introv; split; intro h; repnd; tcsp.
  Qed.

  Lemma ui_in_log_log_new_commit :
    forall (ui : UI) (c : Commit) (l : LOG_state),
      ui_in_log ui (log_new_commit c l)
      = if UI_dec ui (commit2ui_i c) then true
        else if ui_in_log ui l then true
             else if commit_ui_j_rep_not_in_log c l then
                    if UI_dec ui (commit2ui_j c) then true else false
                  else false.
  Proof.
    induction l; introv; simpl in *; autorewrite with bool in *; tcsp;
      smash_minbft; repndors; tcsp; ginv;
        try (complete (unfold ui_in_log_entry, MkNewLogEntryFromCommit in *; simpl;
                       autorewrite with minbft in *; auto; smash_minbft;
                       unfold commit2ui_j in *; tcsp));
        try (complete (destruct a as [rd comms]; simpl in *; smash_minbft;
                       unfold ui_in_log_entry in *; simpl in *; smash_minbft;
                       unfold add_commit2commits in *; smash_minbft));
        try (complete (unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft;
                       allrw not_over_or; repnd; tcsp;
                       destruct a as [rd comms]; simpl in *;
                       unfold add_commit2entry; simpl in *; smash_minbft;
                       unfold ui_in_log_entry; simpl; autorewrite with minbft in *; smash_minbft;
                       unfold log_state_entry2rep in *; simpl in *;
                       unfold ui_in_log_entry in *; simpl in *; smash_minbft;
                       unfold add_commit2commits in *; smash_minbft; repndors; tcsp;
                       rewrite commit2rd2rep_eq in *; tcsp)).
  Qed.

  Lemma Build_HashData_eq_prepare2hash_data :
    forall p,
      Build_HashData (prepare2view p) (prepare2request p) (prepare2ui p)
      = prepare2hash_data p.
  Proof.
    destruct p as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite Build_HashData_eq_prepare2hash_data : minbft.

  Lemma request_data2view_of_prepare2request_data_eq_prepare2view :
    forall p,
      request_data2view (prepare2request_data p) = prepare2view p.
  Proof.
    introv.
    destruct p, prepare_b.
    tcsp.
  Qed.
  Hint Rewrite request_data2view_of_prepare2request_data_eq_prepare2view : minbft.

  Lemma request_data2data_message_of_prepare2request_data_eq_request_b_of_prepare2request :
    forall p,
      request_data2data_message (prepare2request_data p)
      = request_b (prepare2request p).
  Proof.
    introv.
    destruct p, prepare_b.
    tcsp.
  Qed.
  Hint Rewrite request_data2data_message_of_prepare2request_data_eq_request_b_of_prepare2request : minbft.

  Lemma request_data2ui_of_prepare2request_data_eq_prepare2ui :
    forall p,
      request_data2ui (prepare2request_data p)
      = prepare2ui p.
  Proof.
    introv.
    destruct p, prepare_b.
    tcsp.
  Qed.
  Hint Rewrite request_data2ui_of_prepare2request_data_eq_prepare2ui : minbft.

  Lemma prepare2ui_eq_request_data2ui_of_log_entry_request_data_of_MkNewLogEntryFromPrepare :
    forall p,
      request_data2ui (log_entry_request_data (MkNewLogEntryFromPrepare p))
      = prepare2ui p.
  Proof.
    introv.
    destruct p, prepare_b.
    tcsp.
  Qed.
  Hint Rewrite prepare2ui_eq_request_data2ui_of_log_entry_request_data_of_MkNewLogEntryFromPrepare : minbft.

  Lemma prepare2request_data_eq_log_entry_request_dat_of_MkNewLogEntryFromPrepare :
    forall p,
      log_entry_request_data (MkNewLogEntryFromPrepare p)
      = prepare2request_data p.
  Proof.
    introv; destruct p, prepare_b; tcsp.
  Qed.
  Hint Rewrite prepare2request_data_eq_log_entry_request_dat_of_MkNewLogEntryFromPrepare : minbft.


  Lemma log_entry_request_data_add_commit2entry :
    forall c e,
      log_entry_request_data (add_commit2entry c e)
      = log_entry_request_data e.
  Proof.
    destruct e; simpl; smash_minbft.
  Qed.
  Hint Rewrite log_entry_request_data_add_commit2entry : minbft.

  Lemma RequestData2HashData_commit2request_data_i_eq :
    forall c,
      RequestData2HashData (commit2request_data_i c)
      = commit2hash_data_i c.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite RequestData2HashData_commit2request_data_i_eq : minbft.

  Lemma RequestData2HashData_commit2request_data_j_eq :
    forall c,
      RequestData2HashData (commit2request_data_j c)
      = commit2hash_data_j c.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite RequestData2HashData_commit2request_data_j_eq : minbft.

  Lemma RequestDataAndUI2HashData_commit2request_data_i_commit_uj_eq :
    forall c,
      RequestDataAndUI2HashData (commit2request_data_i c) (commit_uj c)
      = commit2hash_data_j c.
  Proof.
    destruct c as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite RequestDataAndUI2HashData_commit2request_data_i_commit_uj_eq : minbft.

  Lemma hash_data_in_log_commits_add_commit2commits_eq :
    forall hd rd c comms,
      hash_data_in_log_commits hd rd (add_commit2commits c comms)
      = if hash_data_in_log_commits hd rd comms then true
        else if in_dec rep_deq (ui2rep c) (map ui2rep comms) then false
             else if HashData_Deq hd (RequestDataAndUI2HashData rd c) then true else false.
  Proof.
    introv; unfold add_commit2commits; smash_minbft.
  Qed.

  Lemma hash_data_in_log_entry_add_commit2entry_eq :
    forall hd c e,
      hash_data_in_log_entry hd (add_commit2entry c e)
      = if hash_data_in_log_entry hd e then true
        else if in_dec rep_deq (ui2rep c) (log_state_entry2reps e) then false
             else if HashData_Deq hd (RequestDataAndUI2HashData (log_entry_request_data e) c) then true else false.
  Proof.
    introv; unfold add_commit2entry.
    destruct e as [rd comms]; simpl;
      unfold hash_data_in_log_entry; simpl; smash_minbft;
        rewrite hash_data_in_log_commits_add_commit2commits_eq; allrw; auto;
          smash_minbft; repndors; tcsp.
  Qed.

  Lemma Build_HashData_commit_i_eq :
    forall c,
      Build_HashData
        (commit2view c)
        (commit2request c)
        (commit2ui_i c)
      = commit2hash_data_i c.
  Proof.
    destruct c as [b ui], b; tcsp.
  Qed.
  Hint Rewrite Build_HashData_commit_i_eq : minbft.

  Lemma Build_HashData_commit_j_eq :
    forall c,
      Build_HashData
        (commit2view c)
        (commit2request c)
        (commit2ui_j c)
      = commit2hash_data_j c.
  Proof.
    destruct c as [b ui], b; tcsp.
  Qed.
  Hint Rewrite Build_HashData_commit_j_eq : minbft.

  Lemma Build_HashData_commit_j_eq2 :
    forall c,
      Build_HashData
        (commit2view c)
        (commit2request c)
        (commit_uj c)
      = commit2hash_data_j c.
  Proof.
    destruct c as [b ui], b; tcsp.
  Qed.
  Hint Rewrite Build_HashData_commit_j_eq2 : minbft.

  Lemma request_data2request_commit2request_data_j_eq :
    forall c,
      request_data2request (commit2request_data_j c)
      = commit2request c.
  Proof.
    destruct c as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2request_commit2request_data_j_eq : minbft.

  Lemma request_data2request_commit2request_data_i_eq :
    forall c,
      request_data2request (commit2request_data_i c)
      = commit2request c.
  Proof.
    destruct c as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2request_commit2request_data_i_eq : minbft.

  Lemma hash_data_in_log_log_new_commit_eq :
    forall hd c l,
      hash_data_in_log hd (log_new_commit c l)
      = if HashData_Deq hd (commit2hash_data_i c) then true
        else if hash_data_in_log hd l then true
             else if commit_ui_j_rep_not_in_log c l then
                    if HashData_Deq hd (commit2hash_data_j c) then true else false
                  else false.
  Proof.
    induction l; simpl; autorewrite with bool; tcsp; smash_minbft;
      repndors; ginv;
      try (complete (unfold MkNewLogEntryFromCommit, hash_data_in_log_entry; simpl;
                     smash_minbft; autorewrite with minbft in *; tcsp));
      try (complete (unfold commit2hash_data_i; allrw; unfold hash_data_in_log_entry;
                     autorewrite with minbft; smash_minbft));
      try (complete (destruct a as [rd comms]; simpl in *; smash_minbft;
                     unfold hash_data_in_log_entry in *; simpl in *; smash_minbft;
                     unfold commit_ui_j_rep_not_in_log in *; simpl in *; smash_minbft;
                     unfold log_state_entry2rep in *; simpl in *;
                     allrw not_over_or; repnd; tcsp;
                     autorewrite with minbft in *; tcsp;
                     rewrite hash_data_in_log_commits_add_commit2commits_eq; smash_minbft;
                     repndors; tcsp;
                     autorewrite with minbft in *; tcsp)).
  Qed.

  Lemma valid_prepare_implies_view :
    forall r keys v p s,
      valid_prepare r keys v p s = true
      -> v = prepare2view p.
  Proof.
    introv h.
    unfold valid_prepare in *; smash_minbft.
  Qed.

  Lemma eq_prepare2request_data :
    forall p,
      request_data (prepare2view p) (prepare2request p) (prepare2ui p)
      = prepare2request_data p.
  Proof.
    introv; destruct p as [b ui], b; simpl in *; tcsp.
  Qed.
  Hint Rewrite eq_prepare2request_data : minbft.

  Lemma prepare_not_already_in_log_implies_find_entry :
    forall p s,
      prepare_already_in_log p s = false
      -> find_entry (prepare2request_data p) (log_new_prepare p s)
         = Some (MkNewLogEntryFromPrepare p).
  Proof.
    induction s; introv h; simpl in *; ginv; smash_minbft.
  Qed.

  Lemma log_state_entry2rep_MkNewLogEntryFromPrepare :
    forall p,
      log_state_entry2rep (MkNewLogEntryFromPrepare p)
      = prepare2sender p.
  Proof.
    introv; unfold log_state_entry2rep; simpl.
    destruct p as [b ui], b; simpl; tcsp.
  Qed.
  Hint Rewrite log_state_entry2rep_MkNewLogEntryFromPrepare : minbft.

  Lemma request_data2view_prepare2request_data_eq :
    forall p,
      request_data2view (prepare2request_data p) = prepare2view p.
  Proof.
    introv; destruct p as [b ui], b; auto.
  Qed.
  Hint Rewrite request_data2view_prepare2request_data_eq : minbft.

  Lemma pre_ui_id_commit2ui_j :
    forall c,
      pre_ui_rid (commit2ui_j c) = commit2sender_j c.
  Proof.
    destruct c as [b ui], b; auto.
  Qed.
  Hint Rewrite pre_ui_id_commit2ui_j : minbft.

  Lemma find_entry_log_new_prepare :
    forall (rd : RequestData) (p : Prepare) (l : LOG_state),
      find_entry rd (log_new_prepare p l)
      = match find_entry rd l with
        | Some e => Some e
        | None =>
          if RequestData_Deq rd (prepare2request_data p)
          then Some (MkNewLogEntryFromPrepare p)
          else None
        end.
  Proof.
    induction l; simpl; smash_minbft.
  Qed.

  Lemma find_entry_log_new_commit :
    forall rd c l,
      find_entry rd (log_new_commit c l)
      = match find_entry rd l with
        | Some e =>
          if RequestData_Deq rd (commit2request_data_i c)
          then Some (add_commit2entry (commit2ui_j c) e)
          else Some e
        | None =>
          if RequestData_Deq rd (commit2request_data_i c)
          then Some (MkNewLogEntryFromCommit c)
          else None
        end.
  Proof.
    induction l; simpl; tcsp; smash_minbft; GC.
  Qed.

  Fixpoint find_latest_executed_request (c : Client) (l : latest_executed_request) : option Timestamp :=
    match l with
    | [] => None
    | (x,t) :: l =>
      if client_deq x c
      then Some t
      else find_latest_executed_request c l
    end.

  Lemma bare_request_c_request_b_eq :
    forall req,
      bare_request_c (request_b req) = request2sender req.
  Proof.
    destruct req; tcsp.
  Qed.
  Hint Rewrite bare_request_c_request_b_eq : minbft.

  Lemma bare_request_t_request_b_eq :
    forall req,
      bare_request_t (request_b req) = request2timestamp req.
  Proof.
    destruct req; tcsp.
  Qed.
  Hint Rewrite bare_request_t_request_b_eq : minbft.

  Lemma find_latest_executed_request_update_latest_executed_request :
    forall req l,
    exists t,
      find_latest_executed_request
        (request2sender req)
        (update_latest_executed_request req l) = Some t
      /\ request2timestamp req <= t.
  Proof.
    induction l; simpl; smash_minbft.
  Qed.
  Hint Resolve find_latest_executed_request_update_latest_executed_request : minbft.

  Fixpoint new_bare_request (r : Bare_Request) (l : latest_executed_request) : bool :=
    match l with
    | [] => true
    | (c,t) :: l =>
      if client_deq c (bare_request2sender r)
      then t <? (bare_request2timestamp r)
      else new_bare_request r l
    end.

  Lemma new_bare_request_as_new_request :
    forall c l,
      new_request (commit2request c) l = new_bare_request (commit2bare_request c) l.
  Proof.
    unfold commit2bare_request, commit2request; simpl.
    induction l; simpl; tcsp; repnd; simpl in *; smash_minbft.
  Qed.

  Lemma find_latest_executed_request_implies_find_update_latest_executed_request :
    forall c t req l,
      find_latest_executed_request c l = Some t
      ->
      exists t',
        find_latest_executed_request c (update_latest_executed_request req l) = Some t'
        /\ t <= t'.
  Proof.
    induction l; introv h; simpl in *; ginv.
    repnd; simpl in *; smash_minbft.
    eexists; dands; eauto; try omega.
  Qed.
  Hint Resolve find_latest_executed_request_implies_find_update_latest_executed_request : minbft.

  Lemma new_bare_request_implies :
    forall r l t,
      new_bare_request r l = true
      -> find_latest_executed_request (bare_request_c r) l = Some t
      -> t < bare_request_t r.
  Proof.
    induction l; introv new find; simpl in *; ginv.
    repnd; simpl in *; smash_minbft.
    destruct r; simpl in *; tcsp.
  Qed.

  Lemma in_minbft_data_ui_prepare2ui_MinBFT_auth2data_prepare2auth_data :
    forall p,
      In (minbft_data_ui (prepare2ui p))
         (MinBFT_auth2data (prepare2auth_data p)).
  Proof.
    introv.
    destruct p, prepare_b. simpl in *.
    destruct prepare_ui. simpl in *.
    right. left. eauto.
  Qed.
  Hint Resolve in_minbft_data_ui_prepare2ui_MinBFT_auth2data_prepare2auth_data : minbft.


  Lemma in_minbft_data_ui_commit2ui_i_MinBFT_auth2data_commit2auth_data :
    forall c,
      In (minbft_data_ui (commit2ui_i c))
         (MinBFT_auth2data (commit2auth_data c)).
  Proof.
    introv.
    destruct c as [b uj], b as [v m ui]; simpl in *.
    unfold commit2ui_i; simpl in *; tcsp.
  Qed.
  Hint Resolve in_minbft_data_ui_commit2ui_i_MinBFT_auth2data_commit2auth_data : minbft.

  Lemma in_minbft_data_ui_commit2ui_j_MinBFT_auth2data_commit2auth_data :
    forall c,
      In (minbft_data_ui (commit2ui_j c))
         (MinBFT_auth2data (commit2auth_data c)).
  Proof.
    introv.
    destruct c as [b uj], b as [v m ui]; simpl in *; tcsp.
    destruct uj; simpl; tcsp.
  Qed.
  Hint Resolve in_minbft_data_ui_commit2ui_j_MinBFT_auth2data_commit2auth_data : minbft.

  Lemma request_b_commit2request :
    forall c, request_b (commit2request c) = commit2bare_request c.
  Proof.
    destruct c as [b ui]; tcsp.
  Qed.
  Hint Rewrite request_b_commit2request : minbft.

  Lemma bare_prepare_v_prepare_b_eq :
    forall p,
      bare_prepare_v (prepare_b p) = prepare2view p.
  Proof.
    destruct p; auto.
  Qed.
  Hint Rewrite bare_prepare_v_prepare_b_eq : minbft.

  Lemma bare_prepare_m_prepare_b_eq :
    forall p,
      bare_prepare_m (prepare_b p) = prepare2request p.
  Proof.
    destruct p; auto.
  Qed.
  Hint Rewrite bare_prepare_m_prepare_b_eq : minbft.

  Definition prepare2digest (p : Prepare) : MinBFT_digest :=
    ui2digest (prepare2ui p).

  Definition prepare2pre_ui (p : Prepare) : preUI :=
    ui_pre (prepare2ui p).

  Lemma prepare2auth_data_eq :
    forall p,
      prepare2auth_data p
      = MkAuthData
          (MinBFT_msg_bare_prepare (prepare_b p) (prepare2pre_ui p))
          [prepare2digest p].
  Proof.
    introv.
    destruct p as [b ui]; simpl; tcsp.
  Qed.

  Lemma build_ui_decomp_prepare_eq :
    forall p,
      Build_UI (prepare2pre_ui p) (prepare2digest p) = prepare2ui p.
  Proof.
    destruct p as [b ui], ui; simpl; auto.
  Qed.
  Hint Rewrite build_ui_decomp_prepare_eq : minbft.

  Lemma request_data2rep_prepare2request_data :
    forall p,
      request_data2rep (prepare2request_data p)
      = prepare2sender p.
  Proof.
    destruct p as [b ui], b; simpl; auto.
  Qed.
  Hint Rewrite request_data2rep_prepare2request_data : minbft.

  Lemma view_0_eq :
    view 0 = initial_view.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite view_0_eq : minbft.

  Definition commit2digest (c : Commit) : MinBFT_digest :=
    ui2digest (commit2ui_j c).

  Definition commit2pre_ui (c : Commit) : preUI :=
    ui_pre (commit2ui_j c).

  Lemma commit2auth_data_eq :
    forall c,
      commit2auth_data c
      = MkAuthData
          (MinBFT_msg_bare_commit (commit_b c) (commit2pre_ui c))
          [commit2digest c].
  Proof.
    introv.
    destruct c as [b ui]; simpl; tcsp.
  Qed.

  Lemma build_ui_decomp_commit_eq :
    forall c,
      Build_UI (commit2pre_ui c) (commit2digest c) = commit2ui_j c.
  Proof.
    destruct c as [b ui], ui; simpl; auto.
  Qed.
  Hint Rewrite build_ui_decomp_commit_eq : minbft.

  Lemma bare_commit_v_commit_b_eq :
    forall c,
      bare_commit_v (commit_b c) = commit2view c.
  Proof.
    destruct c; auto.
  Qed.
  Hint Rewrite bare_commit_v_commit_b_eq : minbft.

  Lemma bare_commit_m_commit_b_eq :
    forall c,
      bare_commit_m (commit_b c) = commit2request c.
  Proof.
    destruct c; tcsp.
  Qed.
  Hint Rewrite bare_commit_m_commit_b_eq : minbft.

  Lemma bare_commit_ui_commit_b_eq :
    forall c,
      bare_commit_ui (commit_b c) = commit2ui_i c.
  Proof.
    destruct c; tcsp.
  Qed.
  Hint Rewrite bare_commit_ui_commit_b_eq : minbft.

  Lemma in_MinBFT_get_contained_auth_data_implies_is_protocol :
    forall a m,
      In a (MinBFT_get_contained_auth_data m)
      -> is_protocol_message m = true.
  Proof.
    introv i; simpl in *.
    unfold is_protocol_message.
    destruct m; simpl in *; eauto.
  Qed.
  Hint Resolve in_MinBFT_get_contained_auth_data_implies_is_protocol : minbft.

  Lemma prepare2ui_in_prepare2auth_data :
    forall p,
      In (minbft_data_ui (prepare2ui p)) (MinBFT_auth2data (prepare2auth_data p)).
  Proof.
    destruct p as [b ui], b as [v m], ui as [pui d]; simpl; tcsp.
  Qed.
  Hint Resolve prepare2ui_in_prepare2auth_data : minbft.

  Lemma commit2ui_i_mk_auth_commit_eq :
    forall v r ui uj,
      commit2ui_i (mk_auth_commit v r ui uj) = ui.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite commit2ui_i_mk_auth_commit_eq : minbft.

  Lemma ui2counter_prepare2ui_eq :
    forall p,
      ui2counter (prepare2ui p) = prepare2counter p.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite ui2counter_prepare2ui_eq : minbft.

  Lemma ui2rep_prepare2ui_eq :
    forall p,
      ui2rep (prepare2ui p) = prepare2sender p.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite ui2rep_prepare2ui_eq : minbft.

  Lemma prepare_already_in_log_ui_in_log_commit :
    forall  (c : Commit) (l : LOG_state),
      prepare_already_in_log (commit2prepare c) l = true
      -> ui_in_log (commit2ui_i c) l = true.
  Proof.
    induction l; introv h; simpl in *; ginv; subst; tcsp; smash_minbft;[].
    destruct c, commit_b. simpl in *.
    unfold commit2ui_i in *. simpl in *.
    destruct a; simpl in *.
    unfold ui_in_log_entry.
    smash_minbft.
  Qed.
  Hint Resolve prepare_already_in_log_ui_in_log_commit : minbft.

  Lemma pre_ui_id_prepare2ui :
    forall p,
      pre_ui_rid (prepare2ui p) = prepare2sender p.
  Proof.
    destruct p as [b ui], b; auto.
  Qed.
  Hint Rewrite pre_ui_id_prepare2ui : minbft.

  Lemma request_data_in_log_log_new_commit :
    forall rd c l,
      request_data_in_log rd (log_new_commit c l)
      = if RequestData_Deq rd (commit2request_data_i c)
        then true
        else request_data_in_log rd l.
  Proof.
    introv.
    unfold request_data_in_log.
    rewrite find_entry_log_new_commit; smash_minbft.
  Qed.
  Hint Rewrite request_data_in_log_log_new_commit : minbft.

  Lemma request_data_in_log_log_new_prepare :
    forall rd p l,
      request_data_in_log rd (log_new_prepare p l)
      = if RequestData_Deq rd (prepare2request_data p)
        then true
        else request_data_in_log rd l.
  Proof.
    introv.
    unfold request_data_in_log.
    rewrite find_entry_log_new_prepare; smash_minbft.
  Qed.
  Hint Rewrite request_data_in_log_log_new_prepare : minbft.

  Lemma request_data_in_log_Build_LOGStateEntry :
    forall rd rd' uis,
      request_data_in_log rd [Build_LOGStateEntry rd' uis]
      = if RequestData_Deq rd rd' then true else false.
  Proof.
    introv; unfold request_data_in_log; simpl; smash_minbft.
  Qed.
  Hint Rewrite request_data_in_log_Build_LOGStateEntry : minbft.

  Lemma ui2rep_Build_UI :
    forall pui d,
      ui2rep (Build_UI pui d) = pre_ui_rid pui.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite ui2rep_Build_UI : minbft.

  Lemma request_data_in_log_MkNewLogEntryFromPrepare :
    forall rd p,
      request_data_in_log rd [MkNewLogEntryFromPrepare p]
      = if RequestData_Deq rd (prepare2request_data p) then true else false.
  Proof.
    introv; unfold request_data_in_log; simpl; smash_minbft.
  Qed.
  Hint Rewrite request_data_in_log_MkNewLogEntryFromPrepare : minbft.

  Lemma request_data_in_log_cons :
    forall rd entry entries,
      request_data_in_log rd (entry :: entries)
      = if RequestData_Deq rd (log_entry_request_data entry)
        then true
        else request_data_in_log rd entries.
  Proof.
    introv; unfold request_data_in_log; simpl; smash_minbft.
  Qed.
  Hint Rewrite request_data_in_log_cons : minbft.

End MinBFTprops0.


Hint Resolve invalid_commit_false_implies : minbft.
Hint Resolve valid_commit2_implies_executed_prior : minbft.
Hint Resolve executed_prior_counter_implies_eq_S : minbft.
Hint Resolve invalid_commit2_false_implies_commit2counter_i_eq : minbft.
Hint Resolve executed_prior_counter_prep_implies_eq_S : minbft.
Hint Resolve invalid_prepare_false_implies_prepare2counter_eq : minbft.
Hint Resolve valid_commit_implies_primary1 : minbft.
Hint Resolve valid_commit_implies_primary2 : minbft.
Hint Resolve valid_commit_implies_commit2view_eq : minbft.
Hint Resolve find_ui_implies_ui_in_log : minbft.
Hint Resolve find_latest_executed_request_update_latest_executed_request : minbft.
Hint Resolve find_latest_executed_request_implies_find_update_latest_executed_request : minbft.
Hint Resolve find_latest_executed_request_implies_find_update_latest_executed_request : minbft.
Hint Resolve in_minbft_data_ui_prepare2ui_MinBFT_auth2data_prepare2auth_data : minbft.
Hint Resolve in_minbft_data_ui_commit2ui_i_MinBFT_auth2data_commit2auth_data : minbft.
Hint Resolve in_minbft_data_ui_commit2ui_j_MinBFT_auth2data_commit2auth_data : minbft.
Hint Resolve in_MinBFT_get_contained_auth_data_implies_is_protocol : minbft.
Hint Resolve prepare2ui_in_prepare2auth_data : minbft.
Hint Resolve prepare_already_in_log_ui_in_log_commit : minbft.


Hint Rewrite @commit2counter_i_mk_auth_commit_prepare2ui : minbft.
Hint Rewrite @commit2rd2ui2counter_eq : minbft.
Hint Rewrite @commit2rd2ui2rep_eq : minbft.
Hint Rewrite @current_view_stop_processing : minbft.
Hint Rewrite @current_view_increment_latest_executed_counter : minbft.
Hint Rewrite @current_view_update_latest_executed : minbft.
Hint Rewrite @current_view_update_highest_received_counter : minbft.
Hint Rewrite @current_view_start_processing : minbft.
Hint Rewrite @eq_commit2request_data : minbft.
Hint Rewrite @commit2rd2rep_eq : minbft.
Hint Rewrite @same_RequestData_Deq : minbft.
Hint Rewrite @request_data2ui_commit2request_data_i : minbft.
Hint Rewrite @request_data2view_commit2request_data_j_eq : minbft.
Hint Rewrite @request_data2view_commit2request_data_i_eq : minbft.
Hint Rewrite @request_data2data_message_commit2request_data_j_eq : minbft.
Hint Rewrite @request_data2data_message_commit2request_data_i_eq : minbft.
Hint Rewrite @ui2rep_commit2ui_j_eq : minbft.
Hint Rewrite @ui2rep_commit2ui_i_eq : minbft.
Hint Rewrite @request_data_eta : minbft.
Hint Rewrite @request_data2ui_prepare2request_data : minbft.
Hint Rewrite @request_data2ui_commit2request_data_j : minbft.
Hint Rewrite @Build_HashData_eq_prepare2hash_data : minbft.
Hint Rewrite @request_data2view_of_prepare2request_data_eq_prepare2view : minbft.
Hint Rewrite @request_data2data_message_of_prepare2request_data_eq_request_b_of_prepare2request : minbft.
Hint Rewrite @request_data2ui_of_prepare2request_data_eq_prepare2ui : minbft.
Hint Rewrite @prepare2ui_eq_request_data2ui_of_log_entry_request_data_of_MkNewLogEntryFromPrepare : minbft.
Hint Rewrite @prepare2request_data_eq_log_entry_request_dat_of_MkNewLogEntryFromPrepare : minbft.
Hint Rewrite @log_entry_request_data_add_commit2entry : minbft.
Hint Rewrite @RequestData2HashData_commit2request_data_i_eq : minbft.
Hint Rewrite @RequestData2HashData_commit2request_data_j_eq : minbft.
Hint Rewrite @RequestDataAndUI2HashData_commit2request_data_i_commit_uj_eq : minbft.
Hint Rewrite @eq_prepare2request_data : minbft.
Hint Rewrite @log_state_entry2rep_MkNewLogEntryFromPrepare : minbft.
Hint Rewrite @Build_HashData_commit_i_eq : minbft.
Hint Rewrite @Build_HashData_commit_j_eq : minbft.
Hint Rewrite @Build_HashData_commit_j_eq2 : minbft.
Hint Rewrite @request_data2view_prepare2request_data_eq : minbft.
Hint Rewrite @pre_ui_id_commit2ui_j : minbft.
Hint Rewrite @bare_request_c_request_b_eq : minbft.
Hint Rewrite @bare_request_t_request_b_eq : minbft.
Hint Rewrite @request_data2request_commit2request_data_j_eq : minbft.
Hint Rewrite @request_data2request_commit2request_data_i_eq : minbft.
Hint Rewrite @request_b_commit2request : minbft.
Hint Rewrite @bare_prepare_v_prepare_b_eq : minbft.
Hint Rewrite @bare_prepare_m_prepare_b_eq : minbft.
Hint Rewrite @build_ui_decomp_prepare_eq : minbft.
Hint Rewrite @request_data2rep_prepare2request_data : minbft.
Hint Rewrite @view_0_eq : minbft.
Hint Rewrite @build_ui_decomp_commit_eq : minbft.
Hint Rewrite @bare_commit_v_commit_b_eq : minbft.
Hint Rewrite @bare_commit_m_commit_b_eq : minbft.
Hint Rewrite @bare_commit_ui_commit_b_eq : minbft.
Hint Rewrite @commit2ui_i_mk_auth_commit_eq : minbft.
Hint Rewrite @ui2counter_prepare2ui_eq : minbft.
Hint Rewrite @ui2rep_prepare2ui_eq : minbft.
Hint Rewrite @pre_ui_id_prepare2ui : minbft.
Hint Rewrite @request_data_in_log_log_new_commit : minbft.
Hint Rewrite @request_data_in_log_log_new_prepare : minbft.
Hint Rewrite @request_data_in_log_Build_LOGStateEntry : minbft.
Hint Rewrite @ui2rep_Build_UI : minbft.
Hint Rewrite @request_data_in_log_MkNewLogEntryFromPrepare : minbft.
Hint Rewrite @request_data_in_log_cons : minbft.
