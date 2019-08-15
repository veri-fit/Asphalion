Require Export MinBFTtacts.


Section MinBFTbreak.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma M_break_MinBFT_state_update :
    forall {O} r s m subs (F : n_procs 1 -> option MAIN_state * DirectedMsgs -> O),
      M_break (MAIN_update r s m) subs F
      = match m with
        | MinBFT_request _ => M_break (interp_s_proc (handle_request r s m)) subs F
        | MinBFT_prepare _ => M_break (interp_s_proc (handle_prepare r s m)) subs F
        | MinBFT_commit  _ => M_break (interp_s_proc (handle_commit  r s m)) subs F
        | MinBFT_accept  _ => M_break (interp_s_proc (handle_accept  r s m)) subs F
        | MinBFT_reply   _ => M_break (interp_s_proc (handle_reply   r s m)) subs F
        | MinBFT_debug   _ => M_break (interp_s_proc (handle_debug   r s m)) subs F
        end.
  Proof.
    destruct m; introv; simpl; auto.
  Qed.
  Hint Rewrite @M_break_MinBFT_state_update : minbft.

  Lemma M_break_LOG_update :
    forall {O} l i subs (F : n_procs 0 -> option LOG_state * LOG_output_interface  -> O),
      M_break (LOG_update l i) subs F
      = match i with
        | log_new_prepare_log_in p => M_break (interp_s_proc (let l' := log_new_prepare p l in [R](l',log_out true))) subs F
        | log_new_commit_log_in c => M_break (interp_s_proc (let l' := log_new_commit c l in [R](l',log_out true))) subs F
        | prepare_already_in_log_in p => M_break (interp_s_proc (let b := prepare_already_in_log p l in [R](l,log_out b))) subs F
        | is_committed_in c => M_break (interp_s_proc (let b := is_committed c l in [R](l,log_out b))) subs F
        end.
  Proof.
    destruct i; repnd; introv; simpl; auto.
  Qed.
  Hint Rewrite @M_break_LOG_update : minbft.

  Lemma M_break_call_create_ui :
    forall {A n} {O}
           (m    : View * Request * nat * nat)
           (d    : unit -> Proc A)
           (f    : UI -> Proc A)
           (subs : n_procs n)
           (F    : n_procs n -> A -> O),
      M_break (interp_proc (call_create_ui m d f)) subs F
      = M_break (call_proc USIGname (create_ui_in m))
                subs
                (fun subs out =>
                   on_create_ui_out
                     (fun ui => M_break (interp_proc (f ui)) subs F)
                     (fun _ => M_break (interp_proc (d tt)) subs F)
                     out).
  Proof.
    introv.
    unfold call_create_ui; simpl.
    rewrite M_break_bind; simpl.
    apply eq_M_break; introv.
    destruct s; simpl; auto; smash_minbft.
  Qed.
  Hint Rewrite @M_break_call_create_ui : minbft.

  Lemma M_break_call_verify_ui :
    forall {A n} {O}
           (mui  : View * Request * UI)
           (d    : unit -> Proc A)
           (f    : unit -> Proc A)
           (subs : n_procs n)
           (F    : n_procs n -> A -> O),
      M_break (interp_proc (call_verify_ui mui d f)) subs F
      = M_break (call_proc USIGname (verify_ui_in mui))
                subs
                (fun subs out =>
                   if_true_verify_ui_out
                     (fun _ => M_break (interp_proc (f tt)) subs F)
                     (fun _ => M_break (interp_proc (d tt)) subs F)
                     out).
  Proof.
    introv.
    unfold call_verify_ui; simpl.
    rewrite M_break_bind; simpl.
    apply eq_M_break; introv.
    destruct s; simpl; auto; smash_minbft.
  Qed.
  Hint Rewrite @M_break_call_verify_ui : minbft.

  Lemma M_break_call_prepare_already_in_log :
    forall {A n} {O}
           (p    : Prepare)
           (d    : unit -> Proc A)
           (f    : unit -> Proc A)
           (subs : n_procs n)
           (F    : n_procs n -> A -> O),
      M_break (interp_proc (call_prepare_already_in_log p d f)) subs F
      = M_break (call_proc LOGname (prepare_already_in_log_in p))
                subs
                (fun subs out =>
                   on_log_out
                     (fun _ => M_break (interp_proc (d tt)) subs F)
                     (fun _ => M_break (interp_proc (f tt)) subs F)
                     out).
  Proof.
    introv.
    unfold call_prepare_already_in_log; simpl.
    rewrite M_break_bind; simpl.
    apply eq_M_break; introv.
    destruct s; simpl; auto; smash_minbft.
  Qed.
  Hint Rewrite @M_break_call_prepare_already_in_log : minbft.

  Lemma M_break_call_prepare_already_in_log_bool :
    forall {A n} {O}
           (p    : Prepare)
           (f    : bool -> Proc A)
           (subs : n_procs n)
           (F    : n_procs n -> A -> O),
      M_break (interp_proc (call_prepare_already_in_log_bool p f)) subs F
      = M_break (call_proc LOGname (prepare_already_in_log_in p))
                subs
                (fun subs out => M_break (interp_proc (on_log_out_bool f out)) subs F).
  Proof.
    introv.
    unfold call_prepare_already_in_log_bool; simpl.
    rewrite M_break_bind; simpl.
    apply eq_M_break; introv.
    destruct s; simpl; auto; smash_minbft.
  Qed.
  Hint Rewrite @M_break_call_prepare_already_in_log_bool : minbft.

  Lemma M_break_call_log_prepare :
    forall {A n} {O}
           (p    : Prepare)
           (f    : unit -> Proc A)
           (subs : n_procs n)
           (F    : n_procs n -> A -> O),
      M_break (interp_proc (call_log_prepare p f)) subs F
      = M_break (call_proc LOGname (log_new_prepare_log_in p))
                subs
                (fun subs out => M_break (interp_proc (f tt)) subs F).
  Proof.
    introv.
    unfold call_log_prepare; simpl.
    rewrite M_break_bind; simpl.
    apply eq_M_break; introv; tcsp.
  Qed.
  Hint Rewrite @M_break_call_log_prepare : minbft.

  Lemma M_break_call_log_commit :
    forall {A n} {O}
           (c    : Commit)
           (f    : unit -> Proc A)
           (subs : n_procs n)
           (F    : n_procs n -> A -> O),
      M_break (interp_proc (call_log_commit c f)) subs F
      = M_break (call_proc LOGname (log_new_commit_log_in c))
                subs
                (fun subs out => M_break (interp_proc (f tt)) subs F).
  Proof.
    introv.
    unfold call_log_commit; simpl.
    rewrite M_break_bind; simpl.
    apply eq_M_break; introv; tcsp.
  Qed.
  Hint Rewrite @M_break_call_log_commit : minbft.

  Lemma M_break_call_is_committed :
    forall {A n} {O}
           (c    : Commit)
           (d    : unit -> Proc A)
           (f    : unit -> Proc A)
           (subs : n_procs n)
           (F    : n_procs n -> A -> O),
      M_break (interp_proc (call_is_committed c d f)) subs F
      = M_break (call_proc LOGname (is_committed_in c))
                subs
                (fun subs out => on_log_out (fun _ => M_break (interp_proc (f tt)) subs F)
                                            (fun _ => M_break (interp_proc (d tt)) subs F)
                                            out).
  Proof.
    introv.
    unfold call_is_committed; simpl.
    rewrite M_break_bind; simpl.
    apply eq_M_break; introv; tcsp.
    destruct s; simpl; tcsp.
    destruct b; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_is_committed : minbft.

End MinBFTbreak.


Hint Rewrite @M_break_MinBFT_state_update : minbft.
Hint Rewrite @M_break_call_create_ui : minbft.
Hint Rewrite @M_break_call_verify_ui : minbft.
Hint Rewrite @M_break_call_prepare_already_in_log : minbft.
Hint Rewrite @M_break_call_prepare_already_in_log_bool : minbft.
Hint Rewrite @M_break_call_log_prepare : minbft.
Hint Rewrite @M_break_call_log_commit : minbft.
Hint Rewrite @M_break_call_is_committed : minbft.
Hint Rewrite @M_break_LOG_update : minbft.
