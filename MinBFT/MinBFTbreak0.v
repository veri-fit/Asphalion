Require Export MinBFTbreak.
Require Export MinBFT.


Section MinBFTbreak0.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Lemma M_break_USIG_update :
    forall {O} s i subs (F : n_procs 0 -> option USIG_state * USIG_output_interface  -> O),
      M_break (USIG_update s i) subs F
      = match i with
        | create_ui_in (v,r,_,_) => M_break (interp_s_proc (let (s',ui) := create_UI v r s in [R](s',create_ui_out (Some ui)))) subs F
        | verify_ui_in (v,r,ui) => M_break (interp_s_proc (let b := verify_UI v r ui s in [R](s,verify_ui_out b))) subs F
        end.
  Proof.
    destruct i; repnd; introv; simpl; auto.
  Qed.
  Hint Rewrite @M_break_USIG_update : minbft.

  Lemma M_break_call_proc_USIGname_MinBFTsubs_new :
    forall {O} i u l (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname i)
        (MinBFTsubs_new u l)
        F
      = M_break
          (USIG_update u i)
          (decr_n_procs (MinBFTsubs_new u l))
          (fun subs out =>
             F (bind_op (MinBFTsubs_new u l)
                        (fun s => replace_subs (MinBFTsubs_new s l) subs)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new : minbft2.

  Lemma M_break_call_proc_LOGname_MinBFTsubs_new :
    forall {O} i u l (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname i)
        (MinBFTsubs_new u l)
        F
      = M_break
          (LOG_update l i)
          (decr_n_procs (MinBFTsubs_new u l))
          (fun subs out =>
             F (bind_op (MinBFTsubs_new u l)
                        (fun s => replace_subs (MinBFTsubs_new u s) subs)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new : minbft2.

  Lemma M_break_call_proc_USIGname_MinBFTsubs :
    forall {O} i n (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname i)
        (MinBFTsubs n)
        F
      = M_break
          (USIG_update (USIG_initial n) i)
          (decr_n_procs (MinBFTsubs n))
          (fun subs out =>
             F (bind_op (MinBFTsubs n)
                        (fun s => replace_subs (MinBFTsubs_new_u s) subs)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs : minbft2.

  Lemma M_break_call_proc_LOGname_MinBFTsubs :
    forall {O} i n (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname i)
        (MinBFTsubs n)
        F
      = M_break
          (LOG_update LOG_initial i)
          (decr_n_procs (MinBFTsubs n))
          (fun subs out =>
             F (bind_op (MinBFTsubs n)
                        (fun s => replace_subs (MinBFTsubs_new_l n s) subs)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs : minbft2.

  Lemma M_break_call_proc_USIGname_MinBFTsubs_new_u :
    forall {O} i u (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname i)
        (MinBFTsubs_new_u u)
        F
      = M_break
          (USIG_update u i)
          (decr_n_procs (MinBFTsubs_new_u u))
          (fun subs out =>
             F (bind_op (MinBFTsubs_new_u u)
                        (fun s => replace_subs (MinBFTsubs_new_u s) subs)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new_u : minbft2.

  Lemma M_break_call_proc_LOGname_MinBFTsubs_new_u :
    forall {O} i u (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname i)
        (MinBFTsubs_new_u u)
        F
      = M_break
          (LOG_update LOG_initial i)
          (decr_n_procs (MinBFTsubs_new_u u))
          (fun subs out =>
             F (bind_op (MinBFTsubs_new_u u)
                        (fun s => replace_subs (MinBFTsubs_new u s) subs)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new_u : minbft2.

  Lemma M_break_call_proc_USIGname_MinBFTsubs_new_l :
    forall {O} i n l (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname i)
        (MinBFTsubs_new_l n l)
        F
      = M_break
          (USIG_update (USIG_initial n) i)
          (decr_n_procs (MinBFTsubs_new_l n l))
          (fun subs out =>
             F (bind_op (MinBFTsubs_new_l n l)
                        (fun s => replace_subs (MinBFTsubs_new s l) subs)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new_l : minbft2.

  Lemma M_break_call_proc_LOGname_MinBFTsubs_new_l :
    forall {O} i n l (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname i)
        (MinBFTsubs_new_l n l)
        F
      = M_break
          (LOG_update l i)
          (decr_n_procs (MinBFTsubs_new_l n l))
          (fun subs out =>
             F (bind_op (MinBFTsubs_new_l n l)
                        (fun s => replace_subs (MinBFTsubs_new_l n s) subs)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new_l : minbft2.

End MinBFTbreak0.


Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new : minbft2.
Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new : minbft2.
Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs : minbft2.
Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs : minbft2.
Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new_u : minbft2.
Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new_u : minbft2.
Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new_l : minbft2.
Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new_l : minbft2.
Hint Rewrite @M_break_USIG_update : minbft.
