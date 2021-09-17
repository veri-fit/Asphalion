Require Export MinBFTbreak.
Require Export TrInc.


Section TrIncbreak.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma on_comp_MinBFTlocalSys_new :
    forall r s u l {A} (F : n_proc 2 (msg_comp_name 0) -> A) (m : A),
      on_comp (MinBFTlocalSys_new r s u l) F m
      = F (MinBFT_replicaSM_new r s).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite on_comp_MinBFTlocalSys_new : minbft.

  Lemma decr_n_procs_MinBFTlocalSys_new :
    forall r s u l,
      decr_n_procs (MinBFTlocalSys_new r s u l)
      = MinBFTsubs_new u l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite decr_n_procs_MinBFTlocalSys_new : minbft.

  Lemma M_break_USIG_update :
    forall {O} s t i subs (F : n_procs 0 -> hoption TRINC_state * USIG_output_interface  -> O),
      M_break (USIG_update s t i) subs F
      = match i with
        | create_ui_in (v,r,cid,nc) => M_break (interp_s_proc (let (s',ui) := create_TrIncUI v r cid nc s in [R](s',create_ui_out ui))) subs F
        | verify_ui_in (v,r,ui) => M_break (interp_s_proc (let b := verify_TrIncUI v r ui s in [R](s,verify_ui_out b))) subs F
        end.
  Proof.
    destruct i; repnd; introv; simpl; auto.
  Qed.
  Hint Rewrite @M_break_USIG_update : minbft.

  Lemma M_break_call_proc_USIGname_MinBFTsubs_new :
    forall {O} t i u l (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname t i)
        (MinBFTsubs_new u l)
        F
      = M_break
          (USIG_update u t i)
          (decr_n_procs (MinBFTsubs_new u l))
          (fun subs out =>
             F (bind_hop (MinBFTsubs_new u l)
                         (fun s => MinBFTsubs_new s l)
                         (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new : minbft2.

  Lemma M_break_call_proc_LOGname_MinBFTsubs_new :
    forall {O} t i u l (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname t i)
        (MinBFTsubs_new u l)
        F
      = M_break
          (LOG_update l t i)
          (decr_n_procs (MinBFTsubs_new u l))
          (fun subs out =>
             F (bind_hop (MinBFTsubs_new u l)
                         (fun s => MinBFTsubs_new u s)
                         (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new : minbft2.

  Lemma M_break_call_proc_USIGname_MinBFTsubs :
    forall {O} t i n (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname t i)
        (MinBFTsubs n)
        F
      = M_break
          (USIG_update (TRINC_initial n) t i)
          (decr_n_procs (MinBFTsubs n))
          (fun subs out =>
             F (bind_hop (MinBFTsubs n)
                        (fun s => MinBFTsubs_new_u s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs : minbft2.

  Lemma M_break_call_proc_LOGname_MinBFTsubs :
    forall {O} t i n (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname t i)
        (MinBFTsubs n)
        F
      = M_break
          (LOG_update LOG_initial t i)
          (decr_n_procs (MinBFTsubs n))
          (fun subs out =>
             F (bind_hop (MinBFTsubs n)
                        (fun s => MinBFTsubs_new_l n s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs : minbft2.

  Lemma M_break_call_proc_USIGname_MinBFTsubs_new_u :
    forall {O} t i u (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname t i)
        (MinBFTsubs_new_u u)
        F
      = M_break
          (USIG_update u t i)
          (decr_n_procs (MinBFTsubs_new_u u))
          (fun subs out =>
             F (bind_hop (MinBFTsubs_new_u u)
                        (fun s => MinBFTsubs_new_u s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new_u : minbft2.

  Lemma M_break_call_proc_LOGname_MinBFTsubs_new_u :
    forall {O} t i u (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname t i)
        (MinBFTsubs_new_u u)
        F
      = M_break
          (LOG_update LOG_initial t i)
          (decr_n_procs (MinBFTsubs_new_u u))
          (fun subs out =>
             F (bind_hop (MinBFTsubs_new_u u)
                        (fun s => MinBFTsubs_new u s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new_u : minbft2.

  Lemma M_break_call_proc_USIGname_MinBFTsubs_new_l :
    forall {O} t i n l (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname t i)
        (MinBFTsubs_new_l n l)
        F
      = M_break
          (USIG_update (TRINC_initial n) t i)
          (decr_n_procs (MinBFTsubs_new_l n l))
          (fun subs out =>
             F (bind_hop (MinBFTsubs_new_l n l)
                        (fun s => MinBFTsubs_new s l)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new_l : minbft2.

  Lemma M_break_call_proc_LOGname_MinBFTsubs_new_l :
    forall {O} t i n l (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname t i)
        (MinBFTsubs_new_l n l)
        F
      = M_break
          (LOG_update l t i)
          (decr_n_procs (MinBFTsubs_new_l n l))
          (fun subs out =>
             F (bind_hop (MinBFTsubs_new_l n l)
                        (fun s => MinBFTsubs_new_l n s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new_l : minbft2.

End TrIncbreak.


Hint Rewrite @on_comp_MinBFTlocalSys_new : minbft.
Hint Rewrite @decr_n_procs_MinBFTlocalSys_new : minbft.
Hint Rewrite @M_break_USIG_update : minbft.
Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new : minbft2.
Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new : minbft2.
Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs : minbft2.
Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs : minbft2.
Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new_u : minbft2.
Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new_u : minbft2.
Hint Rewrite @M_break_call_proc_USIGname_MinBFTsubs_new_l : minbft2.
Hint Rewrite @M_break_call_proc_LOGname_MinBFTsubs_new_l : minbft2.
