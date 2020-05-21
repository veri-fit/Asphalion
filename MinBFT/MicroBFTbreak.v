Require Export MicroBFTtacts.


Section MicroBFTbreak.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.


  Lemma on_comp_MicroBFTlocalSys_new :
    forall r s u l {A} (F : n_proc 2 (msg_comp_name 0) -> A) (m : A),
      on_comp (MicroBFTlocalSys_new r s u l) F m
      = F (MicroBFT_replicaSM_new r s).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite on_comp_MicroBFTlocalSys_new : microbft.

  Lemma decr_n_procs_MicroBFTlocalSys_new :
    forall r s u l,
      decr_n_procs (MicroBFTlocalSys_new r s u l)
      = MicroBFTsubs_new u l.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite decr_n_procs_MicroBFTlocalSys_new : microbft.

  Lemma M_break_MicroBFT_state_update :
    forall {O} r s m subs (F : n_procs 1 -> option MAIN_state * DirectedMsgs -> O),
      M_break (MAIN_update r s m) subs F
      = match m with
        | MicroBFT_request _ => M_break (interp_s_proc (handle_request r s m)) subs F
        | MicroBFT_commit  _ => M_break (interp_s_proc (handle_commit  r s m)) subs F
        | MicroBFT_accept  _ => M_break (interp_s_proc (handle_accept  r s m)) subs F
        end.
  Proof.
    destruct m; introv; simpl; auto.
  Qed.
  Hint Rewrite @M_break_MicroBFT_state_update : microbft.

  Lemma M_break_USIG_update :
    forall {O} s i subs (F : n_procs 0 -> option USIG_state * USIG_output_interface  -> O),
      M_break (USIG_update s i) subs F
      = match i with
        | create_ui_in r => M_break (interp_s_proc (let (s',ui) := create_UI r s in [R](s',create_ui_out ui))) subs F
        | verify_ui_in (r,ui) => M_break (interp_s_proc (let b := verify_UI r ui s in [R](s,verify_ui_out b))) subs F
        end.
  Proof.
    destruct i; repnd; introv; simpl; auto.
  Qed.
  Hint Rewrite @M_break_USIG_update : microbft.

  Lemma M_break_LOG_update :
    forall {O} l i subs (F : n_procs 0 -> option LOG_state * LOG_output_interface  -> O),
      M_break (LOG_update l i) subs F
      = match i with
        | log_new r => M_break (interp_s_proc (let l' :=  r :: l in [R](l',log_out true))) subs F
        end.
  Proof.
    destruct i; repnd; introv; simpl; auto.
  Qed.
  Hint Rewrite @M_break_LOG_update : microbft.

  Lemma M_break_call_proc_USIGname_MicroBFTsubs_new :
    forall {O} i u l (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname i)
        (MicroBFTsubs_new u l)
        F
      = M_break
          (USIG_update u i)
          (decr_n_procs (MicroBFTsubs_new u l))
          (fun subs out =>
             F (bind_op (MicroBFTsubs_new u l)
                        (fun s => MicroBFTsubs_new s l)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MicroBFTsubs_new : microbft2.

  Lemma M_break_call_proc_LOGname_MicroBFTsubs_new :
    forall {O} i u l (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname i)
        (MicroBFTsubs_new u l)
        F
      = M_break
          (LOG_update l i)
          (decr_n_procs (MicroBFTsubs_new u l))
          (fun subs out =>
             F (bind_op (MicroBFTsubs_new u l)
                        (fun s => MicroBFTsubs_new u s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MicroBFTsubs_new : microbft2.

  Lemma M_break_call_proc_USIGname_MicroBFTsubs :
    forall {O} i n (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname i)
        (MicroBFTsubs n)
        F
      = M_break
          (USIG_update (USIG_initial n) i)
          (decr_n_procs (MicroBFTsubs n))
          (fun subs out =>
             F (bind_op (MicroBFTsubs n)
                        (fun s => MicroBFTsubs_new_u s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MicroBFTsubs : microbft2.

  Lemma M_break_call_proc_LOGname_MicroBFTsubs :
    forall {O} i n (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname i)
        (MicroBFTsubs n)
        F
      = M_break
          (LOG_update LOG_initial i)
          (decr_n_procs (MicroBFTsubs n))
          (fun subs out =>
             F (bind_op (MicroBFTsubs n)
                        (fun s => MicroBFTsubs_new_l n s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MicroBFTsubs : microbft2.

  Lemma M_break_call_proc_USIGname_MicroBFTsubs_new_u :
    forall {O} i u (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname i)
        (MicroBFTsubs_new_u u)
        F
      = M_break
          (USIG_update u i)
          (decr_n_procs (MicroBFTsubs_new_u u))
          (fun subs out =>
             F (bind_op (MicroBFTsubs_new_u u)
                        (fun s => MicroBFTsubs_new_u s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MicroBFTsubs_new_u : microbft2.

  Lemma M_break_call_proc_LOGname_MicroBFTsubs_new_u :
    forall {O} i u (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname i)
        (MicroBFTsubs_new_u u)
        F
      = M_break
          (LOG_update LOG_initial i)
          (decr_n_procs (MicroBFTsubs_new_u u))
          (fun subs out =>
             F (bind_op (MicroBFTsubs_new_u u)
                        (fun s => MicroBFTsubs_new u s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MicroBFTsubs_new_u : microbft2.

  Lemma M_break_call_proc_USIGname_MicroBFTsubs_new_l :
    forall {O} i n l (F : n_procs 1 -> USIG_output_interface -> O),
      M_break
        (call_proc USIGname i)
        (MicroBFTsubs_new_l n l)
        F
      = M_break
          (USIG_update (USIG_initial n) i)
          (decr_n_procs (MicroBFTsubs_new_l n l))
          (fun subs out =>
             F (bind_op (MicroBFTsubs_new_l n l)
                        (fun s => MicroBFTsubs_new s l)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_USIGname_MicroBFTsubs_new_l : microbft2.

  Lemma M_break_call_proc_LOGname_MicroBFTsubs_new_l :
    forall {O} i n l (F : n_procs 1 -> LOG_output_interface -> O),
      M_break
        (call_proc LOGname i)
        (MicroBFTsubs_new_l n l)
        F
      = M_break
          (LOG_update l i)
          (decr_n_procs (MicroBFTsubs_new_l n l))
          (fun subs out =>
             F (bind_op (MicroBFTsubs_new_l n l)
                        (fun s => MicroBFTsubs_new_l n s)
                        (fst out))
               (snd out)).
  Proof.
    introv.
    simpl.
    destruct i; repnd; simpl; tcsp.
  Qed.
  Hint Rewrite @M_break_call_proc_LOGname_MicroBFTsubs_new_l : microbft2.

  Lemma M_break_call_create_ui :
    forall {A n} {O}
           (m    : nat)
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
    destruct s; simpl; auto; smash_microbft.
  Qed.
  Hint Rewrite @M_break_call_create_ui : microbft.

  Lemma M_break_call_verify_ui :
    forall {A n} {O}
           (mui  : nat * UI)
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
    destruct s; simpl; auto; smash_microbft.
  Qed.
  Hint Rewrite @M_break_call_verify_ui : microbft.

  Definition lower_out_break {n} {A} {B}
             (l : n_procs (S n))
             (F : n_procs (S n) -> A -> B) : n_procs n -> A -> B :=
    fun k a => F (update_subs l k) a.

  Lemma M_break_M_run_sm_on_input_MicroBFT_replicaSM_new :
    forall {O} r s m subs (F : n_procs 2 -> option MAIN_state * DirectedMsgs -> O),
      M_break (M_run_sm_on_input (MicroBFT_replicaSM_new r s) m) subs F
      = match m with
        | MicroBFT_request _ => M_break (interp_s_proc (handle_request r s m)) (decr_n_procs subs) (lower_out_break subs F)
        | MicroBFT_commit  _ => M_break (interp_s_proc (handle_commit  r s m)) (decr_n_procs subs) (lower_out_break subs F)
        | MicroBFT_accept  _ => M_break (interp_s_proc (handle_accept  r s m)) (decr_n_procs subs) (lower_out_break subs F)
        end.
  Proof.
    introv.
    unfold M_run_sm_on_input.
    destruct m; introv; simpl; auto;
      try (complete (unfold M_on_decr, M_break, MAIN_update;
                     simpl; repeat dest_cases w; ginv)).
  Qed.
  Hint Rewrite @M_break_M_run_sm_on_input_MicroBFT_replicaSM_new : microbft.

  Lemma state_of_component_cons_same :
    forall {cn} {n} (p : n_proc n cn) (l : n_procs n),
      state_of_component cn (MkPProc cn p :: l) = Some (sm2state p).
  Proof.
    introv; unfold state_of_component; simpl; dest_cases w; simpl.
    rewrite (UIP_refl_CompName _ w); auto.
  Qed.
  Hint Rewrite @state_of_component_cons_same : comp.

  Lemma state_of_component_USIGname :
    forall m (u : n_proc 1 USIGname) l,
      state_of_component USIGname
                         [MkPProc (msg_comp_name 0) m,
                          MkPProc USIGname u,
                          MkPProc LOGname l] = Some (sm2state u).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_component_USIGname : microbft.

  Lemma state_of_component_LOGname :
    forall m u (l : n_proc 1 LOGname),
      state_of_component LOGname
                         [MkPProc (msg_comp_name 0) m,
                          MkPProc USIGname u,
                          MkPProc LOGname l] = Some (sm2state l).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite state_of_component_LOGname : microbft.

End MicroBFTbreak.

Hint Rewrite @M_break_MicroBFT_state_update : microbft.
Hint Rewrite @M_break_call_proc_USIGname_MicroBFTsubs_new : microbft2.
Hint Rewrite @M_break_call_proc_LOGname_MicroBFTsubs_new : microbft2.
Hint Rewrite @M_break_call_proc_USIGname_MicroBFTsubs : microbft2.
Hint Rewrite @M_break_call_proc_LOGname_MicroBFTsubs : microbft2.
Hint Rewrite @M_break_call_proc_USIGname_MicroBFTsubs_new_u : microbft2.
Hint Rewrite @M_break_call_proc_LOGname_MicroBFTsubs_new_u : microbft2.
Hint Rewrite @M_break_call_proc_USIGname_MicroBFTsubs_new_l : microbft2.
Hint Rewrite @M_break_call_proc_LOGname_MicroBFTsubs_new_l : microbft2.
Hint Rewrite @M_break_call_create_ui : microbft.
Hint Rewrite @M_break_call_verify_ui : microbft.
Hint Rewrite @M_break_USIG_update : microbft.
Hint Rewrite @M_break_LOG_update : microbft.
Hint Rewrite @M_break_M_run_sm_on_input_MicroBFT_replicaSM_new : microbft.
Hint Rewrite @on_comp_MicroBFTlocalSys_new : microbft.
Hint Rewrite @decr_n_procs_MicroBFTlocalSys_new : microbft.
Hint Rewrite @state_of_component_USIGname : microbft.
Hint Rewrite @state_of_component_LOGname : microbft.


Hint Rewrite @state_of_component_cons_same : comp.
