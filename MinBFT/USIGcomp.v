Require Export MinBFTg.


Section USIGcomp.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : DTimeContext }.

  Context { minbft_context : MinBFT_context }.
  Context { m_initial_keys : MinBFT_initial_keys }.
  Context { u_initial_keys : USIG_initial_keys }.

  Context { usig_hash : USIG_hash }.

  Context { minbft_auth : MinBFT_auth }.


  Global Instance USIG_trusted_info : TrustedInfo :=
    MkTrustedInfo USIG_state.

  (* ===============================================================
     USIG UPDATE & SM
     =============================================================== *)

  Definition USIG_update : M_Update 0 USIGname _ :=
    fun (s : USIG_state) (m : USIG_input_interface) =>
      interp_s_proc
        (match m with
         | create_ui_in (v,r) =>
           let (s', ui) := create_UI v r s in
           [R] (s', create_ui_out ui)
         | verify_ui_in (v,r,ui) =>
           let b := verify_UI v r ui s in
           [R] (s, verify_ui_out b)
         end).

  (* (1) USIG and TrInc will have the same IO interface, but different states
     (2) add a new field to CompName to allow differentiating those states
     (3) call_proc will only look at the old CompName, without the new field
     (4) write a wrapper around TrInc's interface, which is slightly different
     (5) Parametrize UI in MinBFT
     (6) Move this elsewhere (to where all interfaces and states have been defined)
   *)
  Definition USIG_comp (r : Rep) : M_StateMachine 1 USIGname :=
    build_m_sm USIG_update (USIG_initial r).


  Definition MinBFTsubs (n : Rep) : n_procs _ :=
    [
      MkPProc USIGname (USIG_comp n),
      MkPProc LOGname LOG_comp
    ].

  Definition MinBFTsubs_new (s1 : USIG_state) (s2 : LOG_state) : n_procs _ :=
    [
      MkPProc USIGname (build_m_sm USIG_update s1),
      MkPProc LOGname  (build_m_sm LOG_update s2)
    ].

  Definition MinBFTsubs_new_u (u : USIG_state) : n_procs _ :=
    [
      MkPProc USIGname (build_m_sm USIG_update u),
      MkPProc LOGname  LOG_comp
    ].

  Definition MinBFTsubs_new_l n (l : LOG_state) : n_procs _ :=
    [
      MkPProc USIGname (USIG_comp n),
      MkPProc LOGname  (build_m_sm LOG_update l)
    ].

  Definition MinBFTlocalSys (n : Rep) : MinBFTls :=
    MkLocalSystem
      (MAIN_comp n)
      (MinBFTsubs n).

  Definition MinBFTlocalSys_new
             (n  : Rep)
             (s  : MAIN_state)
             (s1 : USIG_state)
             (s2 : LOG_state) : MinBFTls :=
    MkLocalSystem
      (MinBFT_replicaSM_new n s)
      (MinBFTsubs_new s1 s2).

  Definition MinBFTsys : M_USystem MinBFTfunLevelSpace (*name -> M_StateMachine 2 msg_comp_name*) :=
    fun name =>
      match name with
      | MinBFT_replica n => MinBFTlocalSys n
      | _ => unit_ls
      end.

  Lemma MinBFTsubs_new_inj :
    forall a b c d,
      MinBFTsubs_new a b = MinBFTsubs_new c d
      -> a = c /\ b = d.
  Proof.
    introv h.
    repeat (apply eq_cons in h; repnd); GC.
    apply decomp_p_nproc in h0.
    apply decomp_p_nproc in h1.
    inversion h0; inversion h1; subst; simpl in *; auto.
  Qed.

  Lemma MinBFTlocalSys_new_inj :
    forall a1 a2 b1 b2 c1 c2 d1 d2,
      MinBFTlocalSys_new a1 b1 c1 d1 = MinBFTlocalSys_new a2 b2 c2 d2
      -> b1 = b2 /\ c1 = c2 /\ d1 = d2.
  Proof.
    introv h.
    apply decomp_LocalSystem in h; repnd; simpl in *.
    apply MinBFTsubs_new_inj in h; repnd; subst.
    inversion h0; subst; simpl in *; tcsp.
  Qed.

  Lemma MinBFTlocalSys_as_new :
    forall (r  : Rep),
      MinBFTlocalSys r
      = MinBFTlocalSys_new
          r
          (initial_state r)
          (USIG_initial r)
          LOG_initial.
  Proof.
    introv; eauto.
  Qed.

  Definition USIGlocalSys (s : USIG_state) : LocalSystem _ _  :=
    MkLocalSystem (build_mp_sm USIG_update s) [].

End USIGcomp.
