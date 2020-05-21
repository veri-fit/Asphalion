(* TRINC instance *)

Require Export MinBFTprops0.
Require Export TrIncsubs.
Require Export TrIncbreak.
Require Export TrIncstate.


Section TrIncview.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.


  Lemma preserves_view_step0 :
    forall {eo : EventOrdering} (e : Event) r s1 s2 su sl ls,
      M_run_ls_on_this_one_event (MinBFTlocalSys_new r s1 su sl) e = Some ls
      -> state_of_component MAINname ls = Some s2
      -> current_view s1 = current_view s2.
  Proof.
    introv h eqst.
    apply map_option_Some in h; exrepnd; simpl in *; rev_Some; minbft_simp.
    unfold M_run_ls_on_input_ls, M_run_ls_on_input in *.
    autorewrite with comp minbft in *.

    Time minbft_dest_msg Case;
      repeat (simpl in *; autorewrite with minbft comp in * ;
                smash_minbft2; simpl in *; ginv).
  Qed.

  Lemma preserves_view_step1 :
    forall {eo : EventOrdering} (e : Event) s1 s2,
      is_replica e
      -> M_state_sys_before_event MinBFTsys e MAINname = Some s1
      -> M_state_sys_on_event MinBFTsys e MAINname = Some s2
      -> current_view s1 = current_view s2.
  Proof.
    introv isr h q.
    unfold is_replica in isr; exrepnd.
    unfold M_state_sys_before_event in h; simpl in h.
    unfold M_state_sys_on_event in q; simpl in q.
    rewrite isr0 in h; rewrite isr0 in q; simpl in *.
    apply map_option_Some in h; exrepnd.
    apply map_option_Some in q; exrepnd.
    symmetry in h0.
    symmetry in q0.

    rewrite M_run_ls_on_event_unroll in q1.
    rewrite h1 in q1; simpl in q1.

    applydup M_run_ls_before_event_ls_is_minbft in h1; exrepnd; subst; simpl in *; ginv.
    autorewrite with minbft in *; minbft_simp.

    destruct (dec_isFirst e) as [d|d];
      eapply preserves_view_step0 in q1; eauto;[].

    rewrite M_run_ls_before_event_is_first in h1; auto.
    rewrite MinBFTlocalSys_as_new in h1.

    apply eq_Some in h1.
    apply eq_MinBFTlocalSys_newP_implies in h1; repnd; subst; simpl in *.
    apply MinBFTsubs_new_inj in h1; repnd; subst; simpl in *; auto.
  Qed.

  Lemma preserves_view_step :
    forall {eo : EventOrdering}
           (e1 e2 : Event)
           (s1 s2 : MAIN_state),
      is_replica e2
      -> e1 ⊂ e2
      -> M_state_sys_on_event MinBFTsys e1 MAINname = Some s1
      -> M_state_sys_on_event MinBFTsys e2 MAINname = Some s2
      -> current_view s1 = current_view s2.
  Proof.
    introv isr lte eqst1 eqst2.
    applydup pred_implies_local_pred in lte.
    subst.
    rewrite <- M_state_sys_before_event_as_M_state_sys_on_event_pred in eqst1; eauto 3 with eo.
    eapply preserves_view_step1; eauto.
  Qed.

  Lemma preserves_view :
    forall {eo : EventOrdering}
           (e1 e2 : Event)
           (s1 s2 : MAIN_state),
      is_replica e2
      -> M_state_sys_on_event MinBFTsys e1 MAINname = Some s1
      -> M_state_sys_on_event MinBFTsys e2 MAINname = Some s2
      -> e1 ⊑ e2
      -> current_view s1 = current_view s2.
  Proof.
    intros eo e1 e2; revert e1.
    induction e2 as [e2 ind] using predHappenedBeforeInd;[]; introv isrep eqst1 eqst2 lte.

    apply localHappenedBeforeLe_implies_or2 in lte; repndors; subst; tcsp;[|].

    { rewrite eqst1 in eqst2; ginv. }

    apply local_implies_pred_or_local in lte; repndors; exrepnd.

    {
      dup lte as lte'.
      eapply (@M_state_sys_before_event_if_on_event_direct_pred _ _ _ _ _ _ _ _ MAINname) in lte;[|eauto].
      eapply preserves_view_step; eauto.
    }

    pose proof (M_state_sys_on_event_some_between e e2 MinBFTsys MAINname s2) as q.
    repeat (autodimp q hyp); eauto 3 with eo minbft comp;[].
    exrepnd.

    pose proof (ind e lte1 e1 s1 s') as ind; repeat (autodimp ind hyp); eauto 3 with eo minbft comp.
    pose proof (preserves_view_step e e2 s' s2) as q; repeat (autodimp q hyp); try congruence.
  Qed.

  Lemma preserves_view_init :
    forall {eo : EventOrdering} (e : Event) s,
      is_replica e
      -> M_state_sys_on_event MinBFTsys e MAINname = Some s
      -> current_view s = initial_view.
  Proof.
    introv isr h.
    unfold is_replica in isr; exrepnd.
    unfold M_state_sys_on_event in h; simpl in h.
    rewrite isr0 in h; simpl in h.
    apply map_option_Some in h; exrepnd.
    symmetry in h0.

    revert dependent a.
    revert dependent s.
    clear isr0.

    induction e as [e ind] using predHappenedBeforeInd;[]; introv h eqst.
    rewrite M_run_ls_on_event_unroll in h.
    destruct (dec_isFirst e) as [d|d].

    { rewrite MinBFTlocalSys_as_new in h.
      eapply preserves_view_step0 in h; eauto. }

    rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred in h; auto.
    apply map_option_Some in h; exrepnd.
    symmetry in h0.

    applydup M_run_ls_on_event_ls_is_minbft in h1; exrepnd; subst.

    eapply preserves_view_step0 in h0; eauto.
    eapply ind in h1; simpl; try reflexivity; eauto 3 with eo;
      simpl in *; try congruence.
  Qed.

  Lemma preserves_view_init_ls :
    forall {eo : EventOrdering} (e : Event) i j s s1 s2,
      loc e = MinBFT_replica i
      -> M_run_ls_on_event (MinBFTlocalSys i) e = Some (MinBFTlocalSys_new j s s1 s2)
      -> current_view s = initial_view.
  Proof.
    introv isr h.
    eapply (preserves_view_init e); auto; try (complete (eexists; eauto)).
    unfold M_state_sys_on_event.
    unfold M_state_ls_on_event.
    rewrite isr; simpl.
    rewrite h; simpl; auto.
  Qed.

End TrIncview.
