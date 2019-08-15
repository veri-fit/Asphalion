Require Export MinBFTkn0.
Require Export TrInc.
Require Export TrInctacs.
Require Export ComponentAxiom.
Require Export CalculusSM.


Hint Resolve equal_hash_data_implies_equal_request_data : minbft minbft2.


Section TrInckn.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.



  (* === INSTANTIATION OF ComponentAuth === *)

  Definition MinBFT_ca_create (eo : EventOrdering) (e : Event) (a : MinBFT_Bare_Msg) : list MinBFT_digest :=
    match a with
    | MinBFT_msg_bare_request r => []
    | MinBFT_msg_bare_reply r => []   (*FIX: check *)
    | MinBFT_msg_bare_prepare bp pui =>
      match M_byz_state_sys_before_event_of_trusted MinBFTsys e with
      | Some u =>
        let view := bare_prepare_v bp in
        let msg  := bare_prepare_m bp in
        let newc := S (getCounter cid0 (trinc_counters u)) in
        match snd (create_TrIncUI view msg cid0 newc u) with
        | Some ui => [ui2digest ui]
        | None => []
        end
      | None => []
      end
    | MinBFT_msg_bare_commit  bc pui =>
      match M_byz_state_sys_before_event_of_trusted MinBFTsys e with
      | Some u =>
        let view := bare_commit_v bc in
        let msg  := bare_commit_m bc in
        let newc := S (getCounter cid0 (trinc_counters u)) in
        match snd (create_TrIncUI view msg cid0 newc u) with
        | Some ui => [ui2digest ui]
        | None => []
        end
      | None => []
      end
    end.

  Definition MinBFT_ca_verify (eo : EventOrdering) (e : Event) (a : AuthenticatedData) : bool :=
    match a with
    | MkAuthData (MinBFT_msg_bare_prepare bp pui) [d] =>
      match M_byz_state_sys_before_event_of_trusted MinBFTsys e with
      | Some u =>
        verify_TrIncUI (bare_prepare_v bp) (bare_prepare_m bp) (Build_UI pui d) u
      | None => false
      end

    | MkAuthData (MinBFT_msg_bare_commit bc pui) [d] =>
      match M_byz_state_sys_before_event_of_trusted MinBFTsys e with
      | Some u =>
        (verify_TrIncUI (bare_commit_v bc) (bare_commit_m bc) (Build_UI pui d) u)
          && (verify_TrIncUI (bare_commit_v bc) (bare_commit_m bc) (bare_commit_ui bc) u)
      | None => false
      end

    | _ => false
    end.

  Global Instance MinBFT_I_ComponentAuth : ComponentAuth :=
    MkComponentAuth
      MinBFT_ca_create
      MinBFT_ca_verify.

  (* === ======================== === *)




  (* === INSTANTIATION OF KnowledgeComponents === *)

  Lemma minbft_data_ui_inj : injective minbft_data_ui.
  Proof.
    introv h; inversion h; auto.
  Qed.

  Definition data2hdata (d : MinBFT_data) : option HashData :=
    match d with
(*    | minbft_data_prepare (prepare (bare_prepare v r) ui) => Some (Build_HashData v (request_b r) (ui_pre ui))
    | minbft_data_commit (commit (bare_commit v r uip) ui) => Some (Build_HashData v (request_b r) (ui_pre ui))
    | minbft_data_hdata hd => Some hd*)
    | minbft_data_rdata rd => Some (RequestData2HashData rd)
    | minbft_data_ui _ => None
    end.

  Definition hash_data2id (h : HashData) : Rep :=
    pre_ui_rid (hd_pre h).

  Definition MinBFT_data2owner (d : MinBFT_data) : option node_type :=
    match d with
(*    | minbft_data_prepare p => Some (prepare2sender p)
    | minbft_data_commit c => Some (commit2sender_j c)
    | minbft_data_hdata hd => Some (hash_data2id hd)*)
    | minbft_data_rdata rd => Some (request_data2rep rd)
    | minbft_data_ui ui => Some (ui2rep ui)
    end.

  Definition MinBFT_data2ui (d : MinBFT_data) : UI :=
    match d with
    | minbft_data_rdata rd => request_data2ui rd
    | minbft_data_ui ui => ui
    end.

  Definition MinBFT_data2trust (d : MinBFT_data) : list UI :=
    [MinBFT_data2ui d].

  Lemma MinBFT_data2trust_correct : forall t, In t (MinBFT_data2trust (minbft_data_ui t)).
  Proof.
    introv; simpl; tcsp.
  Qed.

  Lemma MinBFT_auth2trust_correct :
    forall a t,
      In t (auth_data2ui a)
      <-> exists d, In t (MinBFT_data2trust d) /\ In d (MinBFT_auth2data a).
  Proof.
    introv.
    destruct a as [ad tok], ad; simpl; tcsp; split; intro h; exrepnd; tcsp.

    { repeat (destruct tok; simpl in *; tcsp).
      repndors; subst; tcsp.
      exists (minbft_data_ui (Build_UI pui t0)); simpl; tcsp. }

    { repeat (destruct tok; simpl in *; tcsp).
      repndors; subst; tcsp.
      destruct p; simpl in *; repndors; subst; tcsp. }

    { repeat (destruct tok; simpl in *; tcsp).
      repndors; subst; tcsp.

      { exists (minbft_data_ui (bare_commit_ui c)); simpl; tcsp. }

      { exists (minbft_data_ui (Build_UI pui t0)); simpl; tcsp. } }

    { repeat (destruct tok; simpl in *; tcsp).
      repndors; subst; tcsp; simpl in *; repndors; subst; tcsp;
        destruct c; simpl in *; repndors; subst; tcsp. }
  Qed.


  Definition generated_for (d : MinBFT_data) (ui : UI) :=
    MinBFT_data2ui d = ui
    /\ forall hd,
      data2hdata d = Some hd
      -> exists r,
        verify_hash_usig hd (ui2digest ui) (usig_initial_keys (MinBFT_replica r)) = true.
  (* We're currently only ever using the same keys in all USIGs *)

  Definition similar_data (d1 d2 : MinBFT_data) : Prop :=
    match d1, d2 with
    | minbft_data_rdata _, minbft_data_rdata _ => True
    | minbft_data_ui _, minbft_data_ui _ => True
    | _, _ => False
    end.

  (* MOVE to USIG *)
  Parameter collision_resistant_verif :
    forall (hd1 hd2 : HashData) (d : MinBFT_digest) (r1 r2 : Rep),
      verify_hash_usig hd1 d (usig_initial_keys r1) = true
      -> verify_hash_usig hd2 d (usig_initial_keys (MinBFT_replica r2)) = true
      -> hd1 = hd2.

  Lemma collision_resistant :
    forall (ui : UI) (d1 d2 : MinBFT_data),
      generated_for d1 ui -> generated_for d2 ui -> similar_data d1 d2 -> d1 = d2.
  Proof.
    introv h q sim.
    unfold generated_for in *; exrepnd; subst.
    destruct d1 as [r1|u1], d2 as [r2|u2]; simpl in *; subst; tcsp.
    pose proof (q (RequestData2HashData r2)) as q; autodimp q hyp.
    pose proof (h (RequestData2HashData r1)) as h; autodimp h hyp.
    exrepnd.
    eapply collision_resistant_verif in h0; try exact q1; ginv; eauto 3 with minbft.
  Qed.

  Lemma same_ui2owner :
    forall (t : UI), MinBFT_data2owner (minbft_data_ui t) = Some (ui2rep t).
  Proof.
    tcsp.
  Qed.

  Definition MinBFT_data_in_log (d : MinBFT_data) (l : LOG_state) :=
    match d with
(*    | minbft_data_prepare p  => prepare_already_in_log p l
    | minbft_data_commit  c  => prepare_already_in_log (commit2prepare c) l
    | minbft_data_hdata   hd => hash_data_in_log hd l*)
    | minbft_data_rdata   rd => request_data_in_log rd l
    | minbft_data_ui      ui => ui_in_log ui l
    end.

  Definition MinBFT_data_knows (d : MinBFT_data) (l : LOG_state) : Prop :=
    MinBFT_data_in_log d l = true.

  Lemma MinBFT_data_knows_dec : forall (d : MinBFT_data) (m : LOG_state), decidable (MinBFT_data_knows d m).
  Proof.
    introv.
    unfold MinBFT_data_knows.
    destruct (MinBFT_data_in_log d m); prove_dec.
  Defined.

  Lemma no_initial_memory :
    forall n i, on_state_of_component LOGname (MinBFTsys n) (fun s => ~ MinBFT_data_knows i s).
  Proof.
    introv.
    unfold on_state_of_component; simpl.
    destruct n; simpl; auto.
    intro h.
    unfold MinBFT_data_knows in h; simpl in *.
    destruct i; simpl in *; ginv.
  Qed.

  Lemma ui_characterization :
    forall t1 t2,
      ui2counter t1 = ui2counter t2
      -> ui2rep t1 = ui2rep t2
      -> ui2cid t1 = ui2cid t2
      -> ui2digest t1 = ui2digest t2
      -> t1 = t2.
  Proof.
    introv h q w z.
    destruct t1 as [p1 d1], t2 as [p2 d2], p1, p2; simpl in *.
    unfold ui2counter, ui2rep, ui2cid in *; simpl in *; subst; tcsp.
  Qed.

  Definition MinBFTmsg2data (m : MinBFT_msg) : list MinBFT_data :=
    match m with
    | MinBFT_request _ => []
    | MinBFT_reply _   => []
    | MinBFT_prepare p => [minbft_data_ui (prepare_ui p), minbft_data_rdata (prepare2request_data p)]
    | MinBFT_commit  c => [minbft_data_ui (commit_uj c),  minbft_data_rdata (commit2request_data_j c)]
    | MinBFT_accept  _ => []
    | MinBFT_debug   _ => []
    end.

  Lemma lt_transitive : transitive _ lt.
  Proof.
    introv; omega.
  Qed.

  Lemma lt_antireflexive : antireflexive lt.
  Proof.
    introv; omega.
  Qed.

  Definition nats := list nat.

  Fixpoint all_zeros (l : nats) :=
    match l with
    | [] => True
    | 0 :: l => all_zeros l
    | _ => False
    end.

  Fixpoint les (l1 l2 : nats) :=
    match l1, l2 with
    | [], _ => True
    | l, [] => all_zeros l
    | a1 :: k1, a2 :: k2 => a1 <= a2 /\ les k1 k2
    end.

  Fixpoint lts (l1 l2 : nats) :=
    match l1, l2 with
    | [], l => ~ all_zeros l
    | l, [] => False
    | a1 :: k1, a2 :: k2 =>
      (a1 < a2 /\ les k1 k2)
      \/ (a1 = a2 /\ lts k1 k2)
    end.


  Lemma lts_implies_not_all_zeros_right :
    forall a b,
      lts a b
      -> ~ all_zeros b.
  Proof.
    induction a; introv h; simpl in *; tcsp.
    destruct b; simpl in *; tcsp.
    repndors; repnd; subst; tcsp; GC.
    { destruct n; simpl in *; tcsp. }
    { destruct n; simpl in *; tcsp; eauto. }
  Qed.
  Hint Resolve lts_implies_not_all_zeros_right : minbft.

  Lemma all_zeros_implies_les_left :
    forall a b,
      all_zeros a
      -> les a b.
  Proof.
    induction a; introv h; simpl in *; tcsp.
    destruct a; simpl in *; tcsp.
    destruct b; simpl in *; tcsp.
    dands; try omega; eauto.
  Qed.
  Hint Resolve all_zeros_implies_les_left : minbft.

  Lemma les_preserves_all_zeros_left :
    forall a b,
      les a b
      -> all_zeros b
      -> all_zeros a.
  Proof.
    induction a; introv h q; simpl in *; tcsp.
    destruct a; simpl in *; tcsp.
    { destruct b; simpl in *; repnd; tcsp.
      destruct n; simpl in *; repnd; tcsp; eauto. }
    { destruct b; simpl in *; repnd; tcsp.
      destruct n; simpl in *; repnd; tcsp; eauto; try omega. }
  Qed.
  Hint Resolve les_preserves_all_zeros_left : minbft.

  Lemma les_transitive : transitive _ les.
  Proof.
    intros x; induction x; introv h q; simpl in *; auto; eauto 3 with minbft.
    destruct y; simpl in *; repnd; tcsp;
      destruct z; simpl in *; repnd; tcsp; GC.
    { destruct a; simpl in *; tcsp; dands; try omega; eauto 3 with minbft. }
    { destruct n; simpl in *; tcsp.
      destruct a; simpl in *; tcsp; eauto 3 with minbft; try omega. }
    { dands; try omega; eauto. }
  Qed.

  Lemma lts_implies_les : forall x y, lts x y -> les x y.
  Proof.
    induction x; introv h; simpl in *; auto; eauto 3 with minbft.
    destruct y; simpl in *; tcsp.
    repndors; repnd; subst; tcsp.
    dands; try omega; auto.
  Qed.
  Hint Resolve lts_implies_les : minbft.

  Lemma lts_les_transitive : forall x y z, lts x y -> les y z -> lts x z.
  Proof.
    induction x; introv h q; simpl in *; auto; eauto 3 with minbft.
    { intro xx; destruct h; eauto 3 with minbft. }
    { destruct y; simpl in *; tcsp.
      destruct z; simpl in *; tcsp.
      { destruct n; simpl in *; tcsp.
        repndors; repnd; subst; GC; tcsp.
        apply lts_implies_not_all_zeros_right in h; tcsp. }
      { repndors; repnd; subst; GC; tcsp.
        { left; dands; eauto; try omega.
          eapply les_transitive; eauto. }
        { apply le_lt_or_eq in q0; repndors; subst; tcsp.
          { left; dands; tcsp; eauto 3 with minbft. }
          { right; dands; eauto. } } } }
  Qed.

  Lemma not_all_zeros_right_implies_lts :
    forall x y,
      all_zeros x
      -> ~ all_zeros y
      -> lts x y.
  Proof.
    induction x; introv h q; simpl in *; tcsp.
    destruct a; simpl in *; tcsp.
    destruct y; simpl in *; tcsp.
    destruct n; simpl in *; tcsp; GC.
    left; dands; eauto; try omega; eauto 3 with minbft.
  Qed.
  Hint Resolve not_all_zeros_right_implies_lts : minbft.

  Lemma les_lts_transitive : forall x y z, les x y -> lts y z -> lts x z.
  Proof.
    induction x; introv h q; simpl in *; auto; eauto 3 with minbft.
    destruct y; simpl in *; tcsp.

    { destruct a; simpl in *; tcsp.
      destruct z; simpl in *; tcsp.
      destruct n; simpl in *; tcsp.
      { right; dands; eauto 3 with minbft. }
      { left; dands; eauto 3 with minbft; try omega. } }

    { destruct z; simpl in *; repnd; tcsp.
      repndors; repnd; subst; GC; tcsp.
      { left; dands; eauto with minbft; try omega.
        eapply les_transitive; eauto. }
      { apply le_lt_or_eq in h0; repndors; subst; tcsp.
        { left; dands; tcsp; eauto 3 with minbft. }
        { right; dands; eauto. } } }
  Qed.

  Lemma lts_transitive : transitive _ lts.
  Proof.
    intros x; induction x; introv h q; simpl in *; auto; eauto 3 with minbft.
    destruct y; simpl in *; repnd; tcsp.
    destruct z; simpl in *; repnd; tcsp.
    repndors; repnd; subst; GC; tcsp; eauto.
    { left; dands; try omega.
      eapply les_transitive; eauto. }
    { left; dands; auto.
      apply lts_implies_les.
      eapply lts_les_transitive; eauto. }
    { left; dands; auto.
      apply lts_implies_les.
      eapply les_lts_transitive; eauto. }
  Qed.

  Lemma les_reflexive : reflexive _ les.
  Proof.
    intros x; induction x; simpl in *; tcsp.
  Qed.

  Lemma lts_antireflexive : antireflexive lts.
  Proof.
    intros x; induction x; introv h; simpl in *; tcsp.
    repndors; repnd; tcsp; try omega.
  Qed.

  Definition ui_has_counter (ui : UI) (l : nats) :=
    getCounter (ui2cid ui) l = ui2counter ui.

  Lemma all_zeros_implies_nth_le :
    forall cid a,
      all_zeros a
      -> nth cid a 0 <= 0.
  Proof.
    induction cid; introv h; simpl in *; destruct a; simpl in *; tcsp;
      destruct n; simpl in *; tcsp.
  Qed.
  Hint Resolve all_zeros_implies_nth_le : minbft.

  Lemma les_preserves_nth :
    forall a b cid,
      les a b
      -> nth cid a 0 <= nth cid b 0.
  Proof.
    induction a; introv h; simpl in *; tcsp; GC.

    { destruct cid; simpl in *; tcsp; omega. }

    { destruct b; simpl in *; tcsp;
        destruct cid; simpl in *; tcsp;
          destruct a; simpl in *; tcsp;
            eauto 3 with minbft. }
  Qed.
  Hint Resolve les_preserves_nth : minbft.

  Lemma lts_preserves_getCounter :
    forall a cid b i,
      getCounter cid a = i
      -> lts a b
      -> exists j,
          getCounter cid b = j /\ i <= j.
  Proof.
    unfold getCounter.
    induction a; introv h q; simpl in *.

    { destruct cid; subst; simpl in *; tcsp;
        eexists; dands; try reflexivity; eauto; try omega. }

    { destruct cid; simpl in *; subst; tcsp.

      { destruct b; simpl in *; tcsp.
        repndors; repnd; subst; tcsp; exists n; dands; auto; try omega. }

      { destruct b; simpl in *; tcsp.
        repndors; repnd; subst; tcsp.
        eexists; dands; eauto 3 with minbft. } }
  Qed.

  Lemma ui_has_counter_pres :
    forall t a b c,
      ui_has_counter t a
      -> ui_has_counter t c
      -> (lts a b \/ a = b)
      -> (lts b c \/ b = c)
      -> ui_has_counter t b.
  Proof.
    introv hca hcb h q.
    unfold ui_has_counter in *.
    repndors; subst; tcsp.
    eapply lts_preserves_getCounter in h; eauto; exrepnd.
    eapply lts_preserves_getCounter in q; eauto; exrepnd.
    try omega.
  Qed.

  Definition similar_ui (ui1 ui2 : UI) : Prop :=
    ui2cid ui1 = ui2cid ui2.

  Lemma similar_ui_equivalence : equivalence _ similar_ui.
  Proof.
    split; introv; tcsp; unfold similar_ui; try congruence.
  Qed.

  Lemma similar_ui_pres :
    forall t t' a b,
      ui_has_counter t a
      -> ui_has_counter t b
      -> similar_ui t t'
      -> ui_has_counter t' a
      -> ui_has_counter t' b.
  Proof.
    introv hca hcb sim hcc.
    unfold ui_has_counter, similar_ui in *; try congruence.
  Qed.

  Definition init_counter : nats := [].

  Lemma init_counter_cond :
    forall n : node_type,
    exists m,
      state_of_trusted_in_ls (MinBFTsys (node2name n)) = Some m
      /\ trinc_counters m = init_counter.
  Proof.
    introv; simpl.
    unfold state_of_trusted_in_ls, state_of_trusted; simpl.
    eexists; dands; eauto.
  Qed.

  Global Instance MinBFT_I_KnowledgeComponents : KnowledgeComponents :=
    MkKnowledgeComponents
      MinBFT_data
      minbft_data_ui
      minbft_data_ui_inj
      generated_for
      similar_data
      collision_resistant
      MinBFT_data2owner
      same_ui2owner
      MinBFT_auth2data
      MinBFT_data2trust
      MinBFT_data2trust_correct
      MinBFT_auth2trust_correct
      LOGname
      MinBFT_data_knows
      MinBFT_data_knows_dec
      MinBFTfunLevelSpace
      MinBFTsys
      no_initial_memory
      MinBFTmsg2data
      nats
      lts
      lts_transitive
      lts_antireflexive
      ui_has_counter
      ui_has_counter_pres
      similar_ui
      similar_ui_equivalence
      similar_ui_pres
      trinc_counters
      init_counter
      init_counter_cond.

  (* === ======================== === *)

End TrInckn.
