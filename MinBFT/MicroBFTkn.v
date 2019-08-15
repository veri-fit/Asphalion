Require Export MicroBFT.
Require Export MicroBFTtacts.
Require Export ComponentAxiom.
Require Export CalculusSM.



Section MicroBFTkn.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext          }.
  Context { microbft_context    : MicroBFT_context      }.
  Context { m_initial_keys      : MicroBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys     }.
  Context { usig_hash           : USIG_hash             }.
  Context { microbft_auth       : MicroBFT_auth         }.



  (* === INSTANTIATION OF ComponentTrust === *)

  Definition auth_data2ui (a : AuthenticatedData) : list UI :=
    match a with
    | MkAuthData (MicroBFT_msg_bare_request _ pui) [d] => [Build_UI pui d]
    | _ => []
    end.

  Definition USIG_output_interface2ui (o : USIG_output_interface) : option UI :=
    match o with
    | create_ui_out ui => Some ui
    | verify_ui_out b => None
    | verify_ui_out_def => None
    end.

  Global Instance MicroBFT_I_ComponentTrust : ComponentTrust :=
    MkComponentTrust
      UI
      auth_data2ui
      USIG_output_interface2ui
      ui2rep.

  (* === ======================== === *)




  (* === INSTANTIATION OF ComponentAuth === *)

  Definition MicroBFT_ca_create (eo : EventOrdering) (e : Event) (a : MicroBFT_Bare_Msg) : list MicroBFT_digest :=
    match a with
    | MicroBFT_msg_bare_request n pui =>
      match M_byz_state_sys_before_event_of_trusted MicroBFTsys e with
      | Some u => [ui2digest (snd (create_UI n u))]
      | None => []
      end
    end.

  Definition MicroBFT_ca_verify (eo : EventOrdering) (e : Event) (a : AuthenticatedData) : bool :=
    match a with
    | MkAuthData (MicroBFT_msg_bare_request n pui) [d] =>
      match M_byz_state_sys_before_event_of_trusted MicroBFTsys e with
      | Some u =>
        verify_UI n (Build_UI pui d) u
      | None => false
      end

   | _ => false
    end.

  Global Instance MicroBFT_I_ComponentAuth : ComponentAuth :=
    MkComponentAuth
      MicroBFT_ca_create
      MicroBFT_ca_verify.

  (* === ======================== === *)




  (* === INSTANTIATION OF KnowledgeComponents === *)

  Inductive MicroBFT_data :=
  | microbft_data_rdata (c  : Commit)
  | microbft_data_acc   (a  : Accept)
  | microbft_data_ui    (ui : UI).

  Lemma microbft_data_ui_inj : injective microbft_data_ui.
  Proof.
    introv h; inversion h; auto.
  Qed.


  Definition Request2HashData (c : Commit) : HashData :=
    Build_HashData
      (commit_n c)
      (ui_pre (commit_ui c)).

  Definition accept2hdata (a : Accept) : HashData :=
    Build_HashData
      (accept_r a)
      (Build_preUI MicroBFT_primary (accept_c a)).

  Definition data2hdata (d : MicroBFT_data) : option HashData :=
    match d with
    | microbft_data_rdata rd => Some (Request2HashData rd)
    | microbft_data_acc a => Some (accept2hdata a)
    | microbft_data_ui _ => None
    end.

  Definition hash_data2id (h : HashData) : MicroBFT_node :=
    pre_ui_id (hd_pre h).

  Definition MicroBFT_data2owner (d : MicroBFT_data) : option node_type :=
    match d with
    | microbft_data_rdata rd => Some (commit2sender rd)
    | microbft_data_acc a => None (*Some MicroBFT_primary*)
    | microbft_data_ui ui => Some (ui2rep ui)
    end.

  Definition MicroBFT_auth2data (a : AuthenticatedData) : list MicroBFT_data :=
    match a with
    | MkAuthData (MicroBFT_msg_bare_request n pui) [d] =>
      let ui := Build_UI pui d in
      [microbft_data_rdata (commit n ui),
       microbft_data_ui ui]

    | _ => []
    end.

  Definition MicroBFT_data2trust (d : MicroBFT_data) : list UI :=
    match d with
    | microbft_data_rdata rd => [commit_ui rd]
    | microbft_data_acc a => []
    | microbft_data_ui ui => [ui]
    end.

  Lemma MicroBFT_data2trust_correct : forall t, In t (MicroBFT_data2trust (microbft_data_ui t)).
  Proof.
    introv; simpl; tcsp.
  Qed.

  Lemma MicroBFT_auth2trust_correct :
    forall a t,
      In t (auth_data2ui a)
      <-> exists d, In t (MicroBFT_data2trust d) /\ In d (MicroBFT_auth2data a).
  Proof.
    introv.
    destruct a as [ad tok], ad; simpl; tcsp; split; intro h; exrepnd; tcsp;[|].

    { repeat (destruct tok; simpl in *; tcsp).
      repndors; subst; tcsp.
      exists (microbft_data_ui (Build_UI pui t0)); simpl; tcsp. }

    { repeat (destruct tok; simpl in *; tcsp).
      repndors; subst; tcsp. }
  Qed.

  Definition generated_for (d : MicroBFT_data) (ui : UI) :=
    match d with
    | microbft_data_rdata rd =>
      commit_ui rd = ui
      /\ exists r, verify_hash_usig (Request2HashData rd) (ui2digest ui) (usig_initial_keys r) = true
      (*/\ create_hash_usig (Request2HashData rd) (usig_initial_keys (ui2rep ui)) = ui2digest ui*)
    | microbft_data_acc a =>
      (*create_hash_usig (accept2hdata a) (usig_initial_keys (ui2rep ui)) = ui2digest ui
      /\*) exists r, verify_hash_usig (accept2hdata a) (ui2digest ui) (usig_initial_keys r) = true
    | microbft_data_ui x => x = ui
    end.
  (* We're currently only ever using the same keys in all USIGs *)

  Definition similar_data (d1 d2 : MicroBFT_data) : Prop :=
    match d1, d2 with
    | microbft_data_rdata _, microbft_data_rdata _ => True
    | microbft_data_acc   _, microbft_data_acc   _ => True
    | microbft_data_ui    _, microbft_data_ui    _ => True
    | _, _ => False
    end.

  Parameter collision_resistant :
    forall (ui : UI) (d1 d2 : MicroBFT_data),
      generated_for d1 ui -> generated_for d2 ui -> similar_data d1 d2 -> d1 = d2.

  Lemma same_ui2owner :
    forall (t : UI), MicroBFT_data2owner (microbft_data_ui t) = Some (ui2rep t).
  Proof.
    tcsp.
  Qed.

  Definition ui_in_log_entry (ui : UI) (e : Commit) : bool :=
    if UI_dec ui (commit_ui e)  then true else false.

  Definition ui_in_log ui l : bool :=
    existsb (ui_in_log_entry ui) l.


  Lemma HashData_Deq : Deq HashData.
  Proof.
    repeat introv.
    destruct x as [n1 pui1], y as [n2 pui2].

    destruct (deq_nat n1 n2); subst; prove_dec.

    destruct pui1 as [id1 counter1], pui2 as [id2 counter2].
    destruct (deq_nat counter1 counter2); subst; prove_dec.

    destruct id1, id2; prove_dec.
  Defined.


  Definition RequestAndUI2HashData (n : nat) (ui : UI) : HashData :=
    Build_HashData
      n
      (ui_pre ui).

  Definition hash_data_in_log_entry (hd : HashData) (e : Commit) : bool :=
    if HashData_Deq hd (Request2HashData e) then true  else false.

  Definition hash_data_in_log (hd : HashData) (l : LOG_state) : bool :=
    existsb (hash_data_in_log_entry hd) l.

  Definition in_log (rd : Commit) (l : LOG_state) : Prop := In rd l.

  Definition Request_dec : Deq Commit.
  Proof.
    introv.
    destruct x as [n1 ui1], y as [n2 ui2].
    destruct (deq_nat n1 n2); subst; prove_dec.
    destruct (UI_dec ui1 ui2); subst; prove_dec.
  Defined.

  Definition request_in_log (r : Commit) (l : LOG_state) : bool :=
    if in_dec Request_dec r l then true else false.

  Definition MicroBFT_data_in_log (d : MicroBFT_data) (l : LOG_state) :=
    match d with
    | microbft_data_rdata   rd => request_in_log rd l
    | microbft_data_acc     a  => false
    | microbft_data_ui      ui => ui_in_log ui l
    end.

  Definition MicroBFT_data_knows (d : MicroBFT_data) (l : LOG_state) : Prop :=
    MicroBFT_data_in_log d l = true.

  Lemma MicroBFT_data_knows_dec : forall (d : MicroBFT_data) (m : LOG_state), decidable (MicroBFT_data_knows d m).
  Proof.
    introv.
    unfold MicroBFT_data_knows.
    destruct (MicroBFT_data_in_log d m); prove_dec.
  Defined.

  Lemma no_initial_memory :
    forall n i, on_state_of_component LOGname (MicroBFTsys n) (fun s => ~ MicroBFT_data_knows i s).
  Proof.
    introv.
    unfold on_state_of_component; simpl.
    destruct n; simpl; auto;
      try (complete (intro h; unfold MicroBFT_data_knows in h; simpl in *; destruct i; simpl in *; ginv)).
  Qed.

  Lemma ui_characterization :
    forall t1 t2,
      ui2counter t1 = ui2counter t2
      -> ui2rep t1 = ui2rep t2
      -> ui2digest t1 = ui2digest t2
      -> t1 = t2.
  Proof.
    introv h q w.
    destruct t1 as [p1 d1], t2 as [p2 d2], p1, p2; simpl in *.
    unfold ui2counter, ui2rep in *; simpl in *; subst; tcsp.
  Qed.

  Definition MicroBFTmsg2data (m : MicroBFT_msg) : list MicroBFT_data :=
    match m with
    | MicroBFT_request _ => []
    | MicroBFT_commit  c => [microbft_data_rdata c, microbft_data_ui (commit_ui c)]
    | MicroBFT_accept  a => [microbft_data_acc a]
    end.

  Lemma lt_transitive : transitive _ lt.
  Proof.
    introv; omega.
  Qed.

  Lemma lt_antireflexive : antireflexive lt.
  Proof.
    introv; omega.
  Qed.

  Definition ui_has_counter (ui : UI) (c : nat) :=
    ui2counter ui = c.

  Definition similar_ui (ui1 ui2 : UI) : Prop := True.

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

  Lemma similar_ui_equivalence : equivalence _ similar_ui.
  Proof.
    split; introv; tcsp.
  Qed.

  Lemma ui_has_counter_pres :
    forall t a b c,
      ui_has_counter t a
      -> ui_has_counter t c
      -> (a < b \/ a = b)
      -> (b < c \/ b = c)
      -> ui_has_counter t b.
  Proof.
    introv hca hcb h q.
    unfold ui_has_counter in *; subst; repndors; tcsp; try omega.
  Qed.

  Definition init_counter : nat := 0.

  Lemma init_counter_cond :
    forall n : node_type,
    exists m,
      state_of_trusted_in_ls (MicroBFTsys (node2name n)) = Some m
      /\ usig_counter m = init_counter.
  Proof.
    introv; simpl.
    unfold state_of_trusted_in_ls, state_of_trusted; simpl.
    eexists; dands; eauto.
  Qed.


  Global Instance MicroBFT_I_KnowledgeComponents : KnowledgeComponents :=
    MkKnowledgeComponents
      MicroBFT_data
      microbft_data_ui
      microbft_data_ui_inj
      generated_for
      similar_data
      collision_resistant
      MicroBFT_data2owner
      same_ui2owner
      MicroBFT_auth2data
      MicroBFT_data2trust
      MicroBFT_data2trust_correct
      MicroBFT_auth2trust_correct
      LOGname
      MicroBFT_data_knows
      MicroBFT_data_knows_dec
      MicroBFTfunLevelSpace
      MicroBFTsys
      no_initial_memory
      MicroBFTmsg2data
      nat
      lt
      lt_transitive
      lt_antireflexive
      ui_has_counter
      ui_has_counter_pres
      similar_ui
      similar_ui_equivalence
      similar_ui_pres
      usig_counter
      init_counter
      init_counter_cond.

  (* === ======================== === *)

End MicroBFTkn.
