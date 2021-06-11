(* USIG instance *)

Require Export MinBFTkn0.
Require Export MinBFT.
Require Export MinBFTtacts.
Require Export ComponentAxiom.
Require Export CalculusSM.


Hint Resolve equal_hash_data_implies_equal_request_data : minbft minbft2.


Section MinBFTkn.

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
      match M_byz_state_sys_before_event MinBFTsys e USIGname with
      | Some u => [ui2digest (snd (create_UI (bare_prepare_v bp) (bare_prepare_m bp) u))]
      | None => []
      end
    | MinBFT_msg_bare_commit  bc pui =>
      match M_byz_state_sys_before_event MinBFTsys e USIGname with
      | Some u => [ui2digest (snd (create_UI (bare_commit_v bc) (bare_commit_m bc) u))]
      | None => []
      end
    end.

  Definition MinBFT_ca_verify (eo : EventOrdering) (e : Event) (a : AuthenticatedData) : bool :=
    match a with
    | MkAuthData (MinBFT_msg_bare_prepare bp pui) [d] =>
      match M_byz_state_sys_before_event MinBFTsys e USIGname with
      | Some u =>
        verify_UI (bare_prepare_v bp) (bare_prepare_m bp) (Build_UI pui d) u
      | None => false
      end

    | MkAuthData (MinBFT_msg_bare_commit bc pui) [d] =>
      match M_byz_state_sys_before_event MinBFTsys e USIGname with
      | Some u =>
        (verify_UI (bare_commit_v bc) (bare_commit_m bc) (Build_UI pui d) u)
          && (verify_UI (bare_commit_v bc) (bare_commit_m bc) (bare_commit_ui bc) u)
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
      -> exists r, verify_hash_usig hd (ui2digest ui) (usig_initial_keys (MinBFT_replica r)) = true.
  (* We're currently only ever using the same keys in all USIGs *)

  Definition similar_data (d1 d2 : MinBFT_data) : Prop :=
    match d1, d2 with
    | minbft_data_rdata _, minbft_data_rdata _ => True
    | minbft_data_ui _, minbft_data_ui _ => True
    | _, _ => False
    end.

  Lemma similar_data_sym : symmetric _ similar_data.
  Proof.
    introv sim; unfold similar_data in *; destruct x, y; tcsp.
  Qed.

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
      -> ui2cid t1 = ui2cid t2
      -> ui2rep t1 = ui2rep t2
      -> ui2digest t1 = ui2digest t2
      -> t1 = t2.
  Proof.
    introv h q w z.
    destruct t1 as [p1 d1], t2 as [p2 d2], p1, p2; simpl in *.
    unfold ui2counter, ui2cid, ui2rep in *; simpl in *; subst; tcsp.
  Qed.

  Definition MinBFTmsg2data (m : MinBFT_msg) : list MinBFT_data :=
    match m with
    | MinBFT_request _ => []
    | MinBFT_reply _   => []
    | MinBFT_prepare p =>

      [minbft_data_ui (prepare_ui p),
       minbft_data_rdata (prepare2request_data p)]

    | MinBFT_commit  c =>

      [minbft_data_ui (commit2ui_i c),
       minbft_data_ui (commit2ui_j c),
       minbft_data_rdata (commit2request_data_i c)(*,
       minbft_data_rdata (commit2request_data_j c)*)]

    (* I removed that one (above) because 'knows' currently doesn't handle request_datas with commit uis.
       See also [MinBFT_auth2data] *)

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

  Definition ui_has_counter (ui : UI) (c : nat) :=
    ui2counter ui = c.

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

  Definition similar_ui (ui1 ui2 : UI) : Prop := True.

  Lemma similar_ui_equivalence : equivalence _ similar_ui.
  Proof.
    split; introv; tcsp.
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

  Definition init_counter : nat := 0.

  Lemma init_counter_cond :
    forall n : node_type,
    exists m,
      state_of_component USIGname (MinBFTsys (node2name n)) = Some m
      /\ usig_counter m = init_counter.
  Proof.
    introv; simpl.
    unfold state_of_component; simpl.
    eexists; dands; eauto.
  Qed.

  Definition ext_prim := True.
  Definition ext_prim_interp : forall (eo : EventOrdering) (e : Event), ext_prim -> Prop :=
    fun eo e p => True.

  Definition minbft_vouchers : Type := unit.
  Definition minbft_num_vouchers : minbft_vouchers -> nat := fun v => 1.
  Definition minbft_add_vouchers : minbft_vouchers -> minbft_vouchers -> minbft_vouchers := fun a b => tt.
  Definition minbft_mk_vouchers : node_type -> minbft_vouchers := fun n => tt.
  Definition minbft_data2category : MinBFT_data -> string := fun d => "".
  Definition minbft_data2vouchers : MinBFT_data -> minbft_vouchers := fun d => tt.
  Definition minbft_data2payload  : MinBFT_data -> MinBFT_data := fun d => d.
  Lemma minbft_app_vouchers_inc1 : forall (v1 v2 : minbft_vouchers), minbft_num_vouchers v1 <= minbft_num_vouchers (minbft_add_vouchers v1 v2).
  Proof. auto. Qed.
  Lemma minbft_app_vouchers_inc2 : forall (v1 v2 : minbft_vouchers), minbft_num_vouchers v2 <= minbft_num_vouchers (minbft_add_vouchers v1 v2).
  Proof. auto. Qed.
  Lemma minbft_num_node2vouchers : forall (n : node_type), minbft_num_vouchers (minbft_mk_vouchers n) = 1.
  Proof. auto. Qed.

  Global Instance MinBFT_I_KnowledgeComponents : KnowledgeComponents :=
    MkKnowledgeComponents
      MinBFT_data
      minbft_data_ui
      minbft_data_ui_inj
      generated_for
      similar_data
      similar_data_sym
      collision_resistant
      (**)
      minbft_vouchers
      minbft_num_vouchers
      minbft_add_vouchers
      minbft_mk_vouchers
      minbft_data2category
      minbft_data2vouchers
      minbft_data2payload
      minbft_app_vouchers_inc1
      minbft_app_vouchers_inc2
      minbft_num_node2vouchers
      (**)
      MinBFT_data2owner
      same_ui2owner
      MinBFT_auth2data
      MinBFT_data2trust
      MinBFT_data2trust_correct
      MinBFT_auth2trust_correct
      LOGname
      preUSIGname
      MinBFT_data_knows
      MinBFT_data_knows_dec
      MinBFTfunLevelSpace
      MinBFTsys
      no_initial_memory
      MinBFTmsg2data
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
      ext_prim
      ext_prim_interp.

  (* === ======================== === *)

End MinBFTkn.
