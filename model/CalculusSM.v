Require Export Quorum.
Require Export CorrectTrace.
Require Export Process.
Require Export ComponentSM.
Require Export ComponentAxiom.
Require Export List.


Section KnowledgeCalculus.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pm  : @Msg }.
  Context { qc  : @Quorum_context pn}.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pda : @DataAuth pd pn }.
  Context { cad : @ContainedAuthData pd pat pm }.
  Context { dtc : @DTimeContext }.
  Context { iot : @IOTrustedFun }.
  Context { ctp : @ComponentTrust pd pn pat qc iot }.
  Context { cap : @ComponentAuth pd pn pk pat pm dtc iot }.

  Local Open Scope eo.
  Local Open Scope proc.


  Context { base_fun_io       : baseFunIO }.
  Context { base_state_fun    : baseStateFun }.
  Context { trusted_state_fun : trustedStateFun }.


  Definition antireflexive {A} (R : A -> A -> Prop) : Prop :=
    forall x, R x x -> False.

  (* === alternative names for the [ComponentTrust] parameters === *)

  (* Some trusted knowledge, e.g. UI *)
  Definition kc_trust       := ct_trust.
  Definition kc_auth2trust  := ct_auth2trust.
  Definition kc_out2trust   := ct_out2trust.
  Definition kc_trust2owner := ct_trust2owner.

  Definition kc_verify {eo : EventOrdering} (e : Event) (a : AuthenticatedData) : bool :=
    ca_verify e a.

  (* === === *)

  Class KnowledgeComponents :=
    MkKnowledgeComponents
      {
        (* === TRUSTED/NON-TRUSTED INFORMATION === *)
        (* known data, e.g. the whole message *)
        kc_data         : Type;

        (* [kc_trust] is a subtype of [kc_data] *)
        kc_trust2data     : kc_trust -> kc_data;
        kc_trust2data_inj : injective kc_trust2data;


        (* relation between data and scrambled/hashed data *)
        kc_generated_for : kc_data -> kc_trust -> Prop;
        kc_sim_data      : kc_data -> kc_data -> Prop;
        kc_sim_data_sym  : symmetric _ kc_sim_data;
        kc_collision_resistant : forall (t : kc_trust) d1 d2, kc_generated_for d1 t -> kc_generated_for d2 t -> kc_sim_data d1 d2 -> d1 = d2;


        (* === OWNER === *)
        (* owner of the data *)
        kc_data2owner       : kc_data -> option node_type;
        kc_same_trust2owner : forall (t : kc_trust), kc_data2owner (kc_trust2data t) = kc_trust2owner t;


        (* === AUTHENTICATED DATA === *)
        kc_auth2data  : AuthenticatedData -> list kc_data;
        kc_data2trust : kc_data -> list kc_trust;
        kc_data2trust_correct : forall t, In t (kc_data2trust (kc_trust2data t));
        kc_auth2trust_correct : forall a t, In t (kc_auth2trust a) <-> exists d, In t (kc_data2trust d) /\ In d (kc_auth2data a);


        (* === MEMORY === *)
        (* name of component holding the knowledge *)
        (* NOTE: This could be generalized to a list of names instead of just one *)
        kc_mem_comp      : CompName;


        (* === TRUSTED === *)
        (* name of the component in charge of generating trusted info *)
        (* NOTE: This could be generalized to a list of names instead of just one *)
        kc_trust_comp   : PreCompName;


        (* === KNOW === *)
        (* express what it means to know some information *)
        kc_knows        : kc_data  -> sf kc_mem_comp -> Prop;
        kc_knows_dec    : forall (d : kc_data) (m : sf kc_mem_comp), decidable (kc_knows d m);


        (* === STATE MACHINE UPDATING THE MEMORY === *)
        (* outputs of the state machine *)
        kc_funLevelSpace      : funLevelSpace;
        kc_sys                : M_USystem kc_funLevelSpace;
        kc_no_initial_memory  : forall n i, on_state_of_component kc_mem_comp (kc_sys n) (fun s => ~ kc_knows i s);
        kc_msg2data           : msg -> list kc_data;


        (* === TRUSTED IDENTIFIER === *)
        (* Note: This does not necessarily has to be the identifier/counter.
            In case of A2M it can be length of the log. *)
        kc_id           : Type;
        kc_id_lt        : kc_id -> kc_id -> Prop;
        kc_id_lt_trans  : transitive _ kc_id_lt;
        kc_id_lt_arefl  : antireflexive kc_id_lt;

        kc_trust_has_id      : kc_trust -> kc_id -> Prop;
        kc_trust_has_id_pres : forall t a b c, kc_trust_has_id t a -> kc_trust_has_id t c -> (kc_id_lt a b \/ a = b) -> (kc_id_lt b c \/ b = c) -> kc_trust_has_id t b;

        kc_sim_trust       : kc_trust -> kc_trust -> Prop;
        kc_sim_trust_equiv : equivalence _ kc_sim_trust;
        kc_sim_trust_pres  : forall t t' a b, kc_trust_has_id t a -> kc_trust_has_id t b -> kc_sim_trust t t' -> kc_trust_has_id t' a -> kc_trust_has_id t' b;

        kc_getId        : tsf (pre2trusted kc_trust_comp) -> kc_id;

        (* ******************** *)
        (* *** EXPERIMENTAL *** *)
        kc_ExtPrim : Type;
        kc_ext_prim_interp : forall (eo : EventOrdering) (e : Event), kc_ExtPrim -> Prop;
      }.

  Context { pkc : KnowledgeComponents }.

  Definition TCN : CompName := pre2trusted kc_trust_comp.
  Definition TST : Type := tsf TCN.


  (* ******************************************************************* *)
  (*  ****** SOME ABSTRACTIONS ****** *)

  Notation "a ≪ b" := (kc_id_lt a b) (at level 70).
  Definition kc_id_le a b := kc_id_lt a b \/ a = b.
  Notation "a ⋘ b" := (kc_id_le a b) (at level 70).
  Notation "a ≈ b" := (kc_sim_trust a b) (at level 70).
  Notation "a ≍ b" := (kc_sim_data a b) (at level 70).

  (* MOVE where it belongs *)

  Definition ex_node_e {eo : EventOrdering} (e : Event) :=
    exists n, name2node (loc e) = Some n.

  Record EventN {eo : EventOrdering} :=
    MkEventN
      {
        en_event :> Event;
        en_node  : ex_node_e en_event;
      }.
  Global Arguments MkEventN [eo] _ _.

  Lemma implies_ex_node_e_local_pred :
    forall {eo : EventOrdering} {e : Event},
      ex_node_e e -> ex_node_e (local_pred e).
  Proof.
    introv h; unfold ex_node_e in *; autorewrite with eo in *; auto.
  Qed.
  Hint Resolve implies_ex_node_e_local_pred : kn.

  Definition mk_eventN_name2node
             {eo : EventOrdering} {e : Event} {n : node_type}
             (p : name2node (loc e) = Some n) : EventN :=
    MkEventN e (ex_intro _ n p).

  Definition mk_eventN_node2name
             {eo : EventOrdering} {e : Event} {n : node_type}
             (p : loc e = node2name n) : EventN.
  Proof.
    assert (name2node (loc e) = Some n) as x.
    { rewrite p; simpl; rewrite node2name_cond; auto. }
    exact (MkEventN e (ex_intro _ n x)).
  Defined.

  Lemma implies_ex_node :
    forall {eo : EventOrdering} (e : EventN), exists n, name2node (loc e) = Some n.
  Proof.
    introv; destruct e as [e cond]; auto.
  Qed.

  Lemma EventN_implies_node2name :
    forall {eo : EventOrdering} (e : EventN), exists n, loc e = node2name n.
  Proof.
    introv; destruct e as [e cond]; auto.
    unfold ex_node_e in cond; exrepnd; simpl in *.
    exists n.
    apply name2node_cond in cond0; auto.
  Qed.

  Lemma ex_node_e_EventN :
    forall {eo : EventOrdering} (e : EventN), ex_node_e e.
  Proof.
    introv; destruct e; auto.
  Qed.
  Hint Resolve ex_node_e_EventN : kn.

  Lemma direct_pred_preserves_ex_node_e :
    forall {eo : EventOrdering} (e1 e2 : Event),
      ex_node_e e2
      -> e1 ⊂ e2
      -> ex_node_e e1.
  Proof.
    introv exe lte.
    unfold ex_node_e in *.
    assert (loc e1 = loc e2) as eqloc by eauto 3 with eo.
    rewrite eqloc; auto.
  Qed.
  Hint Resolve direct_pred_preserves_ex_node_e : kn.

  Lemma local_pred_preserves_ex_node_e :
    forall {eo : EventOrdering} (e1 e2 : Event),
      ex_node_e e2
      -> e1 ⊏ e2
      -> ex_node_e e1.
  Proof.
    introv exe lte.
    unfold ex_node_e in *.
    assert (loc e1 = loc e2) as eqloc by eauto 3 with eo.
    rewrite eqloc; auto.
  Qed.
  Hint Resolve local_pred_preserves_ex_node_e : kn.

  Lemma local_pred_preserves_ex_node_e_forward :
    forall {eo : EventOrdering} (e1 e2 : Event),
      ex_node_e e1
      -> e1 ⊏ e2
      -> ex_node_e e2.
  Proof.
    introv exe lte.
    unfold ex_node_e in *.
    assert (loc e1 = loc e2) as eqloc by eauto 3 with eo.
    rewrite <- eqloc; auto.
  Qed.
  Hint Resolve local_pred_preserves_ex_node_e_forward : kn.

  Lemma local_pred_eq_preserves_ex_node_e :
    forall {eo : EventOrdering} (e1 e2 : Event),
      ex_node_e e2
      -> e1 ⊑ e2
      -> ex_node_e e1.
  Proof.
    introv exe lte.
    unfold ex_node_e in *.
    assert (loc e1 = loc e2) as eqloc by eauto 3 with eo.
    rewrite eqloc; auto.
  Qed.
  Hint Resolve local_pred_eq_preserves_ex_node_e : kn.

  Lemma mk_EventN_LBEQ {eo : EventOrdering} {e1 : Event} {e2 : EventN} (h : e1 ⊑ e2) : EventN.
  Proof.
    exists e1.
    eauto 3 with kn.
  Defined.

  Lemma mk_EventN_LB {eo : EventOrdering} {e1 : Event} {e2 : EventN} (h : e1 ⊏ e2) : EventN.
  Proof.
    exists e1.
    eauto 3 with kn.
  Defined.

  (* express what it means to know some trusted information *)
  (* input -> trusted -> location *)
  Definition kc_Tknows (t : kc_trust) (m : sf kc_mem_comp) : Prop :=
    kc_knows (kc_trust2data t) m.

  Definition kc_Tknows_dec (t : kc_trust)  (m : sf kc_mem_comp) : decidable (kc_Tknows t m) :=
    kc_knows_dec (kc_trust2data t) m.

  Definition kc_no_initial_Tmemory :
    forall n t, on_state_of_component kc_mem_comp (kc_sys n) (fun s => ~ kc_Tknows t s)
    := fun n t => kc_no_initial_memory n (kc_trust2data t).

  Ltac simp_eq_step :=
    match goal with
    | [ H1 : ?x = node2name ?a, H2 : ?x = node2name ?b |- _ ] => rewrite H1 in H2

    | [ H1 : ?x = Some ?a, H2 : ?x = Some ?b |- _ ] => rewrite H1 in H2

    | [ H : node2name ?a = node2name ?b |- _ ] =>
      apply node2name_inj in H;
      try (first [ subst a
                 | subst b
                 | rewrite H in *
                 | rewrite <- H in * ]);
      GC; auto



    | [ H : Some ?a = Some ?b |- _ ] =>
      apply Some_inj in H;
      try (first [ subst a
                 | subst b
                 | rewrite H in *
                 | rewrite <- H in * ]);
      GC; auto
    end.

  Ltac simp_eq := repeat simp_eq_step.


  Definition node_op2name_op (n : option node_type) : option name :=
    option_map node2name n.

  Definition kc_data2name (d : kc_data) : option name :=
    node_op2name_op (kc_data2owner d).

  Definition kc_trust2name (i : kc_trust) : option name :=
    option_map node2name (kc_trust2owner i).

  Definition state_before {eo : EventOrdering} (e : Event) (mem : sf kc_mem_comp) :=
    exists n,
      loc e = node2name n
      /\ M_state_sys_before_event kc_sys e kc_mem_comp = Some mem.

  Definition state_after {eo : EventOrdering} (e : Event) (mem : sf kc_mem_comp) :=
    exists n,
      loc e = node2name n
      /\ M_state_sys_on_event kc_sys e kc_mem_comp = Some mem.

  Definition trusted_state_before {eo : EventOrdering} (e : Event) (mem : TST) :=
    exists n,
      loc e = node2name n
      /\ M_byz_state_sys_before_event kc_sys e TCN = Some mem.

  Definition trusted_state_after {eo : EventOrdering} (e : Event) (mem : TST) :=
    exists n,
      loc e = node2name n
      /\ M_byz_state_sys_on_event kc_sys e TCN = Some mem.

  Definition id_before {eo : EventOrdering} (e : Event) (c : kc_id) :=
    exists (mem : TST),
      trusted_state_before e mem
      /\ kc_getId mem = c.

  Definition id_after {eo : EventOrdering} (e : Event) (c : kc_id) :=
    exists (mem : TST),
      trusted_state_after e mem
      /\ kc_getId mem = c.

  Definition knows_before {eo : EventOrdering} (e : Event) (d : kc_data) :=
    exists mem,
      state_before e mem
      /\ kc_knows d mem.

  Definition Tknows_before {eo : EventOrdering} (e : Event) (t : kc_trust) :=
    exists mem,
      state_before e mem
      /\ kc_Tknows t mem.
  (* do we need something like this here
     /\ kc_getId mem = c
     /\ kc_id t = c.
   *)

  Definition knows_after {eo : EventOrdering} (e : Event) (d : kc_data) :=
    exists mem,
      state_after e mem
      /\ kc_knows d mem.


  Definition Tknows_after {eo : EventOrdering} (e : Event) (t : kc_trust) :=
    exists mem,
      state_after e mem
      /\ kc_Tknows t mem.
  (* do we need something like this here
     /\ kc_getId mem = c
     /\ kc_id t = c.
   *)


  Definition data_is_owned {eo : EventOrdering} (e : Event) (d : kc_data) : Prop :=
    match kc_data2owner d with
    | Some n => node2name n = loc e
    | None => False
    end.

  Definition data_is_owned_by (n : node_type) (d : kc_data) : Prop :=
    match kc_data2owner d with
    | Some x => x = n
    | None => False
    end.

  Definition data_is_owned_by_diff_owner (d1 d2 : kc_data) : Prop :=
    match (kc_data2owner d1), (kc_data2owner d2) with
    | Some x, Some y => x <> y
    | _ , _ => False
    end.

  Definition kc_trust_is_owned {eo : EventOrdering} (e : Event) (i : kc_trust) : Prop :=
    option_map node2name (kc_trust2owner i) = Some (loc e).

  Lemma data_is_owned_local_pred :
    forall {eo : EventOrdering} (e : Event) (d : kc_data),
      data_is_owned (local_pred e) d
      = data_is_owned e d.
  Proof.
    introv; unfold data_is_owned; dest_cases w; autorewrite with eo; auto.
  Qed.
  Hint Rewrite @data_is_owned_local_pred : kn.

  Lemma kc_trust_is_owned_local_pred :
    forall {eo : EventOrdering} (e : Event) (i : kc_trust),
      kc_trust_is_owned (local_pred e) i
      = kc_trust_is_owned e i.
  Proof.
    introv; unfold kc_trust_is_owned; autorewrite with eo; auto.
  Qed.
  Hint Rewrite @kc_trust_is_owned_local_pred : kn.

  Definition never_Tknew {eo : EventOrdering} (e : Event) (t : kc_trust) :=
    forall mem1 e1,
      e1 ⊑ e
      -> state_before e1 mem1
      -> ~kc_Tknows t mem1.

  Definition never_knew {eo : EventOrdering} (e : Event) (d : kc_data) :=
    forall mem1 e1,
      e1 ⊑ e
      -> state_before e1 mem1
      -> ~kc_knows d mem1.

  Lemma exists_state_before_dec :
    forall {eo : EventOrdering} (e : Event),
      (exists mem, state_before e mem)
      \/ forall mem, ~ state_before e mem.
  Proof.
    introv.
    unfold state_before.
    remember (M_state_sys_before_event kc_sys e kc_mem_comp) as w; symmetry in Heqw.
    remember (name2node (loc e)) as z; symmetry in Heqz.

    destruct z, w; try (complete (right; introv h; exrepnd; ginv));[|].

    { apply name2node_cond in Heqz.
      left; exists s n; dands; auto. }

    { right; introv h; exrepnd; ginv.
      rewrite h1 in Heqz; rewrite node2name_cond in Heqz; ginv. }
  Qed.

  Lemma exists_state_after_dec :
    forall {eo : EventOrdering} (e : Event),
      (exists mem, state_after e mem)
      \/ forall mem, ~ state_after e mem.
  Proof.
    introv.
    unfold state_after.
    remember (M_state_sys_on_event kc_sys e kc_mem_comp) as w; symmetry in Heqw.
    remember (name2node (loc e)) as z; symmetry in Heqz.

    destruct z, w; try (complete (right; introv h; exrepnd; ginv));[|].

    { apply name2node_cond in Heqz.
      left; exists s n; dands; auto. }

    { right; introv h; exrepnd; ginv.
      rewrite h1 in Heqz; rewrite node2name_cond in Heqz; ginv. }
  Qed.

  Lemma isFirst_implies_not_knows_before :
    forall {eo : EventOrdering} (e : Event) i,
      isFirst e -> ~knows_before e i.
  Proof.
    introv isf kn.
    pose proof (kc_no_initial_memory (loc e) i) as q.
    unfold on_state_of_component in q.
    unfold knows_before in *; exrepnd; simpl in *.
    unfold state_before in *; exrepnd.
    rewrite M_state_sys_before_event_unfold in kn2.
    apply map_option_Some in kn2; exrepnd; rev_Some.
    rewrite M_run_ls_before_event_is_first in kn2; auto; ginv.
    inversion kn2; subst; simpl in *.
    rewrite kn3 in q; tcsp.
  Qed.

  Lemma knows_after_implies_has_correct_trace_before :
    forall {eo : EventOrdering} (e : Event) i,
      knows_after e i
      -> has_correct_trace_before e (loc e).
  Proof.
    introv h.
    unfold knows_after in *; exrepnd.
    unfold state_after in *; exrepnd.
    rewrite M_state_sys_on_event_unfold in h2.
    apply map_option_Some in h2; exrepnd; rev_Some; simpl in *; eauto 3 with comp.
  Qed.
  Hint Resolve knows_after_implies_has_correct_trace_before : kn.

  Lemma state_before_implies_state_after_not_first :
    forall {eo : EventOrdering} (e : Event) mem,
      ~isFirst e
      -> state_before e mem
      -> state_after (local_pred e) mem.
  Proof.
    introv ni h; unfold state_before in *; unfold state_after; exrepnd.
    rewrite M_state_sys_before_event_unfold in h0.
    apply map_option_Some in h0; exrepnd; rev_Some; simpl in *.
    rewrite M_run_ls_before_event_unroll_on in h0.
    autorewrite with eo; eexists; dands; eauto.
    unfold M_state_sys_on_event; autorewrite with eo.
    unfold M_state_ls_on_event; simpl.
    destruct (dec_isFirst e); ginv; tcsp.
    allrw; simpl; auto.
  Qed.
  Hint Resolve state_before_implies_state_after_not_first : kn.

  Lemma state_before_implies_state_after_first :
    forall {eo : EventOrdering} (e : Event) mem,
      isFirst e
      -> state_before e mem
      -> state_of_component kc_mem_comp (kc_sys (loc e)) = Some mem.
  Proof.
    introv ni h; unfold state_before in *; exrepnd.
    rewrite M_state_sys_before_event_unfold in h0.
    apply map_option_Some in h0; exrepnd; rev_Some; simpl in *.
    rewrite M_run_ls_before_event_unroll_on in h0.
    destruct (dec_isFirst e); tcsp; GC; ginv.
    inversion h0; subst; simpl in *; auto.
  Qed.
  Hint Resolve state_before_implies_state_after_first : kn.

  Lemma trusted_state_before_implies_trusted_state_after_not_first :
    forall {eo : EventOrdering} (e : Event) mem,
      ~isFirst e
      -> trusted_state_before e mem
      -> trusted_state_after (local_pred e) mem.
  Proof.
    introv ni h; unfold trusted_state_before, trusted_state_after in *; exrepnd.
    apply option_map_Some in h0; exrepnd; subst; simpl in *.
    rewrite M_byz_run_ls_before_event_as_M_byz_run_ls_on_event_pred in h0; auto.
    autorewrite with eo; eexists; dands; eauto.
    apply option_map_Some; simpl.
    autorewrite with eo; allrw; eauto.
  Qed.
  Hint Resolve trusted_state_before_implies_trusted_state_after_not_first : kn.

  Lemma trusted_state_after_implies_trusted_state_before_not_first :
    forall {eo : EventOrdering} (e : Event) mem,
      ~isFirst e
      -> trusted_state_after (local_pred e) mem
      -> trusted_state_before e mem.
  Proof.
    introv ni h; unfold trusted_state_before, trusted_state_after in *; exrepnd.
    apply option_map_Some in h0; exrepnd; subst; simpl in *.
    revert dependent a.
    autorewrite with eo in *; eexists; dands; eauto.
    apply option_map_Some.
    rewrite M_byz_run_ls_before_event_as_M_byz_run_ls_on_event_pred; auto.
    allrw; simpl; eauto.
  Qed.
  Hint Resolve trusted_state_after_implies_trusted_state_before_not_first : kn.

  Lemma trusted_state_before_implies_trusted_state_after_first :
    forall {eo : EventOrdering} (e : Event) mem,
      isFirst e
      -> trusted_state_before e mem
      -> state_of_component TCN (kc_sys (loc e)) = Some mem.
  Proof.
    introv ni h; unfold trusted_state_before in *; exrepnd.
    apply map_option_Some in h0; exrepnd; rev_Some; simpl in *; ginv.
    rewrite M_byz_run_ls_before_event_unroll_on in h0.
    destruct (dec_isFirst e); tcsp; GC; ginv.
    unfold state_of_component; allrw; simpl; auto.
  Qed.
  Hint Resolve trusted_state_before_implies_trusted_state_after_first : kn.

  Definition same_id (t1 t2 : kc_trust) :=
    exists i, kc_trust_has_id t1 i /\ kc_trust_has_id t2 i.

(*  Definition in_no_repeats_id (t : kc_trust) (l : list kc_trust) :=
    In t l
    /\ no_repeats (map kc_id l).*)

(*  Definition trusted_out_unique
             {eo : EventOrdering}
             (e  : Event)
             (t  : kc_trust) : Prop :=
    let l := on_M_trusted_out
               (M_byz_output_sys_on_event kc_sys e)
               (fun msgs => mapOption kc_msg2trust msgs)
               (fun o => opt2list (kc_out2trust o)) in
    in_no_repeats_id t l.*)

  Lemma data_is_in_out {s} {eo : EventOrdering} {e : Event}
        (d : kc_data)
        (o : event2out s e) : Prop.
  Proof.
    unfold event2out in o.
    remember (trigger e) as trig; destruct trig; simpl in *.
    { exact (In d (flat_map (fun dm => kc_msg2data (dmMsg dm)) o)). }
    { destruct o. }
    { exact (In d (opt2list (option_map kc_trust2data (kc_out2trust (it_name i) o)))). }
  Defined.

  Lemma data_is_in_out_and_dmsgs_are_out_implies :
    forall {eo : EventOrdering} (e : Event) {s} (o : event2out s e) msgs d,
      dmsgs_are_out msgs o
      -> data_is_in_out d o
      -> In d (flat_map (fun dm => kc_msg2data (dmMsg dm)) msgs).
  Proof.
    introv h q.
    unfold dmsgs_are_out, data_is_in_out, event2out in *; simpl in *.
    remember (trigger e) as trig; destruct trig; subst; simpl in *; tcsp.
  Qed.

  Definition disseminate_data
             {eo : EventOrdering}
             (e  : Event)
             (d  : kc_data) : Prop :=
    exists (o : event2out (fls_space kc_funLevelSpace (loc e)) e),
      M_byz_output_sys_on_event kc_sys e = Some o
      /\ data_is_in_out d o.

  Definition disseminate_data_own
             {eo : EventOrdering}
             (e  : Event)
             (d  : kc_data) : Prop :=
    disseminate_data e d
    /\ data_is_owned e d.

  Definition disseminate_trusted_own
             {eo : EventOrdering}
             (e  : Event)
             (t  : kc_trust) : Prop :=
    disseminate_data_own e (kc_trust2data t).

  Definition disseminate_trusted_unique_at {eo : EventOrdering} (e : EventN) :=
    forall t1 t2,
      disseminate_trusted_own e t1
      -> disseminate_trusted_own e t2
      -> same_id t1 t2
      -> t1 = t2.

  Definition disseminate_trusted_unique (eo : EventOrdering) :=
    forall (e : EventN), disseminate_trusted_unique_at e.

  (* kc_out2trust (M_byz_output_sys_on_event_to_byz kc_sys e) = Some t.*)

  (* exists mem,
      state_after e mem
      /\ kc_Tknows t mem
      /\ forall t', kc_Tknows t' mem -> same_id t t' -> t = t'.*)

  Definition generates_new_at {eo : EventOrdering} (e : EventN) :=
    forall t c1 c2 i,
      disseminate_trusted_own e t
      -> id_before e c1
      -> id_after e c2
      -> kc_trust_has_id t i
      -> (c1 ≪ i /\ i ⋘ c2).

  Definition generates_new (eo : EventOrdering) :=
    forall (e : EventN), generates_new_at e.

  Definition generates_new_ex_at {eo : EventOrdering} (e : EventN) :=
    forall t c1 c2,
      disseminate_trusted_own e t
      -> id_before e c1
      -> id_after e c2
      -> exists i,
          kc_trust_has_id t i
          /\ ~kc_trust_has_id t c1
          /\ c1 ≪ i
          /\ i ⋘ c2.

  Definition generates_new_ex (eo : EventOrdering) :=
    forall (e : EventN), generates_new_ex_at e.

  Definition generates_trusted
             {eo : EventOrdering}
             (e  : Event) :=
    exists c1 c2,
      c1 ≪ c2
      /\ id_before e c1
      /\ id_after e c2.

  Definition no_trusted_generation {eo : EventOrdering} (e : Event) :=
    exists c,
      id_before e c
      /\ id_after e c.

  Definition monotonicity (eo : EventOrdering) :=
    forall (e : EventN),
      no_trusted_generation e
      \/ generates_trusted e.


  Lemma state_after_eq_state_after_implies_eq_mem :
    forall {eo : EventOrdering} (e : Event) (mem mem1 : sf kc_mem_comp),
      state_after e mem
      -> state_after e mem1
      -> mem = mem1.
  Proof.
    introv h1 h2.
    unfold state_after in *; exrepnd; simp_eq.
  Qed.
  Hint Resolve state_after_eq_state_after_implies_eq_mem : kn.

  Lemma state_before_eq_state_before_implies_eq_mem :
    forall {eo : EventOrdering} (e : Event) (mem mem1 : sf kc_mem_comp),
      state_before e mem
      -> state_before e mem1
      -> mem = mem1.
  Proof.
    introv h1 h2.
    unfold state_before in *; exrepnd; simp_eq.
  Qed.
  Hint Resolve state_before_eq_state_before_implies_eq_mem : kn.

  Lemma trusted_state_after_implies_eq_mem :
    forall {eo : EventOrdering} (e : Event) (mem mem1 : TST),
      trusted_state_after e mem
      -> trusted_state_after e mem1
      -> mem = mem1.
  Proof.
    introv h1 h2.
    unfold trusted_state_after in *; exrepnd; simp_eq.
  Qed.
  Hint Resolve trusted_state_after_implies_eq_mem : kn.

  Lemma trusted_state_before_implies_eq_mem :
    forall {eo : EventOrdering} (e : Event) (mem mem1 : TST),
      trusted_state_before e mem
      -> trusted_state_before e mem1
      -> mem = mem1.
  Proof.
    introv h1 h2.
    unfold trusted_state_before in *; exrepnd; simp_eq.
  Qed.
  Hint Resolve trusted_state_before_implies_eq_mem : kn.

  Lemma id_after_eq_id_after_implies_eq_id :
    forall {eo : EventOrdering} (e : Event) (c1 c2 : kc_id),
      id_after e c1
      -> id_after e c2
      -> c1 = c2.
  Proof.
    introv h1 h2.
    unfold id_after in *; exrepnd; subst.
    eapply trusted_state_after_implies_eq_mem in h1; try exact h2; subst; auto.
  Qed.
  Hint Resolve id_after_eq_id_after_implies_eq_id : kn.

  Lemma id_before_eq_id_before_implies_eq_id :
    forall {eo : EventOrdering} (e : Event) (c1 c2 : kc_id),
      id_before e c1
      -> id_before e c2
      -> c1 = c2.
  Proof.
    introv h1 h2.
    unfold id_before in *; exrepnd; subst.
    eapply trusted_state_before_implies_eq_mem in h1; try exact h2; subst; auto.
  Qed.
  Hint Resolve id_before_eq_id_before_implies_eq_id : kn.

  Ltac eq_states :=
    repeat match goal with
           | [ H1 : id_before ?e ?c1
                    , H2 : id_before ?e ?c2 |- _ ] =>
             let h := fresh "h" in
             assert (c2 = c1) as h by eauto 3 with kn;
             subst c2

           | [ H1 : id_after ?e ?c1
                    , H2 : id_after ?e ?c2 |- _ ] =>
             let h := fresh "h" in
             assert (c2 = c1) as h by eauto 3 with kn;
             subst c2

           | [ H1 : state_before ?e ?mem1
                    , H2 : state_before ?e ?mem2 |- _ ] =>
             let h := fresh "h" in
             assert (mem2 = mem1) as h by eauto 3 with kn;
             subst mem2

           | [ H1 : state_after ?e ?mem1
                    , H2 : state_after ?e ?mem2 |- _ ] =>
             let h := fresh "h" in
             assert (mem2 = mem1) as h by eauto 3 with kn;
             subst mem2

           | [ H1 : trusted_state_before ?e ?mem1
                    , H2 : trusted_state_before ?e ?mem2 |- _ ] =>
             let h := fresh "h" in
             assert (mem2 = mem1) as h by eauto 3 with kn;
             subst mem2

           | [ H1 : trusted_state_after ?e ?mem1
                    , H2 : trusted_state_after ?e ?mem2 |- _ ] =>
             let h := fresh "h" in
             assert (mem2 = mem1) as h by eauto 3 with kn;
             subst mem2
           end.

  Lemma same_id_sym :
    forall t1 t2, same_id t1 t2 -> same_id t2 t1.
  Proof.
    introv h; unfold same_id in *; auto.
    exrepnd; eexists; eauto.
  Qed.
  Hint Resolve same_id_sym : kn.

(*  Lemma in_no_repeats_id_unique :
    forall t1 t2 l,
      in_no_repeats_id t1 l
      -> in_no_repeats_id t2 l
      -> same_id t1 t2
      -> t1 = t2.
  Proof.
    introv i j sc.
    unfold in_no_repeats_id in *; repnd.
    induction l; simpl in *; tcsp.
    repndors; subst; tcsp.

    { allrw no_repeats_cons; repnd; GC.
      destruct i.
      rw in_map_iff.
      exists t1; dands; auto. }

    { allrw no_repeats_cons; repnd; GC.
      destruct i.
      rw in_map_iff.
      exists t2; dands; auto. }

    { allrw no_repeats_cons; repnd; GC.
      repeat (autodimp IHl hyp). }
  Qed.*)

(*  Lemma trusted_out_unique_is_unique :
    forall {eo : EventOrdering} (e : Event) t1 t2,
      trusted_out_unique e t1
      -> trusted_out_unique e t2
      -> same_id t1 t2
      -> t1 = t2.
  Proof.
    introv ka kb eqc; unfold trusted_out_unique in *; exrepnd.
    eapply in_no_repeats_id_unique; eauto.
  Qed.*)

  Lemma id_before_unique :
    forall {eo : EventOrdering} (e : Event) c1 c2,
      id_before e c1
      -> id_before e c2
      -> c1 = c2.
  Proof.
    introv ca cb; unfold id_before in *; exrepnd.
    eq_states; tcsp.
  Qed.

  (*Lemma generates_trusted_unique :
    forall {eo : EventOrdering} (e : Event) t1 t2,
      disseminate_trusted_unique e
      -> generates_trusted e t1
      -> generates_trusted e t2
      -> same_id t1 t2
      -> t1 = t2.
  Proof.
    introv uniq gena genb sc; unfold generates_trusted in *; exrepnd; tcsp.
  Qed.*)


  (*  Definition generates_trusted
             {eo : EventOrdering}
             (e  : Event)
             (i  : kc_data)
             (t  : kc_trust) :=
    exists (mem1 mem2 : kc_mem_comp) (c : nat),
      never_Tknew e i t
      /\ state_before e mem1
      /\ state_after e mem2
      /\ kc_createTrusted i mem2 = t (* FIX: Is this the one we need? We need something about the input*)
      /\ kc_getId mem1 = c
      /\ kc_getId mem2 = S(c)
      /\ kc_id t = S(c)
      /\ kc_trust_is_owned e t.*)

(*  Definition simple_monotonicity (eo : EventOrdering) :=
    forall (e : Event),
      ex_node_e e
      ->
      exists c,
        id_before e c
        /\ (id_after e c \/ id_after e (S c)).*)

  Definition learns_data {eo : EventOrdering} (e : Event) (d : kc_data) :=
    exists (n : node_type) (a : AuthenticatedData),
      loc e = node2name n
      /\ In a (bind_op_list get_contained_authenticated_data (trigger_op e))
      /\ In d (kc_auth2data a)
      /\ kc_verify e a = true.

  (* Gen generated some information if
         (1) it wasn't in our state before
         (2) some trusted knowledge is created, based on some info that is already stored in the state
         (3) we own the trusted the information
         (4) trusted knowledge is the part of the generated data
         (5) data is in our state now
   *)
  Definition generates_data {eo : EventOrdering} (e : Event) (d : kc_data) :=
    (*      exists( (mem : kc_mem_comp) t d',*)
    never_knew e d                 (*(1)*)
    (*      /\ kc_createTrusted d' mem = t /\ knows_before  e d'    (*(2)*)
      /\ kc_trust_is_owned e t       (*(3)*)
      /\ In t (kc_data2kc_Tinfo d)   (*(4)*)*)
    /\ knows_after e d             (*(5)*)
    /\ data_is_owned e d.

  (*FIX add the claim about trusted knowledge!!! *)
  Definition knows_data_certificate {eo : EventOrdering} (e : Event) n P :=
    exists (l : list kc_data),
      n <= length l
      /\ no_repeats (map kc_data2owner l)
      /\ P l
      /\ forall d, In d l -> knows_after e d.

  Lemma in_M_output_sys_on_event_implies_disseminate :
    forall {eo : EventOrdering} (e : Event) m dst t d,
      In (MkDMsg m dst t) (M_output_sys_on_event kc_sys e)
      -> In d (kc_msg2data m)
      -> disseminate_data e d.
  Proof.
    introv h j.
    unfold disseminate_data; simpl.
    apply in_M_output_sys_on_event_implies_in_byz in h; exrepnd.
    allrw; eexists; dands; eauto.
    clear h1.
    unfold dmsg_is_in_out, data_is_in_out, event2out, trigger_info2out in *; simpl in *.
    remember (trigger e) as trig; destruct trig; simpl in *; tcsp.
    apply in_flat_map; eexists; dands; eauto.
  Qed.
  Hint Resolve in_M_output_sys_on_event_implies_disseminate : kn.

  Definition preserves_knows_step {eo : EventOrdering} (e : Event) (d : kc_data) :=
    forall ls1 mem1,
      isCorrect e
      -> M_run_ls_before_event (kc_sys (loc e)) e = Some ls1
      -> state_of_component kc_mem_comp ls1 = Some mem1
      -> kc_knows d mem1
      -> exists ls2 mem2,
          M_run_ls_on_this_one_event ls1 e = Some ls2
          /\ state_of_component kc_mem_comp ls2 = Some mem2
          /\ kc_knows d mem2.

  Lemma knows_after_preserved_step :
    forall {eo : EventOrdering} (e1 e2 : Event) d,
      e1 ⊂ e2
      -> isCorrect e2
      -> preserves_knows_step e2 d
      -> knows_after e1 d
      -> knows_after e2 d.
  Proof.
    introv lte isCor pres ka.
    unfold knows_after in *; exrepnd.
    unfold state_after in *; exrepnd.
    unfold M_state_sys_on_event in *; simpl in *.
    unfold M_state_ls_on_event in *.
    apply map_option_Some in ka2; exrepnd; rev_Some; simpl in *.
    rewrite M_run_ls_on_event_unroll2.

    assert (loc e2 = loc e1) as eqloc by (symmetry; eauto 3 with eo).

    revert dependent a.
    rewrite <- eqloc.
    introv run eqst.

    pose proof (pres a mem) as q.
    repeat (autodimp q hyp).
    { rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred; eauto 3 with eo.
      applydup pred_implies_local_pred in lte; subst; auto. }
    exrepnd.

    exists mem2.
    dands; auto.
    exists n; dands; auto; try congruence;[].
    allrw; simpl in *.
    rewrite M_run_ls_before_event_as_M_run_ls_on_event_pred; eauto 3 with eo.
    applydup pred_implies_local_pred in lte; subst; auto.
    revert dependent a.
    revert dependent ls2.
    autorewrite with eo in *; GC.
    rewrite ka1.
    introv eqsta eqstb runa runb.
    repeat (allrw; simpl in *; auto).
  Qed.

  (* ******************************************************************* *)



  (* ******************************************************************* *)
  (*  ****** SIMPLE TYPES ****** *)

  Inductive KType :=
  | KT_ID
  | KT_TRUST
  | KT_DATA
  | KT_NODE.

  Inductive KVal : KType -> Type :=
  | KV_ID    (i : kc_id)     : KVal KT_ID
  | KV_TRUST (t : kc_trust)  : KVal KT_TRUST
  | KV_DATA  (d : kc_data)   : KVal KT_DATA
  | KV_NODE  (n : node_type) : KVal KT_NODE.

  (* ******************************************************************* *)



  (* ******************************************************************* *)
  (*  ****** PRIMITIVES ****** *)

  (* Knowledge Expression *)
  Inductive KExpression :=

  (* first-order logic *)
  | KE_AND      (a b : KExpression)
  | KE_OR       (a b : KExpression)
  | KE_IMPLIES  (a b : KExpression)
  | KE_EX  (T : KType) (f : KVal T -> KExpression)
  | KE_ALL (T : KType) (f : KVal T -> KExpression)

  (* logic of events *)
  | KE_RIGHT_BEFORE    (f : KExpression)
  | KE_HAPPENED_BEFORE (f : KExpression)
  | KE_FORALL_BEFORE   (f : KExpression)

  | KE_CORRECT
  | KE_AT (n : node_type)

  (* data comparison *)
  | KE_SIMILAR_DATA  (a b : kc_data)
  | KE_SIMILAR_TRUST (a b : kc_trust)
  | KE_VAL_EQ        {T : KType} (a b : KVal T)
  | KE_ID_LT         (a b : kc_id)

  (* non-trusted knowledge *)
  | KE_LEARNS (d : kc_data)
  | KE_KNOWS  (d : kc_data)
  | KE_DISS   (d : kc_data) (* dissemination *)

  (* trusted knowledge *)
  | KE_ID_AFTER     (c : kc_id)
  | KE_TRUST_HAS_ID (t : kc_trust) (c : kc_id)
  | KE_HAS_OWNER    (d : kc_data)  (n : node_type)
  | KE_GEN_FOR      (d : kc_data)  (t : kc_trust)
  | KE_IN           (t : kc_trust) (d : kc_data)
  | KE_HAS_INIT_ID  (i : kc_id)

  (* ******************** *)
  (* *** EXPERIMENTAL *** *)
  (* external knowledge *)
  | KE_EXT_PRIM (p : kc_ExtPrim)
  | KE_EXT_KNOW (f : KExpression).

  (* ******************************************************************* *)




  (* ******************************************************************* *)
  (*  ****** NON-PRIMITIVES ****** *)

  Definition ktype2type (T : KType) : Type :=
    match T with
    | KT_ID    => kc_id
    | KT_TRUST => kc_trust
    | KT_DATA  => kc_data
    | kC_NODE  => node_type
    end.

  Definition ktype2type2val {T : KType} (v : ktype2type T) : KVal T.
  Proof.
    destruct T; simpl in *.
    - exact (KV_ID v).
    - exact (KV_TRUST v).
    - exact (KV_DATA v).
    - exact (KV_NODE v).
  Defined.

  Definition kval2id (v : KVal KT_ID) : kc_id :=
    match v with
    | KV_ID i => i
    end.

  Definition kval2trust (v : KVal KT_TRUST) : kc_trust :=
    match v with
    | KV_TRUST t => t
    end.

  Definition kval2data (v : KVal KT_DATA) : kc_data :=
    match v with
    | KV_DATA d => d
    end.

  Definition kval2node (v : KVal KT_NODE) : node_type :=
    match v with
    | KV_NODE n => n
    end.

  Definition KE_DATA_EQ (a b : kc_data) : KExpression :=
    KE_VAL_EQ (KV_DATA a) (KV_DATA b).

  Definition KE_ID_EQ (a b : kc_id) : KExpression :=
    KE_VAL_EQ (KV_ID a) (KV_ID b).

  Definition KE_NODE_EQ (a b : node_type) : KExpression :=
    KE_VAL_EQ (KV_NODE a) (KV_NODE b).

  Definition KE_TRUST_EQ (a b : kc_trust) : KExpression :=
    KE_VAL_EQ (KV_TRUST a) (KV_TRUST b).


  (* universal quantifiers *)
  Definition KE_ALL_ID (f : kc_id -> KExpression) : KExpression :=
    KE_ALL KT_ID (fun i => f (kval2id i)).

  Definition KE_ALL_TRUST (f : kc_trust -> KExpression) : KExpression :=
    KE_ALL KT_TRUST (fun t => f (kval2trust t)).

  Definition KE_ALL_DATA (f : kc_data -> KExpression) : KExpression :=
    KE_ALL KT_DATA (fun d => f (kval2data d)).

  Definition KE_ALL_NODE (f : node_type -> KExpression) : KExpression :=
    KE_ALL KT_NODE (fun n => f (kval2node n)).


  (* existential quantifiers *)
  Definition KE_EX_ID (f : kc_id -> KExpression) : KExpression :=
    KE_EX KT_ID (fun i => f (kval2id i)).

  Definition KE_EX_TRUST (f : kc_trust -> KExpression) : KExpression :=
    KE_EX KT_TRUST (fun t => f (kval2trust t)).

  Definition KE_EX_DATA (f : kc_data -> KExpression) : KExpression :=
    KE_EX KT_DATA (fun d => f (kval2data d)).

  Definition KE_EX_NODE (f : node_type -> KExpression) : KExpression :=
    KE_EX KT_NODE (fun n => f (kval2node n)).


  (* True/False *)
  Definition KE_TRUE  := KE_ALL_ID (fun i => KE_ID_EQ i i).
  Definition KE_FALSE := KE_EX_ID (fun i => KE_ID_LT i i).


  (* Negation *)
  Definition KE_NOT (a : KExpression) : KExpression := KE_IMPLIES a KE_FALSE.


  (* First *)
  Definition KE_NOT_FIRST : KExpression := KE_RIGHT_BEFORE KE_TRUE.
  Definition KE_FIRST := KE_NOT KE_NOT_FIRST.


  (* multi-functions *)
  Fixpoint funN (n : nat) (A B : Type) : Type :=
    match n with
    | 0 => A -> B
    | S n => A -> funN n A B
    end.

  Notation "A -( n )-> B" := (funN n A B) (at level 80).

  Lemma funNS2N {n : nat} {A B : Type} (f : funN (S n) A B) (a : A) : funN n A B.
  Proof.
    destruct n; simpl in *; exact (f a).
  Defined.

  Fixpoint funN_map {n : nat} {A B X} (f : X -> A) : (A -(n)-> B) -> (X -(n)-> B) :=
    match n with
    | 0 => fun g => fun x => g (f x)
    | S n => fun g => fun x => funN_map f (g (f x))
    end.


  (* multi-quantifiers *)
  Fixpoint KE_ALLs {T : KType} {n : nat} : ((KVal T) -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_ALL T f
    | S n => fun f => KE_ALL T (fun v => KE_ALLs (funNS2N f v))
    end.

  (*Definition KE_ALL_IDs {n : nat} (f : kc_id -(n)-> KExpression) : KExpression :=
    KE_ALLs (funN_map kval2id f).*)
  Fixpoint KE_ALL_IDs {n : nat} : (kc_id -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_ALL_ID f
    | S n => fun f => KE_ALL_ID (fun v => KE_ALL_IDs (funNS2N f v))
    end.

  (*Definition KE_ALL_TRUSTs {n : nat} (f : kc_trust -(n)-> KExpression) : KExpression :=
    KE_ALLs (funN_map kval2trust f).*)
  Fixpoint KE_ALL_TRUSTs {n : nat} : (kc_trust -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_ALL_TRUST f
    | S n => fun f => KE_ALL_TRUST (fun v => KE_ALL_TRUSTs (funNS2N f v))
    end.

  (*Definition KE_ALL_DATAs {n : nat} (f : kc_data -(n)-> KExpression) : KExpression :=
    KE_ALLs (funN_map kval2data f).*)
  Fixpoint KE_ALL_DATAs {n : nat} : (kc_data -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_ALL_DATA f
    | S n => fun f => KE_ALL_DATA (fun v => KE_ALL_DATAs (funNS2N f v))
    end.

  (*Definition KE_ALL_NODEs {n : nat} (f : node_type -(n)-> KExpression) : KExpression :=
    KE_ALLs (funN_map kval2node f).*)
  Fixpoint KE_ALL_NODEs {n : nat} : (node_type -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_ALL_NODE f
    | S n => fun f => KE_ALL_NODE (fun v => KE_ALL_NODEs (funNS2N f v))
    end.

  Fixpoint KE_EXs {T : KType} {n : nat} : ((KVal T) -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_EX T f
    | S n => fun f => KE_EX T (fun v => KE_EXs (funNS2N f v))
    end.

  (*Definition KE_EX_IDs {n : nat} (f : kc_id -(n)-> KExpression) : KExpression :=
    KE_EXs (funN_map kval2id f).*)
  Fixpoint KE_EX_IDs {n : nat} : (kc_id -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_EX_ID f
    | S n => fun f => KE_EX_ID (fun v => KE_EX_IDs (funNS2N f v))
    end.

  (*Definition KE_EX_TRUSTs {n : nat} (f : kc_trust -(n)-> KExpression) : KExpression :=
    KE_EXs (funN_map kval2trust f).*)
  Fixpoint KE_EX_TRUSTs {n : nat} : (kc_trust -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_EX_TRUST f
    | S n => fun f => KE_EX_TRUST (fun v => KE_EX_TRUSTs (funNS2N f v))
    end.

  (*Definition KE_EX_DATAs {n : nat} (f : kc_data -(n)-> KExpression) : KExpression :=
    KE_EXs (funN_map kval2data f).*)
  Fixpoint KE_EX_DATAs {n : nat} : (kc_data -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_EX_DATA f
    | S n => fun f => KE_EX_DATA (fun v => KE_EX_DATAs (funNS2N f v))
    end.

  (*Definition KE_EX_NODEs {n : nat} (f : node_type -(n)-> KExpression) : KExpression :=
    KE_EXs (funN_map kval2node f).*)
  Fixpoint KE_EX_NODEs {n : nat} : (node_type -(n)-> KExpression) -> KExpression :=
    match n with
    | 0 => fun f => KE_EX_NODE f
    | S n => fun f => KE_EX_NODE (fun v => KE_EX_NODEs (funNS2N f v))
    end.


  (* restricted multi-quantifiers *)
  Definition KE_ALL_ID2 (f : kc_id -> kc_id -> KExpression) : KExpression :=
    @KE_ALL_IDs 1 f.

  Definition KE_ALL_TRUST2 (f : kc_trust -> kc_trust -> KExpression) : KExpression :=
    @KE_ALL_TRUSTs 1 f.

  Definition KE_ALL_DATA2 (f : kc_data -> kc_data -> KExpression) : KExpression :=
    @KE_ALL_DATAs 1 f.

  Definition KE_ALL_NODE2 (f : node_type -> node_type -> KExpression) : KExpression :=
    @KE_ALL_NODEs 1 f.


  Definition KE_ALL_ID3 (f : kc_id -> kc_id -> kc_id -> KExpression) : KExpression :=
    @KE_ALL_IDs 2 f.

  Definition KE_ALL_TRUST3 (f : kc_trust -> kc_trust -> kc_trust -> KExpression) : KExpression :=
    @KE_ALL_TRUSTs 2 f.

  Definition KE_ALL_DATA3 (f : kc_data -> kc_data -> kc_data -> KExpression) : KExpression :=
    @KE_ALL_DATAs 2 f.

  Definition KE_ALL_NODE3 (f : node_type -> node_type -> node_type -> KExpression) : KExpression :=
    @KE_ALL_NODEs 2 f.


  Definition KE_EX_ID2 (f : kc_id -> kc_id -> KExpression) : KExpression :=
    @KE_EX_IDs 1 f.

  Definition KE_EX_TRUST2 (f : kc_trust -> kc_trust -> KExpression) : KExpression :=
    @KE_EX_TRUSTs 1 f.

  Definition KE_EX_DATA2 (f : kc_data -> kc_data -> KExpression) : KExpression :=
    @KE_EX_DATAs 1 f.

  Definition KE_EX_NODE2 (f : node_type -> node_type -> KExpression) : KExpression :=
    @KE_EX_NODEs 1 f.


  Definition KE_EX_ID3 (f : kc_id -> kc_id -> kc_id -> KExpression) : KExpression :=
    @KE_EX_IDs 2 f.

  Definition KE_EX_TRUST3 (f : kc_trust -> kc_trust -> kc_trust -> KExpression) : KExpression :=
    @KE_EX_TRUSTs 2 f.

  Definition KE_EX_DATA3 (f : kc_data -> kc_data -> kc_data -> KExpression) : KExpression :=
    @KE_EX_DATAs 2 f.

  Definition KE_EX_NODE3 (f : node_type -> node_type -> node_type -> KExpression) : KExpression :=
    @KE_EX_NODEs 2 f.


  Definition KE_NODE := KE_EX_NODE KE_AT.

  Definition KE_LOCAL_BEFORE t :=
    KE_EX_NODE
      (fun n =>
         KE_AND
           (KE_AT n)
           (KE_HAPPENED_BEFORE (KE_AND (KE_AT n) t))).

  Definition KE_LOCAL_FORALL_BEFORE (t : KExpression) :=
    KE_EX_NODE
      (fun n =>
         KE_AND
           (KE_AT n)
           (KE_FORALL_BEFORE (KE_IMPLIES (KE_AT n) t))).

  Definition KE_RIGHT_BEFORE_EQ t := KE_OR (KE_RIGHT_BEFORE t) (KE_AND t KE_FIRST).
  Definition KE_LOCAL_BEFORE_EQ t := KE_OR (KE_LOCAL_BEFORE t) (KE_AND t KE_NODE).
  Definition KE_HAPPENED_BEFORE_EQ t := KE_OR (KE_HAPPENED_BEFORE t) (KE_AND t KE_NODE).
  Definition KE_LOCAL_FORALL_BEFORE_EQ t := KE_AND (KE_LOCAL_FORALL_BEFORE t) t.
  Definition KE_FORALL_BEFORE_EQ t := KE_AND (KE_FORALL_BEFORE t) t.

  Definition KE_CORRECT_TRACE_BEFORE (n : option node_type) : KExpression :=
    match n with
    | Some n =>
      KE_FORALL_BEFORE_EQ (KE_IMPLIES (KE_AT n) (KE_LOCAL_FORALL_BEFORE_EQ KE_CORRECT))
    | None => KE_LOCAL_FORALL_BEFORE_EQ KE_CORRECT
    end.

  Definition KE_LOCAL_CORRECT_TRACE_BEFORE : KExpression :=
    KE_CORRECT_TRACE_BEFORE None.


  Definition KE_AND3 (a b c : KExpression) : KExpression :=
    KE_AND a (KE_AND b c).


  Definition KE_KNEW (d : kc_data) : KExpression :=
    KE_RIGHT_BEFORE (KE_KNOWS d).

  Definition KE_ID_BEFORE (c : kc_id) : KExpression :=
    KE_OR
      (KE_RIGHT_BEFORE (KE_ID_AFTER c))
      (KE_AND3 KE_FIRST KE_NODE (KE_HAS_INIT_ID c)).


  Definition KE_OWNS (d : kc_data) :=
    KE_EX_NODE (fun n => KE_AND (KE_AT n) (KE_HAS_OWNER d n)).

  Definition KE_TOWNS (t : kc_trust) : KExpression :=
    KE_OWNS (kc_trust2data t).

  Definition KE_DISS_OWN (d : kc_data) : KExpression :=
    KE_AND (KE_DISS d) (KE_OWNS d).

  Definition KE_TDISS_OWN (t : kc_trust) : KExpression :=
    KE_DISS_OWN (kc_trust2data t).

  Definition KE_HAS_TOWNER (t : kc_trust) (n : node_type) :=
    KE_HAS_OWNER (kc_trust2data t) n.

  Fixpoint KE_ANDS (l : list KExpression) : KExpression :=
    match l with
    | [] => KE_TRUE
    | e :: l => KE_AND e (KE_ANDS l)
    end.

  Fixpoint KE_ORS (l : list KExpression) : KExpression :=
    match l with
    | [] => KE_FALSE
    | e :: l => KE_OR e (KE_ORS l)
    end.

  Definition KE_TGENS :=
    KE_EX_ID2
      (fun c1 c2 =>
         KE_ANDS
           [ KE_ID_LT c1 c2,
             KE_ID_BEFORE c1,
             KE_ID_AFTER c2]).

  Definition KE_NO_TGENS :=
    KE_EX_ID
      (fun c =>
         KE_ANDS
           [ KE_ID_BEFORE c,
             KE_ID_AFTER c
           ]).

  Definition KE_ID_LE a b := KE_OR (KE_ID_LT a b) (KE_ID_EQ a b).

  Definition KE_TKNOWS (t : kc_trust) : KExpression :=
    KE_KNOWS (kc_trust2data t).

  Definition KE_TLEARNS (t : kc_trust) : KExpression :=
    KE_LEARNS (kc_trust2data t).

  Definition KE_TKNEW (t : kc_trust) : KExpression :=
    KE_KNEW (kc_trust2data t).

  (* FIX: it used to be happened_before, but in that case it is incompatible with the definition of knew *)
  Definition KE_OWNED (d : kc_data) : KExpression :=
    KE_RIGHT_BEFORE_EQ (KE_OWNS d).

  Definition KE_TOWNED (t : kc_trust) : KExpression :=
    KE_RIGHT_BEFORE_EQ (KE_TOWNS t).

  Definition KE_LEARNED (d : kc_data) : KExpression :=
    KE_LOCAL_BEFORE_EQ (KE_LEARNS d).

  Definition KE_TLEARNED (t : kc_trust): KExpression :=
    KE_LOCAL_BEFORE_EQ (KE_TLEARNS t).


  (* ******************************************************************* *)



  (* ******************************************************************* *)
  (*  ******  ****** *)

  Record kc_same_state
             (eo  : EventOrdering)
             (e   : Event)
             (eo' : EventOrdering)
             (e'  : Event) :=
    {
      kc_same_state_event : trigger e = trigger e';
      kc_same_state_trig  : map trigger (localPreds e) = map trigger (localPreds e');
      kc_same_state_loc   : loc e = loc e';
    }.

  Lemma kc_same_state_refl :
    forall {eo : EventOrdering} (e : Event),
      kc_same_state eo e eo e.
  Proof.
    introv; tcsp.
    split; auto.
  Qed.

  Lemma kc_same_state_sym :
    forall (eo : EventOrdering) (e : Event)
           (eo' : EventOrdering) (e' : Event),
      kc_same_state eo e eo' e'
      -> kc_same_state eo' e' eo e.
  Proof.
    introv h.
    destruct h as [sse sst ssl].
    split; auto.
  Qed.

  Lemma kc_same_state_trans :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event)
           (eo3 : EventOrdering) (e3 : Event),
      kc_same_state eo1 e1 eo2 e2
      -> kc_same_state eo2 e2 eo3 e3
      -> kc_same_state eo1 e1 eo3 e3.
  Proof.
    introv h q.
    destruct h as [sse1 sst1 ssl1].
    destruct q as [sse2 sst2 ssl2].
    split; try congruence.
  Qed.

  Lemma kc_same_state_implies_eq_loc :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event),
      kc_same_state eo1 e1 eo2 e2
      -> loc e1 = loc e2.
  Proof.
    introv same.
    destruct same as [sse sst ssl]; auto.
  Qed.

  Lemma kc_same_state_implies_eq_trigger :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event),
      kc_same_state eo1 e1 eo2 e2
      -> trigger e1 = trigger e2.
  Proof.
    introv same.
    destruct same as [sse sst ssl]; auto.
  Qed.

  Lemma kc_same_state_implies_eq_trigger_op :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event),
      kc_same_state eo1 e1 eo2 e2
      -> trigger_op e1 = trigger_op e2.
  Proof.
    introv same.
    apply kc_same_state_implies_eq_trigger in same.
    unfold trigger_op; allrw; auto.
  Qed.

  Lemma kc_same_state_implies_eq_history :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event),
      kc_same_state eo1 e1 eo2 e2
      -> map trigger (localPreds e1) = map trigger (localPreds e2).
  Proof.
    introv same.
    destruct same as [sse sst ssl]; auto.
  Qed.

  Lemma kc_same_state_implies_eq_history_op :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event),
      kc_same_state eo1 e1 eo2 e2
      -> map trigger_op (localPreds e1) = map trigger_op (localPreds e2).
  Proof.
    introv same.
    apply kc_same_state_implies_eq_history in same.
    remember (localPreds e1) as L; clear HeqL.
    remember (localPreds e2) as K; clear HeqK.
    revert dependent K.
    induction L; introv h; simpl in *; tcsp.
    { destruct K; simpl in *; tcsp. }
    destruct K; simpl in *; ginv.
    inversion h.
    rewrite (IHL K); tcsp; f_equal.
    unfold trigger_op; allrw; auto.
  Qed.

  Lemma kc_same_state_preserves_loc :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event)
           (n : node_type),
      kc_same_state eo1 e1 eo2 e2
      -> loc e1 = node2name n
      -> loc e2 = node2name n.
  Proof.
    introv same h.
    apply kc_same_state_implies_eq_loc in same; try congruence.
  Qed.

  Lemma kc_same_state_preserves_run_ls_on_event :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event)
           {L S}
           (ls : LocalSystem L S) m,
      kc_same_state eo1 e1 eo2 e2
      -> M_run_ls_on_event ls e1 = Some m
      -> M_run_ls_on_event ls e2 = Some m.
  Proof.
    introv same h.
    unfold M_run_ls_on_event in *.
    unfold M_run_ls_before_event in *.
    applydup kc_same_state_implies_eq_history_op in same.
    applydup kc_same_state_implies_eq_trigger_op in same.
    rewrite <- same0, <- same1; auto.
  Qed.

  Lemma kc_same_state_preserves_state_sys_on_event :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event)
           m1 m2,
      kc_same_state eo1 e1 eo2 e2
      -> M_state_sys_on_event kc_sys e1 m1 = Some m2
      -> M_state_sys_on_event kc_sys e2 m1 = Some m2.
  Proof.
    introv same h.

    unfold M_state_sys_on_event in *; simpl in *.
    applydup kc_same_state_implies_eq_loc in same as eqloc.
    rewrite <- eqloc.
    remember (kc_sys (loc e1)) as ls; clear Heqls.

    unfold M_state_ls_on_event in *.
    apply map_option_Some in h; exrepnd.
    apply map_option_Some.
    exists a; dands; auto.

    eapply kc_same_state_preserves_run_ls_on_event in same; eauto.
  Qed.

  Lemma same_state_preserves_knows_after :
    forall (eo1 : EventOrdering) (e1 : Event)
           (eo2 : EventOrdering) (e2 : Event)
           (d : kc_data),
      kc_same_state eo1 e1 eo2 e2
      -> knows_after e1 d
      -> knows_after e2 d.
  Proof.
    introv same kn.
    unfold knows_after in *; exrepnd.
    exists mem; dands; auto.
    unfold state_after in *; exrepnd.
    exists n; dands.
    { eapply kc_same_state_preserves_loc in same; eauto. }
    eapply kc_same_state_preserves_state_sys_on_event in same; eauto.
  Qed.

  Definition has_init_id {eo : EventOrdering} (e : Event) (i : kc_id) : Prop :=
    exists m,
      state_of_component (pre2trusted kc_trust_comp) (kc_sys (loc e)) = Some m
      /\ kc_getId m = i.

  Lemma has_init_id_unique :
    forall {eo : EventOrdering} (e : Event) (i1 i2 : kc_id),
      has_init_id e i1
      -> has_init_id e i2
      -> i1 = i2.
  Proof.
    introv h q.
    unfold has_init_id in *; exrepnd.
    rewrite h1 in *; ginv.
  Qed.

  (* ******************************************************************* *)



  (* ******************************************************************* *)
  (*  ****** SEMANTICS OF CALCULUS ****** *)

  Fixpoint interpret
           {eo    : EventOrdering}
           (e     : Event)
           (exp   : KExpression) : Prop :=
    match exp with

    (* first-order logic *)
    | KE_AND     a b => interpret e a /\ interpret e b
    | KE_OR      a b => interpret e a \/ interpret e b
    | KE_IMPLIES a b => interpret e a -> interpret e b

    | KE_EX  T f => exists (c : ktype2type T), interpret e (f (ktype2type2val c))
    | KE_ALL T f => forall (c : ktype2type T), interpret e (f (ktype2type2val c))

    (* logic of events *)
    | KE_RIGHT_BEFORE f =>
      match direct_pred e with
      | Some e' => interpret e' f
      | None => False
      end

    | KE_HAPPENED_BEFORE f => exists (e' : EventN), e' ≺ e /\ interpret e' f
    | KE_FORALL_BEFORE   f => forall (e' : EventN), e' ≺ e -> interpret e' f

    | KE_CORRECT => isCorrect e
    | KE_AT n => loc e = node2name n

    (* data comparison *)
    | KE_SIMILAR_DATA  a b => a ≍ b
    | KE_SIMILAR_TRUST a b => a ≈ b
    | KE_VAL_EQ        a b => a = b
    | KE_ID_LT         a b => a ≪ b

    (* non-trusted knowledge *)
    | KE_LEARNS d => learns_data e d
    | KE_KNOWS  d => knows_after e d
    | KE_DISS   d => disseminate_data e d

    (* trusted knowledge *)
    | KE_ID_AFTER     c   => id_after e c
    | KE_TRUST_HAS_ID t c => kc_trust_has_id t c
    | KE_HAS_OWNER    d n => data_is_owned_by n d
    | KE_GEN_FOR      d t => kc_generated_for d t
    | KE_IN           t d => In t (kc_data2trust d)
    | KE_HAS_INIT_ID  i   => has_init_id e i

    (* ******************** *)
    (* *** EXPERIMENTAL *** *)
    (* external knowledge *)
    | KE_EXT_PRIM p => kc_ext_prim_interp eo e p
    | KE_EXT_KNOW f =>
      forall {eo' : EventOrdering} (e' : Event),
        kc_same_state eo e eo' e'
        -> interpret e' f
    end.

  (* ******************************************************************* *)



  (* ******************************************************************* *)
  (*  ****** RULES + SEMANTICS OF RULES ****** *)

  Definition HName := String.string.
  Definition HName_dec : Deq HName := String.string_dec.

  Definition local_pred_n {eo : EventOrdering} (e : EventN) :=
    MkEventN (local_pred e) (implies_ex_node_e_local_pred (en_node e)).

  Record KExpAt {eo : EventOrdering} :=
    MkKExpAt
      {
        exp_at_exp   :> KExpression;
        exp_at_event : EventN;
      }.
  Global Arguments MkKExpAt [eo] _ _.
  Notation "a @ b" := (MkKExpAt a b) (at level 68).

  Record hypothesis {eo : EventOrdering} :=
    MkHyp
      {
        hyp_name : HName;
        hyp_exp  :> KExpAt;
      }.
  Global Arguments MkHyp [eo] _ _.
  Notation "a › b" := (MkHyp a b) (at level 69).

  Definition hypotheses {eo : EventOrdering} := list hypothesis.
  Definition emHyps {eo : EventOrdering} : hypotheses := [].
  Global Arguments emHyps [eo].
  Notation "∅" := emHyps.
  Definition addHyp {eo : EventOrdering} (H : hypotheses) (h : hypothesis) : hypotheses :=
    snoc H h.
  Notation "H • h" := (addHyp H h) (at level 70).
  Definition addHyps {eo : EventOrdering} (H J : hypotheses) : hypotheses :=
    H ++ J.
  Notation "H » J" := (addHyps H J) (at level 70).

  Inductive causalRel {eo : EventOrdering} : Type :=
  | causal_rel_eq                 (e1 e2 : EventN)
  | causal_rel_right_before       (e1 e2 : EventN)
  | causal_rel_local_before       (e1 e2 : EventN)
  | causal_rel_local_before_eq    (e1 e2 : EventN)
  | causal_rel_happened_before    (e1 e2 : EventN)
  | causal_rel_happened_before_eq (e1 e2 : EventN).
  Notation "e1 ≡ e2" := (causal_rel_eq                 e1 e2) (at level 69).
  Notation "e1 ⋄ e2" := (causal_rel_right_before       e1 e2) (at level 69).
  Notation "e1 □ e2" := (causal_rel_local_before       e1 e2) (at level 69).
  Notation "e1 ■ e2" := (causal_rel_local_before_eq    e1 e2) (at level 69).
  Notation "e1 ▷ e2" := (causal_rel_happened_before    e1 e2) (at level 69).
  Notation "e1 ▶ e2" := (causal_rel_happened_before_eq e1 e2) (at level 69).

  Record namedCausalRel {eo : EventOrdering} :=
    MkNamedCausalRel
      {
        ncr_name : String.string;
        ncr_rel  :> causalRel;
      }.
  Global Arguments MkNamedCausalRel [eo] _ _.
  Notation "a ⋈ b" := (MkNamedCausalRel a b) (at level 70).

  Record sequent {eo : EventOrdering} :=
    MkSeq
      {
        seq_causal : list namedCausalRel;
        seq_hyps   : list hypothesis;
        seq_concl  : KExpAt;
      }.
  Global Arguments MkSeq [eo] _ _ _.
  Notation "⟬ R ⟭ H ⊢ C" := (MkSeq R H C) (at level 70).
(*  Notation "H ⊢ C" := (MkSeq H [] C) (at level 70).*)

  Definition mk_v1 {A} (a : A) : Vector.t A 1 :=
    Vector.cons _ a _ (Vector.nil _).

  Definition mk_v2 {A} (a b : A) : Vector.t A 2 :=
    Vector.cons _ a _ (Vector.cons _ b _ (Vector.nil _)).

  Definition mk_v3 {A} (a b c : A) : Vector.t A 3 :=
    Vector.cons _ a _ (Vector.cons _ b _ (Vector.cons _ c _ (Vector.nil _))).

  Record rule_hypotheses {eo : EventOrdering} :=
    MkRuleHypotheses
      {
        rh_e : nat;
        rh_t : nat;
        rh_d : nat;
        rh_c : nat;
        rh_n : nat;
        rh_f : Vector.t EventN rh_e -> Vector.t kc_trust rh_t -> Vector.t kc_data rh_d -> Vector.t kc_id rh_c -> Vector.t node_type rh_n -> list sequent;
      }.
  Global Arguments MkRuleHypotheses [eo] _ _ _ _ _.

  Record rule {eo : EventOrdering} :=
    MkRule
      {
        rule_hyps  : rule_hypotheses;
        rule_concl : sequent;
      }.
  Global Arguments MkRule [eo] _ _.

  Definition MkRuleHypotheses0 {eo : EventOrdering} (hyps : list sequent) : rule_hypotheses :=
    MkRuleHypotheses 0 0 0 0 0 (fun _ _ _ _ _ => hyps).

  Definition MkRuleHypotheses1e {eo : EventOrdering} (hyps : EventN -> list sequent) : rule_hypotheses :=
    MkRuleHypotheses 1 0 0 0 0 (fun l _ _ _ _ => hyps (Vector.hd l)).

  Definition MkRuleHypotheses2e {eo : EventOrdering} (hyps : EventN -> EventN -> list sequent) : rule_hypotheses :=
    MkRuleHypotheses 2 0 0 0 0 (fun l _ _ _ _ => hyps (Vector.hd l) (Vector.hd (Vector.tl l))).

  Definition MkRuleHypotheses3e {eo : EventOrdering} (hyps : EventN -> EventN -> EventN -> list sequent) : rule_hypotheses :=
    MkRuleHypotheses 3 0 0 0 0 (fun l _ _ _ _ => hyps (Vector.hd l) (Vector.hd (Vector.tl l)) (Vector.hd (Vector.tl (Vector.tl l)))).

  Definition MkRuleHypotheses4e {eo : EventOrdering} (hyps : EventN -> EventN -> EventN -> EventN -> list sequent) : rule_hypotheses :=
    MkRuleHypotheses 4 0 0 0 0 (fun l _ _ _ _ => hyps (Vector.hd l) (Vector.hd (Vector.tl l)) (Vector.hd (Vector.tl (Vector.tl l))) (Vector.hd (Vector.tl (Vector.tl (Vector.tl l))))).

  Definition MkRuleHypotheses5e {eo : EventOrdering} (hyps : EventN -> EventN -> EventN -> EventN -> EventN -> list sequent) : rule_hypotheses :=
    MkRuleHypotheses 5 0 0 0 0 (fun l _ _ _ _ => hyps (Vector.hd l) (Vector.hd (Vector.tl l)) (Vector.hd (Vector.tl (Vector.tl l))) (Vector.hd (Vector.tl (Vector.tl (Vector.tl l)))) (Vector.hd (Vector.tl (Vector.tl (Vector.tl (Vector.tl l)))))).

  Definition MkRuleHypotheses1t {eo : EventOrdering} (hyps : kc_trust -> list sequent) : rule_hypotheses :=
    MkRuleHypotheses 0 1 0 0 0 (fun _ l _ _ _ => hyps (Vector.hd l)).

  Definition MkRuleHypotheses1d {eo : EventOrdering} (hyps : kc_data -> list sequent) : rule_hypotheses :=
    MkRuleHypotheses 0 0 1 0 0 (fun _ _ l _ _ => hyps (Vector.hd l)).

  Definition MkRuleHypotheses1c {eo : EventOrdering} (hyps : kc_id -> list sequent) : rule_hypotheses :=
    MkRuleHypotheses 0 0 0 1 0 (fun _ _ _ l _ => hyps (Vector.hd l)).

  Definition MkRuleHypotheses1n {eo : EventOrdering} (hyps : node_type -> list sequent) : rule_hypotheses :=
    MkRuleHypotheses 0 0 0 0 1 (fun _ _ _ _ l => hyps (Vector.hd l)).

  Definition MkRule0 {eo : EventOrdering} (hyps  : list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses0 hyps) concl.

  Definition MkRule1 {eo : EventOrdering} (hyps  : EventN -> list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses1e hyps) concl.

  Definition MkRule2 {eo : EventOrdering} (hyps  : EventN -> EventN -> list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses2e hyps) concl.

  Definition MkRule3 {eo : EventOrdering} (hyps  : EventN -> EventN -> EventN -> list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses3e hyps) concl.

  Definition MkRule4 {eo : EventOrdering} (hyps  : EventN -> EventN -> EventN -> EventN -> list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses4e hyps) concl.

  Definition MkRule5 {eo : EventOrdering} (hyps  : EventN -> EventN -> EventN -> EventN -> EventN -> list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses5e hyps) concl.

  Definition MkRule1t {eo : EventOrdering} (hyps  : kc_trust -> list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses1t hyps) concl.

  Definition MkRule1d {eo : EventOrdering} (hyps  : kc_data -> list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses1d hyps) concl.

  Definition MkRule1c {eo : EventOrdering} (hyps  : kc_id -> list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses1c hyps) concl.

  Definition MkRule1n {eo : EventOrdering} (hyps  : node_type -> list sequent) (concl : sequent) : rule :=
    MkRule (MkRuleHypotheses1n hyps) concl.

  Definition seq_event {eo : EventOrdering} (s : sequent) : EventN :=
    exp_at_event (seq_concl s).

  Definition hyp_event {eo : EventOrdering} (h : hypothesis) : EventN :=
    exp_at_event (hyp_exp h).

  Definition exp_of_hyp {eo : EventOrdering} (h : hypothesis) : KExpression :=
    hyp_exp h.

  Definition causal_rel_true {eo : EventOrdering} (r : causalRel) : Prop :=
    match r with
    | causal_rel_eq                 e1 e2 => en_event e1 = en_event e2
    | causal_rel_right_before       e1 e2 => (en_event e1) ⊂ e2
    | causal_rel_local_before       e1 e2 => e1 ⊏ e2
    | causal_rel_local_before_eq    e1 e2 => e1 ⊑ e2
    | causal_rel_happened_before    e1 e2 => e1 ≺ e2
    | causal_rel_happened_before_eq e1 e2 => e1 ≼ e2
    end.

  Definition sequent_true {eo : EventOrdering} (s : sequent) :=
    (forall r, In r (seq_causal s) -> causal_rel_true r)
    -> (forall h, In h (seq_hyps s) -> interpret (hyp_event h) h)
    -> interpret (seq_event s) (seq_concl s).


  Definition rule_e_t_d_c_n_hypotheses_true {eo : EventOrdering}
             (e t d c n : nat)
             (f : Vector.t EventN e -> Vector.t kc_trust t -> Vector.t kc_data d -> Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall es ts ds cs ns s, In s (f es ts ds cs ns) -> sequent_true s.

  Definition rule_t_d_c_n_hypotheses_true {eo : EventOrdering}
             (t d c n : nat)
             (f : Vector.t kc_trust t -> Vector.t kc_data d -> Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall ts ds cs ns s, In s (f ts ds cs ns) -> sequent_true s.

  Definition rule_d_c_n_hypotheses_true {eo : EventOrdering}
             (d c n : nat)
             (f : Vector.t kc_data d -> Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall ds cs ns s, In s (f ds cs ns) -> sequent_true s.

  Definition rule_c_n_hypotheses_true {eo : EventOrdering}
             (c n : nat)
             (f : Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall cs ns s, In s (f cs ns) -> sequent_true s.

  Definition rule_n_hypotheses_true {eo : EventOrdering}
             (n : nat)
             (f : Vector.t node_type n -> list sequent) :=
    forall ns s, In s (f ns) -> sequent_true s.

  Definition rule__hypotheses_true {eo : EventOrdering}
             (f : list sequent) :=
    forall s, In s f -> sequent_true s.


  Definition rule_1e_t_d_c_n_hypotheses_true {eo : EventOrdering}
             (t d c n : nat)
             (f : EventN -> Vector.t kc_trust t -> Vector.t kc_data d -> Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall e ts ds cs ns s, In s (f e ts ds cs ns) -> sequent_true s.

  Definition rule_1e_d_c_n_hypotheses_true {eo : EventOrdering}
             (d c n : nat)
             (f : EventN -> Vector.t kc_data d -> Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall e ds cs ns s, In s (f e ds cs ns) -> sequent_true s.

  Definition rule_1e_c_n_hypotheses_true {eo : EventOrdering}
             (c n : nat)
             (f : EventN -> Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall e cs ns s, In s (f e cs ns) -> sequent_true s.

  Definition rule_1e_n_hypotheses_true {eo : EventOrdering}
             (n : nat)
             (f : EventN -> Vector.t node_type n -> list sequent) :=
    forall e ns s, In s (f e ns) -> sequent_true s.

  Definition rule_1e_hypotheses_true {eo : EventOrdering}
             (f : EventN -> list sequent) :=
    forall e s, In s (f e) -> sequent_true s.


  Definition rule_1t_d_c_n_hypotheses_true {eo : EventOrdering}
             (d c n : nat)
             (f : kc_trust -> Vector.t kc_data d -> Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall t ds cs ns s, In s (f t ds cs ns) -> sequent_true s.

  Definition rule_1t_c_n_hypotheses_true {eo : EventOrdering}
             (c n : nat)
             (f : kc_trust -> Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall t cs ns s, In s (f t cs ns) -> sequent_true s.

  Definition rule_1t_n_hypotheses_true {eo : EventOrdering}
             (n : nat)
             (f : kc_trust -> Vector.t node_type n -> list sequent) :=
    forall t ns s, In s (f t ns) -> sequent_true s.

  Definition rule_1t_hypotheses_true {eo : EventOrdering}
             (f : kc_trust -> list sequent) :=
    forall t s, In s (f t) -> sequent_true s.


  Definition rule_1d_c_n_hypotheses_true {eo : EventOrdering}
             (c n : nat)
             (f : kc_data -> Vector.t kc_id c -> Vector.t node_type n -> list sequent) :=
    forall d cs ns s, In s (f d cs ns) -> sequent_true s.

  Definition rule_1d_n_hypotheses_true {eo : EventOrdering}
             (n : nat)
             (f : kc_data -> Vector.t node_type n -> list sequent) :=
    forall d ns s, In s (f d ns) -> sequent_true s.

  Definition rule_1d_hypotheses_true {eo : EventOrdering}
             (f : kc_data -> list sequent) :=
    forall d s, In s (f d) -> sequent_true s.


  Definition rule_1c_n_hypotheses_true {eo : EventOrdering}
             (n : nat)
             (f : kc_id -> Vector.t node_type n -> list sequent) :=
    forall c ns s, In s (f c ns) -> sequent_true s.

  Definition rule_1c_hypotheses_true {eo : EventOrdering}
             (f : kc_id -> list sequent) :=
    forall c s, In s (f c) -> sequent_true s.


  Definition rule_1n_hypotheses_true {eo : EventOrdering}
             (f : node_type -> list sequent) :=
    forall n s, In s (f n) -> sequent_true s.


  Definition rule_hypotheses_true {eo : EventOrdering} (rh : rule_hypotheses) :=
    match rh with
    | MkRuleHypotheses e t d c n f => rule_e_t_d_c_n_hypotheses_true e t d c n f
    end.

  Definition rule_true {eo : EventOrdering} (r : rule) :=
    rule_hypotheses_true (rule_hyps r)
    -> sequent_true (rule_concl r).

(*  Definition sequent_true_at_event {eo : EventOrdering} e (s : sequent) :=
    (forall h, In h (seq_hyps s) -> interpret (hyp_event h) h)
    -> interpret e (seq_concl s).

  Definition rule_hypotheses_true_all_events {eo : EventOrdering} (rh : rule_hypotheses) :=
    match rh with
    | MkRuleHypotheses n f => forall l (e : EventN) s, In s (f l) -> sequent_true_at_event e s
    end.

  Definition rule_true_all_events {eo : EventOrdering} (r : rule) :=
    rule_hypotheses_true_all_events (rule_hyps r)
    -> sequent_true (rule_concl r).*)

  Definition hyps_at_event {eo : EventOrdering} (H : hypotheses) (e : Event) :=
    forall h, In h H -> en_event (hyp_event h) = e.

  Definition rule_0_t_d_c_n_hypotheses_true :
    forall {eo : EventOrdering} t d c n f,
      rule_e_t_d_c_n_hypotheses_true 0 t d c n f
      <-> rule_t_d_c_n_hypotheses_true t d c n (f (Vector.nil _)).
  Proof.
    introv.
    unfold rule_e_t_d_c_n_hypotheses_true, rule_t_d_c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction es using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_0_t_d_c_n_hypotheses_true : rule.

  Definition rule_0_d_c_n_hypotheses_true :
    forall {eo : EventOrdering} d c n f,
      rule_t_d_c_n_hypotheses_true 0 d c n f
      <-> rule_d_c_n_hypotheses_true d c n (f (Vector.nil _)).
  Proof.
    introv.
    unfold rule_t_d_c_n_hypotheses_true, rule_d_c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ts using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_0_d_c_n_hypotheses_true : rule.

  Definition rule_0_c_n_hypotheses_true :
    forall {eo : EventOrdering} c n f,
      rule_d_c_n_hypotheses_true 0 c n f
      <-> rule_c_n_hypotheses_true c n (f (Vector.nil _)).
  Proof.
    introv.
    unfold rule_d_c_n_hypotheses_true, rule_c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ds using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_0_c_n_hypotheses_true : rule.

  Definition rule_0_n_hypotheses_true :
    forall {eo : EventOrdering} n f,
      rule_c_n_hypotheses_true 0 n f
      <-> rule_n_hypotheses_true n (f (Vector.nil _)).
  Proof.
    introv.
    unfold rule_c_n_hypotheses_true, rule_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction cs using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_0_n_hypotheses_true : rule.

  Definition rule_0_hypotheses_true :
    forall {eo : EventOrdering} f,
      rule_n_hypotheses_true 0 f
      <-> rule__hypotheses_true (f (Vector.nil _)).
  Proof.
    introv.
    unfold rule_n_hypotheses_true, rule__hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ns using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_0_hypotheses_true : rule.

  Definition rule_1_t_d_c_n_hypotheses_true :
    forall {eo : EventOrdering} t d c n f,
      rule_e_t_d_c_n_hypotheses_true 1 t d c n f
      <-> rule_1e_t_d_c_n_hypotheses_true t d c n (fun e => f (mk_v1 e)).
  Proof.
    introv.
    unfold rule_e_t_d_c_n_hypotheses_true, rule_1e_t_d_c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction es using Vector.caseS'; simpl in *.
      induction es using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1_t_d_c_n_hypotheses_true : rule.

  Definition rule_1e_0_d_c_n_hypotheses_true :
    forall {eo : EventOrdering} d c n f,
      rule_1e_t_d_c_n_hypotheses_true 0 d c n f
      <-> rule_1e_d_c_n_hypotheses_true d c n (fun e => f e (Vector.nil _)).
  Proof.
    introv.
    unfold rule_1e_t_d_c_n_hypotheses_true, rule_1e_d_c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ts using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1e_0_d_c_n_hypotheses_true : rule.

  Definition rule_1e_0_c_n_hypotheses_true :
    forall {eo : EventOrdering} c n f,
      rule_1e_d_c_n_hypotheses_true 0 c n f
      <-> rule_1e_c_n_hypotheses_true c n (fun e => f e (Vector.nil _)).
  Proof.
    introv.
    unfold rule_1e_d_c_n_hypotheses_true, rule_1e_c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ds using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1e_0_c_n_hypotheses_true : rule.

  Definition rule_1e_0_n_hypotheses_true :
    forall {eo : EventOrdering} n f,
      rule_1e_c_n_hypotheses_true 0 n f
      <-> rule_1e_n_hypotheses_true n (fun e => f e (Vector.nil _)).
  Proof.
    introv.
    unfold rule_1e_c_n_hypotheses_true, rule_1e_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction cs using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1e_0_n_hypotheses_true : rule.

  Definition rule_1e_0_hypotheses_true :
    forall {eo : EventOrdering} f,
      rule_1e_n_hypotheses_true 0 f
      <-> rule_1e_hypotheses_true (fun e => f e (Vector.nil _)).
  Proof.
    introv.
    unfold rule_n_hypotheses_true, rule__hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ns using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1e_0_hypotheses_true : rule.


  Definition rule_1_d_c_n_hypotheses_true :
    forall {eo : EventOrdering} d c n f,
      rule_t_d_c_n_hypotheses_true 1 d c n f
      <-> rule_1t_d_c_n_hypotheses_true d c n (fun t => f (mk_v1 t)).
  Proof.
    introv.
    unfold rule_t_d_c_n_hypotheses_true, rule_1t_d_c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ts using Vector.caseS'; simpl in *.
      induction ts using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1_d_c_n_hypotheses_true : rule.

  Definition rule_1t_0_c_n_hypotheses_true :
    forall {eo : EventOrdering} c n f,
      rule_1t_d_c_n_hypotheses_true 0 c n f
      <-> rule_1t_c_n_hypotheses_true c n (fun t => f t (Vector.nil _)).
  Proof.
    introv.
    unfold rule_1t_d_c_n_hypotheses_true, rule_1t_c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ds using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1t_0_c_n_hypotheses_true : rule.

  Definition rule_1t_0_n_hypotheses_true :
    forall {eo : EventOrdering} n f,
      rule_1t_c_n_hypotheses_true 0 n f
      <-> rule_1t_n_hypotheses_true n (fun t => f t (Vector.nil _)).
  Proof.
    introv.
    unfold rule_1t_c_n_hypotheses_true, rule_1t_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction cs using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1t_0_n_hypotheses_true : rule.

  Definition rule_1t_0_hypotheses_true :
    forall {eo : EventOrdering} f,
      rule_1t_n_hypotheses_true 0 f
      <-> rule_1t_hypotheses_true (fun t => f t (Vector.nil _)).
  Proof.
    introv.
    unfold rule_1t_n_hypotheses_true, rule_1t_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ns using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1t_0_hypotheses_true : rule.


  Definition rule_1_c_n_hypotheses_true :
    forall {eo : EventOrdering} c n f,
      rule_d_c_n_hypotheses_true 1 c n f
      <-> rule_1d_c_n_hypotheses_true c n (fun t => f (mk_v1 t)).
  Proof.
    introv.
    unfold rule_t_d_c_n_hypotheses_true, rule_1t_d_c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ds using Vector.caseS'; simpl in *.
      induction ds using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1_c_n_hypotheses_true : rule.

  Definition rule_1d_0_n_hypotheses_true :
    forall {eo : EventOrdering} n f,
      rule_1d_c_n_hypotheses_true 0 n f
      <-> rule_1d_n_hypotheses_true n (fun t => f t (Vector.nil _)).
  Proof.
    introv.
    unfold rule_1d_c_n_hypotheses_true, rule_1d_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction cs using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1d_0_n_hypotheses_true : rule.

  Definition rule_1d_0_hypotheses_true :
    forall {eo : EventOrdering} f,
      rule_1d_n_hypotheses_true 0 f
      <-> rule_1d_hypotheses_true (fun t => f t (Vector.nil _)).
  Proof.
    introv.
    unfold rule_1d_n_hypotheses_true, rule_1d_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ns using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1d_0_hypotheses_true : rule.


  Definition rule_1_n_hypotheses_true :
    forall {eo : EventOrdering} n f,
      rule_c_n_hypotheses_true 1 n f
      <-> rule_1c_n_hypotheses_true n (fun t => f (mk_v1 t)).
  Proof.
    introv.
    unfold rule_c_n_hypotheses_true, rule_1c_n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction cs using Vector.caseS'; simpl in *.
      induction cs using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1_n_hypotheses_true : rule.

  Definition rule_1c_0_hypotheses_true :
    forall {eo : EventOrdering} f,
      rule_1c_n_hypotheses_true 0 f
      <-> rule_1c_hypotheses_true (fun c => f c (Vector.nil _)).
  Proof.
    introv.
    unfold rule_1c_n_hypotheses_true, rule_1c_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ns using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1c_0_hypotheses_true : rule.

  Definition rule_1_hypotheses_true :
    forall {eo : EventOrdering} f,
      rule_n_hypotheses_true 1 f
      <-> rule_1n_hypotheses_true (fun n => f (mk_v1 n)).
  Proof.
    introv.
    unfold rule_n_hypotheses_true, rule_1n_hypotheses_true; split; intro h;
      introv i.
    { eapply h; eauto. }
    { induction ns using Vector.caseS'; simpl in *.
      induction ns using Vector.case0; simpl in *.
      eapply h; eauto. }
  Qed.
  Hint Rewrite @rule_1_hypotheses_true : rule.

  (**********************)

  Definition hypotheses2expression {eo : EventOrdering} (H : hypotheses) : KExpression :=
    KE_ANDS (map exp_of_hyp H).

  Definition sequent2expression {eo : EventOrdering} (s : sequent) : KExpression :=
    KE_IMPLIES
      (hypotheses2expression (seq_hyps s))
      (seq_concl s).

  (*Definition rule2expression {eo : EventOrdering} (r : rule) : KExpression :=
    KE_IMPLIES
      (KE_ANDS (map sequent2expression (rule_hyps r)))
      (sequent2expression (rule_concl r)).*)

  Definition assume_eo (eo : EventOrdering) (exp : KExpression) :=
    forall (e : EventN), interpret e exp.

  (*Definition assume_e (exp : KExpression) :=
    forall {eo : EventOrdering}, assume_eo eo exp.*)

  Lemma cons_as_addHyp :
    forall {eo : EventOrdering} h H, h :: H = (∅ • h » H).
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @cons_as_addHyp : norm.

  Lemma addHyps_cons_as_addHyp :
    forall {eo : EventOrdering} H1 h H2, (H1 » h :: H2) = (H1 • h » H2).
  Proof.
    introv; unfold addHyp, addHyps; simpl.
    rewrite snoc_as_app.
    rewrite <- app_assoc; simpl; auto.
  Qed.
  Hint Rewrite @addHyps_cons_as_addHyp : norm.

  Lemma addHyps_addHyp_em_eq1 :
    forall {eo : EventOrdering} H1 h H2, (H1 » (∅ • h » H2)) = (H1 • h » H2).
  Proof.
    introv; simpl.
    apply addHyps_cons_as_addHyp.
  Qed.
  Hint Rewrite @addHyps_addHyp_em_eq1 : norm.

  Lemma addHyps_addHyp_em_eq2 :
    forall {eo : EventOrdering} H h, (H » (∅ • h)) = (H • h).
  Proof.
    introv; simpl.
    unfold addHyps, addHyp, emHyps; simpl.
    rewrite snoc_as_app; auto.
  Qed.
  Hint Rewrite @addHyps_addHyp_em_eq2 : norm.

  Lemma addHyps_addHyp_eq3 :
    forall {eo : EventOrdering} H1 h H2, (H1 » (H2 • h)) = ((H1 » H2) • h).
  Proof.
    introv; simpl; unfold addHyps, addHyp; simpl.
    rewrite app_snoc; auto.
  Qed.
  Hint Rewrite @addHyps_addHyp_eq3 : norm.

  Lemma nil_as_emHyps {eo : EventOrdering} : [] = ∅.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @nil_as_emHyps : norm.

  Lemma addHyps_em :
    forall {eo : EventOrdering} H, (H » ∅) = H.
  Proof.
    introv; simpl; unfold addHyps, emHyps; autorewrite with list; auto.
  Qed.
  Hint Rewrite @addHyps_em : norm kc.

  Lemma addHyp_as_addHyps :
    forall {eo : EventOrdering} h H, (H • h) = (H » (∅ • h)).
  Proof.
    introv; simpl.
    autorewrite with norm; auto.
  Qed.

  Lemma state_after_implies_state_before :
    forall {eo : EventOrdering} (e' e : Event) mem,
      e' ⊂ e
      -> state_after e' mem
      -> state_before e mem.
  Proof.
    introv lte h.
    unfold state_after, state_before in *; exrepnd.
    applydup pred_implies_local_pred in lte; subst; autorewrite with eo in *.
    exists n; dands; auto.
    eapply M_state_sys_before_event_if_on_event_direct_pred; eauto.
  Qed.
  Hint Resolve state_after_implies_state_before : kn.

  Lemma kc_no_initial_memory_implies :
    forall n mem i,
      state_of_component kc_mem_comp (kc_sys n) = Some mem
      -> ~ kc_knows i mem.
  Proof.
    introv eqs.
    pose proof (kc_no_initial_memory n i) as q.
    unfold on_state_of_component in q.
    rewrite eqs in q; auto.
  Qed.

  Lemma interpret_implies_sequent_true :
    forall {eo : EventOrdering} (e : EventN) a,
      interpret e a
      -> sequent_true (⟬ [] ⟭ ∅ ⊢ a @ e).
  Proof.
    introv j xx yy; simpl in *; tcsp.
  Qed.

  Lemma sequent_true_iff_interpret :
    forall {eo : EventOrdering} (e : EventN) a,
      sequent_true (⟬ [] ⟭ ∅ ⊢ a @ e)
      <-> interpret e a.
  Proof.
    introv; split; intro h; simpl in *; tcsp.
    { apply h; simpl in *; tcsp. }
    { apply interpret_implies_sequent_true; auto. }
  Qed.

  Lemma interp_KE_TRUE :
    forall {eo : EventOrdering} (e : Event),
      interpret e KE_TRUE <-> True.
  Proof.
    introv; simpl; split; intro h; tcsp.
  Qed.
  Hint Rewrite @interp_KE_TRUE : kn.

  Opaque KE_TRUE.

  Lemma interp_KE_TRUE_true :
    forall {eo : EventOrdering} (e : Event),
      interpret e KE_TRUE.
  Proof.
    introv; tcsp; autorewrite with kn; auto.
  Qed.
  Hint Resolve interp_KE_TRUE_true : kn.

  Lemma interp_KE_FALSE :
    forall {eo : EventOrdering} (e : Event),
      interpret e KE_FALSE <-> False.
  Proof.
    introv; simpl; split; intro h; exrepnd; tcsp.
    apply kc_id_lt_arefl in h0; auto.
  Qed.
  Hint Rewrite @interp_KE_FALSE : kn.

  Opaque KE_FALSE.

  Lemma interp_KE_NOT :
    forall {eo : EventOrdering} (e : Event) a,
      interpret e (KE_NOT a) <-> ~ (interpret e a).
  Proof.
    introv; simpl; split; intro h; tcsp.
    intro q; autodimp h hyp.
    allrw interp_KE_FALSE; auto.
  Qed.

  Lemma interp_KE_NOT_FIRST :
    forall {eo : EventOrdering} (e : Event),
      interpret e KE_NOT_FIRST <-> ~ isFirst e.
  Proof.
    introv; simpl; split; intro h; tcsp; remember (direct_pred e) as d;
      symmetry in Heqd; destruct d; tcsp; eauto 2 with kn.
    apply pred_implies_not_first in Heqd; tcsp.
  Qed.

  Opaque KE_NOT_FIRST.

  Lemma interp_KE_FIRST :
    forall {eo : EventOrdering} (e : Event),
      interpret e KE_FIRST <-> isFirst e.
  Proof.
    introv; simpl; allrw interp_KE_NOT_FIRST; allrw interp_KE_FALSE; split; intro h; tcsp.
    destruct (dec_isFirst e); tcsp.
  Qed.

  Lemma interp_KE_LOCAL_BEFORE :
    forall {eo : EventOrdering} (e : Event) t,
      interpret e (KE_LOCAL_BEFORE t)
      <-> exists (e' : EventN),
        e' ⊏ e
        /\ interpret e' t.
  Proof.
    introv; simpl; split; intro h; exrepnd.
    { exists e'; dands; auto; simpl in *; split; auto; try congruence. }
    { destruct e' as [e' cond]; simpl in *.
      dup cond as w.
      unfold ex_node_e in cond; exrepnd.
      apply name2node_cond in cond0.
      assert (loc e' = loc e) as eqloc by eauto 3 with eo.
      exists n; dands; auto; try congruence.
      exists (MkEventN e' w); simpl; dands; auto; eauto 3 with eo. }
  Qed.

  Lemma interp_KE_LOCAL_FORALL_BEFORE :
    forall {eo : EventOrdering} (e : EventN) t,
      interpret e (KE_LOCAL_FORALL_BEFORE t)
      <-> forall (e' : EventN), e' ⊏ e -> interpret e' t.
  Proof.
    introv; simpl; split; intro h; exrepnd.
    { introv cond.
      assert (loc e' = loc e) as eqloc by eauto 3 with eo.
      pose proof (h0 e') as h0; repeat (autodimp h0 hyp); repnd; eauto 3 with eo; try congruence. }
    { destruct (EventN_implies_node2name e) as [n cond].
      exists n; dands; auto.
      introv w z.
      apply h; split; auto; try congruence. }
  Qed.

  Lemma interp_KE_CORRECT_TRACE_BEFORE :
    forall {eo : EventOrdering} (e : EventN) n,
      interpret e (KE_CORRECT_TRACE_BEFORE n)
      <-> match n with
          | Some node => has_correct_trace_before e (node2name node)
          | None => has_correct_trace_before e (loc e)
          end.
  Proof.
    Opaque KE_LOCAL_FORALL_BEFORE.
    introv; simpl; destruct n; simpl; split; intro h; repnd; tcsp;
      allrw interp_KE_LOCAL_FORALL_BEFORE.
    { introv le1 eqloc le2.
      destruct le1 as [le1|le1].
      { pose proof (h0 (mk_eventN_node2name eqloc)) as h0; repeat (autodimp h0 hyp); repnd.
        allrw interp_KE_LOCAL_FORALL_BEFORE.
        apply localHappenedBeforeLe_implies_or2 in le2; repndors; subst; simpl in *; tcsp.
        assert (loc e'0 = node2name n) as w by (rewrite <- eqloc; eauto 3 with eo).
        pose proof (h1 (mk_eventN_node2name w)) as q; simpl in q; tcsp. }
      { subst; tcsp.
        autodimp h hyp; repnd.
        apply localHappenedBeforeLe_implies_or2 in le2; repndors; subst; tcsp.
        assert (loc e'0 = node2name n) as w by (rewrite <- eqloc; eauto 3 with eo).
        pose proof (h1 (mk_eventN_node2name w)) as q; simpl in q; tcsp. } }
    { dands.
      { introv le1 eqloc; dands; auto.
        { allrw interp_KE_LOCAL_FORALL_BEFORE.
          introv le2.
          eapply h; eauto; eauto 3 with eo. }
        { eapply h; eauto; eauto 3 with eo. } }
      { introv eqloc; dands; auto.
        { introv le2.
          eapply h; eauto; eauto 3 with eo. }
        { eapply h; eauto; eauto 3 with eo. } } }
    { introv le1 eqloc le2.
      assert (e' ⊑ e) as w by eauto 3 with eo.
      apply localHappenedBeforeLe_implies_or2 in w; repndors; subst; tcsp.
      { apply localHappenedBeforeLe_implies_or2 in le2; repndors; subst; tcsp.
        pose proof (h0 (mk_EventN_LB le2)) as q; simpl in *; tcsp. }
      { assert (e'0 ⊏ e) as lee by eauto 3 with eo.
        eapply (h0 (mk_EventN_LB lee)); eauto 3 with eo. } }
    { dands.
      { introv le1.
        eapply h; eauto 3 with eo. }
      { eapply h; eauto 3 with eo. } }
    Transparent KE_LOCAL_FORALL_BEFORE.
  Qed.

  Lemma interp_KE_KNEW :
    forall {eo : EventOrdering} (e : Event) d,
      interpret e (KE_KNEW d) <-> knows_before e d.
  Proof.
    introv; simpl; unfold knows_before, knows_after.
    remember (direct_pred e) as w; symmetry in Heqw; destruct w;
      split; intro h; exrepnd; tcsp.
    { exists mem; dands; auto; eauto 3 with kn. }
    { exists mem; dands; auto; eauto 3 with kn.
      apply state_before_implies_state_after_not_first in h1; eauto 3 with eo.
      unfold local_pred in h1.
      rewrite Heqw in h1; auto. }
    { apply state_before_implies_state_after_first in h1; eauto 3 with eo.
      eapply kc_no_initial_memory_implies in h1; tcsp. }
  Qed.

  Lemma interp_KE_ID_BEFORE :
    forall {eo : EventOrdering} (e : Event) i,
      interpret e (KE_ID_BEFORE i) <-> id_before e i.
  Proof.
    Opaque KE_FIRST.
    introv; simpl; unfold id_before, id_after;
      remember (direct_pred e) as w; symmetry in Heqw; destruct w;
        split; intro h; repndors; exrepnd; ginv; tcsp; allrw interp_KE_FIRST.
    { pose proof (trusted_state_after_implies_trusted_state_before_not_first e mem) as q.
      unfold local_pred in q; rewrite Heqw in q.
      repeat (autodimp q hyp); eauto 3 with eo. }
    { unfold trusted_state_before; allrw.
      unfold M_byz_state_sys_before_event.
      unfold M_byz_state_ls_before_event.
      rewrite M_byz_run_ls_before_event_unroll_on.
      destruct (dec_isFirst e); tcsp; GC; simpl.
      unfold has_init_id in *; exrepnd.
      exists m; dands; auto.
      exists c; dands; auto. }
    { left.
      apply trusted_state_before_implies_trusted_state_after_not_first in h1; eauto 3 with eo.
      unfold local_pred in h1; rewrite Heqw in h1; eauto. }
    { unfold trusted_state_before; allrw.
      unfold M_byz_state_sys_before_event.
      unfold M_byz_state_ls_before_event.
      rewrite M_byz_run_ls_before_event_unroll_on.
      destruct (dec_isFirst e); tcsp; GC; simpl.
      unfold has_init_id in *; exrepnd.
      exists m; dands; auto.
      exists c; dands; auto. }
    { right.
      unfold trusted_state_before in h1; exrepnd.
      unfold M_byz_state_sys_before_event in h2.
      unfold M_byz_state_ls_before_event in h2.
      rewrite M_byz_run_ls_before_event_unroll_on in h2.
      destruct (dec_isFirst e); tcsp; GC; simpl in *.
      rewrite h1 in *; simpl in *.
      dands; eauto 3 with eo.
      exists mem; simpl.
      unfold TCN in *; allrw; tcsp. }
    Transparent KE_FIRST.
  Qed.

  Lemma interp_KE_TKNEW :
    forall {eo : EventOrdering} (e : Event) t,
      interpret e (KE_TKNEW t) <-> knows_before e (kc_trust2data t).
  Proof.
    introv; apply interp_KE_KNEW.
  Qed.

  Lemma interpret_KE_ANDS_implies :
    forall {eo : EventOrdering} (e : Event) l x,
      interpret e (KE_ANDS l)
      -> In x l
      -> interpret e x.
  Proof.
    induction l; introv h q; simpl in *; repndors; subst; tcsp.
  Qed.
  Hint Resolve interpret_KE_ANDS_implies : kn.

  Lemma implies_interpret_KE_ANDS :
    forall {eo : EventOrdering} (e : Event) l,
      (forall x, In x l -> interpret e x)
      -> interpret e (KE_ANDS l).
  Proof.
    induction l; introv h; simpl in *; repndors; subst; tcsp; eauto 2 with kn.
  Qed.
  Hint Resolve implies_interpret_KE_ANDS : kn.

  Lemma interp_KE_LOCAL_BEFORE_EQ :
    forall {eo : EventOrdering} (e : Event) t,
      interpret e (KE_LOCAL_BEFORE_EQ t)
      <->
      exists (e' : EventN),
        e' ⊑ e
        /\ interpret e' t.
  Proof.
    introv.
    Opaque KE_LOCAL_BEFORE.
    simpl.
    rewrite interp_KE_LOCAL_BEFORE.
    Transparent KE_LOCAL_BEFORE.
    split; intro h; repndors; exrepnd; eauto 3 with eo.
    { exists e'; dands; eauto 3 with eo. }
    { assert (ex_node_e e) as x.
      { exists c; allrw; apply node2name_cond. }
      exists (MkEventN e x); simpl; dands; eauto 3 with eo. }
    { apply localHappenedBeforeLe_implies_or2 in h1; repndors; subst; eauto.
      right; dands; tcsp.
      destruct (implies_ex_node e') as [n w].
      apply name2node_cond in w; exists n; auto. }
  Qed.

  Lemma interp_KE_RIGHT_BEFORE_EQ :
    forall {eo : EventOrdering} (e : Event) t,
      interpret e (KE_RIGHT_BEFORE_EQ t)
      <-> interpret (local_pred e) t.
  Proof.
    Opaque KE_FIRST.
    introv; simpl.
    unfold local_pred.
    remember (direct_pred e) as d; destruct d; rev_Some;
      split; intro h; repndors; repnd; tcsp; allrw interp_KE_FIRST.
    { eapply pred_implies_not_first in h; eauto; tcsp. }
    { right; dands; auto; symmetry; auto. }
    Transparent KE_FIRST.
  Qed.

  Lemma interp_KE_HAPPENED_BEFORE_EQ :
    forall {eo : EventOrdering} (e : Event) t,
      interpret e (KE_HAPPENED_BEFORE_EQ t)
      <->
      exists (e' : EventN),
        e' ≼ e
        /\ interpret e' t.
  Proof.
    introv.
    simpl.
    split; intro h; repndors; exrepnd; eauto 3 with eo.
    { exists e'; dands; eauto 3 with eo. }
    { assert (ex_node_e e) as w.
      { exists c; allrw; apply node2name_cond. }
      exists (MkEventN e w); simpl; dands; eauto 3 with eo. }
    { destruct h1 as [h1|h1]; subst; eauto.
      right; dands; auto.
      destruct e' as [e' cond]; simpl in *.
      unfold ex_node_e in *; exrepnd; exists n.
      symmetry; apply name2node_cond; auto. }
  Qed.

(*  Lemma sequent_true_at_event_if_ANDS :
    forall {eo : EventOrdering} (e : Event) S s,
      interpret e (KE_ANDS (map sequent2expression S))
      -> In s S
      -> sequent_true_at_event e s.
  Proof.
    introv h i.
    eapply interpret_KE_ANDS_implies in h;[|apply in_map_iff;eexists;dands;eauto ].
    introv q.
    unfold sequent2expression in h; simpl in h; apply h.
    apply implies_interpret_KE_ANDS; introv j; allrw in_map_iff; exrepnd; subst; simpl in *; tcsp.
  Qed.
  Hint Resolve sequent_true_at_event_if_ANDS : kn.*)

(*  Lemma rule_true_eo_implies_assume_eo :
    forall (eo : EventOrdering) (r : rule),
      rule_true eo r -> assume_eo eo (rule2expression r).
  Proof.
    introv h exe ss hs; introv.
    pose proof (h e exe) as h.
    apply h; clear h; introv i; eauto 3 with kn.
    eapply interpret_KE_ANDS_implies in hs; eauto.
    apply in_map_iff;eexists;eauto.
  Qed.
  Hint Resolve rule_true_eo_implies_assume_eo : kn.*)

  Lemma assume_eo_implies_rule_true_eo :
    forall {eo : EventOrdering} {exp : KExpression} R H,
      assume_eo eo exp -> forall e, rule_true (MkRule0 [] (⟬R⟭ H ⊢ exp @ e)).
  Proof.
    introv h st ct ht; introv; simpl in *.
    apply h; auto; eauto 3 with kn.
  Qed.
  Hint Resolve assume_eo_implies_rule_true_eo : kn.

  (*Lemma rule_true_implies_assume_e :
    forall {eo : EventOrdering} r,
      rule_true r -> assume_e (rule2expression r).
  Proof.
    introv h; introv.
    apply rule_true_eo_implies_assume_eo; auto.
  Qed.
  Hint Resolve rule_true_implies_assume_e : kn.*)

(*  Lemma implies_sequent_true_at_event :
    forall {eo : EventOrdering} e H c e',
      sequent_true (H ⊢ c @ e)
      -> sequent_true_at_event e (H ⊢ c @ e').
  Proof.
    tcsp.
  Qed.*)

  (***********************************************************)

  (***********************************************************)
  (*  ****** SOME KNOWLEDGE ABSTRACTIONS ****** *)

  Definition KE_KNOWS_OWN (d : kc_data) : KExpression :=
    KE_AND (KE_KNOWS d) (KE_OWNS d).

  (* FIX: is here learned or learns? *)
  Definition ASSUMPTION_learns_or_owns (i : kc_data) : KExpression :=
    KE_IMPLIES
      (KE_KNOWS i)
      (KE_OR (KE_LEARNED i) (KE_OWNS i)).

  Definition ASSUMPTION_learns_or_owns_if_knew (i : kc_data) : KExpression :=
    KE_IMPLIES
      (KE_KNEW i)
      (KE_OR (KE_LEARNED i) (KE_OWNS i)).

  Definition ASSUMPTION_learns_if_knows (i : kc_data) :=
    KE_IMPLIES
      (KE_LEARNS i)
      (KE_IMPLIES
         (KE_CORRECT_TRACE_BEFORE (kc_data2owner i))
         (KE_HAPPENED_BEFORE
            (KE_AND
               (KE_OWNS i)
               (KE_KNOWS i)))).

  Definition ASSUMPTION_learned_if_knows (i : kc_data) :=
    KE_IMPLIES
      (KE_LEARNED i)
      (KE_IMPLIES
         (KE_CORRECT_TRACE_BEFORE (kc_data2owner i))
         (KE_HAPPENED_BEFORE
            (KE_AND
               (KE_OWNS i)
               (KE_KNOWS i)))).

  Definition ASSUMPTION_learns_if_gen (d : kc_data) :=
    KE_IMPLIES
      (KE_LEARNS d)
      (KE_HAPPENED_BEFORE (KE_DISS_OWN d)).

  Definition ASSUMPTION_learns_if_trusted_gen_for (d : kc_data) :=
    KE_IMPLIES
      (KE_LEARNS d)
      (KE_EX_TRUST
         (fun t =>
            KE_AND
              (KE_HAPPENED_BEFORE (KE_TDISS_OWN t))
              (KE_GEN_FOR d t))).

  Definition ASSUMPTION_learned_if_gen (d : kc_data) :=
    KE_IMPLIES
      (KE_LEARNED d)
      (KE_HAPPENED_BEFORE (KE_DISS_OWN d)).

  Definition ASSUMPTION_knows_implies_gen (d : kc_data) : KExpression :=
    KE_IMPLIES
      (KE_KNOWS d)
      (KE_HAPPENED_BEFORE_EQ (KE_DISS_OWN d)).

  Definition ASSUMPTION_knew_or_learns_or_gen (d : kc_data) : KExpression :=
    KE_IMPLIES
      (KE_KNOWS d)
      (KE_ORS
         [KE_KNEW d,
          KE_LEARNS d,
          KE_DISS_OWN d]).

  Definition ASSUMPTION_knows_implies_learned_or_gen (d : kc_data) : KExpression :=
    KE_IMPLIES
      (KE_KNOWS d)
      (KE_OR
         (KE_LEARNED d)
         (KE_LOCAL_BEFORE_EQ (KE_DISS_OWN d))).

  Definition ASSUMPTION_disseminate_if_knows (d : kc_data) : KExpression :=
    KE_IMPLIES
      (KE_AND (KE_DISS d) KE_NODE)
      (KE_KNOWS d).


  (***********************************************************)

  (* ******************************************************************* *)
  (*  ****** TRUSTED KNOWLEDGE ASSUMPTIONS ****** *)

  (* FIX: is here learned or learns? *)
  Definition ASSUMPTION_trusted_learns_or_owns (t : kc_trust) : KExpression :=
    ASSUMPTION_learns_or_owns (kc_trust2data t).

  Definition ASSUMPTION_trusted_learns_or_owns_if_knew (t : kc_trust) : KExpression :=
    ASSUMPTION_learns_or_owns_if_knew (kc_trust2data t).

  Definition ASSUMPTION_trusted_learns_if_gen (t : kc_trust) :=
    ASSUMPTION_learns_if_gen (kc_trust2data t).

  Definition ASSUMPTION_trusted_knows_implies_gen (t : kc_trust) : KExpression :=
    ASSUMPTION_knows_implies_gen (kc_trust2data t).

  Definition ASSUMPTION_trusted_knew_or_learns_or_gen (t : kc_trust) : KExpression :=
    ASSUMPTION_knew_or_learns_or_gen (kc_trust2data t).

  Definition ASSUMPTION_trusted_knows_implies_learned_or_gen (t : kc_trust) : KExpression :=
    ASSUMPTION_knows_implies_learned_or_gen (kc_trust2data t).

  (* ASSUMPTION *)
  (* FIX: this one is a bit weaker than the one below. Do we really need this one? *)
  (* no duplicates local -- if the same owner generated 2 trusted pieces of data *)
  Definition ASSUMPTION_trusted_no_dup (t1 t2 : kc_trust) c1 c2 :=
    KE_IMPLIES
      (KE_ANDS
         [KE_TDISS_OWN t1,
          KE_TDISS_OWN t2,
          KE_TRUST_HAS_ID t1 c1,
          KE_TRUST_HAS_ID t1 c1])
      (KE_ID_EQ c1 c2).

  (* This is provable from monotonicity (see below) *)
  Definition ASSUMPTION_same_event_same_output_implies_same_input
             (t1 t2 : kc_trust) c1 c2 :=
  KE_IMPLIES
    (KE_ANDS
       [KE_TDISS_OWN t2,
        KE_LOCAL_BEFORE_EQ (KE_TDISS_OWN t1),
        KE_TRUST_HAS_ID t1 c1,
        KE_TRUST_HAS_ID t2 c2,
        KE_ID_EQ c1 c2]
    )
    (KE_TRUST_EQ t1 t2).

  Definition ASSUMPTION_same_output_before_implies_false
             (t1 t2 : kc_trust) c1 c2 :=
  KE_IMPLIES
    (KE_ANDS
       [KE_TDISS_OWN t2,
        KE_LOCAL_BEFORE (KE_TDISS_OWN t1),
        KE_TRUST_HAS_ID t1 c1,
        KE_TRUST_HAS_ID t2 c2,
        KE_ID_EQ c1 c2]
    )
    KE_FALSE.

  (* ASSUMPTION *)
  Definition ASSUMPTION_monotonicity :=
    KE_OR
      KE_NO_TGENS
      KE_TGENS.

  (* ASSUMPTION *)
  Definition ASSUMPTION_disseminate_unique :=
    KE_ALL_TRUST2
      (fun t1 t2 =>
         KE_ALL_ID2
           (fun c1 c2 =>
              KE_IMPLIES
                (KE_ANDS
                   [KE_TDISS_OWN t1,
                    KE_TDISS_OWN t2,
                    KE_TRUST_HAS_ID t1 c1,
                    KE_TRUST_HAS_ID t2 c2,
                    KE_ID_EQ c1 c2])
                (KE_TRUST_EQ t1 t2))).

  Definition ASSUMPTION_generates_new :=
    KE_ALL_TRUST
      (fun t =>
         KE_ALL_ID3
           (fun c c1 c2 =>
              KE_IMPLIES
                (KE_ANDS
                   [KE_TDISS_OWN t,
                    KE_TRUST_HAS_ID t c,
                    KE_ID_BEFORE c1,
                    KE_ID_AFTER c2])
                (KE_AND (KE_ID_LT c1 c) (KE_ID_LE c c2)))).

  Definition KE_TRUST_DOESNT_HAVE_ID t i := KE_NOT (KE_TRUST_HAS_ID t i).

  Definition ASSUMPTION_generates_new_ex :=
    KE_ALL_TRUST
      (fun t =>
         KE_ALL_ID2
           (fun c1 c2 =>
              KE_IMPLIES
                (KE_ANDS
                   [KE_TDISS_OWN t,
                    KE_ID_BEFORE c1,
                    KE_ID_AFTER c2])
                (KE_EX_ID
                   (fun i =>
                      KE_ANDS
                        [KE_TRUST_HAS_ID t i,
                         KE_TRUST_DOESNT_HAVE_ID t c1,
                         KE_ID_LT c1 i,
                         KE_ID_LE i c2])))).

  Opaque ASSUMPTION_disseminate_unique ASSUMPTION_generates_new ASSUMPTION_generates_new_ex.


  (***********************************************************)
  (***********************************************************)
  (***********************************************************)

  Lemma data_is_owned_iff_kc_trust_is_owned :
    forall {eo : EventOrdering} (e : Event) t,
      data_is_owned e (kc_trust2data t)
      <-> kc_trust_is_owned e t.
  Proof.
    introv.
    unfold kc_trust_is_owned in *.
    unfold data_is_owned, option_map in *; simpl in *.
    rewrite kc_same_trust2owner; tcsp.
    remember (kc_trust2owner t) as o; destruct o; split; intro h; try congruence; tcsp.
  Qed.

  Lemma data_is_owned_implies_kc_trust_is_owned :
    forall {eo : EventOrdering} (e : Event) t,
      data_is_owned e (kc_trust2data t)
      -> kc_trust_is_owned e t.
  Proof.
    introv h; apply data_is_owned_iff_kc_trust_is_owned; auto.
  Qed.
  Hint Resolve data_is_owned_implies_kc_trust_is_owned : kn.

  Lemma kc_trust_is_owned_implies_data_is_owned :
    forall {eo : EventOrdering} (e : Event) t,
      kc_trust_is_owned e t
      -> data_is_owned e (kc_trust2data t).
  Proof.
    introv h; apply data_is_owned_iff_kc_trust_is_owned; auto.
  Qed.
  Hint Resolve kc_trust_is_owned_implies_data_is_owned : kn.

  Lemma interp_owns :
    forall {eo : EventOrdering} e d,
      interpret e (KE_OWNS d) <-> data_is_owned e d.
  Proof.
    introv; simpl; split; introv h; exrepnd; subst; tcsp.
    { unfold data_is_owned_by, data_is_owned in *.
      remember (kc_data2owner d) as q; destruct q; subst; tcsp. }
    { unfold data_is_owned, data_is_owned_by in *.
      remember (kc_data2owner d) as q; destruct q; subst; tcsp.
      eexists; dands; eauto. }
  Qed.

  Opaque KE_OWNS.

  Lemma interp_towns :
    forall {eo : EventOrdering} e t,
      interpret e (KE_TOWNS t) <-> data_is_owned e (kc_trust2data t).
  Proof.
    introv; apply interp_owns.
  Qed.

  Lemma interpret_tgens :
    forall {eo : EventOrdering} (e : Event),
      interpret e KE_TGENS <-> generates_trusted e.
  Proof.
    Opaque KE_ID_BEFORE.
    introv; simpl; unfold generates_trusted; split; introv h; exrepnd;
      try (exists c c0); try (exists c1 c2);
        dands; allrw interp_towns; allrw interp_KE_ID_BEFORE; autorewrite with kn; auto.
    Transparent KE_ID_BEFORE.
  Qed.

  Lemma interpret_no_tgens :
    forall {eo : EventOrdering} (e : Event),
      interpret e KE_NO_TGENS <-> no_trusted_generation e.
  Proof.
    Opaque KE_ID_BEFORE.
    introv; simpl; unfold no_trusted_generation; split; introv h; exrepnd;
      exists c; allrw interp_KE_ID_BEFORE; autorewrite with kn; auto.
    Transparent KE_ID_BEFORE.
  Qed.

  Transparent ASSUMPTION_disseminate_unique ASSUMPTION_generates_new ASSUMPTION_generates_new_ex.

  Lemma interpret_disseminate_unique :
    forall (eo : EventOrdering) (e : EventN),
      interpret e ASSUMPTION_disseminate_unique <-> disseminate_trusted_unique_at e.
  Proof.
    introv; simpl; split; introv h.
    { introv dis1 dis2 id.
      unfold same_id in id; exrepnd.
      pose proof (h t1 t2 i i) as h.
      allrw interp_owns.
      unfold disseminate_trusted_own, disseminate_data_own in *; repnd.
      repeat (autodimp h hyp); dands; tcsp; eauto 3 with comp kn; ginv; auto. }
    { introv q; repnd; subst; simpl in *; ginv.
      allrw interp_owns; repnd; subst; tcsp.
      rewrite (h c c0); auto; unfold disseminate_trusted_own,disseminate_data_own; dands; auto.
      eexists; eauto. }
  Qed.

  Lemma eq_kc_id_le :
    forall a b,
      (a ≪ b \/ KV_ID a = KV_ID b)
      <-> a ⋘ b.
  Proof.
    introv; split; intro h; repndors; ginv; tcsp.
    destruct h as [h|h]; subst; tcsp.
  Qed.
  Hint Rewrite eq_kc_id_le : kn.

  Lemma interpret_generates_new :
    forall (eo : EventOrdering) (e : EventN),
      interpret e ASSUMPTION_generates_new <-> generates_new_at e.
  Proof.
    Opaque KE_ID_BEFORE.
    introv; simpl; split; introv h.
    { introv dis1 dis2 id hc.
      pose proof (h t i c1 c2) as h.
      allrw interp_KE_ID_BEFORE.
      allrw interp_owns.
      unfold disseminate_trusted_own, disseminate_data_own in *; repnd.
      repeat (autodimp h hyp); dands; autorewrite with kn in *; tcsp; eauto 3 with comp. }
    { introv q; repnd; subst; simpl in *;autorewrite with kn in *.
      allrw interp_owns; repnd; subst; tcsp.
      pose proof (h c c1 c2) as h.
      allrw interp_KE_ID_BEFORE.
      unfold disseminate_trusted_own, disseminate_data_own in *.
      apply h; tcsp. }
    Transparent KE_ID_BEFORE.
  Qed.

  Lemma interpret_generates_new_trust :
    forall (eo : EventOrdering) (e : EventN),
      interpret e ASSUMPTION_generates_new_ex <-> generates_new_ex_at e.
  Proof.
    Opaque KE_ID_BEFORE.
    introv; simpl; split; introv h.
    { introv dis1 dis2 id.
      pose proof (h t c1 c2) as h.
      allrw interp_KE_ID_BEFORE.
      allrw interp_KE_FALSE.
      allrw interp_owns.
      unfold disseminate_trusted_own, disseminate_data_own in *; repnd.
      repeat (autodimp h hyp); dands; tcsp; eauto 3 with comp kn.
      exrepnd; autorewrite with kn in *; eexists; dands; eauto. }
    { introv q; repnd; subst; simpl in *.
      allrw interp_KE_ID_BEFORE.
      allrw interp_owns; repnd; subst; tcsp.
      pose proof (h c c0 c1) as h.
      unfold disseminate_trusted_own, disseminate_data_own in *.
      repeat (autodimp h hyp); exrepnd; eexists; autorewrite with kn in *; allrw interp_KE_FALSE; dands; eauto. }
    Transparent KE_ID_BEFORE.
  Qed.

  Opaque KE_TGENS KE_NO_TGENS ASSUMPTION_disseminate_unique.

  Lemma assume_eo_ASSUMPTION_monotonicity_iff_monotonicity :
    forall (eo : EventOrdering),
      assume_eo eo ASSUMPTION_monotonicity
      <-> monotonicity eo.
  Proof.
    introv; split; introv h; introv;
      try (pose proof (h e) as h);
      unfold ASSUMPTION_monotonicity in *;
      simpl in *;
      try rewrite interpret_no_tgens in h;
      try rewrite interpret_tgens in h;
      try rewrite interpret_no_tgens;
      try rewrite interpret_tgens; tcsp.
  Qed.

  Lemma assume_eo_ASSUMPTION_monotonicity_implies_monotonicity :
    forall (eo : EventOrdering),
      assume_eo eo ASSUMPTION_monotonicity
      -> monotonicity eo.
  Proof.
    introv h; apply assume_eo_ASSUMPTION_monotonicity_iff_monotonicity; auto.
  Qed.
  Hint Resolve assume_eo_ASSUMPTION_monotonicity_implies_monotonicity : kn.

  Lemma monotonicity_implies_assume_eo_ASSUMPTION_monotonicity :
    forall (eo : EventOrdering),
      monotonicity eo
      -> assume_eo eo ASSUMPTION_monotonicity.
  Proof.
    introv h; apply assume_eo_ASSUMPTION_monotonicity_iff_monotonicity; auto.
  Qed.
  Hint Resolve monotonicity_implies_assume_eo_ASSUMPTION_monotonicity : kn.

  Lemma Tknows_before_implies_Tknows_after_local_pred :
    forall {eo : EventOrdering} (e : Event) (t : kc_trust),
      Tknows_before e t
      -> Tknows_after (local_pred e) t.
  Proof.
    introv H.
    unfold Tknows_before, Tknows_after in *.
    exrepnd.

    destruct (dec_isFirst e) as [d|d]; [| exists mem; dands; eauto 3 with eo kn];[].

    apply state_before_implies_state_after_first in H1; auto; exrepnd; subst.
    eapply kc_no_initial_memory_implies in H1; apply H1 in H0; tcsp.
  Qed.

  Lemma disseminate_trusted_own_implies_data_is_owned :
    forall {eo : EventOrdering} (e : Event) t,
      disseminate_trusted_own e t
      -> data_is_owned e (kc_trust2data t).
  Proof.
    introv gen; unfold disseminate_trusted_own, disseminate_data_own in *; exrepnd; auto.
  Qed.
  Hint Resolve disseminate_trusted_own_implies_data_is_owned : kn.

  Lemma same_data_is_owned :
    forall {eo : EventOrdering} (e1 e2 : Event) d,
      data_is_owned e1 d
      -> data_is_owned e2 d
      -> loc e1 = loc e2.
  Proof.
    introv h q.
    unfold data_is_owned in *.
    destruct (kc_data2owner d); tcsp.
  Qed.
  Hint Resolve same_data_is_owned : kn.

  Lemma disseminate_trusted_own_and_trust_is_owned_implies_eq_loc :
    forall {eo : EventOrdering} (e e' : Event) t,
      kc_trust_is_owned e t
      -> disseminate_trusted_own e' t
      -> loc e' = loc e.
  Proof.
    introv own gen; unfold disseminate_trusted_own, disseminate_data_own in *; exrepnd; eauto 3 with kn.
  Qed.
  Hint Resolve disseminate_trusted_own_and_trust_is_owned_implies_eq_loc : kn.

  Lemma implies_generates_trusted :
    forall {eo : EventOrdering} (e : Event) c1 c2,
      c1 ≪ c2
      -> id_before e c1
      -> id_after e c2
      -> generates_trusted e .
  Proof.
    introv ltc cb ca; exists c1 c2; dands; auto.
  Qed.
  Hint Resolve implies_generates_trusted : kn.

  (*Lemma Tknows_before_kc_trust_is_owned_implies_generates_trusted :
    forall {eo : EventOrdering} (e : Event) (t : kc_trust),
      ex_node_e e
      -> assume_eo eo (ASSUMPTION_trusted_knows_implies_gen t)
      -> Tknows_before e t
      -> kc_trust_is_owned e t
      ->
      exists e',
        e' ⊑ e
        /\ generates_trusted e' t.
  Proof.
    introv exe asse kbf own.

    pose proof (asse (local_pred e)) as asse; simpl in *.
    repeat (autodimp asse hyp); eauto 3 with kn;[|].
    { eapply Tknows_before_implies_Tknows_after_local_pred in kbf; eauto. }

    exrepnd.
    apply interpret_tgens in asse0.
    exists e'; dands; eauto 3 with eo kn.
    assert (loc e' = loc e) as eqloc by eauto 3 with kn.
    assert (loc e' = loc (local_pred e)) as eqloc' by (autorewrite with eo; auto).
    assert (e' ⊑ (local_pred e)) as lte; eauto 3 with eo.
  Qed.*)

  Lemma id_before_implies_id_after :
    forall {eo : EventOrdering} (e : Event) c,
      ~ isFirst e
      -> id_before e c
      -> id_after (local_pred e) c.
  Proof.
    introv ni h.
    unfold id_before, id_after in *; exrepnd.
    apply trusted_state_before_implies_trusted_state_after_not_first in h1; auto.
    eexists; dands; eauto.
  Qed.

  Lemma id_after_implies_id_before :
    forall {eo : EventOrdering} e1 e2 c,
      e1 ⊂ e2
      -> id_after e1 c
      -> id_before e2 c.
  Proof.
    introv lte h.
    unfold id_before, id_after in *; exrepnd.
    applydup pred_implies_local_pred in lte; subst.
    apply trusted_state_after_implies_trusted_state_before_not_first in h1; eauto 3 with eo.
  Qed.

  Lemma kc_id_lt_trans_lt_lt :
    forall a b c,
      a ≪ b
      -> b ≪ c
      -> a ≪ c.
  Proof.
    apply kc_id_lt_trans.
  Qed.
  Hint Resolve kc_id_lt_trans_lt_lt : kn.

  Lemma kc_id_le_trans_le_lt :
    forall a b c,
      a ⋘ b
      -> b ≪ c
      -> a ⋘ c.
  Proof.
    introv h q.
    destruct h as [h|h]; subst; auto; left; eauto 3 with kn.
  Qed.
  Hint Resolve kc_id_le_trans_le_lt : kn.

  Lemma kc_id_lt_trans_le_lt :
    forall a b c,
      a ⋘ b
      -> b ≪ c
      -> a ≪ c.
  Proof.
    introv h q.
    destruct h as [h|h]; subst; auto; eauto 3 with kn.
  Qed.
  Hint Resolve kc_id_lt_trans_le_lt : kn.

  Lemma kc_id_lt_trans_lt_le :
    forall a b c,
      a ≪ b
      -> b ⋘ c
      -> a ≪ c.
  Proof.
    introv h q.
    destruct q as [q|q]; subst; auto; eauto 3 with kn.
  Qed.
  Hint Resolve kc_id_lt_trans_lt_le : kn.

  (*Lemma disseminate_trusted_own_kc_id_increases_local_pred :
    forall {eo : EventOrdering} (e : EventN) (t1 t2 : kc_trust),
      ~isFirst e
      -> generates_new eo
      -> monotonicity eo
      -> disseminate_trusted_own (local_pred e) t1
      -> disseminate_trusted_own e t2
      -> kc_id t1 ≪ kc_id t2.
  Proof.
    introv isf new mon gt1 gt2.

    pose proof (mon e) as mona.
    unfold no_trusted_generation, generates_trusted in *; repnd.
    repndors; exrepnd.

    { pose proof (new e t2 c c) as newa.
      repeat (autodimp newa hyp); repnd.
      eapply kc_id_lt_trans_lt_le in newa0; eauto.
      apply kc_id_lt_arefl in newa0; tcsp. }

    pose proof (new e t2 c1 c2) as newa.
    repeat (autodimp newa hyp); repnd.

    pose proof (mon (local_pred_n e)) as monb.
    unfold no_trusted_generation, generates_trusted in *; repnd.
    repndors; exrepnd.

    { applydup id_before_implies_id_after in mona2; auto; eq_states; GC.
      pose proof (new (local_pred_n e) t1 c c) as newb.
      repeat (autodimp newb hyp); repnd.
      eapply kc_id_lt_trans_lt_le in newb0; eauto.
      apply kc_id_lt_arefl in newb0; tcsp. }

    applydup id_before_implies_id_after in mona2; auto; eq_states; GC.
    pose proof (new (local_pred_n e) t1 c0 c3) as newb.
    repeat (autodimp newb hyp); repnd.
    eapply kc_id_lt_trans_le_lt; eauto.
  Qed.*)

  (*Lemma trusted_state_before_e_trusted_state_after_e_getId :
    forall {eo : EventOrdering} (e : EventN) (mem1 mem2 : tsf),
      monotonicity eo
      -> trusted_state_before e mem1
      -> trusted_state_after e mem2
      -> kc_getId mem1 ⋘ kc_getId mem2.
  Proof.
    introv mon sb saft.

    pose proof (mon e) as mon.
    destruct mon as [NT|GT]; auto;[|].

    {
      unfold no_trusted_generation, id_after, id_before in *; exrepnd.
      eq_states; allrw; tcsp.
    }

    {
      exrepnd.
      unfold generates_trusted, id_before, id_after in *; exrepnd.
      eq_states; allrw; tcsp.
    }
  Qed.*)

  (*Lemma id_increases_local_pred :
    forall {eo : EventOrdering} (e : EventN) (mem1 mem2 : tsf),
      monotonicity eo
      -> ~isFirst e
      (* part of generates_trusted e i2 t2 *)
      -> trusted_state_after e mem2
      (* part of generates_trusted (local_pred e) i1 t1 *)
      -> trusted_state_after (local_pred e) mem1
      (* id increases over time *)
      -> kc_getId mem1 ⋘ kc_getId mem2.
  Proof.
    introv mon nf safte saftle.
    applydup trusted_state_after_implies_trusted_state_before_not_first in saftle; auto.
    pose proof (trusted_state_before_e_trusted_state_after_e_getId e mem1 mem2) as tt.
    autodimp tt hyp.
  Qed.*)


  (*Lemma id_increases :
    forall {eo : EventOrdering} (e1 e2 : Event) (mem1 mem2 : tsf),
      ex_node_e e2
      -> monotonicity eo
      -> e1 ⊑ e2   (* this implies that the location is same *)
      -> trusted_state_after e2 mem2
      -> trusted_state_after e1 mem1
      -> kc_getId mem1 ⋘ kc_getId mem2.
  Proof.
    introv exe mon lte sbe2 sbe1.

    revert dependent mem2.
    revert dependent e2.

    induction e2 as [e2 ind] using predHappenedBeforeInd.
    introv exe lte sbe2.

    applydup @localHappenedBeforeLe_implies_or in lte; repndors; subst; eq_states; tcsp;[].

    destruct (dec_isFirst e2) as [d|d]; ginv; simpl in *;[|].

    { apply isFirst_localHappenedBeforeLe_implies_eq in lte; subst; auto; eq_states; tcsp. }

    pose proof (ind (local_pred e2)) as ind; repeat (autodimp ind hyp); eauto 3 with eo kn;[].

    pose proof (mon (MkEventN e2 exe)) as mon; repeat (autodimp mon hyp);[].
    repndors; exrepnd;[|].

    {
      unfold no_trusted_generation in *; exrepnd.
      unfold id_before, id_after in *.
      exrepnd; eq_states; subst.
      apply trusted_state_before_implies_trusted_state_after_not_first in mon1; auto;[].
      apply ind in mon1; try congruence.
    }

    {
      unfold generates_trusted in *; exrepnd.
      unfold id_before, id_after in *.
      exrepnd; eq_states; subst.
      apply trusted_state_before_implies_trusted_state_after_not_first in mon2; auto;[].
      apply ind in mon2; eauto 3 with kn.
    }
  Qed.*)

  (*Lemma no_trusted_generation_before_generates_trusted :
    forall {eo : EventOrdering} (e1 e2 : Event) (mem1 mem2 : tsf),
      e1 ⊂ e2
      -> trusted_state_before e2 mem1
      -> trusted_state_after e1 mem2
      -> kc_getId mem1 = kc_getId mem2.
  Proof.
    introv lte sbef saft.
    applydup pred_implies_not_first in lte.
    applydup pred_implies_local_pred in lte; subst.
    apply trusted_state_after_implies_trusted_state_before_not_first in saft; auto.
    eq_states; auto.
  Qed.*)

(*  Lemma generates_trusted_kc_id_increases :
    forall {eo : EventOrdering} (e1 e2 : Event) (t1 t2 : kc_trust),
      ex_node_e e2
      -> monotonicity eo
      -> e1 ⊑ e2 (* this implies that the location is same *)
      -> disseminate_trusted_own e2 t2
      -> disseminate_trusted_own e1 t1 (* This could be replaced by [id_after] *)
      -> kc_id t1 ⋘ kc_id t2.
  Proof.
    introv exe mon lte gt2 gt1.

    revert dependent t2.
    revert dependent e2.

    induction e2 as [e2 ind] using predHappenedBeforeInd.
    introv exe lte dis.

    applydup @localHappenedBeforeLe_implies_or in lte; repndors; subst; eq_states; tcsp.

    { pose proof (mon (MkEventN e2 exe)) as mon; simpl in *.
      unfold no_trusted_generation, generates_trusted in mon.
      repndors; exrepnd.

      {

    destruct (dec_isFirst e2) as [d|d]; ginv; simpl in *;[|].

    { apply isFirst_localHappenedBeforeLe_implies_eq in lte; subst; auto; eq_states; tcsp. }

    pose proof (ind (local_pred e2)) as ind; repeat (autodimp ind hyp); eauto 3 with eo kn;[].

    pose proof (mon (MkEventN e2 exe)) as mon; repeat (autodimp mon hyp);[].
    repndors; exrepnd;[|].

    {
      unfold no_trusted_generation in *; exrepnd.
      unfold id_before, id_after in *.
      exrepnd; eq_states; subst.
      apply trusted_state_before_implies_trusted_state_after_not_first in mon1; auto;[].
      apply ind in mon1; try congruence.
    }

    {
      unfold generates_trusted in *; exrepnd.
      unfold id_before, id_after in *.
      exrepnd; eq_states; subst.
      apply trusted_state_before_implies_trusted_state_after_not_first in mon2; auto;[].
      apply ind in mon2; eauto 3 with kn.
    }


    pose proof (id_increases e1 e2 mem mem1) as xx.
    repeat (autodimp xx hyp); eauto 3 with eo; eauto;[]; try congruence.
  Qed.*)

  Lemma knows_before_implies_knows_after :
    forall {eo : EventOrdering} (e : Event) d,
      knows_before e d
      -> knows_after (local_pred e) d.
  Proof.
    introv kns.
    dup kns as knBef.
    unfold knows_before in kns; unfold knows_after; exrepnd.
    exists mem; dands; auto.
    unfold state_before, state_after in *; exrepnd.
    autorewrite with eo.
    exists n; dands; auto.
    apply map_option_Some in kns2; exrepnd; simpl in *; rev_Some.
    rewrite M_run_ls_before_event_unroll_on in kns2.
    destruct (dec_isFirst e); ginv; simpl in *.
    { apply isFirst_implies_not_knows_before in knBef; tcsp. }
    unfold M_state_sys_on_event; simpl; autorewrite with eo.
    unfold M_state_ls_on_event.
    allrw; simpl; auto.
  Qed.
  Hint Resolve knows_before_implies_knows_after : kn.

  Lemma knows_before_direct_pred_implies_knows_after :
    forall {eo : EventOrdering} (e e' : Event) i,
      e' ⊂ e
      -> knows_before e i
      -> knows_after e' i.
  Proof.
    introv lte kn.
    pose proof (knows_before_implies_knows_after e i) as q.
    unfold local_pred in q.
    rewrite lte in q; tcsp.
  Qed.
  Hint Resolve knows_before_direct_pred_implies_knows_after : kn.

  Lemma knows_after_implies_knows_before :
    forall {eo : EventOrdering} (e e' : Event) i,
      e' ⊂ e
      -> knows_after e' i
      -> knows_before e i.
  Proof.
    introv ka kb; unfold knows_before, knows_after in *; exrepnd.
    exists mem; dands; auto.
    unfold state_after, state_before in *; exrepnd.
    applydup pred_implies_loc in ka.
    exists n; dands; auto; try congruence.
    eapply M_state_sys_before_event_if_on_event_direct_pred in kb2; eauto.
  Qed.
  Hint Resolve knows_after_implies_knows_before : kn.

  Lemma knows_before_not_isFirst :
    forall {eo : EventOrdering} (e : Event) i,
      knows_before e i
      -> ~isFirst e.
  Proof.
    introv kn isf.
    apply isFirst_implies_not_knows_before in kn; auto.
  Qed.
  Hint Resolve knows_before_not_isFirst : kn.

  Lemma data_is_owned_by_and_data_is_owned_implies :
    forall {eo : EventOrdering} (e : Event) n d,
      data_is_owned_by n d
      -> data_is_owned e d
      -> loc e = node2name n.
  Proof.
    introv h q.
    unfold data_is_owned, data_is_owned_by in *.
    remember (kc_data2owner d); destruct o; subst; tcsp.
  Qed.
  Hint Resolve data_is_owned_by_and_data_is_owned_implies : kn.

  Lemma hyp_in_add :
    forall {eo : EventOrdering} h H x,
      In h (H • x) <-> In h H \/ h = x.
  Proof.
    introv; split; intro i; unfold addHyp in *; allrw @in_snoc; tcsp.
  Qed.

  Lemma hyp_in_adds :
    forall {eo : EventOrdering} h H J,
      In h (H » J) <-> In h H \/ In h J.
  Proof.
    introv; split; intro i; unfold addHyps in *; allrw @in_app_iff; tcsp.
  Qed.

  Lemma knows_before_dec :
    forall {eo : EventOrdering} (e : Event) d,
      knows_before e d \/ ~knows_before e d.
  Proof.
    introv.
    pose proof (exists_state_before_dec e) as q; repndors; exrepnd.

    { unfold knows_before.
      destruct (kc_knows_dec d mem) as [d'|d'].
      { left; eexists; dands; eauto. }
      { right; introv xx; exrepnd.
        eapply state_before_eq_state_before_implies_eq_mem in xx1; try exact q0; subst; tcsp. } }

    { right; intro xx.
      unfold knows_before in *; exrepnd; tcsp. }
  Qed.

  Lemma knows_after_dec :
    forall {eo : EventOrdering} (e : Event) d,
      knows_after e d \/ ~knows_after e d.
  Proof.
    introv.
    pose proof (exists_state_after_dec e) as q; repndors; exrepnd.

    { unfold knows_after.
      destruct (kc_knows_dec d mem) as [d'|d'].
      { left; eexists; dands; eauto. }
      { right; introv xx; exrepnd.
        eapply state_after_eq_state_after_implies_eq_mem in xx1; try exact q0; subst; tcsp. } }

    { right; intro xx.
      unfold knows_after in *; exrepnd; tcsp. }
  Qed.

  Lemma snoc_app_eq :
    forall {A} l (a : A) k,
      snoc l a ++ k = l ++ a :: k.
  Proof.
    induction l; introv; simpl; allrw; auto.
  Qed.
  Hint Rewrite @snoc_app_eq : norm.

  Ltac norm_with_aux x exp rest F h :=
    match exp with
    | ?H • (x › ?a) => assert (H • (x › a) » rest = F) as h
    | ?H • (?y › ?a) => norm_with_aux x H (∅ • (y › a) » rest) F h
    end.

  (*Ltac norm_with x :=
    match goal with
    | [ |- context[⟬ _ ⟭ ?exp ⊢ _ ] ] =>
      let h := fresh "h" in
      norm_with_aux x exp ∅ exp h;
      [autorewrite with norm;auto
      |rewrite <- h; clear h]
    end.*)

  Ltac norm_with x :=
    match goal with
    | [ |- context[⟬ _ ⟭ (?exp » ?rest) ⊢ _ ] ] =>
      let h := fresh "h" in
      norm_with_aux x exp rest (exp » rest) h;
      [autorewrite with norm;auto;fail
      |try rewrite <- h; clear h]
    | [ |- context[⟬ _ ⟭ ?exp ⊢ _ ] ] =>
      let h := fresh "h" in
      norm_with_aux x exp ∅ exp h;
      [autorewrite with norm;auto;fail
      |try rewrite <- h; clear h]
    end.

(*  Ltac causal_norm_with_aux x R accum exp hyp :=
    match R with
    | (x ⋈ ?a) :: ?Q => assert (accum ++ (x ⋈ a) :: Q = exp) as hyp
    | (?y ⋈ ?a) :: ?Q => causal_norm_with_aux x Q (snoc accum (y ⋈ a)) exp hyp
    end.

  Ltac causal_norm_with x :=
    match goal with
    | [ |- context[⟬ ?Q ++ ?R ⟭ _ ⊢ _ ] ] =>
      let h := fresh "h" in
      causal_norm_with_aux x R Q (Q ++ R) h;
      [autorewrite with norm;simpl;auto;fail
      |try rewrite <- h; clear h]
    | [ |- context[⟬ ?R ⟭ _ ⊢ _ ] ] =>
      let h := fresh "h" in
      causal_norm_with_aux x R (@nil namedCausalRel) R h;
      [autorewrite with norm;simpl;auto;fail
      |try rewrite <- h; clear h]
    end.*)

  Ltac causal_norm_with_aux x R accum exp hyp :=
    match R with
    | (x ⋈ ?a) :: ?Q => assert (accum ++ (x ⋈ a) :: Q = exp) as hyp
    | (?y ⋈ ?a) :: ?Q => causal_norm_with_aux x Q (snoc accum (y ⋈ a)) exp hyp
    | ?X ++ ?Q => causal_norm_with_aux x Q (app accum X) exp hyp
    end.

  Ltac causal_norm_with x :=
    match goal with
    | [ |- context[⟬ ?R ⟭ _ ⊢ _ ] ] =>
      let h := fresh "h" in
      causal_norm_with_aux x R (@nil namedCausalRel) R h;
      [autorewrite with norm;simpl;auto;fail
      |try rewrite <- h; clear h]
    end.

  Ltac simpl_sem_rule :=
    repeat match goal with
           | [ H : rule_e_t_d_c_n_hypotheses_true 0 _ _ _ _ _ |- _ ] => apply rule_0_t_d_c_n_hypotheses_true in H
           | [ H : rule_e_t_d_c_n_hypotheses_true 1 _ _ _ _ _ |- _ ] => apply rule_1_t_d_c_n_hypotheses_true in H
           | [ H : rule_t_d_c_n_hypotheses_true 0 _ _ _ _ |- _ ] => apply rule_0_d_c_n_hypotheses_true in H
           | [ H : rule_t_d_c_n_hypotheses_true 1 _ _ _ _ |- _ ] => apply rule_1_d_c_n_hypotheses_true in H
           | [ H : rule_d_c_n_hypotheses_true 0 _ _ _ |- _ ] => apply rule_0_c_n_hypotheses_true in H
           | [ H : rule_d_c_n_hypotheses_true 1 _ _ _ |- _ ] => apply rule_1_c_n_hypotheses_true in H
           | [ H : rule_c_n_hypotheses_true 0 _ _ |- _ ] => apply rule_0_n_hypotheses_true in H
           | [ H : rule_c_n_hypotheses_true 1 _ _ |- _ ] => apply rule_1_n_hypotheses_true in H
           | [ H : rule_n_hypotheses_true 0 _ |- _ ] => apply rule_0_hypotheses_true in H
           | [ H : rule_n_hypotheses_true 1 _ |- _ ] => apply rule_1_hypotheses_true in H

           | [ H : rule__hypotheses_true _ |- _ ] => unfold rule__hypotheses_true in H; simpl in H

           | [ H : rule_1e_t_d_c_n_hypotheses_true 0 _ _ _ _ |- _ ] => apply rule_1e_0_d_c_n_hypotheses_true in H
           | [ H : rule_1e_d_c_n_hypotheses_true 0 _ _ _ |- _ ] => apply rule_1e_0_c_n_hypotheses_true in H
           | [ H : rule_1e_c_n_hypotheses_true 0 _ _ |- _ ] => apply rule_1e_0_n_hypotheses_true in H
           | [ H : rule_1e_n_hypotheses_true 0 _ |- _ ] => apply rule_1e_0_hypotheses_true in H

           | [ H : rule_1t_d_c_n_hypotheses_true 0 _ _ _ |- _ ] => apply rule_1t_0_c_n_hypotheses_true in H
           | [ H : rule_1t_c_n_hypotheses_true 0 _ _ |- _ ] => apply rule_1t_0_n_hypotheses_true in H
           | [ H : rule_1t_n_hypotheses_true 0 _ |- _ ] => apply rule_1t_0_hypotheses_true in H

           | [ H : rule_1d_c_n_hypotheses_true 0 _ _ |- _ ] => apply rule_1d_0_n_hypotheses_true in H
           | [ H : rule_1d_n_hypotheses_true 0 _ |- _ ] => apply rule_1d_0_hypotheses_true in H

           | [ H : rule_1c_n_hypotheses_true 0 _ |- _ ] => apply rule_1c_0_hypotheses_true in H

           | [ H : Vector.t _ 0 -> _ |- _ ] => pose proof (H (Vector.nil _)) as H
           | [ H : Vector.t _ 0 |- _ ] => induction H using Vector.case0; simpl in *
           | [ H : Vector.t _ 1 |- _ ] => induction H using Vector.caseS'; simpl in *
           end.

  Ltac intro_sem_rule :=
    repeat match goal with
           | [ |- rule_e_t_d_c_n_hypotheses_true 0 _ _ _ _ _ ] => apply rule_0_t_d_c_n_hypotheses_true
           | [ |- rule_e_t_d_c_n_hypotheses_true 1 _ _ _ _ _ ] => apply rule_1_t_d_c_n_hypotheses_true
           | [ |- rule_t_d_c_n_hypotheses_true 0 _ _ _ _ ] => apply rule_0_d_c_n_hypotheses_true
           | [ |- rule_t_d_c_n_hypotheses_true 1 _ _ _ _ ] => apply rule_1_d_c_n_hypotheses_true
           | [ |- rule_d_c_n_hypotheses_true 0 _ _ _ ] => apply rule_0_c_n_hypotheses_true
           | [ |- rule_d_c_n_hypotheses_true 1 _ _ _ ] => apply rule_1_c_n_hypotheses_true
           | [ |- rule_c_n_hypotheses_true 0 _ _ ] => apply rule_0_n_hypotheses_true
           | [ |- rule_c_n_hypotheses_true 1 _ _ ] => apply rule_1_n_hypotheses_true
           | [ |- rule_n_hypotheses_true 0 _ ] => apply rule_0_hypotheses_true
           | [ |- rule_n_hypotheses_true 1 _ ] => apply rule_1_hypotheses_true

           | [ |- rule__hypotheses_true _ ] => unfold rule__hypotheses_true; simpl

           | [ |- rule_1e_t_d_c_n_hypotheses_true 0 _ _ _ _ ] => apply rule_1e_0_d_c_n_hypotheses_true
           | [ |- rule_1e_d_c_n_hypotheses_true 0 _ _ _ ] => apply rule_1e_0_c_n_hypotheses_true
           | [ |- rule_1e_c_n_hypotheses_true 0 _ _ ] => apply rule_1e_0_n_hypotheses_true
           | [ |- rule_1e_n_hypotheses_true 0 _ ] => apply rule_1e_0_hypotheses_true

           | [ |- rule_1t_d_c_n_hypotheses_true 0 _ _ _ ] => apply rule_1t_0_c_n_hypotheses_true
           | [ |- rule_1t_c_n_hypotheses_true 0 _ _ ] => apply rule_1t_0_n_hypotheses_true
           | [ |- rule_1t_n_hypotheses_true 0 _ ] => apply rule_1t_0_hypotheses_true

           | [ |- rule_1d_c_n_hypotheses_true 0 _ _ ] => apply rule_1d_0_n_hypotheses_true
           | [ |- rule_1d_n_hypotheses_true 0 _ ] => apply rule_1d_0_hypotheses_true

           | [ |- rule_1c_n_hypotheses_true 0 _ ] => apply rule_1c_0_hypotheses_true

           | [ |- rule_1e_hypotheses_true _ ] =>
             let e := fresh "e" in
             intro e; try clear e

           | [ |- rule_1t_hypotheses_true _ ] =>
             let t := fresh "t" in
             intro t; try clear t

           | [ |- rule_1c_hypotheses_true _ ] =>
             let c := fresh "c" in
             intro c; try clear c

           | [ |- rule_1n_hypotheses_true _ ] =>
             let n := fresh "n" in
             intro n; try clear n

           | [ |- Vector.t _ 0 -> _ ] =>
             let l := fresh "l" in
             intro l; try clear l
           | [ |- Vector.t _ 1 -> _ ] =>
             let l := fresh "l" in
             intro l; try clear l
           end.

  Ltac simseqs a :=
    simpl; auto;
    intro_sem_rule;
    simpl_sem_rule;
    introv a; simpl in a;
    repndors; subst; tcsp;
    autorewrite with norm;
    simpl_sem_rule; auto.

  Ltac inst_hyp t h :=
    match goal with
    | [ H : rule_1e_hypotheses_true _ |- _ ] =>
      let H' := fresh H in
      dup H as H';
      pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

    | [ H : rule_1t_hypotheses_true _ |- _ ] =>
      let H' := fresh H in
      dup H as H';
      pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

    | [ H : rule_1d_hypotheses_true _ |- _ ] =>
      let H' := fresh H in
      dup H as H';
      pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

    | [ H : rule_1c_hypotheses_true _ |- _ ] =>
      let H' := fresh H in
      dup H as H';
      pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto

    | [ H : rule_1n_hypotheses_true _ |- _ ] =>
      let H' := fresh H in
      dup H as H';
      pose proof (H t) as H; simpl in H; simpl_sem_rule; dLin_hyp h; auto
    end.

  (* To prove primitive rules *)
  Ltac start_proving_primitive st ct ht :=
    introv st ct ht; simpl in *;
    simpl_sem_rule;
    dLin_hyp st; simpl in *.

  (* To prove derived rules *)
  Ltac start_proving_derived st :=
    introv st; simpl in *; simpl_sem_rule; dLin_hyp st.

  Lemma add_nil2guards :
    forall {eo : EventOrdering} G H a,
      sequent_true (MkSeq ([] ++ G) H a)
      -> sequent_true (MkSeq G H a).
  Proof.
    simpl in *; tcsp.
  Qed.


  (*  ****** PRIMITIVE RULES ****** *)


  (***********************************************************)
  Definition PRIMITIVE_RULE_implies_intro x {eo : EventOrdering} e R H A B :=
    MkRule0
      [⟬R⟭ H • (x › A @ e) ⊢ B @ e]
      (⟬R⟭ H ⊢ KE_IMPLIES A B @ e).

  Lemma PRIMITIVE_RULE_implies_intro_true :
    forall x {eo : EventOrdering} e R H A B,
      rule_true (PRIMITIVE_RULE_implies_intro x e R H A B).
  Proof.
    start_proving_primitive st ct ht; introv h.
    apply st0; introv i; simpl in *; auto.
    apply hyp_in_add in i; repndors; subst; simpl in *; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_and_intro {eo : EventOrdering} e R H A B :=
    MkRule0
      [⟬R⟭ H ⊢ A @ e,
       ⟬R⟭ H ⊢ B @ e]
      (⟬R⟭ H ⊢ KE_AND A B @ e).

  Lemma PRIMITIVE_RULE_and_intro_true :
    forall {eo : EventOrdering} e R H A B,
      rule_true (PRIMITIVE_RULE_and_intro e R H A B).
  Proof.
    start_proving_primitive st ct ht.
    dands; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_implies_elim x {eo : EventOrdering} e R H J a b c :=
    MkRule0
      [⟬R⟭ H » J ⊢ a @ e,
       ⟬R⟭ H • (x › b @ e) » J ⊢ c]
      (⟬R⟭ H • (x › KE_IMPLIES a b @ e) » J ⊢ c).

  Lemma PRIMITIVE_RULE_implies_elim_true :
    forall x {eo : EventOrdering} e R H J a b c,
      rule_true (PRIMITIVE_RULE_implies_elim x e R H J a b c).
  Proof.
    start_proving_primitive st ct ht.
    apply st1; introv i; simpl in *; auto.
    allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; simpl in *; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp));[].
    pose proof (ht (x › KE_IMPLIES a b @ e)) as q; simpl in *.
    unfold hyp_event in *; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; autodimp q hyp; tcsp.
    apply q; clear q.
    apply st0; simpl; introv i; auto.
    apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_exists_node_intro c {eo : EventOrdering} e R H f :=
    MkRule0
      [⟬R⟭ H ⊢ f c @ e]
      (⟬R⟭ H ⊢ KE_EX_NODE f @ e).

  Lemma PRIMITIVE_RULE_exists_node_intro_true :
    forall c {eo : EventOrdering} e R H f,
      rule_true (PRIMITIVE_RULE_exists_node_intro c e R H f).
  Proof.
    start_proving_primitive st ct ht.
    exists c; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_at {eo : EventOrdering} e n R H :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_AT n @ e).

  Lemma PRIMITIVE_RULE_at_true :
    forall {eo : EventOrdering} (e : EventN) n R H (cond : name2node (loc e) = Some n),
      rule_true (PRIMITIVE_RULE_at e n R H).
  Proof.
    introv cond; start_proving_primitive st ct ht.
    unfold seq_event; simpl.
    apply name2node_cond in cond; auto.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_hypothesis {eo : EventOrdering} x R H J a :=
    MkRule0
      []
      (⟬R⟭ H • (x › a) » J ⊢ a).

  Lemma PRIMITIVE_RULE_hypothesis_true :
    forall {eo : EventOrdering} x R H J a,
      rule_true (PRIMITIVE_RULE_hypothesis x R H J a).
  Proof.
    start_proving_primitive st ct ht.
    apply (ht (x › a)); apply hyp_in_adds; tcsp; left; apply hyp_in_add; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_thin x {eo : EventOrdering} R H a J b :=
    MkRule0
      [⟬R⟭ H » J ⊢ b]
      (⟬R⟭ H • (x › a) » J ⊢ b).

  Lemma PRIMITIVE_RULE_thin_true :
    forall x {eo : EventOrdering} R H a J b,
      rule_true (PRIMITIVE_RULE_thin x R H a J b).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; simpl; tcsp.
    introv i; apply hyp_in_adds in i; repndors; tcsp.
    { apply ht; apply hyp_in_adds; left; apply hyp_in_add; tcsp. }
    { apply ht; apply hyp_in_adds; tcsp. }
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_or_intro_left {eo : EventOrdering} e R H A B :=
    MkRule0
      [⟬R⟭ H ⊢ A @ e]
      (⟬R⟭ H ⊢ KE_OR A B @ e).

  Lemma PRIMITIVE_RULE_or_intro_left_true :
    forall {eo : EventOrdering} e R H A B,
      rule_true (PRIMITIVE_RULE_or_intro_left e R H A B).
  Proof.
    start_proving_primitive st ct ht.
    dands; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_or_intro_right {eo : EventOrdering} e R H A B :=
    MkRule0
      [⟬R⟭ H ⊢ B @ e]
      (⟬R⟭ H ⊢ KE_OR A B @ e).

  Lemma PRIMITIVE_RULE_or_intro_right_true :
    forall {eo : EventOrdering} e R H A B,
      rule_true (PRIMITIVE_RULE_or_intro_right e R H A B).
  Proof.
    start_proving_primitive st ct ht.
    dands; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_cut {eo : EventOrdering} x a R H b :=
    MkRule0
      [⟬R⟭ H ⊢ a,
       ⟬R⟭ H • (x › a) ⊢ b]
      (⟬R⟭ H ⊢ b).

  Lemma PRIMITIVE_RULE_cut_true :
    forall {eo : EventOrdering} x a R H b,
      rule_true (PRIMITIVE_RULE_cut x a R H b).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; clear st0; simpl in *; auto.
    apply st1; simpl; introv i; auto.
    apply hyp_in_add in i; repndors; subst; simpl in *; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_cut_after {eo : EventOrdering} x y a R H b c J :=
    MkRule0
      [⟬R⟭ H • (y › c) » J ⊢ a,
       ⟬R⟭ H • (y › c) • (x › a) » J ⊢ b]
      (⟬R⟭ H • (y › c) » J ⊢ b).

  Lemma PRIMITIVE_RULE_cut_after_true :
    forall {eo : EventOrdering} x y a R H b c J,
      rule_true (PRIMITIVE_RULE_cut_after x y a R H b c J).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; clear st0; simpl in *; auto.
    apply st1; simpl; introv i; auto.
    apply hyp_in_adds in i; repndors; tcsp.
    { apply hyp_in_add in i; repndors; subst; simpl in *; tcsp.
      apply ht; apply hyp_in_adds; tcsp. }
    { apply ht; apply hyp_in_adds; tcsp. }
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_thin_all {eo : EventOrdering} R H a :=
    MkRule0
      [⟬R⟭ ∅ ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_thin_all_true :
    forall {eo : EventOrdering} R H a,
      rule_true (PRIMITIVE_RULE_thin_all R H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; simpl; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_revert_all {eo : EventOrdering} e R H (a : KExpression) :=
    MkRule0
      [⟬R⟭ ∅ ⊢ KE_IMPLIES (hypotheses2expression H) a @ e]
      (⟬R⟭ H ⊢ a @ e).

  Lemma PRIMITIVE_RULE_revert_all_true :
    forall {eo : EventOrdering} (e : EventN) R H a (Hate : hyps_at_event H e),
      rule_true (PRIMITIVE_RULE_revert_all e R H a).
  Proof.
    introv Hate; start_proving_primitive st ct ht.
    unfold sequent_true in st0; simpl in *.
    apply st0; tcsp.
    apply implies_interpret_KE_ANDS; introv i.
    allrw in_map_iff; exrepnd; subst; tcsp.
    unfold seq_event, exp_of_hyp in *; simpl in *.
    applydup Hate in i0; subst; rewrite <- i1; auto.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_unrevert_all {eo : EventOrdering} e R H (a : KExpression) :=
    MkRule0
      [⟬R⟭ H ⊢ a @ e]
      (⟬R⟭ ∅ ⊢ KE_IMPLIES (hypotheses2expression H) a @ e).

  Lemma PRIMITIVE_RULE_unrevert_all_true :
    forall {eo : EventOrdering} (e : EventN) R H a (Hate : hyps_at_event H e),
      rule_true (PRIMITIVE_RULE_unrevert_all e R H a).
  Proof.
    introv Hate; start_proving_primitive st ct ht; introv h.
    unfold sequent_true in *; simpl in *.
    apply st0; tcsp.
    introv ci.
    applydup Hate in ci; rewrite ci0.
    eapply interpret_KE_ANDS_implies in h;[eauto|].
    unfold seq_event, exp_of_hyp in *; simpl in *.
    apply in_map_iff; eexists; dands; eauto.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_thin_but_last {eo : EventOrdering} R H h a :=
    MkRule0
      [⟬R⟭ ∅ • h ⊢ a]
      (⟬R⟭ H • h ⊢ a).

  Lemma PRIMITIVE_RULE_thin_but_last_true :
    forall {eo : EventOrdering} R H h a,
      rule_true (PRIMITIVE_RULE_thin_but_last R H h a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; simpl; tcsp.
    introv i; repndors; subst; tcsp.
    apply ht; apply hyp_in_add; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_or_elim x {eo : EventOrdering} e R H J A B c :=
    MkRule0
      [⟬R⟭ H • (x › A @ e) » J ⊢ c,
       ⟬R⟭ H • (x › B @ e) » J ⊢ c]
      (⟬R⟭ H • (x › KE_OR A B @ e) » J ⊢ c).

  Lemma PRIMITIVE_RULE_or_elim_true :
    forall x {eo : EventOrdering} e R H J A B c,
      rule_true (PRIMITIVE_RULE_or_elim x e R H J A B c).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_OR A B @ e)) as q; simpl in q; autodimp q hyp.
    { allrw hyp_in_adds; allrw hyp_in_add; tcsp. }
    repndors.
    { apply st0; introv i; simpl in *; auto.
      allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
        apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp. }
    { apply st1; introv i; simpl in *; auto.
      allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
        apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp. }
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_and_elim x y {eo : EventOrdering} e R H J A B c :=
    MkRule0
      [⟬R⟭ H • (x › B @ e) • (y › A @ e) » J ⊢ c]
      (⟬R⟭ H • (x › KE_AND A B @ e) » J ⊢ c).

  Lemma PRIMITIVE_RULE_and_elim_true :
    forall x y {eo : EventOrdering} e R H J A B c,
      rule_true (PRIMITIVE_RULE_and_elim x y e R H J A B c).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; introv j; simpl in *; clear st0; auto.
    allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; simpl in *; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp));
      pose proof (ht (x › KE_AND A B @ e)) as ht; allrw hyp_in_adds; allrw hyp_in_add;
        autodimp ht hyp; simpl in *; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_rename_hyp x y {eo : EventOrdering} e R H J A c :=
    MkRule0
      [⟬R⟭ H • (y › A @ e) » J ⊢ c]
      (⟬R⟭ H • (x › A @ e) » J ⊢ c).

  Lemma PRIMITIVE_RULE_rename_hyp_true :
    forall x y {eo : EventOrdering} e R H J A c,
      rule_true (PRIMITIVE_RULE_rename_hyp x y e R H J A c).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; introv j; simpl in *; clear st0; auto.
    allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; simpl in *; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp));
      pose proof (ht (x › A @ e)) as ht; allrw hyp_in_adds; allrw hyp_in_add;
        autodimp ht hyp; simpl in *; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_rename_causal u v {eo : EventOrdering} Q R H a c :=
    MkRule0
      [⟬Q ++ (u ⋈ a) :: R⟭ H ⊢ c]
      (⟬Q ++ (v ⋈ a) :: R⟭ H ⊢ c).

  Lemma PRIMITIVE_RULE_rename_causal_true :
    forall u v {eo : EventOrdering} Q R H a c,
      rule_true (PRIMITIVE_RULE_rename_causal u v Q R H a c).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; introv j; simpl in *; clear st0; auto.
    allrw in_app_iff; simpl in *; repndors; subst; simpl; tcsp;
      try (complete (apply ct; apply in_app_iff; simpl; tcsp)).
    pose proof (ct (v ⋈ a)) as ct; simpl in *; apply ct; apply in_app_iff; simpl; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_unright_before_hyp_if_causal u x {eo : EventOrdering} e R H J a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ⋄ e) :: R⟭ H • (x › a @ e') » J ⊢ b])
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE a @ e) » J ⊢ b).

  Lemma PRIMITIVE_RULE_unright_before_hyp_if_causal_true :
    forall u x {eo : EventOrdering} e R H J a b,
      rule_true (PRIMITIVE_RULE_unright_before_hyp_if_causal u x e R H J a b).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_RIGHT_BEFORE a @ e)) as q.
    allrw hyp_in_adds; allrw hyp_in_add; simpl in *.
    repeat (autodimp q hyp); exrepnd; unfold hyp_event, seq_event in *; simpl in *.
    remember (direct_pred e) as d; symmetry in Heqd; destruct d; tcsp.
    applydup direct_pred_preserves_ex_node_e in Heqd as w; eauto 3 with kn;[].

    pose proof (st (MkEventN e0 w)) as st; simpl in *; simpl_sem_rule.
    dLin_hyp ht.
    apply ht0; simpl; introv j; allrw hyp_in_adds; allrw hyp_in_add;
      repndors; subst; tcsp;
        apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_node_eq_dec {eo : EventOrdering} e a b R H :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_OR (KE_NODE_EQ a b) (KE_NOT (KE_NODE_EQ a b)) @ e).

  Lemma PRIMITIVE_RULE_node_eq_dec_true :
    forall {eo : EventOrdering} e a b R H,
      rule_true (PRIMITIVE_RULE_node_eq_dec e a b R H).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    destruct (node_deq a b); subst; tcsp.
    right; intro xx; ginv.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_direct_pred_if_local_pred x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e' ⋄ e) :: Q⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_direct_pred_if_local_pred_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (PRIMITIVE_RULE_direct_pred_if_local_pred x e' e R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; tcsp.
    introv i; simpl in *.
    allrw in_app_iff; simpl in *; repndors; subst; tcsp; simpl;
      try (complete (apply ct; allrw in_app_iff; simpl in *; repndors; subst; tcsp)).
    pose proof (ct (x ⋈ e' ⋄ e)) as ct; allrw in_app_iff; simpl in *; autodimp ct hyp; eauto 3 with eo.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_subst_causal_eq_concl u {eo : EventOrdering} e1 e2 Q R H a :=
    MkRule0
      [⟬ Q ++ (u ⋈ e1 ≡ e2) :: R ⟭ H ⊢ a @ e1]
      (⟬ Q ++ (u ⋈ e1 ≡ e2) :: R ⟭ H ⊢ a @ e2).

  Lemma PRIMITIVE_RULE_subst_causal_eq_concl_true :
    forall u {eo : EventOrdering} e1 e2 Q R H a,
      rule_true (PRIMITIVE_RULE_subst_causal_eq_concl u e1 e2 Q R H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e1 ≡ e2)) as w; allrw in_app_iff; simpl in *.
    autodimp w hyp; tcsp.
    rewrite <- w.
    apply st0; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_causal_eq_sym u {eo : EventOrdering} e1 e2 Q R H a :=
    MkRule0
      [⟬ Q ++ (u ⋈ e2 ≡ e1) :: R ⟭ H ⊢ a]
      (⟬ Q ++ (u ⋈ e1 ≡ e2) :: R ⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_causal_eq_sym_true :
    forall u {eo : EventOrdering} e1 e2 Q R H a,
      rule_true (PRIMITIVE_RULE_causal_eq_sym u e1 e2 Q R H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; simpl; tcsp.
    introv i; allrw in_app_iff; simpl in *; repndors; subst; tcsp;
      try (complete (apply ct; apply in_app_iff; tcsp));[].
    pose proof (ct (u ⋈ e1 ≡ e2)) as w; simpl in *; autodimp w hyp.
    apply in_app_iff; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_remove_causal {eo : EventOrdering} c Q R H a :=
    MkRule0
      [⟬Q ++ R⟭ H ⊢ a]
      (⟬Q ++ c :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_remove_causal_true :
    forall {eo : EventOrdering} c Q R H a,
      rule_true (PRIMITIVE_RULE_remove_causal c Q R H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; simpl; tcsp.
    introv i; apply ct; allrw in_app_iff; simpl in *; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_localle_if_eq x {eo : EventOrdering} e1 e2 Q R H a :=
    MkRule0
      [⟬Q ++ (x ⋈ e1 ■ e2) :: R⟭ H ⊢ a]
      (⟬Q ++ (x ⋈ e1 ≡ e2) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_localle_if_eq_true :
    forall x {eo : EventOrdering} e1 e2 Q R H a,
      rule_true (PRIMITIVE_RULE_localle_if_eq x e1 e2 Q R H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; simpl in *; tcsp.
    pose proof (ct (x ⋈ e1 ≡ e2)) as w.
    rewrite in_app_iff in w; simpl in w; autodimp w hyp; subst.
    introv i; apply in_app_iff in i; simpl in *; repndors; subst; simpl in *; tcsp; eauto 3 with eo;
      try (complete (apply ct; apply in_app_iff; simpl; tcsp)).
    rewrite w; eauto 3 with eo.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_add_eq_refl x {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬(x ⋈ e ≡ e) :: R⟭ H ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_add_eq_refl_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (PRIMITIVE_RULE_add_eq_refl x e R H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; simpl in *; tcsp.
    introv i; repndors; subst; simpl in *; tcsp; eauto 3 with eo.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_local_if_localle x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_local_if_localle_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (PRIMITIVE_RULE_local_if_localle x e' e R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; tcsp.
    introv i; simpl in *.
    allrw in_app_iff; simpl in *; repndors; subst; tcsp; simpl;
      try (complete (apply ct; allrw in_app_iff; simpl in *; repndors; subst; tcsp)).
    pose proof (ct (x ⋈ e' □ e)) as ct; allrw in_app_iff; simpl in *; autodimp ct hyp; eauto 3 with eo.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_unright_before_hyp x {eo : EventOrdering} e R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › a @ local_pred_n e) » J ⊢ b]
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE a @ e) » J ⊢ b).

  Lemma PRIMITIVE_RULE_unright_before_hyp_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (PRIMITIVE_RULE_unright_before_hyp x e R H J a b).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_RIGHT_BEFORE a @ e)) as q.
    allrw hyp_in_adds; allrw hyp_in_add; simpl in *.
    repeat (autodimp q hyp); exrepnd; unfold hyp_event, seq_event in *; simpl in *.
    remember (direct_pred e) as d; destruct d; rev_Some; tcsp.
    apply st0; simpl; auto;[].
    introv i; allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp; simpl;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
    pose proof (ht (x › KE_RIGHT_BEFORE a @ e)) as w; simpl in w.
    unfold local_pred; rewrite Heqd in *; apply w; clear w.
    allrw hyp_in_adds; allrw hyp_in_add; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_exists_node_elim x {eo : EventOrdering} e R H J f a :=
    MkRule1n
      (fun n => [⟬R⟭ H • (x › f n @ e) » J ⊢ a])
      (⟬R⟭ H • (x › KE_EX_NODE f @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_exists_node_elim_true :
    forall x {eo : EventOrdering} e R H J f a,
      rule_true (PRIMITIVE_RULE_exists_node_elim x e R H J f a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_EX_NODE f @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    exrepnd.
    unfold hyp_event, seq_event in *; simpl in *.
    inst_hyp c st.
    apply st1; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_exists_trust_elim x {eo : EventOrdering} e R H J f a :=
    MkRule1t
      (fun t => [⟬R⟭ H • (x › f t @ e) » J ⊢ a])
      (⟬R⟭ H • (x › KE_EX_TRUST f @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_exists_trust_elim_true :
    forall x {eo : EventOrdering} e R H J f a,
      rule_true (PRIMITIVE_RULE_exists_trust_elim x e R H J f a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_EX_TRUST f @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    exrepnd.
    unfold hyp_event, seq_event in *; simpl in *.
    inst_hyp c st.
    apply st1; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_exists_trust_intro t {eo : EventOrdering} e R H f :=
    MkRule0
      [⟬R⟭ H ⊢ f t @ e]
      (⟬R⟭ H ⊢ KE_EX_TRUST f @ e).

  Lemma PRIMITIVE_RULE_exists_trust_intro_true :
    forall t {eo : EventOrdering} e R H f,
      rule_true (PRIMITIVE_RULE_exists_trust_intro t e R H f).
  Proof.
    start_proving_primitive st ct ht.
    exists t; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_all_trust_elim x t {eo : EventOrdering} e R H J f a :=
    MkRule0
      [⟬R⟭ H • (x › f t @ e) » J ⊢ a]
      (⟬R⟭ H • (x › KE_ALL_TRUST f @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_all_trust_elim_true :
    forall x t {eo : EventOrdering} e R H J f a,
      rule_true (PRIMITIVE_RULE_all_trust_elim x t e R H J f a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_ALL_TRUST f @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    pose proof (h t) as h.
    unfold hyp_event, seq_event in *; simpl in *.

    apply st0; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_all_trust_intro {eo : EventOrdering} e R H f :=
    MkRule1t
      (fun t => [⟬R⟭ H ⊢ f t @ e])
      (⟬R⟭ H ⊢ KE_ALL_TRUST f @ e).

  Lemma PRIMITIVE_RULE_all_trust_intro_true :
    forall {eo : EventOrdering} e R H f,
      rule_true (PRIMITIVE_RULE_all_trust_intro e R H f).
  Proof.
    start_proving_primitive st ct ht.
    introv; unfold seq_event; simpl.
    inst_hyp c st.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_exists_data_elim x {eo : EventOrdering} e R H J f a :=
    MkRule1d
      (fun d => [⟬R⟭ H • (x › f d @ e) » J ⊢ a])
      (⟬R⟭ H • (x › KE_EX_DATA f @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_exists_data_elim_true :
    forall x {eo : EventOrdering} e R H J f a,
      rule_true (PRIMITIVE_RULE_exists_data_elim x e R H J f a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_EX_DATA f @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    exrepnd.
    unfold hyp_event, seq_event in *; simpl in *.
    inst_hyp c st.
    apply st1; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_exists_data_intro d {eo : EventOrdering} e R H f :=
    MkRule0
      [⟬R⟭ H ⊢ f d @ e]
      (⟬R⟭ H ⊢ KE_EX_DATA f @ e).

  Lemma PRIMITIVE_RULE_exists_data_intro_true :
    forall d {eo : EventOrdering} e R H f,
      rule_true (PRIMITIVE_RULE_exists_data_intro d e R H f).
  Proof.
    start_proving_primitive st ct ht.
    exists d; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_all_data_intro {eo : EventOrdering} e R H f :=
    MkRule1d
      (fun d => [⟬R⟭ H ⊢ f d @ e])
      (⟬R⟭ H ⊢ KE_ALL_DATA f @ e).

  Lemma PRIMITIVE_RULE_all_data_intro_true :
    forall {eo : EventOrdering} e R H f,
      rule_true (PRIMITIVE_RULE_all_data_intro e R H f).
  Proof.
    start_proving_primitive st ct ht.
    introv; unfold seq_event; simpl.
    inst_hyp c st.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_all_data_elim x d {eo : EventOrdering} e R H J f a :=
    MkRule0
      [⟬R⟭ H • (x › f d @ e) » J ⊢ a]
      (⟬R⟭ H • (x › KE_ALL_DATA f @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_all_data_elim_true :
    forall x d {eo : EventOrdering} e R H J f a,
      rule_true (PRIMITIVE_RULE_all_data_elim x d e R H J f a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_ALL_DATA f @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    pose proof (h d) as h.
    unfold hyp_event, seq_event in *; simpl in *.

    apply st0; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_exists_id_elim x {eo : EventOrdering} e R H J f a :=
    MkRule1c
      (fun c => [⟬R⟭ H • (x › f c @ e) » J ⊢ a])
      (⟬R⟭ H • (x › KE_EX_ID f @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_exists_id_elim_true :
    forall x {eo : EventOrdering} e R H J f a,
      rule_true (PRIMITIVE_RULE_exists_id_elim x e R H J f a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_EX_ID f @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    exrepnd.
    unfold hyp_event, seq_event in *; simpl in *.

    inst_hyp c st.
    apply st1; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_unhappened_before_if_causal x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma PRIMITIVE_RULE_unhappened_before_if_causal_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (PRIMITIVE_RULE_unhappened_before_if_causal x e' e R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    exists e'; dands; eauto 3 with eo kn.
    pose proof (ct (x ⋈ e' ▷ e)) as ct; allrw in_app_iff; simpl in *; autodimp ct hyp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_unhappened_before_hyp u x {eo : EventOrdering} e R H J a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ▷ e) :: R⟭ H • (x › a @ e') » J ⊢ b])
      (⟬R⟭ H • (x › KE_HAPPENED_BEFORE a @ e) » J ⊢ b).

  Lemma PRIMITIVE_RULE_unhappened_before_hyp_true :
    forall u x {eo : EventOrdering} e R H J a b,
      rule_true (PRIMITIVE_RULE_unhappened_before_hyp u x e R H J a b).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_HAPPENED_BEFORE a @ e)) as q.
    allrw hyp_in_adds; allrw hyp_in_add; simpl in *.
    repeat (autodimp q hyp); exrepnd; unfold hyp_event, seq_event in *; simpl in *.
    inst_hyp e' ht.
    apply ht0; simpl; introv j; allrw hyp_in_adds; allrw hyp_in_add;
      repndors; subst; tcsp;
        apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp.
  Qed.


  (* TODO: this should be derivable from [PRIMITIVE_RULE_tri_if_same_loc] *)
  (***********************************************************)
  Definition PRIMITIVE_RULE_at_implies_local x n {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ▷ e2) :: Q⟭ H ⊢ KE_AT n @ e1,
       ⟬R ++ (x ⋈ e1 ▷ e2) :: Q⟭ H ⊢ KE_AT n @ e2,
       ⟬R ++ (x ⋈ e1 □ e2) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e1 ▷ e2) :: Q⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_at_implies_local_true :
    forall x n {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_at_implies_local x n e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; clear st0.
    applydup st1 in ht; simpl in *; tcsp; clear st1.
    unfold seq_event in *; simpl in *.
    apply st2; simpl in *; tcsp.
    introv i; allrw in_app_iff; simpl in *; repndors; subst; simpl in *; tcsp;
      try (complete (apply ct; allrw in_app_iff; simpl in *; repndors; subst; tcsp)).
    pose proof (ct (x ⋈ e1 ▷ e2)) as ct; allrw in_app_iff; simpl in *.
    autodimp ct hyp; tcsp; eauto 3 with eo; split; auto; try congruence.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_has_owner_implies_eq d {eo : EventOrdering} e a b R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_HAS_OWNER d a @ e,
       ⟬R⟭ H ⊢ KE_HAS_OWNER d b @ e]
      (⟬R⟭ H ⊢ KE_NODE_EQ a b @ e).

  Lemma PRIMITIVE_RULE_has_owner_implies_eq_true :
    forall d {eo : EventOrdering} e a b R H,
      rule_true (PRIMITIVE_RULE_has_owner_implies_eq d e a b R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp.
    applydup st1 in ht; simpl in *; tcsp.
    unfold data_is_owned_by in *.
    remember (kc_data2owner d) as w; destruct w; subst; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_has_owner_change_event {eo : EventOrdering} e1 e2 R H n d :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_HAS_OWNER d n @ e2]
      (⟬ R ⟭ H ⊢ KE_HAS_OWNER d n @ e1).

  Lemma PRIMITIVE_RULE_has_owner_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H n d,
      rule_true (PRIMITIVE_RULE_has_owner_change_event e1 e2 R H n d).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_subst_node_in_at a b {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_NODE_EQ a b @ e,
       ⟬R⟭ H ⊢ KE_AT a @ e]
      (⟬R⟭ H ⊢ KE_AT b @ e).

  Lemma PRIMITIVE_RULE_subst_node_in_at_true :
    forall a b {eo : EventOrdering} e R H,
      rule_true (PRIMITIVE_RULE_subst_node_in_at a b e R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; ginv.
    applydup st1 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_eq_sym {eo : EventOrdering} e R H t1 t2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_ID_EQ t2 t1 @ e]
      (⟬ R ⟭ H ⊢ KE_ID_EQ t1 t2 @ e).

  Lemma PRIMITIVE_RULE_id_eq_sym_true :
    forall {eo : EventOrdering} e R H t1 t2,
      rule_true (PRIMITIVE_RULE_id_eq_sym e R H t1 t2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_trust_eq_sym {eo : EventOrdering} e R H t1 t2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_TRUST_EQ t2 t1 @ e]
      (⟬ R ⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma PRIMITIVE_RULE_trust_eq_sym_true :
    forall {eo : EventOrdering} e R H t1 t2,
      rule_true (PRIMITIVE_RULE_trust_eq_sym e R H t1 t2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_node_eq_sym {eo : EventOrdering} e R H n1 n2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_NODE_EQ n2 n1 @ e]
      (⟬ R ⟭ H ⊢ KE_NODE_EQ n1 n2 @ e).

  Lemma PRIMITIVE_RULE_node_eq_sym_true :
    forall {eo : EventOrdering} e R H n1 n2,
      rule_true (PRIMITIVE_RULE_node_eq_sym e R H n1 n2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_causal_if_causalle x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_causal_if_causalle_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (PRIMITIVE_RULE_causal_if_causalle x e' e R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; tcsp.
    introv i; simpl in *.
    allrw in_app_iff; simpl in *; repndors; subst; tcsp; simpl;
      try (complete (apply ct; allrw in_app_iff; simpl in *; repndors; subst; tcsp)).
    pose proof (ct (x ⋈ e' ▷ e)) as ct; allrw in_app_iff; simpl in *; autodimp ct hyp; eauto 3 with eo.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_localle_if_causalle x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_localle_if_causalle_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (PRIMITIVE_RULE_localle_if_causalle x e' e R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; tcsp.
    introv i; simpl in *.
    allrw in_app_iff; simpl in *; repndors; subst; tcsp; simpl;
      try (complete (apply ct; allrw in_app_iff; simpl in *; repndors; subst; tcsp)).
    pose proof (ct (x ⋈ e' ■ e)) as ct; allrw in_app_iff; simpl in *; autodimp ct hyp; eauto 3 with eo.
  Qed.


  (* FIX *)
  (* TOOD: is this derivable? *)
  (************************************************************************************************)
  Definition PRIMITIVE_RULE_split_local_before_eq2 u {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ≡ e2) :: R⟭ H ⊢ a,
       ⟬Q ++ (u ⋈ e1 □ e2) :: R⟭ H ⊢ a]
      (⟬Q ++ (u ⋈ e1 ■ e2) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_split_local_before_eq2_true :
    forall u {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_split_local_before_eq2 u e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e1 ■ e2)) as h; simpl in *.
    allrw in_app_iff; allsimpl; autodimp h hyp.
    apply localHappenedBeforeLe_implies_or2 in h; repndors; subst.

    { apply st0 in ht; simpl in *; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)). }

    { apply st1 in ht; simpl in *; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)). }
  Qed.


  (* FIX *)
  (* TOOD: is this derivable? *)
  (************************************************************************************************)
  Definition PRIMITIVE_RULE_split_happened_before_eq2 u {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ≡ e2) :: R⟭ H ⊢ a,
       ⟬Q ++ (u ⋈ e1 ▷ e2) :: R⟭ H ⊢ a]
      (⟬Q ++ (u ⋈ e1 ▶ e2) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_split_happened_before_eq2_true :
    forall u {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_split_happened_before_eq2 u e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e1 ▶ e2)) as h; simpl in *.
    allrw in_app_iff; allsimpl; autodimp h hyp.
    destruct h as [h|h]; subst.

    { apply st1 in ht; simpl in *; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)). }

    { apply st0 in ht; simpl in *; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)). }
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_local_if_causal x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_local_if_causal_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (PRIMITIVE_RULE_local_if_causal x e' e R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; tcsp.
    introv i; simpl in *.
    allrw in_app_iff; simpl in *; repndors; subst; tcsp; simpl;
      try (complete (apply ct; allrw in_app_iff; simpl in *; repndors; subst; tcsp)).
    pose proof (ct (x ⋈ e' □ e)) as ct; allrw in_app_iff; simpl in *; autodimp ct hyp; eauto 3 with eo.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_duplicate_guard u v {eo : EventOrdering} g R Q H a :=
    MkRule0
      [⟬Q ++ (v ⋈ g) :: (u ⋈ g) :: R⟭ H ⊢ a]
      (⟬Q ++ (u ⋈ g) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_duplicate_guard_true :
    forall u v {eo : EventOrdering} g R Q H a,
      rule_true (PRIMITIVE_RULE_duplicate_guard u v g R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; simpl in *; tcsp.
    pose proof (ct (u ⋈ g)) as q; allrw in_app_iff; allsimpl; autodimp q hyp.
    introv i; allrw in_app_iff; simpl in *.
    repndors; subst; tcsp; simpl;
      try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)).
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_at_change_localle x {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_AT a @ e1]
      (⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_AT a @ e2).

  Lemma PRIMITIVE_RULE_at_change_localle_true :
    forall x {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_at_change_localle x e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; clear st0; auto;[].
    simpl in *; exrepnd.
    unfold seq_event in *; simpl in *; eauto 3 with kn.
    allrw interp_owns.
    pose proof (ct (x ⋈ e1 ■ e2)) as ct; allrw in_app_iff; simpl in *.
    autodimp ct hyp.
    rewrite <- ht; symmetry; eauto 3 with eo.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_at_change_localle_fwd x {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_AT a @ e2]
      (⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_AT a @ e1).

  Lemma PRIMITIVE_RULE_at_change_localle_fwd_true :
    forall x {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_at_change_localle_fwd x e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; clear st0; auto;[].
    simpl in *; exrepnd.
    unfold seq_event in *; simpl in *; eauto 3 with kn.
    allrw interp_owns.
    pose proof (ct (x ⋈ e1 ■ e2)) as ct; allrw in_app_iff; simpl in *.
    autodimp ct hyp.
    rewrite <- ht; eauto 3 with eo.
  Qed.


  (* DISCUSS *)
  (***********************************************************)
  Definition PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e']
      (⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq x e' e R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
    unfold seq_event in *; simpl in *; exrepnd.
    exists e'0; dands; eauto 3 with eo.
    pose proof (ct (x ⋈ e' ▷ e)) as ct; allrw in_app_iff; simpl in *; autodimp ct hyp; eauto 3 with eo.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_exists_id_intro c {eo : EventOrdering} e R H f :=
    MkRule0
      [⟬R⟭ H ⊢ f c @ e]
      (⟬R⟭ H ⊢ KE_EX_ID f @ e).

  Lemma PRIMITIVE_RULE_exists_id_intro_true :
    forall c {eo : EventOrdering} e R H f,
      rule_true (PRIMITIVE_RULE_exists_id_intro c e R H f).
  Proof.
    start_proving_primitive st ct ht.
    exists c; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_unright_before_if_causal x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ⋄ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' ⋄ e) :: Q⟭ H ⊢ KE_RIGHT_BEFORE a @ e).

  Lemma PRIMITIVE_RULE_unright_before_if_causal_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (PRIMITIVE_RULE_unright_before_if_causal x e' e R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp; clear st0.
    unfold seq_event in *; simpl in *.
    pose proof (ct (x ⋈ e' ⋄ e)) as ct; allrw in_app_iff; simpl in *; autodimp ct hyp.
    rewrite ct; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_forall_before_elim u x {eo : EventOrdering} e e' R Q H J t a :=
    MkRule0
      [⟬R ++ (u ⋈ e' ▷ e) :: Q⟭ H • (x › t @ e') » J ⊢ a]
      (⟬R ++ (u ⋈ e' ▷ e) :: Q⟭ H • (x › KE_FORALL_BEFORE t @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_forall_before_elim_true :
    forall u x {eo : EventOrdering} e e' R Q H J t a,
      rule_true (PRIMITIVE_RULE_forall_before_elim u x e e' R Q H J t a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_FORALL_BEFORE t @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    unfold hyp_event, seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e' ▷ e)) as w; simpl in w; autodimp w hyp.
    { apply in_app_iff; simpl; tcsp. }
    pose proof (h e') as h; autodimp h hyp.
    apply st0; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_subst_causal_eq_hyp u x {eo : EventOrdering} e1 e2 Q R H J a b :=
    MkRule0
      [⟬ Q ++ (u ⋈ e1 ≡ e2) :: R ⟭ H • (x › b @ e2) » J ⊢ a]
      (⟬ Q ++ (u ⋈ e1 ≡ e2) :: R ⟭ H • (x › b @ e1) » J ⊢ a).

  Lemma PRIMITIVE_RULE_subst_causal_eq_hyp_true :
    forall u x {eo : EventOrdering} e1 e2 Q R H J a b,
      rule_true (PRIMITIVE_RULE_subst_causal_eq_hyp u x e1 e2 Q R H J a b).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ct (u ⋈ e1 ≡ e2)) as w; rewrite in_app_iff in w; simpl in *.
    autodimp w hyp.
    unfold seq_event in *; simpl in *.
    apply st0; simpl in *; tcsp.
    introv i; apply in_app_iff in i; repndors;[|apply ht; apply in_app_iff; tcsp];[].
    apply in_snoc in i; repndors; subst; simpl in *; tcsp.
    { apply ht; apply in_app_iff; left; apply in_snoc; tcsp. }
    unfold hyp_event; simpl.
    rewrite <- w; auto.
    apply (ht (x › b @ e1)); apply in_app_iff; left; apply in_snoc; tcsp.
  Qed.


  (* TODO: derivable? *)
  (***********************************************************)
  Definition PRIMITIVE_RULE_at_implies_localle x n {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ▶ e2) :: Q⟭ H ⊢ KE_AT n @ e1,
       ⟬R ++ (x ⋈ e1 ▶ e2) :: Q⟭ H ⊢ KE_AT n @ e2,
       ⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e1 ▶ e2) :: Q⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_at_implies_localle_true :
    forall x n {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_at_implies_localle x n e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; clear st0.
    applydup st1 in ht; simpl in *; tcsp; clear st1.
    unfold seq_event in *; simpl in *.
    allrw interp_owns.
    apply st2; simpl in *; tcsp.
    introv i; allrw in_app_iff; simpl in *; repndors; subst; simpl in *; tcsp;
      try (complete (apply ct; allrw in_app_iff; simpl in *; repndors; subst; tcsp)).
    pose proof (ct (x ⋈ e1 ▶ e2)) as ct; allrw in_app_iff; simpl in *.
    autodimp ct hyp; tcsp; eauto 3 with eo.
    split; auto; try congruence.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_tri_if_same_loc u n {eo : EventOrdering} e1 e2 R H a :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_AT n @ e1,
       ⟬ R ⟭ H ⊢ KE_AT n @ e2,
       ⟬ (u ⋈ e1 ≡ e2) :: R ⟭ H ⊢ a,
       ⟬ (u ⋈ e1 □ e2) :: R ⟭ H ⊢ a,
       ⟬ (u ⋈ e2 □ e1) :: R ⟭ H ⊢ a]
      (⟬ R ⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_tri_if_towned_true :
    forall u n {eo : EventOrdering} e1 e2 R H a,
      rule_true (PRIMITIVE_RULE_tri_if_same_loc u n e1 e2 R H a).
  Proof.
    start_proving_primitive st ct ht; simpl in *.
    applydup st0 in ht; simpl in *; tcsp; clear st0.
    applydup st1 in ht; simpl in *; tcsp; clear st1.
    unfold seq_event in *; simpl in *.
    assert (loc e1 = loc e2) as eqloc by (subst; congruence).

    pose proof (tri_if_same_loc _ _ eqloc) as xx; repndors; tcsp.

    { apply st3; simpl; tcsp.
      introv i; repndors; subst; tcsp. }

    { apply st2; simpl; tcsp.
      introv i; repndors; subst; tcsp. }

    { apply st4; simpl; tcsp.
      introv i; repndors; subst; tcsp. }
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_has_owner_dec {eo : EventOrdering} e d n R H :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_OR (KE_HAS_OWNER d n) (KE_NOT (KE_HAS_OWNER d n)) @ e).

  Lemma PRIMITIVE_RULE_has_owner_dec_true :
    forall {eo : EventOrdering} e d n R H,
      rule_true (PRIMITIVE_RULE_has_owner_dec e d n R H).
  Proof.
    start_proving_primitive st ct ht.
    unfold data_is_owned_by, seq_event; simpl; allrw interp_KE_FALSE.
    remember (kc_data2owner d) as o; symmetry in Heqo; destruct o; tcsp.
    destruct (node_deq n0 n); subst; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_subst_node_in_has_owner a b d {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_NODE_EQ a b @ e,
       ⟬R⟭ H ⊢ KE_HAS_OWNER d a @ e]
      (⟬R⟭ H ⊢ KE_HAS_OWNER d b @ e).

  Lemma PRIMITIVE_RULE_subst_node_in_has_owner_true :
    forall a b d {eo : EventOrdering} e R H,
      rule_true (PRIMITIVE_RULE_subst_node_in_has_owner a b d e R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp.
    applydup st1 in ht; simpl in *; tcsp.
    ginv; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_gen_for_change_event {eo : EventOrdering} e1 e2 R H d t :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_GEN_FOR d t @ e2]
      (⟬ R ⟭ H ⊢ KE_GEN_FOR d t @ e1).

  Lemma PRIMITIVE_RULE_gen_for_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H d t,
      rule_true (PRIMITIVE_RULE_gen_for_change_event e1 e2 R H d t).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_decidable_knows {eo : EventOrdering} e R H a :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_OR (KE_KNOWS a) (KE_NOT (KE_KNOWS a)) @ e).

  Lemma PRIMITIVE_RULE_decidable_knows_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (PRIMITIVE_RULE_decidable_knows e R H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *; allrw interp_KE_FALSE.
    apply knows_after_dec.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_unlocal_before_eq_correct_trace_before_hyp x {eo : EventOrdering} e R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › KE_LOCAL_BEFORE_EQ (KE_CORRECT_TRACE_BEFORE a) @ e) » J ⊢ b]
      (⟬R⟭ H • (x › KE_CORRECT_TRACE_BEFORE a @ e) » J ⊢ b).

  Lemma PRIMITIVE_RULE_unlocal_before_eq_correct_trace_before_hyp_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (PRIMITIVE_RULE_unlocal_before_eq_correct_trace_before_hyp x e R H J a b).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; clear st0; auto;[].
    introv i; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; simpl in *; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp));[].
    pose proof (ht (x › KE_CORRECT_TRACE_BEFORE a @ e)) as ht; simpl in *.
    autodimp ht hyp; allrw hyp_in_adds; allrw hyp_in_add; tcsp.
    destruct (implies_ex_node e) as [n w]; apply name2node_cond in w.
    unfold hyp_event in *; simpl in *; right; dands; tcsp; eauto.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_correct_trace_before_if_causal u {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (u ⋈ e' ■ e) :: Q⟭ H ⊢ KE_CORRECT_TRACE_BEFORE a @ e]
      (⟬R ++ (u ⋈ e' ■ e) :: Q⟭ H ⊢ KE_CORRECT_TRACE_BEFORE a @ e').

  Lemma PRIMITIVE_RULE_correct_trace_before_if_causal_true :
    forall u {eo : EventOrdering} e' e R Q H a,
      rule_true (PRIMITIVE_RULE_correct_trace_before_if_causal u e' e R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; auto; clear st0.
    unfold seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e' ■ e)) as ct; allrw in_app_iff; simpl in *.
    autodimp ct hyp; eauto 3 with eo.
    allrw interp_KE_CORRECT_TRACE_BEFORE.
    destruct a; simpl in *; tcsp; eauto 3 with eo.
    assert (loc e' = loc e) as eqloc by eauto 3 with eo.
    rewrite eqloc; eauto 3 with eo.
  Qed.


  (****************************************************************)
  Definition PRIMITIVE_RULE_knows_implies_correct (i : kc_data) {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_KNOWS i @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_CORRECT_TRACE_BEFORE @ e).

  Lemma PRIMITIVE_RULE_knows_implies_correct_true :
    forall (i : kc_data) {eo : EventOrdering} e R H,
      rule_true (PRIMITIVE_RULE_knows_implies_correct i e R H).
  Proof.
    Opaque KE_CORRECT_TRACE_BEFORE.
    start_proving_primitive st ct ht.
    unfold seq_event, KE_LOCAL_CORRECT_TRACE_BEFORE; simpl.
    allrw interp_KE_CORRECT_TRACE_BEFORE.
    Transparent KE_CORRECT_TRACE_BEFORE.
    apply st0 in ht; clear st0; simpl in *; eauto 3 with kn.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_trust_eq_change_event {eo : EventOrdering} e1 e2 R H t1 t2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e2]
      (⟬ R ⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e1).

  Lemma PRIMITIVE_RULE_trust_eq_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H t1 t2,
      rule_true (PRIMITIVE_RULE_trust_eq_change_event e1 e2 R H t1 t2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_eq_change_event {eo : EventOrdering} e1 e2 R H t1 t2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_ID_EQ t1 t2 @ e2]
      (⟬ R ⟭ H ⊢ KE_ID_EQ t1 t2 @ e1).

  Lemma PRIMITIVE_RULE_id_eq_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H t1 t2,
      rule_true (PRIMITIVE_RULE_id_eq_change_event e1 e2 R H t1 t2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_collision_resistant t1 t2 {eo : EventOrdering} e R H d1 d2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_GEN_FOR d1 t1 @ e,
       ⟬ R ⟭ H ⊢ KE_GEN_FOR d2 t2 @ e,
       ⟬ R ⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e,
       ⟬ R ⟭ H ⊢ KE_SIMILAR_DATA d1 d2 @ e]
      (⟬ R ⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma PRIMITIVE_RULE_collision_resistant_true :
    forall t1 t2 {eo : EventOrdering} e R H d1 d2,
      rule_true (PRIMITIVE_RULE_collision_resistant t1 t2 e R H d1 d2).
  Proof.
    start_proving_primitive st ct ht; simpl in *.
    applydup st0 in ht; clear st0; simpl in *; tcsp.
    applydup st1 in ht; clear st1; simpl in *; tcsp.
    applydup st2 in ht; clear st2; simpl in *; tcsp; ginv.
    applydup st3 in ht; clear st3; simpl in *; tcsp; ginv.
    f_equal; eapply kc_collision_resistant; eauto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_at_implies_same_node a b {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_AT b @ e,
       ⟬R⟭ H ⊢ KE_AT a @ e]
      (⟬R⟭ H ⊢ KE_NODE_EQ a b @ e).

  Lemma PRIMITIVE_RULE_at_implies_same_node_true :
    forall a b {eo : EventOrdering} e R H,
      rule_true (PRIMITIVE_RULE_at_implies_same_node a b e R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; ginv.
    applydup st1 in ht; simpl in *; tcsp.
    unfold seq_event in *; simpl in *.
    rewrite ht0 in ht1; ginv.
    apply node2name_inj in ht1; subst; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_split_local_before u v {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule1
      (fun e =>
         [⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ a,
          ⟬Q ++ (u ⋈ e1 □ e) :: (v ⋈ e ⋄ e2) :: R⟭ H ⊢ a])
      (⟬Q ++ (u ⋈ e1 □ e2) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_split_local_before_true :
    forall u v {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_split_local_before u v e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    pose proof (ct (u ⋈ e1 □ e2)) as h; simpl in *.
    allrw in_app_iff; allsimpl; autodimp h hyp.
    pose proof (local_implies_pred_or_local _ _ h) as q.
    repndors; exrepnd.

    { inst_hyp e2 st.
      apply st1; simpl; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)). }

    { assert (ex_node_e e) as exe by eauto 3 with kn.
      inst_hyp (MkEventN e exe) st.
      apply st2; simpl; tcsp.
      introv i; allrw in_app_iff; simpl in *.
      repndors; subst; tcsp; simpl;
        try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)). }
  Qed.


(*  (************************************************************************************************)
  Definition PRIMITIVE_RULE_has_ids_imply_eq_ids t {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c1 @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e).

  Lemma PRIMITIVE_RULE_has_ids_imply_eq_ids_true :
    forall t {eo : EventOrdering} e c1 c2 R H,
      rule_true (PRIMITIVE_RULE_has_ids_imply_eq_ids t e c1 c2 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp.
    applydup st1 in ht; simpl in *; tcsp.
  Qed.*)


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_after_subst c2 {eo : EventOrdering} e c1 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e,
       ⟬R⟭ H ⊢ KE_ID_AFTER c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_AFTER c1 @ e).

  Lemma PRIMITIVE_RULE_id_after_subst_true :
    forall c2 {eo : EventOrdering} e c1 R H,
      rule_true (PRIMITIVE_RULE_id_after_subst c2 e c1 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; ginv.
    applydup st1 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_eq_trans c {eo : EventOrdering} e R H c1 c2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_ID_EQ c1 c @ e,
       ⟬ R ⟭ H ⊢ KE_ID_EQ c c2 @ e]
      (⟬ R ⟭ H ⊢ KE_ID_EQ c1 c2 @ e).

  Lemma PRIMITIVE_RULE_id_eq_trans_true :
    forall c {eo : EventOrdering} e R H c1 c2,
      rule_true (PRIMITIVE_RULE_id_eq_trans c e R H c1 c2).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; ginv.
    applydup st1 in ht; simpl in *; tcsp; ginv.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_ids_after_imply_eq_ids {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_AFTER c1 @ e,
       ⟬R⟭ H ⊢ KE_ID_AFTER c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e).

  Lemma PRIMITIVE_RULE_ids_after_imply_eq_ids_true :
    forall {eo : EventOrdering} e c1 c2 R H,
      rule_true (PRIMITIVE_RULE_ids_after_imply_eq_ids e c1 c2 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp.
    applydup st1 in ht; simpl in *; tcsp.
    f_equal; unfold seq_event in *; simpl in *; eauto 3 with kn.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_lt_trans_eq_lt c {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_EQ c1 c @ e,
       ⟬R⟭ H ⊢ KE_ID_LT c c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma PRIMITIVE_RULE_id_lt_trans_eq_lt_true :
    forall c {eo : EventOrdering} e c1 c2 R H,
      rule_true (PRIMITIVE_RULE_id_lt_trans_eq_lt c e c1 c2 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; ginv.
    applydup st1 in ht; simpl in *; tcsp; subst; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_lt_trans_lt_eq c {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_LT c1 c @ e,
       ⟬R⟭ H ⊢ KE_ID_EQ c c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma PRIMITIVE_RULE_id_lt_trans_lt_eq_true :
    forall c {eo : EventOrdering} e c1 c2 R H,
      rule_true (PRIMITIVE_RULE_id_lt_trans_lt_eq c e c1 c2 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp.
    applydup st1 in ht; simpl in *; subst; ginv; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_lt_trans_lt_lt c {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_LT c1 c @ e,
       ⟬R⟭ H ⊢ KE_ID_LT c c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma PRIMITIVE_RULE_id_lt_trans_lt_lt_true :
    forall c {eo : EventOrdering} e c1 c2 R H,
      rule_true (PRIMITIVE_RULE_id_lt_trans_lt_lt c e c1 c2 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp.
    applydup st1 in ht; simpl in *; tcsp; subst; eauto 3 with kn.
  Qed.


  (* TODO: we can derive this one *)
  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_lt_trans_le_lt c {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_LE c1 c @ e,
       ⟬R⟭ H ⊢ KE_ID_LT c c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma PRIMITIVE_RULE_id_lt_trans_le_lt_true :
    forall c {eo : EventOrdering} e c1 c2 R H,
      rule_true (PRIMITIVE_RULE_id_lt_trans_le_lt c e c1 c2 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; autorewrite with kn in *.
    applydup st1 in ht; simpl in *; tcsp; repndors; subst; eauto 3 with kn.
  Qed.


  (* TODO: we can derive this one *)
  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_lt_trans_lt_le c {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_LT c1 c @ e,
       ⟬R⟭ H ⊢ KE_ID_LE c c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma PRIMITIVE_RULE_id_lt_trans_lt_le_true :
    forall c {eo : EventOrdering} e c1 c2 R H,
      rule_true (PRIMITIVE_RULE_id_lt_trans_lt_le c e c1 c2 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp.
    applydup st1 in ht; simpl in *; tcsp; repndors; ginv; subst; eauto 3 with kn.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_lt_change_event {eo : EventOrdering} e1 e2 R H t1 t2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_ID_LT t1 t2 @ e2]
      (⟬ R ⟭ H ⊢ KE_ID_LT t1 t2 @ e1).

  Lemma PRIMITIVE_RULE_id_lt_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H t1 t2,
      rule_true (PRIMITIVE_RULE_id_lt_change_event e1 e2 R H t1 t2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_all_id_intro {eo : EventOrdering} e R H f :=
    MkRule1c
      (fun c => [⟬R⟭ H ⊢ f c @ e])
      (⟬R⟭ H ⊢ KE_ALL_ID f @ e).

  Lemma PRIMITIVE_RULE_all_id_intro_true :
    forall {eo : EventOrdering} e R H f,
      rule_true (PRIMITIVE_RULE_all_id_intro e R H f).
  Proof.
    start_proving_primitive st ct ht.
    introv; unfold seq_event; simpl.
    inst_hyp c st.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_all_id_elim x c {eo : EventOrdering} e R H J f a :=
    MkRule0
      [⟬R⟭ H • (x › f c @ e) » J ⊢ a]
      (⟬R⟭ H • (x › KE_ALL_ID f @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_all_id_elim_true :
    forall x c {eo : EventOrdering} e R H J f a,
      rule_true (PRIMITIVE_RULE_all_id_elim x c e R H J f a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_ALL_ID f @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    exrepnd.
    unfold hyp_event, seq_event in *; simpl in *.
    apply st0; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
    unfold hyp_event; simpl; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_all_node_intro {eo : EventOrdering} e R H f :=
    MkRule1n
      (fun n => [⟬R⟭ H ⊢ f n @ e])
      (⟬R⟭ H ⊢ KE_ALL_NODE f @ e).

  Lemma PRIMITIVE_RULE_all_node_intro_true :
    forall {eo : EventOrdering} e R H f,
      rule_true (PRIMITIVE_RULE_all_node_intro e R H f).
  Proof.
    start_proving_primitive st ct ht.
    introv; unfold seq_event; simpl.
    inst_hyp c st.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_all_node_elim x n {eo : EventOrdering} e R H J f a :=
    MkRule0
      [⟬R⟭ H • (x › f n @ e) » J ⊢ a]
      (⟬R⟭ H • (x › KE_ALL_NODE f @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_all_node_elim_true :
    forall x n {eo : EventOrdering} e R H J f a,
      rule_true (PRIMITIVE_RULE_all_node_elim x n e R H J f a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_ALL_NODE f @ e)) as h; simpl in *.
    allrw hyp_in_adds; allrw hyp_in_add; repeat (autodimp h hyp).
    exrepnd.
    unfold hyp_event, seq_event in *; simpl in *.
    apply st0; simpl in *; tcsp.
    introv i;allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp)).
    unfold hyp_event; simpl; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_weaken_direct_pred_to_local_pred u {eo : EventOrdering} e1 e2 Q R H a :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ≡ local_pred_n e2) :: R⟭ H ⊢ a]
      (⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_weaken_direct_pred_to_local_pred_true :
    forall u {eo : EventOrdering} e1 e2 Q R H a,
      rule_true (PRIMITIVE_RULE_weaken_direct_pred_to_local_pred u e1 e2 Q R H a).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; clear st0.
    pose proof (ct (u ⋈ e1 ⋄ e2)) as w; allrw in_app_iff; simpl in *; autodimp w hyp.
    introv i; allrw in_app_iff; simpl in *; repndors; subst; simpl; tcsp;
      try (complete (apply ct; allrw in_app_iff; simpl in *; tcsp)).
    unfold local_pred; rewrite w; auto.
  Qed.


  (* TODO: primitive? *)
  (************************************************************************************************)
  Definition PRIMITIVE_RULE_split_local_before2 u v w {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬Q ++ (v ⋈ e1 ■ local_pred_n e2) :: (w ⋈ local_pred_n e2 ⋄ e2) :: (u ⋈ e1 □ e2) :: R⟭ H ⊢ a]
      (⟬Q ++ (u ⋈ e1 □ e2) :: R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_split_local_before2_true :
    forall u v w {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (PRIMITIVE_RULE_split_local_before2 u v w e1 e2 R Q H a).
  Proof.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *.
    apply st0; simpl in *; tcsp.
    introv i.
    pose proof (ct (u ⋈ e1 □ e2)) as q.
    allrw in_app_iff; simpl in *.
    autodimp q hyp.
    repndors; subst; tcsp; simpl; eauto 3 with eo;
      try (complete (apply ct; allrw in_app_iff; allsimpl; tcsp)).
    apply localHappenedBefore_implies_le_local_pred; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_lt_elim x {eo : EventOrdering} e c R H J a :=
    MkRule0
      []
      (⟬R⟭ H • (x › KE_ID_LT c c @ e) » J ⊢ a).

  Lemma PRIMITIVE_RULE_id_lt_elim_true :
    forall x {eo : EventOrdering} e c R H J a,
      rule_true (PRIMITIVE_RULE_id_lt_elim x e c R H J a).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (ht (x › KE_ID_LT c c @ e)) as ht.
    allrw hyp_in_adds; allrw hyp_in_add; autodimp ht hyp; simpl in *.
    apply kc_id_lt_arefl in ht; tcsp.
  Qed.



  (* TODO: derive that *)
  (************************************************************************************************)
  Definition PRIMITIVE_RULE_unicity c1 c2 {eo : EventOrdering} e R H t1 t2 :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e,
       ⟬R⟭ H ⊢ KE_TDISS_OWN t1 @ e,
       ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e,
       ⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e]
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma PRIMITIVE_RULE_unicity_true :
    forall c1 c2 {eo : EventOrdering} e R H t1 t2,
      rule_true (PRIMITIVE_RULE_unicity c1 c2 e R H t1 t2).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; clear st0.
    applydup st1 in ht; simpl in *; tcsp; clear st1.
    applydup st2 in ht; simpl in *; tcsp; clear st2.
    applydup st3 in ht; simpl in *; tcsp; clear st3.
    applydup st4 in ht; simpl in *; tcsp; clear st4.
    applydup st5 in ht; simpl in *; tcsp; clear st5.
    subst; ginv.
    unfold seq_event in *; simpl in *; repnd.
    allrw interpret_disseminate_unique; simpl in *.
    pose proof (ht0 t1 t2) as ht0; simpl in *.
    allrw interp_owns.
    unfold disseminate_trusted_own, disseminate_data_own in *.
    allrw data_is_owned_iff_kc_trust_is_owned.
    repeat (autodimp ht0 hyp); subst; tcsp.
    eexists; eauto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_has_id_change_event {eo : EventOrdering} e1 e2 t c R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c @ e2]
      (⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c @ e1).

  Lemma PRIMITIVE_RULE_has_id_change_event_true :
    forall {eo : EventOrdering} e1 e2 c1 c2 R H,
      rule_true (PRIMITIVE_RULE_has_id_change_event e1 e2 c1 c2 R H).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_similar_trust_preserves
             t2 i1 t1 i2 {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 i1 @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 i2 @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 i1 @ e]
      (⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 i2 @ e).

  Lemma PRIMITIVE_RULE_similar_trust_preserves_true :
    forall t2 i1 t1 i2 {eo : EventOrdering} e R H,
      rule_true (PRIMITIVE_RULE_similar_trust_preserves t2 i1 t1 i2 e R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp.
    applydup st1 in ht; simpl in *; tcsp.
    applydup st2 in ht; simpl in *; tcsp.
    applydup st3 in ht; simpl in *; tcsp.
    apply (kc_sim_trust_pres t2 t1 i1 i2); auto.
    pose proof kc_sim_trust_equiv as eqv.
    destruct eqv as [refl trans sym]; apply sym; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_trust_has_id_preserves
             a c t b {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TRUST_HAS_ID t a @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c @ e,
       ⟬R⟭ H ⊢ KE_ID_LE a b   @ e,
       ⟬R⟭ H ⊢ KE_ID_LE b c   @ e]
      (⟬R⟭ H ⊢ KE_TRUST_HAS_ID t b @ e).

  Lemma PRIMITIVE_RULE_trust_has_id_preserves_true :
    forall a c t b {eo : EventOrdering} e R H,
      rule_true (PRIMITIVE_RULE_trust_has_id_preserves a c t b e R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp.
    applydup st1 in ht; simpl in *; tcsp.
    applydup st2 in ht; simpl in *; tcsp; autorewrite with kn in *.
    applydup st3 in ht; simpl in *; tcsp; autorewrite with kn in *.
    apply (kc_trust_has_id_pres t a b c); auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_similar_trust_sym {eo : EventOrdering} e R H t1 t2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_SIMILAR_TRUST t2 t1 @ e]
      (⟬ R ⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e).

  Lemma PRIMITIVE_RULE_similar_trust_sym_true :
    forall {eo : EventOrdering} e R H t1 t2,
      rule_true (PRIMITIVE_RULE_similar_trust_sym e R H t1 t2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
    pose proof kc_sim_trust_equiv as eqv.
    destruct eqv as [refl trans sym]; apply sym; auto.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_similar_trust_change_event {eo : EventOrdering} e1 e2 R H t1 t2 :=
    MkRule0
      [⟬ R ⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e2]
      (⟬ R ⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e1).

  Lemma PRIMITIVE_RULE_similar_trust_change_event_true :
    forall {eo : EventOrdering} e1 e2 R H t1 t2,
      rule_true (PRIMITIVE_RULE_similar_trust_change_event e1 e2 R H t1 t2).
  Proof.
    start_proving_primitive st ct ht.
    apply st0 in ht; simpl in *; tcsp.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_trust_has_id_subst_id c2 {eo : EventOrdering} e t c1 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c2 @ e]
      (⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c1 @ e).

  Lemma PRIMITIVE_RULE_trust_has_id_subst_id_true :
    forall c2 {eo : EventOrdering} e t c1 R H,
      rule_true (PRIMITIVE_RULE_trust_has_id_subst_id c2 e t c1 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; ginv.
    applydup st1 in ht; simpl in *; tcsp.
  Qed.


  (* TODO: this should be derivable now *)
  (***********************************************************)
  Definition PRIMITIVE_RULE_unall_before_correct_trace_before_hyp x {eo : EventOrdering} e R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › KE_LOCAL_FORALL_BEFORE (KE_CORRECT_TRACE_BEFORE a) @ e) » J ⊢ b]
      (⟬R⟭ H • (x › KE_CORRECT_TRACE_BEFORE a @ e) » J ⊢ b).

  Lemma PRIMITIVE_RULE_unall_before_correct_trace_before_hyp_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (PRIMITIVE_RULE_unall_before_correct_trace_before_hyp x e R H J a b).
  Proof.
    start_proving_primitive st ct ht.
    apply st0; clear st0; auto;[].
    introv i; simpl in *.
    Opaque KE_LOCAL_FORALL_BEFORE.
    allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; simpl in *; tcsp;
      try (complete (apply ht; allrw hyp_in_adds; allrw hyp_in_add; tcsp));[].
    Transparent KE_LOCAL_FORALL_BEFORE.
    apply interp_KE_LOCAL_FORALL_BEFORE.
    introv lte.
    pose proof (ht (x › KE_CORRECT_TRACE_BEFORE a @ e)) as ht; simpl in *.
    autodimp ht hyp; allrw hyp_in_adds; allrw hyp_in_add; tcsp.
    unfold hyp_event in *; simpl in *.
    allrw interp_KE_CORRECT_TRACE_BEFORE.
    destruct a; tcsp; eauto 3 with eo.
    assert (loc e' = loc e) as eqloc by eauto 3 with eo.
    rewrite eqloc; eauto 3 with eo.
  Qed.


(* (* NOT NECESSARY ANYMORE *)

  (***********************************************************)
  Definition PRIMITIVE_RULE_unexists_before_hyp2 x y a b c :=
    MkRule0
      [∅ • (x › a) • (y › b) ⊢ c ]
      (∅ • (x › KE_LOCAL_BEFORE_EQ a) • (y › KE_LOCAL_FORALL_BEFORE b) ⊢ KE_LOCAL_BEFORE_EQ c).

  Lemma PRIMITIVE_RULE_unexists_before_hyp2_true :
    forall x y a b c,
      rule_true_all_eo (PRIMITIVE_RULE_unexists_before_hyp2 x y a b c).
  Proof.
    introv st exe ht; simpl in *.
    dLin_hyp ht.
    unfold sequent_true_at_event in *; simpl in *; exrepnd.
    applydup ht1 in ht0; clear ht1.
    pose proof (st e') as st; repeat (autodimp st hyp); eauto 3 with kn.
    dLin_hyp st; simpl in *.
    repeat (autodimp st0 hyp); simpl in *; tcsp; eauto 3 with kn.
    introv j; simpl in *; repndors; subst; tcsp.
  Qed.*)


(* (* NOT NECESSARY ANYMORE *)

  (***********************************************************)
  Definition PRIMITIVE_RULE_unexists_before_hyp3 x y z a b c d :=
    MkRule0
      [∅ • (x › a) • (y › b) • (z › c) ⊢ d ]
      (∅ • (x › KE_LOCAL_BEFORE_EQ a) • (y › KE_LOCAL_FORALL_BEFORE b) • (z › KE_LOCAL_FORALL_BEFORE c) ⊢ KE_LOCAL_BEFORE_EQ d).

  Lemma PRIMITIVE_RULE_unexists_before_hyp3_true :
    forall x y z a b c d,
      rule_true_all_eo (PRIMITIVE_RULE_unexists_before_hyp3 x y z a b c d).
  Proof.
    introv st exe ht; simpl in *.
    dLin_hyp ht.
    unfold sequent_true_at_event in *; simpl in *; exrepnd.
    applydup ht1 in ht0; clear ht1.
    applydup ht2 in ht0; clear ht2.
    pose proof (st e') as st; repeat (autodimp st hyp); eauto 3 with kn.
    dLin_hyp st; simpl in *.
    repeat (autodimp st0 hyp); simpl in *; tcsp; eauto 3 with kn.
    introv j; simpl in *; repndors; subst; tcsp.
  Qed.*)


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_id_eq_refl {eo : EventOrdering} e R H i :=
    MkRule0
      []
      (⟬ R ⟭ H ⊢ KE_ID_EQ i i @ e).

  Lemma PRIMITIVE_RULE_id_eq_refl_true :
    forall {eo : EventOrdering} e R H i,
      rule_true (PRIMITIVE_RULE_id_eq_refl e R H i).
  Proof.
    start_proving_primitive st ct ht; auto.
  Qed.


  (***********************************************************)
  Definition PRIMITIVE_RULE_pred_induction x {eo : EventOrdering} e R H a :=
    MkRule1
      (fun e' => [⟬(x ⋈ e' ■ e) :: R⟭ H ⊢ KE_IMPLIES KE_FIRST a @ e',
                  ⟬(x ⋈ e' ■ e) :: R⟭ H ⊢ KE_IMPLIES (KE_RIGHT_BEFORE a) a @ e'])
      (⟬R⟭ H ⊢ a @ e).

  Lemma PRIMITIVE_RULE_pred_induction_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (PRIMITIVE_RULE_pred_induction x e R H a).
  Proof.
    introv hyps; introv; simpl in *; simpl_sem_rule.

    unfold seq_event in *; simpl in *.
    destruct e as [e exn]; simpl in *.
    induction e as [e ind] using predHappenedBeforeInd_type.

    introv ct ht; simpl in *.
    destruct (dec_isFirst e) as [d|d].

    { clear ind.
      inst_hyp (MkEventN e exn) hyp.
      apply hyp; tcsp; allrw interp_KE_FIRST; tcsp.
      introv xx; simpl in *; repndors; subst; simpl in *; tcsp; eauto 3 with eo. }

    { pose proof (ind (local_pred e)) as ind.
      repeat (autodimp ind hyp); eauto 3 with eo kn;[].
      dup hyps as HS; inst_hyp (MkEventN e exn) hyp.
      applydup hyp0 in ht as w; clear hyp0 hyp; simpl in *;
        try (complete (introv xx; simpl in *; repndors; subst; simpl in *; tcsp; eauto 3 with eo));[].
      apply w; clear w.
      pose proof (implies_ex_node_e_local_pred exn) as q.
      unfold isFirst, local_pred in *.
      remember (direct_pred e) as w; symmetry in Heqw; destruct w; tcsp.
      apply (ind q); clear ind; auto; simseqs j.

      { introv ct' ht' isF; simpl in *.
        unfold seq_event in *; simpl in *.
        inst_hyp e1 st.
        apply st0; simpl in *; tcsp.
        introv xx; repndors; subst; simpl in *; tcsp.
        dLin_hyp ct'; simpl in *; eauto 4 with eo. }

      { introv ct' ht' isF; simpl in *.
        unfold seq_event in *; simpl in *.
        inst_hyp e1 st.
        apply st1; simpl in *; tcsp.
        introv xx; repndors; subst; simpl in *; tcsp.
        dLin_hyp ct'; simpl in *; eauto 4 with eo. } }
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_introduce_direct_pred u {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_NOT_FIRST @ e,
       ⟬(u ⋈ local_pred_n e ⋄ e) :: R⟭ H ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_introduce_direct_pred_true :
    forall u {eo : EventOrdering} e R H a,
      rule_true (PRIMITIVE_RULE_introduce_direct_pred u e R H a).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; clear st0.
    unfold seq_event in *; simpl in *; allrw interp_KE_FALSE.
    allrw interp_KE_NOT_FIRST.
    apply st1; simpl in *; tcsp.
    introv i; repndors; subst; simpl; tcsp; eauto 3 with eo.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_introduce_direct_pred_eq u {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_FIRST @ e,
       ⟬(u ⋈ local_pred_n e ≡ e) :: R⟭ H ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma PRIMITIVE_RULE_introduce_direct_pred_eq_true :
    forall u {eo : EventOrdering} e R H a,
      rule_true (PRIMITIVE_RULE_introduce_direct_pred_eq u e R H a).
  Proof.
    Opaque KE_FIRST.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; clear st0.
    unfold seq_event in *; simpl in *; allrw interp_KE_FIRST.
    apply st1; simpl in *; tcsp.
    introv i; repndors; subst; simpl; tcsp; eauto 3 with eo.
    unfold local_pred; rewrite ht0; auto.
    Transparent KE_FIRST.
  Qed.


  (* derived? *)
  (***********************************************************)
  Definition PRIMITIVE_RULE_first_dec {eo : EventOrdering} e R H :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_OR KE_FIRST KE_NOT_FIRST @ e).

  Lemma PRIMITIVE_RULE_first_dec_true :
    forall {eo : EventOrdering} e R H,
      rule_true (PRIMITIVE_RULE_first_dec e R H).
  Proof.
    Opaque KE_FIRST.
    start_proving_primitive st ct ht.
    unfold seq_event in *; simpl in *; allrw interp_KE_NOT_FIRST; allrw interp_KE_FIRST.
    destruct (dec_isFirst e); tcsp.
    Transparent KE_FIRST.
  Qed.


  (************************************************************************************************)
  Definition PRIMITIVE_RULE_has_init_id_unique {eo : EventOrdering} e i1 i2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_HAS_INIT_ID i1 @ e,
       ⟬R⟭ H ⊢ KE_HAS_INIT_ID i2 @ e]
      (⟬R⟭ H ⊢ KE_ID_EQ i1 i2 @ e).

  Lemma PRIMITIVE_RULE_has_init_id_unique_true :
    forall {eo : EventOrdering} e i1 i2 R H,
      rule_true (PRIMITIVE_RULE_has_init_id_unique e i1 i2 R H).
  Proof.
    start_proving_primitive st ct ht.
    applydup st0 in ht; simpl in *; tcsp; clear st0.
    applydup st1 in ht; simpl in *; tcsp; clear st1.
    unfold seq_event in *; simpl in *.
    eapply has_init_id_unique in ht0; try exact ht1; subst; auto.
    Transparent KE_FIRST.
  Qed.


  (*  ****** SIMPLE DERIVED RULES ****** *)


  (***********************************************************)
  Definition DERIVED_RULE_false_elim x {eo : EventOrdering} e e' R H J a :=
    MkRule0
      []
      (⟬R⟭ H • (x › KE_FALSE @ e') » J ⊢ a @ e).

  Lemma DERIVED_RULE_false_elim_true :
    forall x {eo : EventOrdering} e e' R H J a,
      rule_true (DERIVED_RULE_false_elim x e e' R H J a).
  Proof.
    Transparent KE_FALSE.
    start_proving_derived st.
    apply PRIMITIVE_RULE_exists_id_elim_true; simseqs j.
    apply PRIMITIVE_RULE_id_lt_elim_true; simseqs j.
    Opaque KE_FALSE.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_true {eo : EventOrdering} e R H :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_TRUE @ e).

  Lemma DERIVED_RULE_true_true :
    forall {eo : EventOrdering} e R H, rule_true (DERIVED_RULE_true e R H).
  Proof.
    Transparent KE_TRUE.
    start_proving_derived st.
    apply PRIMITIVE_RULE_all_id_intro_true; simseqs j.
    apply PRIMITIVE_RULE_id_eq_refl_true; simseqs j.
    Opaque KE_TRUE.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_node {eo : EventOrdering} e R H :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_NODE @ e).

  Lemma DERIVED_RULE_node_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_node e R H).
  Proof.
    start_proving_derived st.
    destruct (implies_ex_node e) as [n cond].
    apply (PRIMITIVE_RULE_exists_node_intro_true n); simseqs j.
    apply PRIMITIVE_RULE_at_true; simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_not_first u {eo : EventOrdering} e1 e2 Q R H :=
    MkRule0
      []
      (⟬ Q ++ (u ⋈ e1 □ e2) :: R ⟭ H ⊢ KE_NOT_FIRST @ e2).

  Lemma DERIVED_RULE_not_first_true :
    forall u {eo : EventOrdering} e1 e2 Q R H,
      rule_true (DERIVED_RULE_not_first u e1 e2 Q R H).
  Proof.
    Transparent KE_NOT_FIRST.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_split_local_before_true u "u"); simseqs j.
    { apply PRIMITIVE_RULE_unright_before_if_causal_true; simseqs j.
      apply DERIVED_RULE_true_true; simseqs j. }
    causal_norm_with "u"; apply PRIMITIVE_RULE_unright_before_if_causal_true; simseqs j.
    apply DERIVED_RULE_true_true; simseqs j.
    Opaque KE_NOT_FIRST.
  Qed.


  (*  ****** TACTICS ****** *)


  Ltac LOCKapply x :=
    let j := fresh "j" in
    apply x; simseqs j.

  Tactic Notation "LOCKapply@" constr(y) constr(x) :=
    first [norm_with y | causal_norm_with y]; LOCKapply x.

  Tactic Notation "LOCKapply@" constr(y) constr(x) constr(z) :=
    first [norm_with y | causal_norm_with y];
    first [norm_with x | causal_norm_with x];
    LOCKapply z.

  Ltac LOCKcut1 v t :=
    LOCKapply (PRIMITIVE_RULE_cut_true v t).

  Ltac LOCKcut2 v w t :=
    LOCKapply (PRIMITIVE_RULE_cut_after_true v w t).

  Tactic Notation "LOCKcut" constr(v) constr(t) := LOCKcut1 v t.
  Tactic Notation "LOCKcut" constr(v) constr(w) constr(t) := LOCKcut2 v w t.

  (* Eventually move to tactics file *)
  Ltac LOCKintro0 :=
    match goal with
    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_AND ?a ?b @ ?e)] =>
      LOCKapply PRIMITIVE_RULE_and_intro_true

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_NODE ?f @ ?e)] =>
      LOCKapply PRIMITIVE_RULE_all_node_intro_true

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_ID ?f @ ?e)] =>
      LOCKapply PRIMITIVE_RULE_all_id_intro_true

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_DATA ?f @ ?e)] =>
      LOCKapply PRIMITIVE_RULE_all_data_intro_true

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_ALL_TRUST ?f @ ?e)] =>
      LOCKapply PRIMITIVE_RULE_all_trust_intro_true

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a @ ?e)] =>
      unfold a; LOCKintro0

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ @ ?e)] =>
      unfold a; LOCKintro0

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ @ ?e)] =>
      unfold a; LOCKintro0
    end.

  Ltac LOCKintro1 x :=
    match goal with
    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_IMPLIES ?a ?b @ ?e)] =>
      LOCKapply (PRIMITIVE_RULE_implies_intro_true x)

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_OR ?a ?b @ ?e)] =>
      match x with
      | 0 => LOCKapply PRIMITIVE_RULE_or_intro_left_true
      | _ => LOCKapply PRIMITIVE_RULE_or_intro_right_true
      end

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_NODE ?f @ ?e)] =>
      LOCKapply (PRIMITIVE_RULE_exists_node_intro_true x)

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_ID ?f @ ?e)] =>
      LOCKapply (PRIMITIVE_RULE_exists_id_intro_true x)

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_DATA ?f @ ?e)] =>
      LOCKapply (PRIMITIVE_RULE_exists_data_intro_true x)

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ KE_EX_TRUST ?f @ ?e)] =>
      LOCKapply (PRIMITIVE_RULE_exists_trust_intro_true x)

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a @ ?e)] =>
      unfold a; LOCKintro1 x

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ @ ?e)] =>
      unfold a; LOCKintro1 x

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a _ _ @ ?e)] =>
      unfold a; LOCKintro1 x
    end.

  Tactic Notation "LOCKintro" := LOCKintro0.
  Tactic Notation "LOCKintro" constr(x) := LOCKintro1 x.

  Ltac LOCKelim1 v :=
    norm_with v;
    match goal with
    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_IMPLIES ?a ?b @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply PRIMITIVE_RULE_implies_elim_true

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_OR ?a ?b @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply PRIMITIVE_RULE_or_elim_true

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_NODE ?f @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply (PRIMITIVE_RULE_exists_node_elim_true v)

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_ID ?f @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply (PRIMITIVE_RULE_exists_id_elim_true v)

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_DATA ?f @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply (PRIMITIVE_RULE_exists_data_elim_true v)

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_EX_TRUST ?f @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply (PRIMITIVE_RULE_exists_trust_elim_true v)

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a @ ?e) » ?J ⊢ ?c)] =>
      unfold a; LOCKelim1 v

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ @ ?e) » ?J ⊢ ?c)] =>
      unfold a; LOCKelim1 v

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ @ ?e) » ?J ⊢ ?c)] =>
      unfold a; LOCKelim1 v
    end.

  Ltac LOCKelim2 v w :=
    norm_with v;
    match goal with
    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_AND ?a ?b @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply (PRIMITIVE_RULE_and_elim_true v w)

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_NODE ?f @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply (PRIMITIVE_RULE_all_node_elim_true v w)

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_ID ?f @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply (PRIMITIVE_RULE_all_id_elim_true v w)

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_DATA ?f @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply (PRIMITIVE_RULE_all_data_elim_true v w)

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › KE_ALL_TRUST ?f @ ?e) » ?J ⊢ ?c)] =>
      LOCKapply (PRIMITIVE_RULE_all_trust_elim_true v w)

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a @ ?e) » ?J ⊢ ?c)] =>
      unfold a; LOCKelim2 v w

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ @ ?e) » ?J ⊢ ?c)] =>
      unfold a; LOCKelim2 v w

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ @ ?e) » ?J ⊢ ?c)] =>
      unfold a; LOCKelim2 v w

    | [ |- sequent_true (⟬ ?R ⟭ (?H • v › ?a _ _ _ @ ?e) » ?J ⊢ ?c)] =>
      unfold a; LOCKelim2 v w
    end.

  Tactic Notation "LOCKelim" constr(x) := LOCKelim1 x.
  Tactic Notation "LOCKelim" constr(x) constr(y) := LOCKelim2 x y.

  Ltac LOCKauto :=
    match goal with
    | [ |- sequent_true (⟬ _ ⟭ _ ⊢ KE_NODE @ ?e)] =>
      LOCKapply DERIVED_RULE_node_true

    | [ |- sequent_true (⟬ _ ⟭ _ ⊢ KE_AT _ @ ?e)] =>
      LOCKapply PRIMITIVE_RULE_at_true

    | [ |- sequent_true (⟬ _ ⟭ _ ⊢ KE_TRUE @ ?e)] =>
      LOCKapply DERIVED_RULE_true_true

    | [ |- sequent_true (⟬ _ ⟭ _ ⊢ KE_OR KE_FIRST KE_NOT_FIRST @ ?e)] =>
      LOCKapply PRIMITIVE_RULE_first_dec_true

    | [ |- sequent_true (⟬ ?R ⟭ ?H ⊢ ?a) ] =>
      match H with
      | context[?v › ?a] =>
        norm_with v; LOCKapply PRIMITIVE_RULE_hypothesis_true

      | context[?v › KE_FALSE @ ?e] =>
        norm_with v; LOCKapply DERIVED_RULE_false_elim_true

      | context[?v › KE_ID_LT ?i ?i @ ?e] =>
        norm_with v; LOCKapply PRIMITIVE_RULE_id_lt_elim_true
      end
    end.

  Ltac LOCKclearH :=
    match goal with
    | [ |- sequent_true (⟬ ?R ⟭ (?H • (?v › _ @ _)) ⊢ _)] =>
      norm_with v; LOCKapply PRIMITIVE_RULE_thin_true
    end.

  Ltac LOCKclearH_at x :=
    norm_with x;
    match goal with
    | [ |- sequent_true (⟬ ?R ⟭ ?H • (x › ?a) » ?J ⊢ _)] =>
      norm_with x; LOCKapply PRIMITIVE_RULE_thin_true
    end.

  Ltac LOCKclearG_at x :=
    causal_norm_with x;
    match goal with
    | [ |- sequent_true (⟬ ?R ++ (x ⋈ ?c) :: ?Q ⟭ _ ⊢ _)] =>
      causal_norm_with x; LOCKapply PRIMITIVE_RULE_remove_causal_true
    end.

  Tactic Notation "LOCKclear" := LOCKclearH.
  Tactic Notation "LOCKclear" constr(x) := first [LOCKclearG_at x | LOCKclearH_at x].
  Tactic Notation "LOCKclear" constr(x1) constr(x2) :=
    first [LOCKclearG_at x1 | LOCKclearH_at x1];
    first [LOCKclearG_at x2 | LOCKclearH_at x2].
  Tactic Notation "LOCKclear" constr(x1) constr(x2) constr(x3) :=
    first [LOCKclearG_at x1 | LOCKclearH_at x1];
    first [LOCKclearG_at x2 | LOCKclearH_at x2];
    first [LOCKclearG_at x3 | LOCKclearH_at x3].
  Tactic Notation "LOCKclear" constr(x1) constr(x2) constr(x3) constr(x4) :=
    first [LOCKclearG_at x1 | LOCKclearH_at x1];
    first [LOCKclearG_at x2 | LOCKclearH_at x2];
    first [LOCKclearG_at x3 | LOCKclearH_at x3];
    first [LOCKclearG_at x4 | LOCKclearH_at x4].
  Tactic Notation "LOCKclear" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) :=
    first [LOCKclearG_at x1 | LOCKclearH_at x1];
    first [LOCKclearG_at x2 | LOCKclearH_at x2];
    first [LOCKclearG_at x3 | LOCKclearH_at x3];
    first [LOCKclearG_at x4 | LOCKclearH_at x4];
    first [LOCKclearG_at x5 | LOCKclearH_at x5].


  (*  ****** DERIVED RULES ****** *)


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_forall_before_hyp u x {eo : EventOrdering} e' e Q R H J a b :=
    MkRule0
      [⟬Q ++ (u ⋈ e' □ e) :: R⟭ H • (x › a @ e') » J ⊢ b]
      (⟬Q ++ (u ⋈ e' □ e) :: R⟭ H • (x › KE_LOCAL_FORALL_BEFORE a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unlocal_forall_before_hyp_true :
    forall u x {eo : EventOrdering} e' e Q R H J a b,
      rule_true (DERIVED_RULE_unlocal_forall_before_hyp u x e' e Q R H J a b).
  Proof.
    start_proving_derived st.
    LOCKelim x.
    LOCKelim x "x".
    LOCKapply@ u (PRIMITIVE_RULE_duplicate_guard_true u "u").
    LOCKapply@ "u" PRIMITIVE_RULE_local_if_causal_true.
    LOCKapply@ "u" x PRIMITIVE_RULE_forall_before_elim_true.
    LOCKelim x.
    { LOCKapply@ u PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ u PRIMITIVE_RULE_at_change_localle_fwd_true; try LOCKauto. }
    LOCKclear "x".
    LOCKclear "u".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owns_implies_local x t {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ▷ e2) :: Q⟭ H ⊢ KE_OWNS t @ e1,
       ⟬R ++ (x ⋈ e1 ▷ e2) :: Q⟭ H ⊢ KE_OWNS t @ e2,
       ⟬R ++ (x ⋈ e1 □ e2) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e1 ▷ e2) :: Q⟭ H ⊢ a).

  Lemma DERIVED_RULE_owns_implies_local_true :
    forall x t {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_owns_implies_local x t e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "o1" (KE_OWNS t @ e1).
    LOCKcut "o2" (KE_OWNS t @ e2).
    { LOCKclear "o1". }
    Transparent KE_OWNS.
    LOCKelim "o1".
    LOCKelim "o2".
    Opaque KE_OWNS.
    LOCKelim "o1" "o1'".
    LOCKelim "o2" "o2'".
    LOCKcut "eq" (KE_NODE_EQ n n0 @ e2).
    { LOCKapply (PRIMITIVE_RULE_has_owner_implies_eq_true t); try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_has_owner_change_event_true e2 e1); try LOCKauto. }
    LOCKapply@ x (PRIMITIVE_RULE_at_implies_local_true x n); try LOCKauto.
    { LOCKapply (PRIMITIVE_RULE_subst_node_in_at_true n0); try LOCKauto.
      LOCKapply PRIMITIVE_RULE_node_eq_sym_true; try LOCKauto. }
    LOCKclear "o1" "o1'" "o2" "o2'" "eq".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owns_implies_localle x t {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ▶ e2) :: Q⟭ H ⊢ KE_OWNS t @ e1,
       ⟬R ++ (x ⋈ e1 ▶ e2) :: Q⟭ H ⊢ KE_OWNS t @ e2,
       ⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ a]
      (⟬R ++ (x ⋈ e1 ▶ e2) :: Q⟭ H ⊢ a).

  Lemma DERIVED_RULE_owns_implies_localle_true :
    forall x t {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_owns_implies_localle x t e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "o1" (KE_OWNS t @ e1).
    LOCKcut "o2" (KE_OWNS t @ e2).
    { LOCKclear "o1". }
    Transparent KE_OWNS.
    LOCKelim "o1".
    LOCKelim "o2".
    Opaque KE_OWNS.
    LOCKelim "o1" "o1'".
    LOCKelim "o2" "o2'".
    LOCKcut "eq" (KE_NODE_EQ n n0 @ e2).
    { LOCKapply (PRIMITIVE_RULE_has_owner_implies_eq_true t); try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_has_owner_change_event_true e2 e1); try LOCKauto. }
    LOCKapply@ x (PRIMITIVE_RULE_at_implies_localle_true x n); try LOCKauto.
    { LOCKapply (PRIMITIVE_RULE_subst_node_in_at_true n0); try LOCKauto.
      LOCKapply PRIMITIVE_RULE_node_eq_sym_true; try LOCKauto. }
    LOCKclear "o1" "o1'" "o2" "o2'" "eq".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_hyp u x {eo : EventOrdering} e R H J a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' □ e) :: R⟭ H • (x › a @ e') » J ⊢ b])
      (⟬R⟭ H • (x › KE_LOCAL_BEFORE a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unlocal_before_hyp_true :
    forall u x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unlocal_before_hyp u x e R H J a b).
  Proof.
    start_proving_derived st.
    LOCKelim x.
    LOCKelim x "x".
    LOCKapply@ x (PRIMITIVE_RULE_unhappened_before_hyp_true u).
    LOCKelim x "y".
    inst_hyp e0 hyp.
    LOCKapply@ u (PRIMITIVE_RULE_at_implies_local_true u n); try LOCKauto.
    LOCKclear "x" "y".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_if_causal x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE a @ e).

  Lemma DERIVED_RULE_unlocal_before_if_causal_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_if_causal x e' e R Q H a).
  Proof.
    start_proving_derived st.
    destruct (implies_ex_node e) as [n cond].
    LOCKintro n.
    LOCKintro; try LOCKauto.
    LOCKapply@ x (PRIMITIVE_RULE_duplicate_guard_true x "u").
    LOCKapply@ "u" PRIMITIVE_RULE_local_if_causal_true.
    LOCKapply@ "u" PRIMITIVE_RULE_unhappened_before_if_causal_true.
    LOCKintro.
    { LOCKapply@ x PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ x PRIMITIVE_RULE_at_change_localle_fwd_true; try LOCKauto. }
    LOCKapply@ "u" PRIMITIVE_RULE_remove_causal_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_if_local_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE a @ e).

  Lemma DERIVED_RULE_unlocal_before_if_causal_local_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_if_local_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_LOCAL_BEFORE a @ e').
    LOCKelim "x".
    LOCKintro n.
    LOCKelim "x" "y".
    LOCKintro.
    { LOCKapply@ x PRIMITIVE_RULE_local_if_localle_true.
      LOCKapply@ x PRIMITIVE_RULE_at_change_localle_true; try LOCKauto. }
    LOCKapply@ "x" (PRIMITIVE_RULE_unhappened_before_hyp_true "u").
    LOCKapply@ x (PRIMITIVE_RULE_duplicate_guard_true x "v").
    LOCKapply@ "v" PRIMITIVE_RULE_local_if_causal_true.
    LOCKapply@ "v" PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq_true.
    LOCKapply@ "u" PRIMITIVE_RULE_unhappened_before_if_causal_true; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knew_before_implies_knows
             {eo : EventOrdering} (e : EventN) R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_KNEW i @ e]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE (KE_KNOWS i) @ e).

  Lemma DERIVED_RULE_knew_before_implies_knows_true :
    forall {eo : EventOrdering} (e : EventN) R H (i : kc_data),
      rule_true (DERIVED_RULE_knew_before_implies_knows e R H i).
  Proof.
    start_proving_derived st; auto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knows_before_implies_knew
             {eo : EventOrdering} (e : EventN) R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE (KE_KNOWS i) @ e]
      (⟬R⟭ H ⊢ KE_KNEW i @ e).

  Lemma DERIVED_RULE_knows_before_implies_knew_true :
    forall {eo : EventOrdering} (e : EventN) R H (i : kc_data),
      rule_true (DERIVED_RULE_knows_before_implies_knew e R H i).
  Proof.
    start_proving_derived st; auto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knew_implies_knows
             {eo : EventOrdering} (e : EventN) R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_KNEW i @ e]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_KNOWS i) @ e).

  Lemma DERIVED_RULE_knew_implies_knows_true :
    forall {eo : EventOrdering} (e : EventN) R H (i : kc_data),
      rule_true (DERIVED_RULE_knew_implies_knows e R H i).
  Proof.
    start_proving_derived st.
    LOCKintro 0.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_knew_implies_knows {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TKNEW t @ e]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_TKNOWS t) @ e).

  Lemma DERIVED_RULE_trusted_knew_implies_knows_true :
    forall {eo : EventOrdering} (e : EventN) R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_knew_implies_knows e R H t).
  Proof.
    introv; apply DERIVED_RULE_knew_implies_knows_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_revert x {eo : EventOrdering} e R H c J (a : KExpression) :=
    MkRule0
      [⟬R⟭ H » J ⊢ KE_IMPLIES c a @ e]
      (⟬R⟭ H • (x › c @ e) » J ⊢ a @ e).

  Lemma DERIVED_RULE_revert_true :
    forall x {eo : EventOrdering} (e : EventN) R H c J a,
      rule_true (DERIVED_RULE_revert x e R H c J a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" x (KE_IMPLIES c a @ e).
    { LOCKclear x. }
    LOCKelim "x"; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_revert_last {eo : EventOrdering} e R H x a (b : KExpression) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_IMPLIES a b @ e]
      (⟬R⟭ H • (x › a @ e) ⊢ b @ e).

  Lemma DERIVED_RULE_revert_last_true :
    forall {eo : EventOrdering} (e : EventN) R H x a b,
      rule_true (DERIVED_RULE_revert_last e R H x a b).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_IMPLIES a b @ e); try complete LOCKclear.
    LOCKelim "x"; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_thin_last {eo : EventOrdering} R H h a :=
    MkRule0
      [⟬R⟭ H ⊢ a]
      (⟬R⟭ H • h ⊢ a).

  Lemma DERIVED_RULE_thin_last_true :
    forall {eo : EventOrdering} R H h a,
      rule_true (DERIVED_RULE_thin_last R H h a).
  Proof.
    start_proving_derived st.
    destruct h as [x h]; LOCKapply@ x PRIMITIVE_RULE_thin_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_implies_elim x {eo : EventOrdering} e R H a b c :=
    MkRule0
      [⟬R⟭ H ⊢ a @ e,
       ⟬R⟭ H • (x › b @ e) ⊢ c]
      (⟬R⟭ H • (x › KE_IMPLIES a b @ e) ⊢ c).

  Lemma DERIVED_RULE_implies_elim_true :
    forall x {eo : EventOrdering} e R H a b c,
      rule_true (DERIVED_RULE_implies_elim x e R H a b c).
  Proof.
    start_proving_derived st.
    LOCKelim x.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_or_elim x {eo : EventOrdering} e R H A B c :=
    MkRule0
      [⟬R⟭ H • (x › A @ e) ⊢ c,
       ⟬R⟭ H • (x › B @ e) ⊢ c]
      (⟬R⟭ H • (x › KE_OR A B @ e) ⊢ c).

  Lemma DERIVED_RULE_or_elim_true :
    forall x {eo : EventOrdering} e R H A B c,
      rule_true (DERIVED_RULE_or_elim x e R H A B c).
  Proof.
    start_proving_derived st.
    LOCKelim x.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_and_elim x y {eo : EventOrdering} e R H A B c :=
    MkRule0
      [⟬R⟭ H • (x › B @ e) • (y › A @ e) ⊢ c]
      (⟬R⟭ H • (x › KE_AND A B @ e) ⊢ c).

  Lemma DERIVED_RULE_and_elim_true :
    forall x y {eo : EventOrdering} e R H A B c,
      rule_true (DERIVED_RULE_and_elim x y e R H A B c).
  Proof.
    start_proving_derived st.
    LOCKelim x y.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_hypothesis_last {eo : EventOrdering} R H x a :=
    MkRule0
      []
      (⟬R⟭ H • (x › a) ⊢ a).

  Lemma DERIVED_RULE_hypothesis_last_true :
    forall {eo : EventOrdering} R H x a,
      rule_true (DERIVED_RULE_hypothesis_last R H x a).
  Proof.
    start_proving_derived st; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_implies_not_first a {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE a @ e]
      (⟬R⟭ H ⊢ KE_NOT_FIRST @ e).

  Lemma DERIVED_RULE_right_before_implies_not_first_true :
    forall a {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_right_before_implies_not_first a e R H).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_RIGHT_BEFORE a @ e).
    LOCKapply@ "x" (PRIMITIVE_RULE_unright_before_hyp_if_causal_true "u").
    LOCKapply@ "u" PRIMITIVE_RULE_direct_pred_if_local_pred_true.
    LOCKapply@ "u" DERIVED_RULE_not_first_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knew_implies_not_first c {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_KNEW c @ e]
      (⟬R⟭ H ⊢ KE_NOT_FIRST @ e).

  Lemma DERIVED_RULE_knew_implies_not_first_true :
    forall c {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_knew_implies_not_first c e R H).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_KNEW c @ e).
    LOCKcut "y" (KE_RIGHT_BEFORE (KE_KNOWS c) @ e).
    { LOCKapply DERIVED_RULE_knew_before_implies_knows_true; try LOCKauto. }
    LOCKapply (DERIVED_RULE_right_before_implies_not_first_true (KE_KNOWS c)); try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_first_implies_at_local_pred {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ e,
       ⟬R⟭ H ⊢ KE_FIRST @ e]
      (⟬R⟭ H ⊢ a @ local_pred_n e).

  Lemma DERIVED_RULE_first_implies_at_local_pred_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_first_implies_at_local_pred e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_eq_true "u" e).
    LOCKapply@ "u" PRIMITIVE_RULE_causal_eq_sym_true.
    LOCKapply@ "u" PRIMITIVE_RULE_subst_causal_eq_concl_true.
    LOCKclear "u".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_at_local_pred_first_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ local_pred_n e,
       ⟬R⟭ H ⊢ KE_FIRST @ e]
      (⟬R⟭ H ⊢ a @ e).

  Lemma DERIVED_RULE_at_local_pred_first_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_at_local_pred_first_implies e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_eq_true "u" e).
    LOCKapply@ "u" PRIMITIVE_RULE_subst_causal_eq_concl_true.
    LOCKclear "u".
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_add_local_pred_localle x {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬(x ⋈ local_pred_n e ■ e) :: R⟭ H ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma DERIVED_RULE_add_local_pred_localle_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_add_local_pred_localle x e R H a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_OR KE_FIRST KE_NOT_FIRST @ e); try LOCKauto.
    LOCKelim "x".
    { LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_eq_true x e); try LOCKauto.
      LOCKclear.
      causal_norm_with x; LOCKapply PRIMITIVE_RULE_localle_if_eq_true. }
    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_true x e); try LOCKauto.
    LOCKapply@ "x" (PRIMITIVE_RULE_thin_true "x").
    LOCKapply@ x PRIMITIVE_RULE_direct_pred_if_local_pred_true.
    LOCKapply@ x PRIMITIVE_RULE_local_if_localle_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_add_local_pred_local x {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬(x ⋈ local_pred_n e □ e) :: R⟭ H ⊢ a,
       ⟬R⟭ H ⊢ KE_NOT_FIRST @ e]
      (⟬R⟭ H ⊢ a).

  Lemma DERIVED_RULE_add_local_pred_local_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_add_local_pred_local x e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_introduce_direct_pred_true x e).
    LOCKapply@ x PRIMITIVE_RULE_direct_pred_if_local_pred_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unright_before_eq_hyp x {eo : EventOrdering} e R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › a @ local_pred_n e) » J ⊢ b]
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unright_before_eq_hyp_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unright_before_eq_hyp x e R H J a b).
  Proof.
    start_proving_derived st.
    LOCKcut "x" x (a @ local_pred_n e).
    { LOCKelim x.
      { LOCKapply PRIMITIVE_RULE_unright_before_hyp_true; try LOCKauto. }
      LOCKelim x "y".
      LOCKapply DERIVED_RULE_first_implies_at_local_pred_true; try LOCKauto. }
    LOCKclear x.
    LOCKapply@ "x"(PRIMITIVE_RULE_rename_hyp_true "x" x).
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_add_localle_refl x {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬(x ⋈ e ■ e) :: R⟭ H ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma DERIVED_RULE_add_localle_refl_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_add_localle_refl x e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_add_eq_refl_true x e).
    LOCKapply@ x PRIMITIVE_RULE_localle_if_eq_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_hyp u x {eo : EventOrdering} e R H J a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ■ e) :: R⟭ H • (x › a @ e') » J ⊢ b])
      (⟬R⟭ H • (x › KE_LOCAL_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unlocal_before_eq_hyp_true :
    forall u x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unlocal_before_eq_hyp u x e R H J a b).
  Proof.
    start_proving_derived st.
    LOCKelim x.

    { LOCKapply (DERIVED_RULE_unlocal_before_hyp_true u).
      LOCKapply@ u PRIMITIVE_RULE_local_if_localle_true.
      inst_hyp e0 st. }

    { LOCKelim x "x".
      LOCKclear x.
      LOCKapply@ "x"(PRIMITIVE_RULE_rename_hyp_true "x" x).
      LOCKapply (DERIVED_RULE_add_localle_refl_true u e).
      inst_hyp e st. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_eq_hyp u x {eo : EventOrdering} e R H J a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ▶ e) :: R⟭ H • (x › a @ e') » J ⊢ b])
      (⟬R⟭ H • (x › KE_HAPPENED_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unhappened_before_eq_hyp_true :
    forall u x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unhappened_before_eq_hyp u x e R H J a b).
  Proof.
    start_proving_derived st.
    LOCKelim x.

    { LOCKapply (PRIMITIVE_RULE_unhappened_before_hyp_true u).
      LOCKapply@ u PRIMITIVE_RULE_causal_if_causalle_true.
      inst_hyp e0 st. }

    { LOCKapply (DERIVED_RULE_add_localle_refl_true u e).
      LOCKapply@ u (PRIMITIVE_RULE_localle_if_causalle_true u).
      LOCKelim x "y".
      LOCKclear x.
      LOCKapply@ "y"(PRIMITIVE_RULE_rename_hyp_true "y" x).
      inst_hyp e st. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_remove_first_causal {eo : EventOrdering} c R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a]
      (⟬c :: R⟭ H ⊢ a).

  Lemma DERIVED_RULE_remove_first_causal_true :
    forall {eo : EventOrdering} c R H a,
      rule_true (DERIVED_RULE_remove_first_causal c R H a).
  Proof.
    start_proving_derived st.
    destruct c as [n r].
    LOCKclear n.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_causalle x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_causalle_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_causalle x e' e R Q H a).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_duplicate_guard_true x "u").
    LOCKapply PRIMITIVE_RULE_split_local_before_eq2_true.
    { LOCKintro 1.
      LOCKapply PRIMITIVE_RULE_subst_causal_eq_concl_true.
      LOCKapply@ "u" PRIMITIVE_RULE_remove_causal_true.
      LOCKintro; try LOCKauto. }
    { LOCKintro 0.
      LOCKapply@ "u" DERIVED_RULE_unlocal_before_if_causal_true.
      LOCKapply@ "u" PRIMITIVE_RULE_remove_causal_true. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_causal x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_causal_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_causal x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
    apply DERIVED_RULE_unlocal_before_if_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_causal_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_causal_trans_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_causal_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_LOCAL_BEFORE_EQ a @ e').
    LOCKapply (PRIMITIVE_RULE_duplicate_guard_true x "u").
    LOCKapply PRIMITIVE_RULE_split_local_before_eq2_true.

    { LOCKapply PRIMITIVE_RULE_subst_causal_eq_concl_true; try LOCKauto. }

    LOCKelim "x".

    { LOCKintro 0.
      LOCKapply DERIVED_RULE_unlocal_before_if_causal_local_true; try LOCKauto. }

    LOCKapply DERIVED_RULE_unlocal_before_eq_if_causal_true.
    LOCKapply@ "u" PRIMITIVE_RULE_remove_causal_true; try LOCKauto.
    LOCKelim "x" "y"; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_if_causal_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE a @ e).

  Lemma DERIVED_RULE_unlocal_before_if_causal_trans_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_if_causal_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE_EQ a @ e')); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.

    { apply DERIVED_RULE_unlocal_before_if_causal_local_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    apply DERIVED_RULE_unlocal_before_if_causal_true; simseqs j.
    LOCKelim "x" "y".
    norm_with "y"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (* DISCUSS *)
  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_if_causalle_trans_eq x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e']
      (⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma DERIVED_RULE_unhappened_before_if_causalle_trans_eq_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unhappened_before_if_causalle_trans_eq x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE a @ e')); simseqs j.
    apply (PRIMITIVE_RULE_duplicate_guard_true x "u"); simseqs j.

    causal_norm_with "u"; apply PRIMITIVE_RULE_split_happened_before_eq2_true; simseqs j.
    { causal_norm_with "u"; apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    causal_norm_with "u"; apply PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq_true; simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_if_causal_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' ▷ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma DERIVED_RULE_unhappened_before_if_causal_trans_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unhappened_before_if_causal_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE_EQ a @ e')); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.

    { apply PRIMITIVE_RULE_unhappened_before_if_causal_trans_eq_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    apply PRIMITIVE_RULE_unhappened_before_if_causal_true; simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    norm_with "c"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_eq_if_causalle x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unhappened_before_eq_if_causalle_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unhappened_before_eq_if_causalle x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (a @ e')); simseqs j.
    apply (PRIMITIVE_RULE_duplicate_guard_true x "u"); simseqs j.

    apply PRIMITIVE_RULE_split_happened_before_eq2_true; simseqs j.
    { apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_and_intro_true; simseqs j.
      { norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
      apply DERIVED_RULE_node_true; simseqs j. }

    apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
    apply PRIMITIVE_RULE_unhappened_before_if_causal_true; simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_eq_if_causalle_trans x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' ▶ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unhappened_before_eq_if_causalle_trans x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE_EQ a @ e')); simseqs j.
    apply (PRIMITIVE_RULE_duplicate_guard_true x "u"); simseqs j.
    apply PRIMITIVE_RULE_split_happened_before_eq2_true; simseqs j.

    { apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
    apply DERIVED_RULE_unhappened_before_if_causal_trans_true; simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_add_happenedle_refl x {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬(x ⋈ e ▶ e) :: R⟭ H ⊢ a]
      (⟬R⟭ H ⊢ a).

  Lemma DERIVED_RULE_add_happenedle_refl_true :
    forall x {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_add_happenedle_refl x e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_localle_refl_true x e); simseqs j.
    apply add_nil2guards.
    apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_weaken_local_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_weaken_local_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_weaken_local_before_eq e R H a).
  Proof.
    start_proving_derived st.
    LOCKapply PRIMITIVE_RULE_or_intro_right_true.
    LOCKintro; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_pred {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ (local_pred_n e)]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_pred_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_pred e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_local_pred_localle_true "x" e); simseqs j.
    causal_norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_if_causalle_true "x"); simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_causal_lt x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ a @ e']
      (⟬R ++ (x ⋈ e' □ e) :: Q⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_causal_lt_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_causal_lt x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (a @ e')); simseqs j.
    apply PRIMITIVE_RULE_local_if_localle_true; simseqs j.
    apply DERIVED_RULE_unlocal_before_eq_if_causalle_true; simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_if_pred {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ (local_pred_n e)]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_if_pred_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_if_pred e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_local_pred_localle_true "v" e); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_unlocal_before_eq_if_causal_trans_true "v"); simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unhappened_before_eq_if_pred {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ (local_pred_n e)]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unhappened_before_eq_if_pred_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unhappened_before_eq_if_pred e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_local_pred_localle_true "v" e); simseqs j.
    causal_norm_with "v"; apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    causal_norm_with "v"; apply DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true; simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unright_before {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ local_pred_n e,
       ⟬R⟭ H ⊢ KE_NOT_FIRST @ e]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE a @ e).

  Lemma DERIVED_RULE_unright_before_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unright_before e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e); simseqs j.
    causal_norm_with "u"; apply PRIMITIVE_RULE_unright_before_if_causal_true; simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unright_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ (local_pred_n e)]
      (⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unright_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unright_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_OR KE_FIRST KE_NOT_FIRST @ e)); simseqs j.
    { apply PRIMITIVE_RULE_first_dec_true; simseqs j. }
    apply (DERIVED_RULE_or_elim_true "x"); simseqs j.
    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_and_intro_true; simseqs j.
      { apply DERIVED_RULE_at_local_pred_first_implies_true; simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j. }
        apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
    apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
    apply DERIVED_RULE_unright_before_true; simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j. }
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_before_implies_happened_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE a @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_before_implies_happened_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_before_implies_happened_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE a @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_hyp_true "u" "x"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_local_if_causal_true); simseqs j.
    causal_norm_with "u"; apply PRIMITIVE_RULE_causal_if_causalle_true; simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "u"); simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_implies {eo : EventOrdering} e R H a b :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_IMPLIES a b) @ e]
      (⟬R⟭ H ⊢ KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e).

  Lemma DERIVED_RULE_right_before_over_implies_true :
    forall {eo : EventOrdering} e R H a b,
      rule_true (DERIVED_RULE_right_before_over_implies e R H a b).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_IMPLIES a b) @ e)).
    LOCKintro "y".
    LOCKapply@ "x" DERIVED_RULE_unright_before_eq_hyp_true.
    LOCKapply@ "y" DERIVED_RULE_unright_before_eq_hyp_true.
    LOCKapply DERIVED_RULE_unright_before_eq_true.
    LOCKapply@ "x" PRIMITIVE_RULE_implies_elim_true; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_forall_before_eq_hyp u x {eo : EventOrdering} e' e Q R H J a b :=
    MkRule0
      [⟬Q ++ (u ⋈ e' ■ e) :: R⟭ H • (x › a @ e') » J ⊢ b]
      (⟬Q ++ (u ⋈ e' ■ e) :: R⟭ H • (x › KE_LOCAL_FORALL_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unlocal_forall_before_eq_hyp_true :
    forall u x {eo : EventOrdering} e' e Q R H J a b,
      rule_true (DERIVED_RULE_unlocal_forall_before_eq_hyp u x e' e Q R H J a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_duplicate_guard_true u "v"); simseqs j.
    causal_norm_with "v"; apply PRIMITIVE_RULE_split_local_before_eq2_true; simseqs j.
    { apply PRIMITIVE_RULE_causal_eq_sym_true; simseqs j.
      apply PRIMITIVE_RULE_subst_causal_eq_hyp_true; simseqs j.
      apply (PRIMITIVE_RULE_and_elim_true x "y"); simseqs j.
      norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j.
      causal_norm_with "v"; apply PRIMITIVE_RULE_remove_causal_true; simseqs j. }
    apply (PRIMITIVE_RULE_and_elim_true x "y"); simseqs j.
    causal_norm_with "v"; norm_with "y"; apply (DERIVED_RULE_unlocal_forall_before_hyp_true "v" "y"); simseqs j.
    norm_with x; apply (PRIMITIVE_RULE_thin_true x); simseqs j.
    norm_with "y"; apply (PRIMITIVE_RULE_rename_hyp_true "y" x); simseqs j.
    causal_norm_with "v"; apply PRIMITIVE_RULE_remove_causal_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_happened_before_over_implies {eo : EventOrdering} e R H a b :=
    MkRule0
      [⟬R⟭ H ⊢ KE_FORALL_BEFORE (KE_IMPLIES a b) @ e]
      (⟬R⟭ H ⊢ KE_IMPLIES (KE_HAPPENED_BEFORE a) (KE_HAPPENED_BEFORE b) @ e).

  Lemma DERIVED_RULE_happened_before_over_implies_true :
    forall {eo : EventOrdering} e R H a b,
      rule_true (DERIVED_RULE_happened_before_over_implies e R H a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_FORALL_BEFORE (KE_IMPLIES a b) @ e)); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    norm_with "y"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "u" "y"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true "u" e0); simseqs j.
    causal_norm_with "u"; norm_with "x"; apply (PRIMITIVE_RULE_forall_before_elim_true "u" "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { norm_with "y"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (* NOTE: We don't need [KE_FORALL_BEFORE] as in [DERIVED_RULE_happened_before_over_implies] *)
  (***********************************************************)
  Definition DERIVED_RULE_happened_before_over_implies2 u {eo : EventOrdering} e R H a b :=
    MkRule1
      (fun e' => [⟬(u ⋈ e' ▷ e) :: R⟭ H ⊢ KE_IMPLIES a b @ e'])
      (⟬R⟭ H ⊢ KE_IMPLIES (KE_HAPPENED_BEFORE a) (KE_HAPPENED_BEFORE b) @ e).

  Lemma DERIVED_RULE_happened_before_over_implies2_true :
    forall u {eo : EventOrdering} e R H a b,
      rule_true (DERIVED_RULE_happened_before_over_implies2 u e R H a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    norm_with "y"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true u "y"); simseqs j.
    causal_norm_with u; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true u e0); simseqs j.
    inst_hyp e0 st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_IMPLIES a b @ e0)); simseqs j.
    { norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j. }
    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { norm_with "y"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_or {eo : EventOrdering} e R H a b :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_OR a b) @ e]
      (⟬R⟭ H ⊢ KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e).

  Lemma DERIVED_RULE_right_before_over_or_true :
    forall {eo : EventOrdering} e R H a b,
      rule_true (DERIVED_RULE_right_before_over_or e R H a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_OR a b) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unright_before_eq_hyp_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.
    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply DERIVED_RULE_unright_before_eq_true; simseqs j.
      norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
    apply DERIVED_RULE_unright_before_eq_true; simseqs j.
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_implies_seq x {eo : EventOrdering} e R H J a b :=
    MkRule0
      []
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ (KE_IMPLIES a b) @ e) » J ⊢ KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e).

  Lemma DERIVED_RULE_right_before_over_implies_seq_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_right_before_over_implies_seq x e R H J a b).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_right_before_over_implies_true; simseqs j.
    apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_or_seq x {eo : EventOrdering} e R H J a b :=
    MkRule0
      []
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ (KE_OR a b) @ e) » J ⊢ KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e).

  Lemma DERIVED_RULE_right_before_over_or_seq_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_right_before_over_or_seq x e R H J a b).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_right_before_over_or_true; simseqs j.
    apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_implies_hyp x {eo : EventOrdering} e R H J a b c :=
    MkRule0
      [⟬R⟭ H • (x › KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e) » J ⊢ c]
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ (KE_IMPLIES a b) @ e) » J ⊢ c).

  Lemma DERIVED_RULE_right_before_over_implies_hyp_true :
    forall x {eo : EventOrdering} e R H J a b c,
      rule_true (DERIVED_RULE_right_before_over_implies_hyp x e R H J a b c).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_after_true "z" x (KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e)); simseqs j.
    { apply DERIVED_RULE_right_before_over_implies_seq_true; simseqs j. }
    norm_with x; apply (PRIMITIVE_RULE_thin_true x); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_rename_hyp_true "z" x); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_over_or_hyp x {eo : EventOrdering} e R H J a b c :=
    MkRule0
      [⟬R⟭ H • (x › KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e) » J ⊢ c]
      (⟬R⟭ H • (x › KE_RIGHT_BEFORE_EQ (KE_OR a b) @ e) » J ⊢ c).

  Lemma DERIVED_RULE_right_before_over_or_hyp_true :
    forall x {eo : EventOrdering} e R H J a b c,
      rule_true (DERIVED_RULE_right_before_over_or_hyp x e R H J a b c).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "z" (KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e)); simseqs j.
    { apply DERIVED_RULE_right_before_over_or_seq_true; simseqs j. }
    (* FIX *)
    introv ct ht; apply st0; simpl in *; tcsp.
    introv i; allrw hyp_in_adds; allrw hyp_in_add; repndors; subst; simpl in *; tcsp;
      try (complete (apply ht; allrw hyp_in_add; allrw hyp_in_adds; allrw hyp_in_add; simpl in *; tcsp)).
    unfold hyp_event; simpl.
    pose proof (ht ("z" › KE_OR (KE_RIGHT_BEFORE_EQ a) (KE_RIGHT_BEFORE_EQ b) @ e)) as ht;
      allrw hyp_in_add; allrw hyp_in_adds; allrw hyp_in_add; simpl in *; tcsp.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_happened_before_eq {eo : EventOrdering} e R H c :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ c) @ e,
       ⟬R⟭ H ⊢ KE_NOT_FIRST @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE c @ e).

  Lemma DERIVED_RULE_right_before_happened_before_eq_true :
    forall {eo : EventOrdering} e R H c,
      rule_true (DERIVED_RULE_right_before_happened_before_eq e R H c).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_local_pred_local_true "u" e); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "z" (KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ c) @ e)); simseqs j.
    { apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
    norm_with "z"; apply (DERIVED_RULE_unright_before_eq_hyp_true "z"); simseqs j.
    norm_with "z"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "v" "z"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_local_if_causal_true "u"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_if_causal_trans_true "u"); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "v"); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_not_first_implies_not_first {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_NOT_FIRST @ e]
      (⟬R⟭ H ⊢ KE_NOT KE_FIRST @ e).

  Lemma DERIVED_RULE_not_first_implies_not_first_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_not_first_implies_not_first e R H).
  Proof.
    start_proving_derived st.
    LOCKintro "x".
    LOCKelim "x"; try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_first_implies_not_knew {eo : EventOrdering} e R H c :=
    MkRule0
      [⟬R⟭ H ⊢ KE_FIRST @ e]
      (⟬R⟭ H ⊢ KE_NOT (KE_KNEW c) @ e).

  Lemma DERIVED_RULE_first_implies_not_knew_true :
    forall {eo : EventOrdering} e R H c,
      rule_true (DERIVED_RULE_first_implies_not_knew e R H c).
  Proof.
    start_proving_derived st.
    LOCKcut "y" (KE_FIRST @ e).
    LOCKintro "x".
    LOCKelim "y"; try LOCKauto.
    LOCKapply (DERIVED_RULE_knew_implies_not_first_true c); try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_exists_before_idem {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_LOCAL_BEFORE_EQ a) @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_exists_before_idem_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_exists_before_idem e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE_EQ (KE_LOCAL_BEFORE_EQ a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "v" "x"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causal_trans_true "u"); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_unlocal_before_eq_if_causalle_true "v"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_learned_local_pred_implies {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_LEARNED i) @ e]
      (⟬R⟭ H ⊢ KE_LEARNED i @ e).

  Lemma DERIVED_RULE_learned_local_pred_implies_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_learned_local_pred_implies e R H i).
  Proof.
    introv; apply DERIVED_RULE_exists_before_idem_true.
  Qed.


  (****************************************************************************************)
  Definition DERIVED_RULE_trusted_learned_local_pred_implies {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_TLEARNED t) @ e]
      (⟬R⟭ H ⊢ KE_TLEARNED t @ e).

  Lemma DERIVED_RULE_trusted_learned_local_pred_implies_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_learned_local_pred_implies e R H t).
  Proof.
    introv; apply DERIVED_RULE_exists_before_idem_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owns_change_localle x {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_OWNS a @ e1]
      (⟬R ++ (x ⋈ e1 ■ e2) :: Q⟭ H ⊢ KE_OWNS a @ e2).

  Lemma DERIVED_RULE_owns_change_localle_true :
    forall x {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_owns_change_localle x e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_OWNS a @ e1).
    Transparent KE_OWNS.
    LOCKelim "x".
    LOCKintro n.
    Opaque KE_OWNS.
    LOCKelim "x" "y".
    LOCKintro.
    { LOCKapply PRIMITIVE_RULE_at_change_localle_true; try LOCKauto. }
    LOCKapply (PRIMITIVE_RULE_has_owner_change_event_true e2 e1); try LOCKauto.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_owns_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_OWNS a) @ e]
      (⟬R⟭ H ⊢ KE_OWNS a @ e).

  Lemma DERIVED_RULE_right_before_owns_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_right_before_owns_implies e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_OWNS a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unright_before_eq_hyp_true "x"); simseqs j.
    apply (DERIVED_RULE_add_local_pred_localle_true "u" e); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_owns_change_localle_true "u"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owns_local_pred_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_OWNS a @ local_pred_n e]
      (⟬R⟭ H ⊢ KE_OWNS a @ e).

  Lemma DERIVED_RULE_owns_local_pred_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_owns_local_pred_implies e R H a).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_right_before_owns_implies_true; simseqs j.
    apply DERIVED_RULE_unright_before_eq_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_owned_happened_before_tgens_implies_before {eo : EventOrdering} e R H t :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TOWNED t @ e,
       ⟬R⟭ H ⊢ KE_HAPPENED_BEFORE (KE_TDISS_OWN t) @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE (KE_TDISS_OWN t) @ e).

  Lemma DERIVED_RULE_owned_happened_before_tgens_implies_before_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_owned_happened_before_tgens_implies_before e R H t).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE (KE_TDISS_OWN t) @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "o" (KE_TOWNED t @ e)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    norm_with "o"; apply (DERIVED_RULE_unright_before_eq_hyp_true "o"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "u" "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_owns_implies_local_true "u" (kc_trust2data t)); simseqs j.

    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    { apply DERIVED_RULE_owns_local_pred_implies_true; simseqs j.
      norm_with "o"; apply (PRIMITIVE_RULE_hypothesis_true "o"); simseqs j. }

    causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_if_causal_true "u"); simseqs j.

    apply PRIMITIVE_RULE_and_intro_true; simseqs j.
    { norm_with "c"; apply (PRIMITIVE_RULE_hypothesis_true "c"); simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_knew {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_gen t @ local_pred_n e,
       ⟬R⟭ H ⊢ KE_TKNEW t @ e,
       ⟬R⟭ H ⊢ KE_TOWNED t @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE (KE_TDISS_OWN t) @ e).

  Lemma DERIVED_RULE_trusted_knew_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_knew e R H t).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_TKNOWS t) @ e)); simseqs j.

    apply (PRIMITIVE_RULE_cut_true
             "y"
             (KE_IMPLIES
                (KE_RIGHT_BEFORE_EQ (KE_TKNOWS t))
                (KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ (KE_TDISS_OWN t))) @ e)); simseqs i.

    { apply DERIVED_RULE_right_before_over_implies_true; simseqs i.
      apply DERIVED_RULE_unright_before_eq_true; simseqs i.
      apply DERIVED_RULE_thin_last_true; simseqs i. }

    apply DERIVED_RULE_implies_elim_true; simseqs i.

    { apply DERIVED_RULE_hypothesis_last_true; simseqs i. }

    apply (PRIMITIVE_RULE_cut_true
             "z"
             (KE_HAPPENED_BEFORE (KE_TDISS_OWN t) @ e)); simseqs i.

    { apply DERIVED_RULE_right_before_happened_before_eq_true; simseqs i.

      { apply PRIMITIVE_RULE_thin_but_last_true; simseqs i.
        apply DERIVED_RULE_hypothesis_last_true; simseqs i. }

      { apply DERIVED_RULE_thin_last_true; simseqs i.
        apply DERIVED_RULE_thin_last_true; simseqs i.
        apply (DERIVED_RULE_knew_implies_not_first_true (kc_trust2data t)); simseqs i. } }

    apply DERIVED_RULE_owned_happened_before_tgens_implies_before_true; simseqs i.

    { apply DERIVED_RULE_thin_last_true; simseqs i.
      apply DERIVED_RULE_thin_last_true; simseqs i.
      apply DERIVED_RULE_thin_last_true; simseqs i. }

    apply DERIVED_RULE_hypothesis_last_true; simseqs i.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_pred_eq_induction {eo : EventOrdering} e R H a :=
    MkRule1
      (fun e => [⟬R⟭ H ⊢ KE_IMPLIES KE_FIRST a @ e,
                 ⟬R⟭ H ⊢ KE_IMPLIES KE_NOT_FIRST (KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) a) @ e])
      (⟬R⟭ H ⊢ a @ e).

  Lemma DERIVED_RULE_pred_eq_induction_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_pred_eq_induction e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_pred_induction_true "x"); simseqs j; inst_hyp e0 st;
      apply DERIVED_RULE_remove_first_causal_true; simseqs j; auto;[].
    apply (PRIMITIVE_RULE_cut_true "x" (KE_IMPLIES KE_NOT_FIRST (KE_IMPLIES (KE_RIGHT_BEFORE_EQ a) a) @ e0)); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { apply (DERIVED_RULE_right_before_implies_not_first_true a); simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs i. }
    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs i. }
    norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_decidable_knew {eo : EventOrdering} e R H a :=
    MkRule0
      []
      (⟬R⟭ H ⊢ KE_OR (KE_KNEW a) (KE_NOT (KE_KNEW a)) @ e).

  Lemma DERIVED_RULE_decidable_knew_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_decidable_knew e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "or" (KE_OR KE_FIRST KE_NOT_FIRST @ e)); simseqs j.
    { apply PRIMITIVE_RULE_first_dec_true; simseqs j. }
    norm_with "or"; apply PRIMITIVE_RULE_or_elim_true; simseqs j.
    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply DERIVED_RULE_first_implies_not_knew_true; simseqs j.
      norm_with "or"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e); simseqs j.
    { norm_with "or"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "h" (KE_OR (KE_KNOWS a) (KE_NOT (KE_KNOWS a)) @ local_pred_n e)); simseqs j.
    { apply PRIMITIVE_RULE_decidable_knows_true; simseqs j. }
    norm_with "h"; apply PRIMITIVE_RULE_or_elim_true; simseqs j.
    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_unright_before_if_causal_true; simseqs j.
      norm_with "h"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "q"); simseqs j.
    LOCKelim "h"; try LOCKauto.
    norm_with "q"; apply PRIMITIVE_RULE_unright_before_hyp_true; simseqs j.
    norm_with "q"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_local_before_eq_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_LOCAL_BEFORE_EQ a) @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_right_before_local_before_eq_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_right_before_local_before_eq_implies e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_LOCAL_BEFORE_EQ a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unright_before_eq_hyp_true "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    apply DERIVED_RULE_unlocal_before_eq_if_pred_true; simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causalle_true "u"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_happened_before_eq_implies {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ a) @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_right_before_happened_before_eq_implies_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_right_before_happened_before_eq_implies e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_RIGHT_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unright_before_eq_hyp_true "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "u" "x"); simseqs j.
    apply DERIVED_RULE_unhappened_before_eq_if_pred_true; simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "u"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_knowledge_acquired {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_KNOWS i @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_AND (KE_KNOWS i) (KE_NOT (KE_KNEW i))) @ e).

  Lemma DERIVED_RULE_knowledge_acquired_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_knowledge_acquired e R H i).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "k" (KE_KNOWS i @ e)); simseqs j;[].
    clear st0.

    apply DERIVED_RULE_revert_last_true; simseqs j;[].

    apply DERIVED_RULE_pred_eq_induction_true; simseqs j.

    { apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
      apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
      apply DERIVED_RULE_weaken_local_before_eq_true; simseqs j.
      apply PRIMITIVE_RULE_and_intro_true; simseqs j.

      { apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

      apply DERIVED_RULE_thin_last_true; simseqs j.
      apply DERIVED_RULE_first_implies_not_knew_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "z"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true
             "w"
             (KE_IMPLIES
                (KE_RIGHT_BEFORE_EQ (KE_KNOWS i))
                (KE_RIGHT_BEFORE_EQ (KE_LOCAL_BEFORE_EQ (KE_AND (KE_KNOWS i) (KE_NOT (KE_KNEW i))))) @ e0)); simseqs j.

    { norm_with "y".
      apply (DERIVED_RULE_right_before_over_implies_seq_true "y"); simseqs j. }

    norm_with "y".
    apply (PRIMITIVE_RULE_thin_true "y"); simseqs j.

    apply (PRIMITIVE_RULE_cut_true "y" (KE_OR (KE_KNEW i) (KE_NOT (KE_KNEW i)) @ e0)); simseqs j.

    { apply DERIVED_RULE_decidable_knew_true; simseqs j. }

    apply (DERIVED_RULE_or_elim_true "y"); simseqs j.

    { norm_with "w".
      apply (PRIMITIVE_RULE_implies_elim_true "w"); simseqs j.

      { apply DERIVED_RULE_knew_implies_knows_true; simseqs j.
        apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

      apply DERIVED_RULE_right_before_local_before_eq_implies_true; simseqs j.
      norm_with "w".
      apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }

    apply DERIVED_RULE_weaken_local_before_eq_true; simseqs j.
    apply PRIMITIVE_RULE_and_intro_true; simseqs j.

    { norm_with "z".
      apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }

    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_learns_or_knows_implies_learns_or_knows_if_knew {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns i @ local_pred_n e]
      (⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns_if_knew i @ e).

  Lemma DERIVED_RULE_learns_or_knows_implies_learns_or_knows_if_new_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_learns_or_knows_implies_learns_or_knows_if_knew e R H i).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (KE_RIGHT_BEFORE_EQ (KE_KNOWS i) @ e)); simseqs j.

    { apply DERIVED_RULE_knew_implies_knows_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
    norm_with "y"; apply DERIVED_RULE_unright_before_eq_hyp_true; simseqs j.

    apply (PRIMITIVE_RULE_cut_true "z" (KE_RIGHT_BEFORE_EQ (KE_OR (KE_LEARNED i) (KE_OWNS i)) @ e)); simseqs j.
    { apply DERIVED_RULE_unright_before_eq_true; simseqs j.
      norm_with "y"; apply (DERIVED_RULE_revert_true "y"); simseqs j. }

    norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "w" (KE_OR (KE_RIGHT_BEFORE_EQ (KE_LEARNED i)) (KE_RIGHT_BEFORE_EQ (KE_OWNS i)) @ e)); simseqs j.

    { norm_with "z"; apply (DERIVED_RULE_right_before_over_or_seq_true "z"); simseqs j. }

    apply PRIMITIVE_RULE_thin_but_last_true; simseqs j.

    apply (DERIVED_RULE_or_elim_true "w"); simseqs j.

    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply DERIVED_RULE_right_before_local_before_eq_implies_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply DERIVED_RULE_right_before_owns_implies_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_happened_before {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_HAPPENED_BEFORE a) @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_happened_before_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_happened_before e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE_EQ (KE_HAPPENED_BEFORE a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "v" "x"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_localle_if_causalle_true "u"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_if_causalle_trans_eq_true "u"); simseqs j.
    causal_norm_with "v"; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true "v"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unlocal_before_eq_happened_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ a) @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_unlocal_before_eq_happened_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_unlocal_before_eq_happened_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE_EQ (KE_HAPPENED_BEFORE_EQ a) @ e)); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "v" "x"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_localle_if_causalle_true "u"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true "u"); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "v"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_unall_before_correct_trace_before_eq_hyp x {eo : EventOrdering} e R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › KE_LOCAL_FORALL_BEFORE_EQ (KE_CORRECT_TRACE_BEFORE a) @ e) » J ⊢ b]
      (⟬R⟭ H • (x › KE_CORRECT_TRACE_BEFORE a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_unall_before_correct_trace_before_eq_hyp_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_unall_before_correct_trace_before_eq_hyp x e R H J a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_after_true "x" x (KE_LOCAL_FORALL_BEFORE_EQ (KE_CORRECT_TRACE_BEFORE a) @ e)); simseqs j.
    { apply PRIMITIVE_RULE_and_intro_true; simseqs j.
      { apply PRIMITIVE_RULE_unall_before_correct_trace_before_hyp_true; simseqs j.
        norm_with x; apply (PRIMITIVE_RULE_hypothesis_true x); simseqs j. }
      norm_with x; apply (PRIMITIVE_RULE_hypothesis_true x); simseqs j. }
    norm_with x; apply (PRIMITIVE_RULE_thin_true x); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_rename_hyp_true "x" x); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_happened_before_if_local_eq x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e']
      (⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE a @ e).

  Lemma DERIVED_RULE_happened_before_if_local_eq_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_happened_before_if_local_eq x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE a @ e')); simseqs j.
    apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    apply DERIVED_RULE_unhappened_before_if_causalle_trans_eq_true; simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_happened_before_eq_if_local_eq x {eo : EventOrdering} e' e R Q H a :=
    MkRule0
      [⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e']
      (⟬R ++ (x ⋈ e' ■ e) :: Q⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_happened_before_eq_if_local_eq_true :
    forall x {eo : EventOrdering} e' e R Q H a,
      rule_true (DERIVED_RULE_happened_before_eq_if_local_eq x e' e R Q H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE_EQ a @ e')); simseqs j.
    apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    apply DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true; simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_learns_if_knows_implies_learned_if_knows {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule1
      (fun e => [⟬R⟭ H ⊢ ASSUMPTION_learns_if_knows i @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_learned_if_knows i @ e).

  Lemma DERIVED_RULE_learns_if_knows_implies_learned_if_knows_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_learns_if_knows_implies_learned_if_knows e R H i).
  Proof.
    introv st; simpl in *.
    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "x"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "z" (ASSUMPTION_learns_if_knows i @ e0)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j.
      apply DERIVED_RULE_thin_last_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      inst_hyp e0 st. }

    norm_with "z"; apply (PRIMITIVE_RULE_implies_elim_true "z"); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "z"; apply (PRIMITIVE_RULE_implies_elim_true "z"); simseqs j.
    { causal_norm_with "u"; apply (PRIMITIVE_RULE_correct_trace_before_if_causal_true "u"); simseqs j.
      norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

    norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "v" "z"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_happened_before_if_local_eq_true "u"); simseqs j.
    causal_norm_with "v"; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true "v"); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_knowledge_acquired {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TKNOWS t @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_AND (KE_TKNOWS t) (KE_NOT (KE_TKNEW t))) @ e).

  Lemma DERIVED_RULE_trusted_knowledge_acquired_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_knowledge_acquired e R H t).
  Proof.
    introv exe h; simpl in *.
    apply DERIVED_RULE_knowledge_acquired_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_knows_implies_correct (t : kc_trust) {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TKNOWS t @ e]
      (⟬R⟭ H ⊢ KE_LOCAL_CORRECT_TRACE_BEFORE @ e).

  Lemma DERIVED_RULE_trusted_knows_implies_correct_true :
    forall (t : kc_trust) {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_trusted_knows_implies_correct t e R H).
  Proof.
    introv; apply PRIMITIVE_RULE_knows_implies_correct_true.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_happened_before_implies_happened_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ KE_HAPPENED_BEFORE a @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_happened_before_implies_happened_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_happened_before_implies_happened_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_HAPPENED_BEFORE a @ e)); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "u" "x"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_causal_if_causalle_true "u"); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "u"); simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_weaken_happened_before_eq {eo : EventOrdering} e R H a :=
    MkRule0
      [⟬R⟭ H ⊢ a @ e]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ a @ e).

  Lemma DERIVED_RULE_weaken_happened_before_eq_true :
    forall {eo : EventOrdering} e R H a,
      rule_true (DERIVED_RULE_weaken_happened_before_eq e R H a).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_add_happenedle_refl_true "u" e); simseqs j.
    causal_norm_with "u"; apply (DERIVED_RULE_unhappened_before_eq_if_causalle_true "u"); simseqs j.
    apply DERIVED_RULE_remove_first_causal_true; simseqs j.
  Qed.


  (****************************************************************)
  Definition DERIVED_RULE_knows_propagates {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [
        ⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns i @ e,
        ⟬R⟭ H ⊢ KE_LOCAL_FORALL_BEFORE_EQ (ASSUMPTION_learns_if_knows i) @ e,
        ⟬R⟭ H ⊢ KE_KNOWS i @ e,
        ⟬R⟭ H ⊢ KE_CORRECT_TRACE_BEFORE (kc_data2owner i) @ e
      ]
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE_EQ (KE_AND (KE_KNOWS i) (KE_OWNS i)) @ e).

  Lemma DERIVED_RULE_knows_propagates_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_knows_propagates e R H i).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    dLin_hyp st.

    apply (PRIMITIVE_RULE_cut_true "k" (KE_KNOWS i @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (ASSUMPTION_learns_or_owns i @ e)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    apply DERIVED_RULE_implies_elim_true; simseqs j.
    { apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
    apply (DERIVED_RULE_or_elim_true "y"); simseqs j.

    { norm_with "y"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "y"); simseqs j.
      apply (PRIMITIVE_RULE_cut_true "z" (KE_LOCAL_FORALL_BEFORE_EQ (ASSUMPTION_learns_if_knows i) @ e)); simseqs j.
      { apply DERIVED_RULE_thin_last_true; simseqs j.
        apply DERIVED_RULE_thin_last_true; simseqs j.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
      norm_with "z"; causal_norm_with "u"; apply (DERIVED_RULE_unlocal_forall_before_eq_hyp_true "u" "z"); simseqs j.
      norm_with "z"; apply (PRIMITIVE_RULE_implies_elim_true "z"); simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      norm_with "z"; apply (PRIMITIVE_RULE_implies_elim_true "z"); simseqs j.
      { apply (PRIMITIVE_RULE_cut_true "z" (KE_CORRECT_TRACE_BEFORE (kc_data2owner i) @ e)); simseqs j.
        { apply DERIVED_RULE_thin_last_true; simseqs j.
          apply DERIVED_RULE_thin_last_true; simseqs j.
          apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
        causal_norm_with "u"; apply (PRIMITIVE_RULE_correct_trace_before_if_causal_true "u"); simseqs j.
        norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
      causal_norm_with "u"; apply (DERIVED_RULE_happened_before_eq_if_local_eq_true "u"); simseqs j.
      apply DERIVED_RULE_happened_before_implies_happened_before_eq_true; simseqs j.
      norm_with "z"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "v" "z"); simseqs j.
      causal_norm_with "v"; apply (PRIMITIVE_RULE_unhappened_before_if_causal_true "v"); simseqs j.
      norm_with "z"; apply (PRIMITIVE_RULE_and_elim_true "z" "w"); simseqs j.
      apply PRIMITIVE_RULE_and_intro_true; simseqs j.
      { norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
      norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }

    apply DERIVED_RULE_weaken_happened_before_eq_true; simseqs j.
    apply PRIMITIVE_RULE_and_intro_true; simseqs j.
    { norm_with "k"; apply (PRIMITIVE_RULE_hypothesis_true "k"); simseqs j. }
    norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_trusted_learns_or_knows_implies_learns_or_knows_if_knew {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_or_owns t @ local_pred_n e]
      (⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_or_owns_if_knew t @ e).

  Lemma DERIVED_RULE_trusted_learns_or_knows_implies_learns_or_knows_if_knew_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_learns_or_knows_implies_learns_or_knows_if_knew e R H t).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    dLin_hyp st.

    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (KE_RIGHT_BEFORE_EQ (KE_TKNOWS t) @ e)); simseqs j.

    { apply DERIVED_RULE_knew_implies_knows_true; simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
    norm_with "y"; apply (DERIVED_RULE_unright_before_eq_hyp_true "y"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "z" (KE_OR (KE_TLEARNED t) (KE_TOWNS t) @ local_pred_n e)); simseqs j.
    { apply (PRIMITIVE_RULE_cut_true "w" (ASSUMPTION_trusted_learns_or_owns t @ local_pred_n e)); simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_thin_true "y"); simseqs j. }
      norm_with "w"; apply (PRIMITIVE_RULE_implies_elim_true "w"); simseqs j.
      { apply DERIVED_RULE_hypothesis_last_true; simseqs j. }
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    apply (DERIVED_RULE_or_elim_true "z"); simseqs j.

    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      norm_with "z"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "z"); simseqs j.
      apply DERIVED_RULE_unlocal_before_eq_if_pred_true; simseqs j.
      causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causalle_true "u"); simseqs j.
      apply DERIVED_RULE_hypothesis_last_true; simseqs j. }

    apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
    apply DERIVED_RULE_owns_local_pred_implies_true; simseqs j.
    apply DERIVED_RULE_hypothesis_last_true; simseqs j.
  Qed.



(*  (* NOT USED *)
  (****************************************************************)
  Definition OLD_RULE_TGEN_MONOTONICITY_local_trusted_component {eo : EventOrdering} e R H t1 t2 c1 c2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ KE_TGENS t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_TGENS t1) @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e])
      (⟬R⟭ H ⊢ KE_ID_LE c1 c2 @ e).

  Lemma OLD_RULE_TGEN_MONOTONICITY_local_trusted_component_true :
    forall {eo : EventOrdering} e R H t1 t2 c1 c2,
      rule_true (OLD_RULE_TGEN_MONOTONICITY_local_trusted_component e R H t1 t2 c1 c2).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (st (mk_v1 e)) as st'; simpl_sem_rule; dLin_hyp st'.
    unfold sequent_true in *; simpl in *.
    clear st'0.
    repeat (autodimp st'1 hyp); tcsp.
    repeat (autodimp st'2 hyp); tcsp.
    repeat (autodimp st'3 hyp); tcsp.
    repeat (autodimp st'4 hyp); tcsp.
    exrepnd.
    allrw interpret_tgens.
    unfold seq_event in *; simpl in *.

    assert (monotonicity eo) as mon.
    { introv exe.
      pose proof (st (mk_v1 (MkEventN e0 exe))) as st; simpl_sem_rule; dLin_hyp st; simpl in *.
      clear st1 st2.
      repeat (autodimp st0 hyp); tcsp.
      allrw interpret_no_tgens; allrw interpret_exists_tgens; tcsp. }

    assert (c1 ⋘ c2) as q; try omega; subst; tcsp.
    eapply generates_trusted_kc_id_increases; eauto; tcsp; eauto 3 with kn.
  Qed.*)


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition OLD_RULE_trusted_learns_or_gens {eo : EventOrdering} e R H (t : kc_trust):=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_or_owns t @ e,
       ⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_gen t @ e,
       ⟬R⟭ H ⊢ KE_TKNOWS t @ e]
      (⟬R⟭ H ⊢ KE_OR
           (KE_TLEARNED t)
           (KE_LOCAL_BEFORE_EQ (KE_DISS_OWN t)) @ e).

  Lemma OLD_RULE_trusted_learns_or_gens_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (OLD_RULE_trusted_learns_or_gens e R H t).
  Proof.
    start_proving_primitive st ct ht.
    unfold sequent_true in *; simpl in *.
    repeat (autodimp st0 hyp); tcsp.
    repeat (autodimp st1 hyp); tcsp.
    repeat (autodimp st2 hyp); tcsp.
    unfold seq_event in *; simpl in *.

    destruct st0 as [LER|OWN].

    { (* learned *)
      clear st1.
      exrepnd.
      left.
      exists e'; dands; eauto.
    }

    {
      (* owned *)
      allrw interp_towns.
      exrepnd.
      right; exists e'; dands; auto.
      allrw interpret_tgens.
      applydup generates_trusted_implies_data_is_owned in st0.
      assert (loc e' = loc e) as eqloc; eauto 3 with kn eo.
    }
  Qed.*)


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition OLD_RULE_learns_or_gens {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns i @ e,
       ⟬R⟭ H ⊢ ASSUMPTION_knows_and_owns i @ e,
       ⟬R⟭ H ⊢ KE_KNOWS i @ e]
      (⟬R⟭ H ⊢ KE_OR
           (KE_LEARNED i)
           (KE_LOCAL_BEFORE_EQ (KE_GENS i)) @ e).

  Lemma OLD_RULE_learns_or_gens_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (OLD_RULE_learns_or_gens e R H i).
  Proof.
    start_proving_primitive st ct ht.
    unfold sequent_true in *; simpl in *.
    repeat (autodimp st0 hyp); tcsp.
    autodimp st1 hyp; tcsp.
    autodimp st1 hyp; tcsp.
    repeat (autodimp st2 hyp); tcsp.
    unfold seq_event in *; simpl in *.

    destruct st0 as [LER|OWN].

    { (* learned *)
      exrepnd.
      left.
      exists e'; dands; eauto.
    }

    {
      (* owned *)
      autodimp st1 hyp; eauto 3 with kn.
    }
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_it_owns_owned_implies_at d {eo : EventOrdering} e p R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_OWNS d @ e,
       ⟬R⟭ H ⊢ KE_HAS_OWNER d p @ e]
      (⟬R⟭ H ⊢ KE_AT p @ e).

  Lemma DERIVED_RULE_it_owns_owned_implies_at_true :
    forall d {eo : EventOrdering} e p R H,
      rule_true (DERIVED_RULE_it_owns_owned_implies_at d e p R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_OWNS d @ e)); simseqs j.
    Transparent KE_OWNS.
    norm_with "x"; apply (PRIMITIVE_RULE_exists_node_elim_true "x"); simseqs j.
    Opaque KE_OWNS.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "z" (KE_HAS_OWNER d p @ e)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    apply (PRIMITIVE_RULE_cut_true "w" (KE_NODE_EQ n p @ e)); simseqs j.
    { apply (PRIMITIVE_RULE_has_owner_implies_eq_true d); simseqs j.
      { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
    apply (PRIMITIVE_RULE_subst_node_in_at_true n); simseqs j.
    { norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
    norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knows_and_not_owns_implies_learns {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns i @ e,
       ⟬R⟭ H ⊢ KE_KNOWS i @ e,
       ⟬R⟭ H ⊢ KE_NOT (KE_OWNS i) @ e]
      (⟬R⟭ H ⊢ KE_LEARNED i @ e).

  Lemma DERIVED_RULE_knows_and_not_owns_implies_learns_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (DERIVED_RULE_knows_and_not_owns_implies_learns e R H i).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_learns_or_owns i @ e)); simseqs j.
    norm_with "ass"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j.
    norm_with "ass"; apply PRIMITIVE_RULE_or_elim_true; simseqs j.
    { norm_with "ass"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "not" (KE_NOT (KE_OWNS i) @ e)); simseqs j.
    { norm_with "ass"; apply PRIMITIVE_RULE_thin_true; simseqs j. }
    LOCKelim "not"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knows_and_not_owns_implies_learns2
             p a {eo : EventOrdering} e R H d :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_learns_or_owns d @ e,
       ⟬R⟭ H ⊢ KE_KNOWS d        @ e,
       ⟬R⟭ H ⊢ KE_HAS_OWNER d p  @ e,
       ⟬R⟭ H ⊢ KE_AT a           @ e,
       ⟬R⟭ H ⊢ KE_NOT (KE_NODE_EQ p a) @ e]
      (⟬R⟭ H ⊢ KE_LEARNED d       @ e).

  Lemma DERIVED_RULE_knows_and_not_owns_implies_learns2_true :
    forall p a {eo : EventOrdering} (e : EventN) R H (d : kc_data),
      rule_true (DERIVED_RULE_knows_and_not_owns_implies_learns2 p a e R H d).
  Proof.
    start_proving_derived st.

    apply DERIVED_RULE_knows_and_not_owns_implies_learns_true; simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "own"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "ho" (KE_AT p @ e)); simseqs j.
    { apply (DERIVED_RULE_it_owns_owned_implies_at_true d); simseqs j.
      { norm_with "own"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
      norm_with "own"; apply PRIMITIVE_RULE_thin_true; simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "d" (KE_NOT (KE_NODE_EQ p a) @ e)); simseqs j.
    { norm_with "own"; apply PRIMITIVE_RULE_thin_true; simseqs j.
      norm_with "ho"; apply PRIMITIVE_RULE_thin_true; simseqs j. }

    norm_with "d"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j.

    { apply PRIMITIVE_RULE_at_implies_same_node_true; simseqs j.
      { norm_with "own"; apply PRIMITIVE_RULE_thin_true; simseqs j.
        norm_with "ho"; apply PRIMITIVE_RULE_thin_true; simseqs j. }
      norm_with "ho"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }

    norm_with "d"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_knows_and_not_owns_implies_learns {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_or_owns t @ e,
       ⟬R⟭ H ⊢ KE_TKNOWS t @ e,
       ⟬R⟭ H ⊢ KE_NOT (KE_TOWNS t) @ e]
      (⟬R⟭ H ⊢ KE_TLEARNED t @ e).

  Lemma DERIVED_RULE_trusted_knows_and_not_owns_implies_learns_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (DERIVED_RULE_trusted_knows_and_not_owns_implies_learns e R H t).
  Proof.
    start_proving_derived st; apply DERIVED_RULE_knows_and_not_owns_implies_learns_true; simseqs j.
  Qed.



  (***************************************************************************)
  Definition DERIVED_RULE_implies_learned_if_gen
             {eo : EventOrdering} e d R H :=
    MkRule1
      (fun e' => [⟬R⟭ H ⊢ ASSUMPTION_learns_if_gen d @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_learned_if_gen d @ e).

  Lemma DERIVED_RULE_implies_learned_if_gen_true :
    forall {eo : EventOrdering} (e : EventN) d R H,
      rule_true (DERIVED_RULE_implies_learned_if_gen e d R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    norm_with "x"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (ASSUMPTION_learns_if_gen d @ e0)); simseqs j.
    { inst_hyp e0 h.
      norm_with "x"; apply PRIMITIVE_RULE_thin_true; simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_remove_causal_true; simseqs j. }
    norm_with "y"; apply PRIMITIVE_RULE_implies_elim_true; simseqs j.
    { norm_with "x"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    causal_norm_with "u"; apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    causal_norm_with "u"; apply DERIVED_RULE_unhappened_before_if_causalle_trans_eq_true; simseqs j.
    norm_with "y"; apply PRIMITIVE_RULE_hypothesis_true; simseqs j.
  Qed.


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition OLD_RULE_trusted_learned_implies_generates_and_owns {eo : EventOrdering} e R H (t : kc_trust) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_if_gen t @ e',
          ⟬R⟭ H ⊢ KE_TLEARNED t @ e])
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE
           (KE_AND
              (KE_TGENS t)
              (KE_TOWNS t)) @ e).

  Lemma OLD_RULE_trusted_learned_implies_generates_trusted_true :
    forall {eo : EventOrdering} e R H (t : kc_trust),
      rule_true (OLD_RULE_trusted_learned_implies_generates_and_owns e R H t).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (st (mk_v1 e)) as st'; simpl_sem_rule; dLin_hyp st'; simpl in *.
    clear st'0.
    unfold sequent_true in *; simpl in *.
    repeat (autodimp st'1 hyp); tcsp.
    unfold seq_event in *; simpl in *.
    exrepnd.

    assert (ex_node_e e') as exe by eauto 3 with kn.
    pose proof (st (mk_v1 (MkEventN e' exe))) as st; simpl_sem_rule; dLin_hyp st; simpl in *.
    clear st1.

    repeat (autodimp st0 hyp); exrepnd.
    exists e'0; dands; eauto 3 with eo; eauto.
    allrw interp_towns.
    allrw interpret_tgens; eauto 3 with kn.
  Qed.*)


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition OLD_RULE_learned_implies_generates {eo : EventOrdering} e R H (i : kc_data) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_learned_if_knows i @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_knows_and_owns i @ e',
          ⟬R⟭ H ⊢ KE_LEARNED i @ e,
          ⟬R⟭ H ⊢ KE_CORRECT_TRACE_BEFORE (kc_data2name i) @ e])
      (⟬R⟭ H ⊢ KE_HAPPENED_BEFORE (KE_GENS i) @ e).

  Lemma OLD_RULE_learned_implies_generated_true :
    forall {eo : EventOrdering} e R H (i : kc_data),
      rule_true (OLD_RULE_learned_implies_generates e R H i).
  Proof.
    start_proving_primitive st ct ht.
    pose proof (st (mk_v1 e)) as st'; simpl_sem_rule; dLin_hyp st'; simpl in *.
    unfold sequent_true in *; simpl in *.
    clear st'1.
    repeat (autodimp st'0 hyp); tcsp.
    repeat (autodimp st'2 hyp); tcsp.
    repeat (autodimp st'3 hyp); tcsp.
    unfold seq_event in *; simpl in *.
    exrepnd.

    pose proof (st (mk_v1 (MkEventN e'0 st'0))) as st; simpl_sem_rule; dLin_hyp st; simpl in *.
    clear st0 st2 st3.
    repeat (autodimp st1 hyp); tcsp; eauto 3 with kn;[].
    exrepnd.

    exists e'1; dands; eauto 3 with kn eo.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_local_before_implies_not_first u x {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 □ e2) :: R⟭ H • (x › KE_NOT_FIRST @ e2) ⊢ a]
      (⟬Q ++ (u ⋈ e1 □ e2) :: R⟭ H ⊢ a).

  Lemma DERIVED_RULE_local_before_implies_not_first_true :
    forall u x {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_local_before_implies_not_first u x e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    LOCKcut x (KE_NOT_FIRST @ e2).
    LOCKapply DERIVED_RULE_not_first_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_after_is_id_before u {eo : EventOrdering} e1 e2 c Q R H :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_AFTER c @ e1]
      (⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_BEFORE c @ e2).

  Lemma DERIVED_RULE_id_after_is_id_before_true :
    forall u {eo : EventOrdering} e1 e2 c Q R H,
      rule_true (DERIVED_RULE_id_after_is_id_before u e1 e2 c Q R H).
  Proof.
    start_proving_derived st.
    LOCKintro 0.
    LOCKapply@ u PRIMITIVE_RULE_unright_before_if_causal_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_ids_before_imply_eq_ids {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_BEFORE c1 @ e,
       ⟬R⟭ H ⊢ KE_ID_BEFORE c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e).

  Lemma DERIVED_RULE_ids_before_imply_eq_ids_true :
    forall {eo : EventOrdering} e c1 c2 R H,
      rule_true (DERIVED_RULE_ids_before_imply_eq_ids e c1 c2 R H).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_ID_BEFORE c1 @ e).
    LOCKcut "q" (KE_ID_BEFORE c2 @ e).
    { LOCKclear "h". }
    LOCKelim "h"; LOCKelim "q".
    { LOCKapply@ "h" PRIMITIVE_RULE_unright_before_hyp_true.
      LOCKapply@ "q" PRIMITIVE_RULE_unright_before_hyp_true.
      LOCKapply (PRIMITIVE_RULE_id_eq_change_event_true e (local_pred_n e)).
      LOCKapply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; try LOCKauto. }
    { LOCKelim "q" "x".
      LOCKelim "x"; try LOCKauto.
      LOCKapply (DERIVED_RULE_right_before_implies_not_first_true (KE_ID_AFTER c1)); try LOCKauto. }
    { LOCKelim "h" "x".
      LOCKelim "x"; try LOCKauto.
      LOCKapply (DERIVED_RULE_right_before_implies_not_first_true (KE_ID_AFTER c2)); try LOCKauto. }
    { LOCKelim "h" "x".
      LOCKelim "h" "y".
      LOCKelim "q" "a".
      LOCKelim "q" "b".
      LOCKapply PRIMITIVE_RULE_has_init_id_unique_true; try LOCKauto. }
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_right_before_elim u x {eo : EventOrdering} e e' Q R H J a b :=
    MkRule0
      [⟬Q ++ (u ⋈ e' ⋄ e) :: R⟭ H • (x › a @ e') » J ⊢ b]
      (⟬Q ++ (u ⋈ e' ⋄ e) :: R⟭ H • (x › KE_RIGHT_BEFORE a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_right_before_elim_true :
    forall u x {eo : EventOrdering} e e' Q R H J a b,
      rule_true (DERIVED_RULE_right_before_elim u x e e' Q R H J a b).
  Proof.
    start_proving_derived st.
    LOCKapply@ x PRIMITIVE_RULE_unright_before_hyp_true.
    LOCKapply@ u (PRIMITIVE_RULE_duplicate_guard_true u "u").
    LOCKapply@ "u" PRIMITIVE_RULE_weaken_direct_pred_to_local_pred_true.
    LOCKapply@ "u" PRIMITIVE_RULE_causal_eq_sym_true.
    LOCKapply@ "u" x PRIMITIVE_RULE_subst_causal_eq_hyp_true.
    LOCKclear "u".
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_move_to_concl x {eo : EventOrdering} e b c R H J :=
    MkRule0
      [⟬R⟭ H » J ⊢ KE_IMPLIES b c @ e]
      (⟬R⟭ H • (x › b @ e) » J ⊢ c @ e).

  Lemma DERIVED_RULE_move_to_concl_true :
    forall x {eo : EventOrdering} e b c R H J,
      rule_true (DERIVED_RULE_move_to_concl x e b c R H J).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_IMPLIES b c @ e).
    { LOCKclear x. }
    LOCKelim "h"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_before_is_id_after u {eo : EventOrdering} e1 e2 c Q R H :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_BEFORE c @ e2]
      (⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_AFTER c @ e1).

  Lemma DERIVED_RULE_id_before_is_id_after_true :
    forall u {eo : EventOrdering} e1 e2 c Q R H,
      rule_true (DERIVED_RULE_id_before_is_id_after u e1 e2 c Q R H).
  Proof.
    start_proving_derived st.
    LOCKcut "h" (KE_ID_BEFORE c @ e2).
    LOCKelim "h".
    { LOCKapply@ u "h" DERIVED_RULE_right_before_elim_true; LOCKauto. }
    LOCKelim "h" "x".
    LOCKelim "h" "y".
    LOCKelim "x"; try LOCKauto.
    LOCKapply PRIMITIVE_RULE_direct_pred_if_local_pred_true.
    LOCKapply DERIVED_RULE_not_first_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_causalle_is_equal_if_first u {eo : EventOrdering} e1 e2 R H a :=
    MkRule0
      [⟬ (u ⋈ e1 ■ e2) :: R ⟭ H ⊢ KE_FIRST @ e2,
       ⟬ (u ⋈ e1 ≡ e2) :: R ⟭ H ⊢ a]
      (⟬ (u ⋈ e1 ■ e2) :: R ⟭ H ⊢ a).

  Lemma DERIVED_RULE_causalle_is_equal_if_first_true :
    forall u {eo : EventOrdering} e1 e2 R H a,
      rule_true (DERIVED_RULE_causalle_is_equal_if_first u e1 e2 R H a).
  Proof.
    start_proving_derived st.
    LOCKcut "w" (KE_FIRST @ e2).
    LOCKapply@ u PRIMITIVE_RULE_split_local_before_eq2_true.
    { LOCKclear "w". }
    LOCKelim "w"; try LOCKauto.
    LOCKapply@ u DERIVED_RULE_not_first_true.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_split_local_before_eq u {eo : EventOrdering} e1 e2 R Q H a :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ≡ e2) :: R⟭ H ⊢ a,
       ⟬Q ++ (u ⋈ e1 ■ local_pred_n e2) :: R⟭ H ⊢ a]
      (⟬Q ++ (u ⋈ e1 ■ e2) :: R⟭ H ⊢ a).

  Lemma DERIVED_RULE_split_local_before_eq_true :
    forall u {eo : EventOrdering} e1 e2 R Q H a,
      rule_true (DERIVED_RULE_split_local_before_eq u e1 e2 R Q H a).
  Proof.
    start_proving_derived st.
    apply PRIMITIVE_RULE_split_local_before_eq2_true; simseqs j.
    apply (PRIMITIVE_RULE_split_local_before2_true u "v" "w"); simseqs j.
    causal_norm_with "w"; apply PRIMITIVE_RULE_remove_causal_true; simseqs j.
    causal_norm_with u; apply PRIMITIVE_RULE_remove_causal_true; simseqs j.
    apply (PRIMITIVE_RULE_rename_causal_true u); simseqs j.
  Qed.


  (***********************************************************)
  Definition DERIVED_RULE_relocal_before_eq_hyp u x {eo : EventOrdering} e e' R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › KE_LOCAL_BEFORE_EQ a @ e) » J ⊢ b]
      (⟬(u ⋈ e' ■ e) :: R⟭ H • (x › a @ e') » J ⊢ b).

  Lemma DERIVED_RULE_relocal_before_eq_hyp_true :
    forall u x {eo : EventOrdering} e e' R H J a b,
      rule_true (DERIVED_RULE_relocal_before_eq_hyp u x e e' R H J a b).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_after_true "z" x (KE_LOCAL_BEFORE_EQ a @ e)); simseqs j.
    { causal_norm_with u; apply DERIVED_RULE_unlocal_before_eq_if_causalle_true; simseqs j.
      norm_with x; apply PRIMITIVE_RULE_hypothesis_true; simseqs j. }
    norm_with x; apply (PRIMITIVE_RULE_thin_true x); simseqs j.
    norm_with "z"; apply (PRIMITIVE_RULE_rename_hyp_true "z" x); simseqs j.
    causal_norm_with u; apply PRIMITIVE_RULE_remove_causal_true; simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_le_trans c {eo : EventOrdering} e c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_LE c1 c @ e,
       ⟬R⟭ H ⊢ KE_ID_LE c c2 @ e]
      (⟬R⟭ H ⊢ KE_ID_LE c1 c2 @ e).

  Lemma DERIVED_RULE_id_le_trans_true :
    forall c {eo : EventOrdering} e c1 c2 R H,
      rule_true (DERIVED_RULE_id_le_trans c e c1 c2 R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_ID_LE c1 c @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (KE_ID_LE c c2 @ e)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.

    { norm_with "y"; apply (PRIMITIVE_RULE_or_elim_true "y"); simseqs j.

      { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
        apply (PRIMITIVE_RULE_id_lt_trans_lt_lt_true c); simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

      { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
        apply (PRIMITIVE_RULE_id_lt_trans_lt_eq_true c); simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. } }

    { norm_with "y"; apply (PRIMITIVE_RULE_or_elim_true "y"); simseqs j.

      { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
        apply (PRIMITIVE_RULE_id_lt_trans_eq_lt_true c); simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

      { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
        apply (PRIMITIVE_RULE_id_eq_trans_true c); simseqs j.
        { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. } }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_le_change_event {eo : EventOrdering} e1 e2 c1 c2 R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_ID_LE c1 c2 @ e2]
      (⟬R⟭ H ⊢ KE_ID_LE c1 c2 @ e1).

  Lemma DERIVED_RULE_id_le_change_event_true :
    forall {eo : EventOrdering} e1 e2 c1 c2 R H,
      rule_true (DERIVED_RULE_id_le_change_event e1 e2 c1 c2 R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_ID_LE c1 c2 @ e2)); simseqs j.

    norm_with "x"; apply (PRIMITIVE_RULE_or_elim_true "x"); simseqs j.

    { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply (PRIMITIVE_RULE_id_lt_change_event_true _ e2); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply (PRIMITIVE_RULE_id_eq_change_event_true _ e2); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
  Qed.


(*  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_implies_id_after t {eo : EventOrdering} e c R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TGENS t @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c @ e]
      (⟬R⟭ H ⊢ KE_ID_AFTER c @ e).

  Lemma DERIVED_RULE_generates_trusted_implies_id_after_true :
    forall t {eo : EventOrdering} e c R H,
      rule_true (DERIVED_RULE_generates_trusted_implies_id_after t e c R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "w" (KE_TRUST_HAS_ID t c @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_TGENS t @ e)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    Transparent KE_TGENS.
    norm_with "x"; apply (PRIMITIVE_RULE_unexists_id_true "x"); simseqs j.
    Opaque KE_TGENS.
    norm_with "x"; apply (PRIMITIVE_RULE_unexists_id_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "z"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "u"); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "p" (KE_ID_EQ c h0 @ e)); simseqs j.
    { apply (PRIMITIVE_RULE_has_ids_imply_eq_ids_true t); simseqs j.
      { norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
      norm_with "u"; apply (PRIMITIVE_RULE_hypothesis_true "u"); simseqs j. }
    apply (PRIMITIVE_RULE_id_after_subst_true h0); simseqs j.
    { norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }
    norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j.
  Qed.*)


  (* Lemma generates_trusted_implies_id_after :
    forall {eo : EventOrdering} (e : Event) (t : kc_trust),
      generates_trusted e t
      -> id_after e (kc_id t).
  Proof.
    introv gen.
    unfold generates_trusted in *; exrepnd; allrw; auto.
  Qed.*)



  (************************************************************************************************)
  Definition KE_EX_ID_BETWEEN c :=
    KE_EX_ID2 (fun c1 c2 => KE_ANDS
                                 [KE_ID_BEFORE c1,
                                  KE_ID_AFTER c2,
                                  KE_ID_LT c1 c,
                                  KE_ID_LE c c2]).

  Definition DERIVED_RULE_disseminate_implies_id
             t {eo : EventOrdering} e c R H :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
       ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e,
       ⟬R⟭ H ⊢ KE_TDISS_OWN t @ e,
       ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t c @ e]
      (⟬R⟭ H ⊢ KE_EX_ID_BETWEEN c @ e).

  Lemma DERIVED_RULE_disseminate_implies_id_true :
    forall t {eo : EventOrdering} e c R H,
      rule_true (DERIVED_RULE_disseminate_implies_id
                   t e c R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "dis" (KE_TDISS_OWN t @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "hid" (KE_TRUST_HAS_ID t c @ e)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    apply (PRIMITIVE_RULE_cut_true "new" (ASSUMPTION_generates_new @ e)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    apply (PRIMITIVE_RULE_cut_true "mon" (ASSUMPTION_monotonicity @ e)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    apply (DERIVED_RULE_or_elim_true "mon"); simseqs j.

    { Transparent KE_NO_TGENS.
      LOCKelim "mon".
      Opaque KE_NO_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".

      LOCKelim "new" t.
      LOCKelim "new" c.
      LOCKelim "new" c0.
      LOCKelim "new" c0.

      norm_with "new"; apply (PRIMITIVE_RULE_implies_elim_true "new"); simseqs j.
      { repeat (LOCKintro; try LOCKauto). }

      norm_with "new"; apply (PRIMITIVE_RULE_and_elim_true "new" "new1"); simseqs j.

      LOCKcut "p" (KE_ID_LT c c @ e); try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c0); try LOCKauto. }

    { Transparent KE_TGENS.
      LOCKelim "mon".
      LOCKelim "mon".
      Opaque KE_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".
      LOCKelim "mon" "mon3".

      LOCKelim "new" t.
      LOCKelim "new" c.
      LOCKelim "new" c0.
      LOCKelim "new" c1.

      LOCKelim "new".
      { repeat (LOCKintro; try LOCKauto). }

      LOCKelim "new" "new1".
      LOCKintro c0.
      LOCKintro c1.

      repeat (LOCKintro; try LOCKauto). }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred
             u t2 {eo : EventOrdering} e1 e2 e c1 c2 Q R H :=
    MkRule0
      [⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e2,
       ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ ASSUMPTION_generates_new @ e2,
       ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
       ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
       ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_AFTER c1 @ e1]
      (⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred_true :
    forall u t2 {eo : EventOrdering} e1 e2 e c1 c2 Q R H,
      rule_true (DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred
                   u t2 e1 e2 e c1 c2 Q R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_cut_true "bid" (KE_ID_BEFORE c1 @ e2)); simseqs j.
    { apply DERIVED_RULE_id_after_is_id_before_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "hid" (KE_TRUST_HAS_ID t2 c2 @ e2)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "dis" (KE_TDISS_OWN t2 @ e2)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    apply (PRIMITIVE_RULE_cut_true "between" (KE_EX_ID_BETWEEN c2 @ e2)); simseqs j.
    { apply (DERIVED_RULE_disseminate_implies_id_true t2); simseqs j;
        try (complete (repeat (apply DERIVED_RULE_thin_last_true; simseqs j))). }
    LOCKelim "between".
    LOCKelim "between".
    LOCKelim "between" "between1".
    LOCKelim "between" "between2".
    LOCKelim "between" "between3".
    LOCKelim "between" "between4".

    apply (PRIMITIVE_RULE_cut_true "p" (KE_ID_EQ c1 c @ e)); simseqs j.
    { apply (PRIMITIVE_RULE_id_eq_change_event_true _ e2); simseqs j.
      apply DERIVED_RULE_ids_before_imply_eq_ids_true; simseqs j.
      { norm_with "bid"; apply (PRIMITIVE_RULE_hypothesis_true "bid"); simseqs j. }
      norm_with "between1"; apply (PRIMITIVE_RULE_hypothesis_true "between1"); simseqs j. }

    apply (PRIMITIVE_RULE_id_lt_trans_eq_lt_true c); simseqs j.
    { norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }
    apply (PRIMITIVE_RULE_id_lt_change_event_true _ e2); simseqs j.
    norm_with "between3"; apply (PRIMITIVE_RULE_hypothesis_true "between3"); simseqs j.
  Qed.

  (*Lemma generates_trusted_kc_id_increases_direct_pred :
    forall {eo : EventOrdering} (e1 e2 : Event) (c : nat) (t2 : kc_trust),
      e1 ⊂ e2
      -> id_after e1 c
      -> generates_trusted e2 t2
      -> c < kc_id t2.
  Proof.
    introv dp gt1 gt2.
    dup dp as dp'.
    eapply pred_implies_local_pred in dp.
    rewrite dp in *.
    unfold generates_trusted, id_after, id_before in *.
    exrepnd; subst.

    pose proof (trusted_state_before_implies_trusted_state_after_not_first e2 mem0) as xx.
    repeat (autodimp xx hyp); eauto 3 with eo.
    eq_states; tcsp; try omega.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred2
             u t1 t2 {eo : EventOrdering} e1 e2 e c1 c2 Q R H :=
    MkRule1
      (fun e' =>
         [⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TDISS_OWN t1 @ e1,
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2])
      (⟬Q ++ (u ⋈ e1 ⋄ e2) :: R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred2_true :
    forall u t1 t2 {eo : EventOrdering} e1 e2 e c1 c2 Q R H,
      rule_true (DERIVED_RULE_generates_trusted_kc_id_increases_direct_pred2 u t1 t2 e1 e2 e c1 c2 Q R H).
  Proof.
    start_proving_derived st.

    inst_hyp e1 sta; inst_hyp e2 stb; clear st1; GC.

    apply (PRIMITIVE_RULE_cut_true "hida" (KE_TRUST_HAS_ID t1 c1 @ e1)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "hidb" (KE_TRUST_HAS_ID t2 c2 @ e2)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    apply (PRIMITIVE_RULE_cut_true "disa" (KE_TDISS_OWN t1 @ e1)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    apply (PRIMITIVE_RULE_cut_true "disb" (KE_TDISS_OWN t2 @ e2)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    apply (PRIMITIVE_RULE_cut_true "betweena" (KE_EX_ID_BETWEEN c1 @ e1)); simseqs j.
    { apply (DERIVED_RULE_disseminate_implies_id_true t1); simseqs j;
        try (complete (repeat (apply DERIVED_RULE_thin_last_true; simseqs j))). }
    LOCKelim "betweena".
    LOCKelim "betweena".
    LOCKelim "betweena" "betweena1".
    LOCKelim "betweena" "betweena2".
    LOCKelim "betweena" "betweena3".
    LOCKelim "betweena" "betweena4".

    apply (PRIMITIVE_RULE_cut_true "betweenb" (KE_EX_ID_BETWEEN c2 @ e2)); simseqs j.
    { apply (DERIVED_RULE_disseminate_implies_id_true t2); simseqs j;
        try (complete (repeat (apply DERIVED_RULE_thin_last_true; simseqs j))). }
    LOCKelim "betweenb".
    LOCKelim "betweenb".
    LOCKelim "betweenb" "betweenb1".
    LOCKelim "betweenb" "betweenb2".
    LOCKelim "betweenb" "betweenb3".
    LOCKelim "betweenb" "betweenb4".

    apply (PRIMITIVE_RULE_cut_true "id" (KE_ID_AFTER c3 @ e1)); simseqs j.
    { apply DERIVED_RULE_id_before_is_id_after_true; simseqs j.
      norm_with "betweenb1"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb1"); simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "p" (KE_ID_EQ c3 c0 @ e)); simseqs j.
    { apply (PRIMITIVE_RULE_id_eq_change_event_true _ e1); simseqs j.
      apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
      { norm_with "id"; apply (PRIMITIVE_RULE_hypothesis_true "id"); simseqs j. }
      norm_with "betweena2"; apply (PRIMITIVE_RULE_hypothesis_true "betweena2"); simseqs j. }

    apply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c0); simseqs j.
    { apply (DERIVED_RULE_id_le_change_event_true _ e1); simseqs j.
      norm_with "betweena4"; apply (PRIMITIVE_RULE_hypothesis_true "betweena4"); simseqs j. }
    apply (PRIMITIVE_RULE_id_lt_trans_eq_lt_true c3); simseqs j.
    { apply PRIMITIVE_RULE_id_eq_sym_true; simseqs j.
      norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }
    apply (PRIMITIVE_RULE_id_lt_change_event_true _ e2); simseqs j.
    norm_with "betweenb3"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb3"); simseqs j.
  Qed.


  (*Lemma generates_trusted_kc_id_increases_direct_pred2 :
    forall {eo : EventOrdering} (e1 e2 : Event) (t1 t2 : kc_trust),
      e1 ⊂ e2 (* this implies that the events have the same location *)
      -> generates_trusted e1 t1
      -> generates_trusted e2 t2
      -> kc_id t1 < kc_id t2.
  Proof.
    introv dp gt1 gt2.
    apply generates_trusted_implies_id_after in gt1.
    eapply generates_trusted_kc_id_increases_direct_pred; eauto.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_no_trusted_generation_implies_id_after {eo : EventOrdering} e R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_NO_TGENS @ e]
      (⟬R⟭ H ⊢ KE_EX_ID (fun c => KE_ID_AFTER c) @ e).

  Lemma DERIVED_RULE_no_trusted_generation_implies_id_after_true :
    forall {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_no_trusted_generation_implies_id_after e R H).
  Proof.
    start_proving_derived st.
    LOCKcut "x" (KE_NO_TGENS @ e).
    Transparent KE_NO_TGENS.
    LOCKelim "x".
    Opaque KE_NO_TGENS.
    LOCKelim "x" "y".
    LOCKelim "x" "z".
    LOCKintro c; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_split_local_before_eq_hyp x {eo : EventOrdering} e R H J a b :=
    MkRule0
      [⟬R⟭ H • (x › a @ e) » J ⊢ b,
       ⟬R⟭ H • (x › KE_LOCAL_BEFORE_EQ a @ local_pred_n e) » J ⊢ b]
      (⟬R⟭ H • (x › KE_LOCAL_BEFORE_EQ a @ e) » J ⊢ b).

  Lemma DERIVED_RULE_split_local_before_hyp_true :
    forall x {eo : EventOrdering} e R H J a b,
      rule_true (DERIVED_RULE_split_local_before_eq_hyp x e R H J a b).
  Proof.
    start_proving_derived st.
    apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u"); simseqs j.
    causal_norm_with "u"; apply DERIVED_RULE_split_local_before_eq_true; simseqs j.
    { causal_norm_with "u"; apply PRIMITIVE_RULE_subst_causal_eq_hyp_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
    apply DERIVED_RULE_relocal_before_eq_hyp_true; simseqs j.
  Qed.


  (************************************************************************************************)
  Definition ID_INCREASES c1 :=
    KE_IMPLIES
      (KE_LOCAL_BEFORE_EQ (KE_ID_AFTER c1))
      (KE_ALL_ID (fun c2 =>
                    KE_IMPLIES
                      (KE_ID_AFTER c2)
                      (KE_ID_LE c1 c2))).

  Definition DERIVED_RULE_id_after_increases0 {eo : EventOrdering} e c1 R H :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e'])
      (⟬R⟭ H ⊢ ID_INCREASES c1 @ e).

  Lemma DERIVED_RULE_id_after_increases0_true :
    forall {eo : EventOrdering} e c1 R H,
      rule_true (DERIVED_RULE_id_after_increases0 e c1 R H).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_pred_eq_induction_true; simseqs j.

    { apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
      apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.
      apply PRIMITIVE_RULE_all_id_intro_true; simseqs j.
      rename c into c2.
      apply (PRIMITIVE_RULE_implies_intro_true "z"); simseqs j.
      norm_with "y"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "y"); simseqs j.
      apply DERIVED_RULE_causalle_is_equal_if_first_true; simseqs j.
      { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      causal_norm_with "u"; norm_with "y"; apply (PRIMITIVE_RULE_subst_causal_eq_hyp_true "u" "y"); simseqs j.
      apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }

    apply (PRIMITIVE_RULE_implies_intro_true "nf"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "rb"); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "lb"); simseqs j.
    apply PRIMITIVE_RULE_all_id_intro_true; simseqs j.
    rename c into c2.
    apply (PRIMITIVE_RULE_implies_intro_true "ca"); simseqs j.
    norm_with "rb"; apply (DERIVED_RULE_unright_before_eq_hyp_true "rb"); simseqs j.
    norm_with "lb"; apply DERIVED_RULE_split_local_before_hyp_true; simseqs j.

    { apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
      { norm_with "lb"; apply (PRIMITIVE_RULE_hypothesis_true "lb"); simseqs j. }
      norm_with "ca"; apply (PRIMITIVE_RULE_hypothesis_true "ca"); simseqs j. }

    norm_with "rb"; apply (PRIMITIVE_RULE_implies_elim_true "rb"); simseqs j.
    { norm_with "lb"; apply (PRIMITIVE_RULE_hypothesis_true "lb"); simseqs j. }

    inst_hyp e0 st.
    apply (PRIMITIVE_RULE_cut_true "mon" (ASSUMPTION_monotonicity @ e0)); simseqs j.
    { repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    apply (DERIVED_RULE_or_elim_true "mon"); simseqs j.

    { Transparent KE_NO_TGENS.
      LOCKelim "mon".
      Opaque KE_NO_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".
      apply (PRIMITIVE_RULE_cut_true "mon" (KE_ID_EQ c2 c @ e0)); simseqs j.
      { apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
        { norm_with "ca"; apply (PRIMITIVE_RULE_hypothesis_true "ca"); simseqs j. }
        norm_with "mon2"; apply (PRIMITIVE_RULE_hypothesis_true "mon2"); simseqs j. }
      norm_with "rb"; apply (PRIMITIVE_RULE_all_id_elim_true "rb" c); simseqs j.
      norm_with "rb"; apply (PRIMITIVE_RULE_implies_elim_true "rb"); simseqs j.
      { apply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e0); simseqs j.
        { norm_with "nf"; apply (PRIMITIVE_RULE_hypothesis_true "nf"); simseqs j. }
        causal_norm_with "u"; apply DERIVED_RULE_id_before_is_id_after_true; simseqs j.
        norm_with "mon1"; apply (PRIMITIVE_RULE_hypothesis_true "mon1"); simseqs j. }
      apply (DERIVED_RULE_id_le_trans_true c); simseqs j.
      { apply (DERIVED_RULE_id_le_change_event_true _ (local_pred_n e0)); simseqs j.
        norm_with "rb"; apply (PRIMITIVE_RULE_hypothesis_true "rb"); simseqs j. }
      apply PRIMITIVE_RULE_or_intro_right_true; simseqs j.
      apply PRIMITIVE_RULE_id_eq_sym_true; simseqs j.
      norm_with "mon"; apply (PRIMITIVE_RULE_hypothesis_true "mon"); simseqs j. }

    { Transparent KE_TGENS.
      LOCKelim "mon".
      LOCKelim "mon".
      Opaque KE_TGENS.
      LOCKelim "mon" "mon0".
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".
      apply (PRIMITIVE_RULE_cut_true "mon" (KE_ID_EQ c2 c0 @ e0)); simseqs j.
      { apply PRIMITIVE_RULE_ids_after_imply_eq_ids_true; simseqs j.
        { norm_with "ca"; apply (PRIMITIVE_RULE_hypothesis_true "ca"); simseqs j. }
        norm_with "mon2"; apply (PRIMITIVE_RULE_hypothesis_true "mon2"); simseqs j. }
      norm_with "rb"; apply (PRIMITIVE_RULE_all_id_elim_true "rb" c); simseqs j.
      norm_with "rb"; apply (PRIMITIVE_RULE_implies_elim_true "rb"); simseqs j.
      { apply (PRIMITIVE_RULE_introduce_direct_pred_true "u" e0); simseqs j.
        { norm_with "nf"; apply (PRIMITIVE_RULE_hypothesis_true "nf"); simseqs j. }
        causal_norm_with "u"; apply DERIVED_RULE_id_before_is_id_after_true; simseqs j.
        norm_with "mon1"; apply (PRIMITIVE_RULE_hypothesis_true "mon1"); simseqs j. }
      apply (DERIVED_RULE_id_le_trans_true c); simseqs j.
      { apply (DERIVED_RULE_id_le_change_event_true _ (local_pred_n e0)); simseqs j.
        norm_with "rb"; apply (PRIMITIVE_RULE_hypothesis_true "rb"); simseqs j. }
      apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
      apply (PRIMITIVE_RULE_id_lt_trans_lt_eq_true c0); simseqs j.
      { norm_with "mon0"; apply (PRIMITIVE_RULE_hypothesis_true "mon0"); simseqs j. }
      apply (PRIMITIVE_RULE_id_eq_sym_true); simseqs j.
      norm_with "mon"; apply (PRIMITIVE_RULE_hypothesis_true "mon"); simseqs j. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_after_increases u {eo : EventOrdering} e1 e2 e c1 c2 R H :=
    MkRule1
      (fun e' =>
         [⟬(u ⋈ e1 ■ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬(u ⋈ e1 ■ e2) :: R⟭ H ⊢ KE_ID_AFTER c1 @ e1,
          ⟬(u ⋈ e1 ■ e2) :: R⟭ H ⊢ KE_ID_AFTER c2 @ e2])
      (⟬(u ⋈ e1 ■ e2) :: R⟭ H ⊢ KE_ID_LE c1 c2 @ e).

  Lemma DERIVED_RULE_id_after_increases_true :
    forall u {eo : EventOrdering} e1 e2 e c1 c2 R H,
      rule_true (DERIVED_RULE_id_after_increases u e1 e2 e c1 c2 R H).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (ID_INCREASES c1 @ e2)); simseqs j.
    { apply DERIVED_RULE_id_after_increases0_true; simseqs j.
      inst_hyp e0 st. }

    inst_hyp e1 st.

    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { causal_norm_with u; apply DERIVED_RULE_unlocal_before_eq_if_causalle_true; simseqs j. }
    norm_with "x"; apply (PRIMITIVE_RULE_all_id_elim_true "x" c2); simseqs j.

    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    apply (DERIVED_RULE_id_le_change_event_true _ e2); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_id_after_increases2 u {eo : EventOrdering} e1 e2 e c1 c2 R H :=
    MkRule1
      (fun e' =>
         [⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_ID_AFTER c1 @ e1,
          ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_ID_BEFORE c2 @ e2])
      (⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_ID_LE c1 c2 @ e).

  Lemma DERIVED_RULE_id_after_increases2_true :
    forall u {eo : EventOrdering} e1 e2 e c1 c2 R H,
      rule_true (DERIVED_RULE_id_after_increases2 u e1 e2 e c1 c2 R H).
  Proof.
    start_proving_derived st.
    inst_hyp e2 sta.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_ID_AFTER c1 @ e1)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "y" (KE_ID_BEFORE c2 @ e2)); simseqs j.
    { apply DERIVED_RULE_thin_last_true; simseqs j. }
    causal_norm_with u; apply (PRIMITIVE_RULE_split_local_before2_true u "v" "w"); simseqs j.
    causal_norm_with "v"; apply (DERIVED_RULE_id_after_increases_true "v"); simseqs j.
    { inst_hyp e0 st.
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j).
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j). }
    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
    causal_norm_with "w"; apply (DERIVED_RULE_id_before_is_id_after_true "w"); simseqs j.
    norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j.
  Qed.

  (*Lemma id_after_increases :
    forall {eo : EventOrdering} e1 e2 c1 c2,
      ex_node_e e2
      -> monotonicity eo
      -> e1 ⊑ e2
      -> id_after e2 c2
      -> id_after e1 c1
      -> c1 <= c2.
  Proof.
    introv exe mon lte sbe2 sbe1.

    revert dependent c2.
    revert dependent e2.

    induction e2 as [e2 ind] using predHappenedBeforeInd.
    introv exe lte sbe2.

    applydup @localHappenedBeforeLe_implies_or in lte; repndors; subst; eq_states; tcsp;[].

    destruct (dec_isFirst e2) as [d|d]; ginv; simpl in *;[|].

    { apply isFirst_localHappenedBeforeLe_implies_eq in lte; subst; auto; eq_states; auto. }

    pose proof (ind (local_pred e2)) as ind; repeat (autodimp ind hyp); eauto 3 with eo kn;[].

    pose proof (mon e2) as mon; repeat (autodimp mon hyp);[].
    repndors; exrepnd;[|].

    {
      unfold no_trusted_generation in *; exrepnd; eq_states.
      apply id_before_implies_id_after in mon1; auto.
    }

    {
      unfold generates_trusted in *; exrepnd; eq_states.
      apply id_before_implies_id_after in mon0; auto.
    }
  Qed.*)


(*  (************************************************************************************************)
  Definition DERIVED_RULE_tgens_implies_has_id {eo : EventOrdering} e R H t :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TGENS t @ e]
      (⟬R⟭ H ⊢ KE_EX_ID (fun c => KE_AND (KE_TRUST_HAS_ID t c) (KE_ID_AFTER c)) @ e).

  Lemma DERIVED_RULE_tgens_implies_has_id_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_tgens_implies_has_id e R H t).
  Proof.
    introv st; simpl in *; simpl_sem_rule; dLin_hyp st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TGENS t @ e)); simseqs j.
    clear st0.
    Transparent KE_TGENS.
    norm_with "x"; apply (PRIMITIVE_RULE_unexists_id_true "x"); simseqs j.
    Opaque KE_TGENS.
    norm_with "x"; apply (PRIMITIVE_RULE_unexists_id_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "z"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "w"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "u"); simseqs j.
    apply (PRIMITIVE_RULE_exists_id_intro_true h0); simseqs j.
    apply PRIMITIVE_RULE_and_intro_true; simseqs j.
    { norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
    norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_kc_id_increases_strict_before
             u t1 t2 {eo : EventOrdering} e1 e2 e c1 c2 R H :=
    MkRule1
      (fun e' => [⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_generates_new @ e',
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TDISS_OWN t1 @ e1,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2])
      (⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_true :
    forall u t1 t2 {eo : EventOrdering} e1 e2 e c1 c2 R H,
      rule_true (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before u t1 t2 e1 e2 e c1 c2 R H).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "betweena" (KE_EX_ID_BETWEEN c1 @ e1)); simseqs j.
    { inst_hyp e1 sta.
      apply (DERIVED_RULE_disseminate_implies_id_true t1); simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "betweenb" (KE_EX_ID_BETWEEN c2 @ e2)); simseqs j.
    { inst_hyp e2 stb.
      apply DERIVED_RULE_thin_last_true; simseqs j.
      apply (DERIVED_RULE_disseminate_implies_id_true t2); simseqs j. }

    LOCKelim "betweena".
    LOCKelim "betweena".
    LOCKelim "betweena" "betweena1".
    LOCKelim "betweena" "betweena2".
    LOCKelim "betweena" "betweena3".
    LOCKelim "betweena" "betweena4".

    LOCKelim "betweenb".
    LOCKelim "betweenb".
    LOCKelim "betweenb" "betweenb1".
    LOCKelim "betweenb" "betweenb2".
    LOCKelim "betweenb" "betweenb3".
    LOCKelim "betweenb" "betweenb4".

    apply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c0); simseqs j.
    { apply (DERIVED_RULE_id_le_change_event_true _ e1); simseqs j.
      norm_with "betweena4"; apply (PRIMITIVE_RULE_hypothesis_true "betweena4"); simseqs j. }

    apply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c3); simseqs j.
    { apply (DERIVED_RULE_id_after_increases2_true u); simseqs j.
      { inst_hyp e0 sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "betweena2"; apply (PRIMITIVE_RULE_hypothesis_true "betweena2"); simseqs j. }
      norm_with "betweenb1"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb1"); simseqs j. }

    apply (PRIMITIVE_RULE_id_lt_change_event_true _ e2); simseqs j.
    norm_with "betweenb3"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb3"); simseqs j.
  Qed.


  (*Lemma generates_trusted_kc_id_increases_strict_before :
    forall {eo : EventOrdering} (e1 e2 : Event) (t1 t2 : kc_trust),
      ex_node_e e2
      -> monotonicity eo
      -> e1 ⊏ e2  (* this implies that the location is same *)
      -> generates_trusted e2 t2
      -> generates_trusted e1 t1 (* This could be replaced by [id_after] *)
      -> kc_id t1 < kc_id t2.
  Proof.
    introv exe mon lte gen2 gen1.

    apply local_implies_pred_or_local in lte; repndors; exrepnd;[|].

    { eapply generates_trusted_kc_id_increases_direct_pred2; eauto. }

    dup lte1 as lteb.
    pose proof (mon e) as q; repeat (autodimp q hyp); eauto 3 with eo kn; repndors; exrepnd;[|].

    { apply no_trusted_generation_implies_id_after in q; exrepnd.
      eapply generates_trusted_kc_id_increases_direct_pred in lte1;
        try exact q0; try exact gen2.
      apply generates_trusted_implies_id_after in gen1.
      eapply id_after_increases in gen1; try exact q0; eauto 3 with eo kn; try omega. }

    { eapply generates_trusted_kc_id_increases_direct_pred2 in lte1;
        try exact q0; try exact gen2.
      pose proof (generates_trusted_kc_id_increases e1 e t1 t) as h.
      repeat (autodimp h hyp); eauto 3 with eo kn; try omega. }
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_same_output_before_implies_false t1 t2 c1 c2 {eo : EventOrdering} e R H :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_same_output_before_implies_false t1 t2 c1 c2 @ e).

  Lemma DERIVED_RULE_same_output_before_implies_false_true :
    forall t1 t2 c1 c2 {eo : EventOrdering} e R H,
      rule_true (DERIVED_RULE_same_output_before_implies_false t1 t2 c1 c2 e R H).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "z"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "w"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "p"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "q"); simseqs j.
    norm_with "z"; apply (DERIVED_RULE_unlocal_before_hyp_true "u" "z"); simseqs j.

    apply (PRIMITIVE_RULE_cut_true "lt" (KE_ID_LT c1 c2 @ e)); simseqs j.
    { causal_norm_with "u"; apply (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_true "u" t1 t2); simseqs j.
      { inst_hyp e1 st.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { inst_hyp e1 st.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      { apply (PRIMITIVE_RULE_has_id_change_event_true _ e); simseqs j.
        norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
      norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }

    LOCKcut "lt" (KE_ID_LT c1 c1 @ e); try LOCKauto.
    LOCKapply (PRIMITIVE_RULE_id_lt_trans_lt_eq_true c2); try LOCKauto.
    LOCKapply PRIMITIVE_RULE_id_eq_sym_true; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_same_event_same_output_implies_same_input {eo : EventOrdering} e R H t1 t2 c1 c2 :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_same_event_same_output_implies_same_input t1 t2 c1 c2 @ e).

  Lemma DERIVED_RULE_same_event_same_output_implies_same_input_true :
    forall {eo : EventOrdering} e R H t1 t2 c1 c2,
      rule_true (DERIVED_RULE_same_event_same_output_implies_same_input e R H t1 t2 c1 c2).
  Proof.
    start_proving_derived st.
    LOCKapply (PRIMITIVE_RULE_implies_intro_true "x").
    LOCKelim "x" "y".
    LOCKelim "x" "z".
    LOCKelim "x" "w".
    LOCKelim "x" "p".
    LOCKelim "x" "q".

    LOCKelim "z".
    { LOCKapply (PRIMITIVE_RULE_cut_true "ass" (ASSUMPTION_same_output_before_implies_false t1 t2 c1 c2 @ e)).
      { repeat LOCKclear.
        LOCKapply DERIVED_RULE_same_output_before_implies_false_true; inst_hyp e0 st. }
      LOCKapply@ "ass" PRIMITIVE_RULE_implies_elim_true; try LOCKauto.
      repeat (LOCKintro; try LOCKauto). }

    apply (PRIMITIVE_RULE_unicity_true c1 c2); simseqs j; try LOCKauto.
    { inst_hyp e st; repeat LOCKclear. }
    LOCKelim "z" "u"; try LOCKauto.
  Qed.


(*  (* NOT USED *)
  (************************************************************************************************)
  Definition DERIVED_RULE_TGEN_MONOTONICITY_local_trusted_component_strictly_less {eo : EventOrdering} e R H t1 t2 c1 c2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ KE_TGENS t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE (KE_TGENS t1) @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e])
      (⟬R⟭ H ⊢ KE_ID_LT c1 c2 @ e).

  Lemma DERIVED_RULE_TGEN_MONOTONICITY_local_trusted_component_strictly_less_true :
    forall {eo : EventOrdering} e R H t1 t2 c1 c2,
      rule_true (DERIVED_RULE_TGEN_MONOTONICITY_local_trusted_component_strictly_less e R H t1 t2 c1 c2).
  Proof.
    start_proving_derived st.

    pose proof (st (mk_v1 e)) as st'; simpl_sem_rule; dLin_hyp st'; simpl in *.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_LOCAL_BEFORE (KE_TGENS t1) @ e)); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_unlocal_before_hyp_true "x"); simseqs j.

    apply (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_true "x" t1 t2 h e); simseqs j;
      try (complete (apply DERIVED_RULE_remove_first_causal_true; simseqs j;
                     apply DERIVED_RULE_thin_last_true; simseqs j)).

    { apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      apply DERIVED_RULE_thin_last_true; simseqs j.
      pose proof (st (mk_v1 h0)) as st; simpl_sem_rule; dLin_hyp st; simpl in *; auto. }

    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_same_id_before_implies_false c1 c2 {eo : EventOrdering} e R H t1 t2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE (KE_TDISS_OWN t1) @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e])
      (⟬R⟭ H ⊢ KE_FALSE @ e).

  Lemma DERIVED_RULE_same_id_before_implies_false_true :
    forall c1 c2 {eo : EventOrdering} e R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_same_id_before_implies_false c1 c2 e R H t1 t2).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    inst_hyp e st'.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_same_output_before_implies_false t1 t2 c1 c2 @ e)); simseqs j.
    { apply DERIVED_RULE_same_output_before_implies_false_true; simseqs j;
        inst_hyp e0 st. }

    apply DERIVED_RULE_implies_elim_true; simseqs j; repeat LOCKintro; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_same_input_if_same_id c1 c2 {eo : EventOrdering} e R H t1 t2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_TDISS_OWN t1) @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma DERIVED_RULE_trusted_same_input_if_same_id_true :
    forall c1 c2 {eo : EventOrdering} e R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_trusted_same_input_if_same_id c1 c2 e R H t1 t2).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    inst_hyp e st'.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_same_event_same_output_implies_same_input t1 t2 c1 c2 @ e)); simseqs j.
    { apply DERIVED_RULE_same_event_same_output_implies_same_input_true; simseqs j;
        inst_hyp e0 st. }

    apply DERIVED_RULE_implies_elim_true; simseqs j; try LOCKauto.
    repeat (LOCKintro;[]); LOCKauto.
  Qed.


(*
(* NOT USED *)

  (************************************************************************************************)
  Lemma OLD_RULE_trusted_same_input_if_same_id_true_from_mon :
    forall {eo : EventOrdering} (t' t'' : kc_trust),
      assume_eo eo (ASSUMPTION_monotonicity)
      -> rule_true_eo eo (OLD_RULE_trusted_same_input_if_same_id t' t'').
  Proof.
    introv mon exe ht h; simpl in *.
    dLin_hyp h.
    unfold sequent_true_at_event in *; simpl in *.
    autodimp h0 hyp; tcsp.
    autodimp h1 hyp; tcsp.
    autodimp h2 hyp; tcsp.
    simpl in *.
    exrepnd.

    eapply localHappenedBeforeLe_implies_or2 in h1; repndors; subst.

    { eapply generates_trusted_unique in h0; try exact h3; subst; auto. }

    apply (OLD_RULE_TGEN_MONOTONICITY_local_trusted_component_strictly_less_true t' t'') in mon.

    pose proof (mon e) as mon; simpl in mon; autodimp mon hyp.
    unfold rule_true_at_event in mon; simpl in *.
    repeat (autodimp mon hyp); eauto 3 with kn;
      try (complete (unfold sequent_true_at_event in *; simpl in *;
                     autodimp mon hyp; tcsp; omega)).
    introv q ht; repndors; tcsp; subst; simpl; auto.
    exists e'; dands; auto.
  Qed.*)


  (************************************************************************************************)
  Definition DERIVED_RULE_tgens_implies_towns {eo : EventOrdering} e R H t :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TDISS_OWN t @ e]
      (⟬R⟭ H ⊢ KE_TOWNS t @ e).

  Lemma DERIVED_RULE_tgens_implies_towns_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_tgens_implies_towns e R H t).
  Proof.
    introv st; simpl in *; simpl_sem_rule; dLin_hyp st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TDISS_OWN t @ e)); simseqs j.
    clear st0.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_disseminate_unique
             c1 c2 n {eo : EventOrdering} e1 e2 R H (t1 t2 : kc_trust) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t1 @ e1,
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
          ⟬R⟭ H ⊢ KE_AT n @ e1,
          ⟬R⟭ H ⊢ KE_AT n @ e2,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e2])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e2).

  Lemma DERIVED_RULE_trusted_disseminate_unique_true :
    forall c1 c2 n {eo : EventOrdering} e1 e2 R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_trusted_disseminate_unique c1 c2 n e1 e2 R H t1 t2).
  Proof.
    introv st; simpl in *; simpl_sem_rule.
    inst_hyp e1 st'.

    apply (PRIMITIVE_RULE_tri_if_towned_true "u" n e1 e2); simseqs j.

    { (* e1 = e2 *)
      apply (DERIVED_RULE_trusted_same_input_if_same_id_true c1 c2); simseqs j;
      try (complete (inst_hyp e st; apply DERIVED_RULE_remove_first_causal_true; simseqs j)).

      inst_hyp e st.
      apply DERIVED_RULE_weaken_local_before_eq_true; simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

    { (* (e1) ⊏ (e2) *)
      apply (PRIMITIVE_RULE_cut_true "x" (KE_FALSE @ e2)); simseqs j; try LOCKauto.
      apply (DERIVED_RULE_same_id_before_implies_false_true c1 c2 _ _ _ t1 t2); simseqs j;
        try (complete (apply DERIVED_RULE_remove_first_causal_true; simseqs j; inst_hyp e st)).
      causal_norm_with "u"; apply DERIVED_RULE_unlocal_before_if_causal_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

    { (* (e2) ⊏ (e1) *)
      apply PRIMITIVE_RULE_trust_eq_sym_true; simseqs j.
      apply (PRIMITIVE_RULE_trust_eq_change_event_true e2 e1); simseqs j.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_FALSE @ e1)); simseqs j; try LOCKauto.
      apply (DERIVED_RULE_same_id_before_implies_false_true c2 c1 _ _ _ t2 t1); simseqs j;
        try (complete (apply DERIVED_RULE_remove_first_causal_true; simseqs j; inst_hyp e st)).
      { causal_norm_with "u"; apply DERIVED_RULE_unlocal_before_if_causal_true; simseqs j.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
      apply PRIMITIVE_RULE_id_eq_sym_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_knows_implies_learned_or_gen_implies_gen {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_learns_if_gen d @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_knows_implies_learned_or_gen d @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_knows_implies_gen d @ e).

  Lemma DERIVED_RULE_knows_implies_learned_or_gen_implies_gen_true :
    forall (eo : EventOrdering) e R H d,
      rule_true (DERIVED_RULE_knows_implies_learned_or_gen_implies_gen e R H d).
  Proof.
    start_proving_derived st.
    inst_hyp e st'.

    apply (PRIMITIVE_RULE_cut_true "a" (ASSUMPTION_knows_implies_learned_or_gen d @ e)); simseqs j.
    apply (PRIMITIVE_RULE_implies_intro_true "kn"); simseqs j.
    norm_with "a"; apply (PRIMITIVE_RULE_implies_elim_true "a"); simseqs j.
    { norm_with "kn"; apply (PRIMITIVE_RULE_hypothesis_true "kn"); simseqs j. }

    norm_with "a"; apply (PRIMITIVE_RULE_or_elim_true "a"); simseqs j.

    { norm_with "a"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "a"); simseqs j.
      inst_hyp e0 st.
      apply (PRIMITIVE_RULE_cut_true "b" (ASSUMPTION_learns_if_gen d @ e0)); simseqs j.
      { apply DERIVED_RULE_remove_first_causal_true; simseqs j.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      norm_with "b"; apply (PRIMITIVE_RULE_implies_elim_true "b"); simseqs j.
      { norm_with "a"; apply (PRIMITIVE_RULE_hypothesis_true "a"); simseqs j. }
      norm_with "b"; apply (PRIMITIVE_RULE_unhappened_before_hyp_true "v" "b"); simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
      causal_norm_with "u"; apply DERIVED_RULE_unhappened_before_eq_if_causalle_trans_true; simseqs j.
      causal_norm_with "v"; apply PRIMITIVE_RULE_causal_if_causalle_true; simseqs j.
      causal_norm_with "v"; apply DERIVED_RULE_unhappened_before_eq_if_causalle_true; simseqs j.
      norm_with "b"; apply (PRIMITIVE_RULE_hypothesis_true "b"); simseqs j. }

    norm_with "a"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u"); simseqs j.
    causal_norm_with "u"; apply PRIMITIVE_RULE_localle_if_causalle_true; simseqs j.
    causal_norm_with "u"; apply DERIVED_RULE_unhappened_before_eq_if_causalle_true; simseqs j.
    norm_with "a"; apply (PRIMITIVE_RULE_hypothesis_true "a"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_knows_implies_learned_or_gen_implies_gen {eo : EventOrdering} e R H t :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_if_gen t @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_learned_or_gen t @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_gen t @ e).

  Lemma DERIVED_RULE_trusted_knows_implies_learned_or_gen_implies_gen_true :
    forall (eo : EventOrdering) e R H t,
      rule_true (DERIVED_RULE_trusted_knows_implies_learned_or_gen_implies_gen e R H t).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_knows_implies_learned_or_gen_implies_gen_true; simseqs j;
      inst_hyp e0 st'.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_KLD_implies_or {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_knew_or_learns_or_gen d @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_knows_implies_learned_or_gen d @ e).

  Lemma DERIVED_RULE_KLD_implies_or_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_KLD_implies_or e R H d).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_pred_eq_induction_true; simseqs j.

    { inst_hyp e0 st'.
      apply (PRIMITIVE_RULE_cut_true "z" (ASSUMPTION_knew_or_learns_or_gen d @ e0)); simseqs j.
      apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
      apply (PRIMITIVE_RULE_implies_intro_true "y"); simseqs j.

      LOCKelim "z"; try LOCKauto.
      LOCKelim "z".
      { LOCKelim "x"; try LOCKauto.
        LOCKapply (DERIVED_RULE_knew_implies_not_first_true d); try LOCKauto. }
      LOCKelim "z".
      { LOCKintro 0.
        LOCKapply DERIVED_RULE_weaken_local_before_eq_true; try LOCKauto. }
      LOCKelim "z"; try LOCKauto.
      LOCKintro 1.
      LOCKapply DERIVED_RULE_weaken_local_before_eq_true; try LOCKauto. }

    inst_hyp e0 st'.
    LOCKcut "z" (ASSUMPTION_knew_or_learns_or_gen d @ e0).
    LOCKintro "x".
    LOCKintro "w".
    LOCKintro "y".

    LOCKelim "z"; try LOCKauto.

    LOCKelim "z".
    { LOCKapply@ "w" DERIVED_RULE_right_before_over_implies_hyp_true.
      LOCKelim "w".
      { LOCKapply DERIVED_RULE_knew_implies_knows_true; try LOCKauto. }
      LOCKapply@ "w" DERIVED_RULE_right_before_over_or_hyp_true.
      LOCKelim "w".
      { LOCKintro 0.
        LOCKapply DERIVED_RULE_right_before_local_before_eq_implies_true; try LOCKauto. }
      LOCKintro 1.
      LOCKapply DERIVED_RULE_right_before_local_before_eq_implies_true; try LOCKauto. }

    LOCKelim "z".
    { LOCKintro 0.
      LOCKapply DERIVED_RULE_weaken_local_before_eq_true; try LOCKauto. }

    LOCKelim "z"; try LOCKauto.
    { LOCKintro 1.
      LOCKapply DERIVED_RULE_weaken_local_before_eq_true; try LOCKauto. }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_KLD_implies_or {eo : EventOrdering} e R H t :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_trusted_knew_or_learns_or_gen t @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_learned_or_gen t @ e).

  Lemma DERIVED_RULE_trusted_KLD_implies_or_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_trusted_KLD_implies_or e R H t).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_KLD_implies_or_true; simseqs j; inst_hyp e0 st'.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_KLD_implies_gen {eo : EventOrdering} e R H d :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_learns_if_gen d @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_knew_or_learns_or_gen d @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_knows_implies_gen d @ e).

  Lemma DERIVED_RULE_KLD_implies_gen_true :
    forall {eo : EventOrdering} e R H d,
      rule_true (DERIVED_RULE_KLD_implies_gen e R H d).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_knows_implies_learned_or_gen_implies_gen_true; simseqs j.
    { inst_hyp e0 st. }
    apply DERIVED_RULE_KLD_implies_or_true; simseqs j.
    inst_hyp e1 st.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_KLD_implies_gen {eo : EventOrdering} e R H t :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_trusted_learns_if_gen t @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_trusted_knew_or_learns_or_gen t @ e'])
      (⟬R⟭ H ⊢ ASSUMPTION_trusted_knows_implies_gen t @ e).

  Lemma DERIVED_RULE_trusted_KLD_implies_gen_true :
    forall {eo : EventOrdering} e R H t,
      rule_true (DERIVED_RULE_trusted_KLD_implies_gen e R H t).
  Proof.
    start_proving_derived st.
    apply DERIVED_RULE_KLD_implies_gen_true; simseqs j; inst_hyp e0 st'.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_it_owns_tgens_implies_at t {eo : EventOrdering} e p R H :=
    MkRule0
      [⟬R⟭ H ⊢ KE_TDISS_OWN t @ e,
       ⟬R⟭ H ⊢ KE_HAS_TOWNER t p @ e]
      (⟬R⟭ H ⊢ KE_AT p @ e).

  Lemma DERIVED_RULE_it_owns_tgens_implies_at_true :
    forall t {eo : EventOrdering} e p R H,
      rule_true (DERIVED_RULE_it_owns_tgens_implies_at t e p R H).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "o" (KE_HAS_TOWNER t p @ e)); simseqs j.
    apply (PRIMITIVE_RULE_cut_true "x" (KE_TDISS_OWN t @ e)); simseqs j.
    { norm_with "o"; apply (PRIMITIVE_RULE_thin_true "o"); simseqs j. }
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "c"); simseqs j.
    apply (DERIVED_RULE_it_owns_owned_implies_at_true (kc_trust2data t)); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
    norm_with "o"; apply (PRIMITIVE_RULE_hypothesis_true "o"); simseqs j.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_knowledge_unique
             p c1 c2 {eo : EventOrdering} e1 e2 e R H t1 t2 :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ KE_TKNOWS t1 @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2 @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e,
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2 @ e])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique_true :
    forall p c1 c2 {eo : EventOrdering} e1 e2 e R H t1 t2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique p c1 c2 e1 e2 e R H t1 t2).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_trusted_knows_implies_gen t1 @ e1)); simseqs j.
    { apply DERIVED_RULE_trusted_KLD_implies_gen_true; simseqs j.
      { inst_hyp e0 st'.
        apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e0)); simseqs j.
        norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t1); simseqs j.
        norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      inst_hyp e0 st'.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e0)); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t1); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { inst_hyp e st'. }

    norm_with "x"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "u" "x"); simseqs j.

    apply (PRIMITIVE_RULE_cut_true "y" (ASSUMPTION_trusted_knows_implies_gen t2 @ e2)); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
      apply (DERIVED_RULE_remove_first_causal_true); simseqs j.
      apply DERIVED_RULE_trusted_KLD_implies_gen_true; simseqs j.
      { inst_hyp e3 st'.
        apply (PRIMITIVE_RULE_cut_true "y" (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e3)); simseqs j.
        norm_with "y"; apply (PRIMITIVE_RULE_all_trust_elim_true "y" t2); simseqs j.
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      inst_hyp e3 st'.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e3)); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t2); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "y"; apply (PRIMITIVE_RULE_implies_elim_true "y"); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
      apply (DERIVED_RULE_remove_first_causal_true); simseqs j.
      inst_hyp e st'. }

    norm_with "y"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "v" "y"); simseqs j.
    apply (PRIMITIVE_RULE_trust_eq_change_event_true e e3); simseqs j.
    apply (DERIVED_RULE_trusted_disseminate_unique_true c1 c2 p e0 e3); simseqs j;
      try (complete (repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j);
                     repeat (apply DERIVED_RULE_thin_last_true; simseqs j);
                     inst_hyp e4 st)).

    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

    { apply (DERIVED_RULE_it_owns_tgens_implies_at_true t1); simseqs j.
      { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      inst_hyp e3 st.
      apply (PRIMITIVE_RULE_has_owner_change_event_true _ e1); simseqs j.
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j).
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    { apply (DERIVED_RULE_it_owns_tgens_implies_at_true t2); simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      inst_hyp e4 st.
      apply (PRIMITIVE_RULE_has_owner_change_event_true _ e1); simseqs j.
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j).
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
  Qed.


  Definition DERIVED_RULE_trusted_knowledge_unique2
             {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e',
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TKNOWS t1           @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p     @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2           @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p     @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e2,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2    @ e,
          ⟬R⟭ H ⊢ KE_GEN_FOR d1 t1       @ e,
          ⟬R⟭ H ⊢ KE_GEN_FOR d2 t2       @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2  @ e])
      (⟬R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique2_true :
    forall (eo : EventOrdering) e1 e2 e R H p t1 t2 c1 c2 d1 d2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique2 e1 e2 e R H p t1 t2 c1 c2 d1 d2).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TRUST_EQ t1 t2 @ e)); simseqs j.
    { apply (DERIVED_RULE_trusted_knowledge_unique_true p c1 c2 e1 e2); simseqs j; inst_hyp e0 st. }

    apply (PRIMITIVE_RULE_collision_resistant_true t1 t2); simseqs j; try LOCKauto;
      norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j;
        inst_hyp e st.
  Qed.


  Definition DERIVED_RULE_trusted_knowledge_unique3
             {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e',
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TKNOWS t1           @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p     @ e1,
          ⟬R⟭ H ⊢ KE_GEN_FOR d1 t1       @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2           @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p     @ e2,
          ⟬R⟭ H ⊢ KE_GEN_FOR d2 t2       @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e2,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2         @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2  @ e])
      (⟬R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique3_true :
    forall {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique3 e1 e2 e R H p t1 t2 c1 c2 d1 d2).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TRUST_EQ t1 t2 @ e)); simseqs j.
    { apply (DERIVED_RULE_trusted_knowledge_unique_true p c1 c2 e1 e2); simseqs j; inst_hyp e0 st. }

    apply (PRIMITIVE_RULE_collision_resistant_true t1 t2); simseqs j; try LOCKauto;
      norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j;
        inst_hyp e st.
  Qed.


  (************************************************************************************************)
  Definition KE_EX_TRUST_BETWEEN t :=
    KE_EX_ID3 (fun i i1 i2 => KE_ANDS
                                [KE_ID_BEFORE i1,
                                 KE_ID_AFTER i2,
                                 KE_TRUST_HAS_ID t i,
                                 KE_TRUST_DOESNT_HAVE_ID t i1,
                                 KE_ID_LT i1 i,
                                 KE_ID_LE i i2]).

  Definition DERIVED_RULE_disseminate_implies_id_ex
             {eo : EventOrdering} e t R H :=
    MkRule0
      [⟬R⟭ H ⊢ ASSUMPTION_monotonicity @ e,
       ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex @ e,
       ⟬R⟭ H ⊢ KE_TDISS_OWN t @ e]
      (⟬R⟭ H ⊢ KE_EX_TRUST_BETWEEN t @ e).

  Lemma DERIVED_RULE_disseminate_implies_id_ex_true :
    forall {eo : EventOrdering} e t R H,
      rule_true (DERIVED_RULE_disseminate_implies_id_ex
                   e t R H).
  Proof.
    start_proving_derived st.
    LOCKcut "dis" (KE_TDISS_OWN t @ e).
    LOCKcut "new" (ASSUMPTION_generates_new_ex @ e).
    { repeat LOCKclear. }
    LOCKcut "mon" (ASSUMPTION_monotonicity @ e).
    { repeat LOCKclear. }

    LOCKelim "mon".

    { Transparent KE_NO_TGENS.
      LOCKelim "mon".
      Opaque KE_NO_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".

      LOCKelim "new" t.
      LOCKelim "new" c.
      LOCKelim "new" c.

      LOCKelim "new".
      { repeat (LOCKintro; try LOCKauto). }

      LOCKelim "new".
      LOCKelim "new" "new1".
      LOCKelim "new" "new2".
      LOCKelim "new" "new3".
      LOCKelim "new" "new4".

      LOCKcut "p" (KE_ID_LT c0 c0 @ e); try LOCKauto.
      LOCKapply (PRIMITIVE_RULE_id_lt_trans_le_lt_true c); try LOCKauto. }

    { Transparent KE_TGENS.
      LOCKelim "mon".
      LOCKelim "mon".
      Opaque KE_TGENS.
      LOCKelim "mon" "mon1".
      LOCKelim "mon" "mon2".
      LOCKelim "mon" "mon3".

      LOCKelim "new" t.
      LOCKelim "new" c.
      LOCKelim "new" c0.

      LOCKelim "new".
      { repeat (LOCKintro; try LOCKauto). }

      LOCKelim "new".
      LOCKelim "new" "new1".
      LOCKelim "new" "new2".
      LOCKelim "new" "new3".
      LOCKelim "new" "new4".

      LOCKintro c1.
      LOCKintro c.
      LOCKintro c0.

      repeat (LOCKintro; try LOCKauto). }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_ex
             u t1 t2 {eo : EventOrdering} e1 e2 e c R H :=
    MkRule1
      (fun e' => [⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_monotonicity     @ e',
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ ASSUMPTION_generates_new_ex @ e',
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TDISS_OWN t1        @ e1,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TDISS_OWN t2        @ e2,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t1 c   @ e1,
                  ⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_TRUST_HAS_ID t2 c   @ e2])
      (⟬(u ⋈ e1 □ e2) :: R⟭ H ⊢ KE_FALSE @ e).

  Lemma DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_ex_true :
    forall u t1 t2 {eo : EventOrdering} e1 e2 e c R H,
      rule_true (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_ex u t1 t2 e1 e2 e c R H).
  Proof.
    start_proving_derived st.

    LOCKcut "betweena" (KE_EX_TRUST_BETWEEN t1 @ e1).
    { inst_hyp e1 sta.
      apply DERIVED_RULE_disseminate_implies_id_ex_true; simseqs j. }

    LOCKcut "betweenb" (KE_EX_TRUST_BETWEEN t2 @ e2).
    { inst_hyp e2 stb.
      apply DERIVED_RULE_thin_last_true; simseqs j.
      apply DERIVED_RULE_disseminate_implies_id_ex_true; simseqs j. }

    LOCKelim "betweena".
    LOCKelim "betweena".
    LOCKelim "betweena".
    LOCKelim "betweena" "betweena1".
    LOCKelim "betweena" "betweena2".
    LOCKelim "betweena" "betweena3".
    LOCKelim "betweena" "betweena4".
    LOCKelim "betweena" "betweena5".
    LOCKelim "betweena" "betweena6".

    LOCKelim "betweenb".
    LOCKelim "betweenb".
    LOCKelim "betweenb".
    LOCKelim "betweenb" "betweenb1".
    LOCKelim "betweenb" "betweenb2".
    LOCKelim "betweenb" "betweenb3".
    LOCKelim "betweenb" "betweenb4".
    LOCKelim "betweenb" "betweenb5".
    LOCKelim "betweenb" "betweenb6".

    apply (PRIMITIVE_RULE_cut_true "ile1" (KE_ID_LE c2 c4 @ e1)); simseqs j.
    { apply (DERIVED_RULE_id_after_increases2_true u); simseqs j.
      { inst_hyp e0 sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "betweena2"; apply (PRIMITIVE_RULE_hypothesis_true "betweena2"); simseqs j. }
      norm_with "betweenb1"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb1"); simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "ile2" (KE_ID_LE c0 c4 @ e1)); simseqs j.
    { apply (DERIVED_RULE_id_le_trans_true c2); simseqs j.
      { norm_with "betweena6"; apply (PRIMITIVE_RULE_hypothesis_true "betweena6"); simseqs j. }
      norm_with "ile1"; apply (PRIMITIVE_RULE_hypothesis_true "ile1"); simseqs j. }

    apply (PRIMITIVE_RULE_cut_true "thi1" (KE_TRUST_HAS_ID t1 c3 @ e2)); simseqs j.
    { apply (PRIMITIVE_RULE_similar_trust_preserves_true t2 c); simseqs j.
      { apply (PRIMITIVE_RULE_similar_trust_change_event_true _ e); simseqs j.
        inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "betweenb3"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb3"); simseqs j. }
      { apply (PRIMITIVE_RULE_has_id_change_event_true _ e1); simseqs j.
        inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). } }

    apply (PRIMITIVE_RULE_cut_true "thi2" (KE_TRUST_HAS_ID t1 c4 @ e2)); simseqs j.
    { apply (PRIMITIVE_RULE_trust_has_id_preserves_true c0 c3); simseqs j.
      { apply (PRIMITIVE_RULE_has_id_change_event_true _ e1); simseqs j.
        norm_with "betweena3"; apply (PRIMITIVE_RULE_hypothesis_true "betweena3"); simseqs j. }
      { norm_with "thi1"; apply (PRIMITIVE_RULE_hypothesis_true "thi1"); simseqs j. }
      { apply (DERIVED_RULE_id_le_change_event_true _ e1); simseqs j.
        norm_with "ile2"; apply (PRIMITIVE_RULE_hypothesis_true "ile2"); simseqs j. }
      { apply PRIMITIVE_RULE_or_intro_left_true; simseqs j.
        norm_with "betweenb5"; apply (PRIMITIVE_RULE_hypothesis_true "betweenb5"); simseqs j. } }

    apply (PRIMITIVE_RULE_cut_true "thi3" (KE_TRUST_HAS_ID t2 c4 @ e2)); simseqs j.
    { apply (PRIMITIVE_RULE_similar_trust_preserves_true t1 c); simseqs j.
      { apply (PRIMITIVE_RULE_similar_trust_change_event_true _ e); simseqs j.
        apply PRIMITIVE_RULE_similar_trust_sym_true; simseqs j.
        inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "thi2"; apply (PRIMITIVE_RULE_hypothesis_true "thi2"); simseqs j. }
      { inst_hyp e sta.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). } }

    LOCKelim "betweenb4"; try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_same_event_same_output_implies_same_input_ex {eo : EventOrdering} e R H t1 t2 c1 c2 :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity       @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex   @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2        @ e])
      (⟬R⟭ H ⊢ ASSUMPTION_same_event_same_output_implies_same_input t1 t2 c1 c2 @ e).

  Lemma DERIVED_RULE_same_event_same_output_implies_same_input_ex_true :
    forall {eo : EventOrdering} e R H t1 t2 c1 c2,
      rule_true (DERIVED_RULE_same_event_same_output_implies_same_input_ex e R H t1 t2 c1 c2).
  Proof.
    start_proving_derived st.
    apply (PRIMITIVE_RULE_implies_intro_true "x"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "y"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "z"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "w"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "p"); simseqs j.
    norm_with "x"; apply (PRIMITIVE_RULE_and_elim_true "x" "q"); simseqs j.
    norm_with "z"; apply (DERIVED_RULE_unlocal_before_eq_hyp_true "u" "z"); simseqs j.
    causal_norm_with "u"; apply (PRIMITIVE_RULE_split_local_before_eq2_true "u"); simseqs j.

    { causal_norm_with "u"; norm_with "z"; apply (PRIMITIVE_RULE_subst_causal_eq_hyp_true "u" "z"); simseqs j.
      apply (PRIMITIVE_RULE_unicity_true c1 c2); simseqs j.
      { inst_hyp e st.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j.
        repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
      { norm_with "z"; apply (PRIMITIVE_RULE_hypothesis_true "z"); simseqs j. }
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      { norm_with "w"; apply (PRIMITIVE_RULE_hypothesis_true "w"); simseqs j. }
      { norm_with "p"; apply (PRIMITIVE_RULE_hypothesis_true "p"); simseqs j. }
      norm_with "q"; apply (PRIMITIVE_RULE_hypothesis_true "q"); simseqs j. }

    LOCKcut "false" (KE_FALSE @ e); try LOCKauto.
    LOCKapply@ "u" (DERIVED_RULE_generates_trusted_kc_id_increases_strict_before_ex_true "u" t1 t2 e0 e e c1); try LOCKauto.
    { inst_hyp e1 st.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    { inst_hyp e1 st.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    { inst_hyp e1 st.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j.
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
    { LOCKapply (PRIMITIVE_RULE_has_id_change_event_true e0 e); LOCKauto. }

    LOCKapply (PRIMITIVE_RULE_trust_has_id_subst_id_true c2); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_same_input_if_same_id_ex c1 c2 {eo : EventOrdering} e R H t1 t2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity       @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex   @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e,
          ⟬R⟭ H ⊢ KE_LOCAL_BEFORE_EQ (KE_TDISS_OWN t1) @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2    @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma DERIVED_RULE_trusted_same_input_if_same_id_ex_true :
    forall c1 c2 {eo : EventOrdering} e R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_trusted_same_input_if_same_id_ex c1 c2 e R H t1 t2).
  Proof.
    start_proving_derived st.
    inst_hyp e st'.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_same_event_same_output_implies_same_input t1 t2 c1 c2 @ e)); simseqs j.
    { apply DERIVED_RULE_same_event_same_output_implies_same_input_ex_true; simseqs j; inst_hyp e0 st. }

    apply DERIVED_RULE_implies_elim_true; simseqs j; try LOCKauto.
    repeat (apply PRIMITIVE_RULE_and_intro_true; simseqs j;[]); try LOCKauto.
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_disseminate_unique_ex
             c1 c2 n {eo : EventOrdering} e1 e2 R H (t1 t2 : kc_trust) :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ ASSUMPTION_monotonicity       @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex   @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique @ e',
          ⟬R⟭ H ⊢ KE_TDISS_OWN t1 @ e1,
          ⟬R⟭ H ⊢ KE_TDISS_OWN t2 @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
          ⟬R⟭ H ⊢ KE_AT n @ e1,
          ⟬R⟭ H ⊢ KE_AT n @ e2,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e2,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2    @ e2])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e2).

  Lemma DERIVED_RULE_trusted_disseminate_unique_ex_true :
    forall c1 c2 n {eo : EventOrdering} e1 e2 R H (t1 t2 : kc_trust),
      rule_true (DERIVED_RULE_trusted_disseminate_unique_ex c1 c2 n e1 e2 R H t1 t2).
  Proof.
    start_proving_derived st.
    inst_hyp e1 st'.

    apply (PRIMITIVE_RULE_tri_if_towned_true "u" n e1 e2); simseqs j.

    { (* e1 = e2 *)
      apply (DERIVED_RULE_trusted_same_input_if_same_id_ex_true c1 c2); simseqs j;
        try (complete (inst_hyp e st; apply DERIVED_RULE_remove_first_causal_true; simseqs j)).

      inst_hyp e st.
      apply DERIVED_RULE_weaken_local_before_eq_true; simseqs j.
      causal_norm_with "u"; apply PRIMITIVE_RULE_subst_causal_eq_concl_true; simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

    { (* (e1) ⊏ (e2) *)
      apply (DERIVED_RULE_trusted_same_input_if_same_id_ex_true c1 c2); simseqs j;
        try (complete (inst_hyp e st; apply DERIVED_RULE_remove_first_causal_true; simseqs j)).

      inst_hyp e st.
      causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causal_lt_true "u"); simseqs j.
      apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

    { (* (e2) ⊏ (e1) *)
      apply PRIMITIVE_RULE_trust_eq_sym_true; simseqs j.
      apply (PRIMITIVE_RULE_trust_eq_change_event_true e2 e1); simseqs j.
      apply (DERIVED_RULE_trusted_same_input_if_same_id_ex_true c2 c1); simseqs j;
        try (complete (inst_hyp e st; apply DERIVED_RULE_remove_first_causal_true; simseqs j)).

      { inst_hyp e st.
        causal_norm_with "u"; apply (DERIVED_RULE_unlocal_before_eq_if_causal_lt_true "u"); simseqs j.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j. }

      { inst_hyp e st.
        apply PRIMITIVE_RULE_id_eq_sym_true; simseqs j.
        apply (DERIVED_RULE_remove_first_causal_true); simseqs j. }

      { apply PRIMITIVE_RULE_similar_trust_sym_true; simseqs j.
        apply (PRIMITIVE_RULE_similar_trust_change_event_true _ e2); simseqs j.
        apply DERIVED_RULE_remove_first_causal_true; simseqs j. } }
  Qed.


  (************************************************************************************************)
  Definition DERIVED_RULE_trusted_knowledge_unique_ex
             p c1 c2 {eo : EventOrdering} e1 e2 e R H t1 t2 :=
    MkRule1
      (fun e =>
         [⟬R⟭ H ⊢ KE_TKNOWS t1          @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p    @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1 @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2          @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p    @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2 @ e2,
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e,
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen         @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity                               @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex                           @ e,
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique                         @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2                                @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2                                        @ e])
      (⟬R⟭ H ⊢ KE_TRUST_EQ t1 t2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique_ex_true :
    forall p c1 c2 {eo : EventOrdering} e1 e2 e R H t1 t2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique_ex p c1 c2 e1 e2 e R H t1 t2).
  Proof.
    start_proving_derived st.

    apply (PRIMITIVE_RULE_cut_true "x" (ASSUMPTION_trusted_knows_implies_gen t1 @ e1)); simseqs j.
    { apply DERIVED_RULE_trusted_KLD_implies_gen_true; simseqs j.
      { inst_hyp e0 st'.
        apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e0)); simseqs j.
        norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t1); simseqs j.
        norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      inst_hyp e0 st'.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e0)); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t1); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "x"; apply (PRIMITIVE_RULE_implies_elim_true "x"); simseqs j.
    { inst_hyp e st'. }

    norm_with "x"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "u" "x"); simseqs j.

    apply (PRIMITIVE_RULE_cut_true "y" (ASSUMPTION_trusted_knows_implies_gen t2 @ e2)); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
      apply (DERIVED_RULE_remove_first_causal_true); simseqs j.
      apply DERIVED_RULE_trusted_KLD_implies_gen_true; simseqs j.
      { inst_hyp e3 st'.
        apply (PRIMITIVE_RULE_cut_true "y" (KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen @ e3)); simseqs j.
        norm_with "y"; apply (PRIMITIVE_RULE_all_trust_elim_true "y" t2); simseqs j.
        norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      inst_hyp e3 st'.
      apply (PRIMITIVE_RULE_cut_true "x" (KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e3)); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_all_trust_elim_true "x" t2); simseqs j.
      norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    norm_with "y"; apply (PRIMITIVE_RULE_implies_elim_true "y"); simseqs j.
    { norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j.
      apply (DERIVED_RULE_remove_first_causal_true); simseqs j.
      inst_hyp e st'. }

    norm_with "y"; apply (DERIVED_RULE_unhappened_before_eq_hyp_true "v" "y"); simseqs j.
    apply (PRIMITIVE_RULE_trust_eq_change_event_true e e3); simseqs j.

    apply (DERIVED_RULE_trusted_disseminate_unique_ex_true c1 c2 p e0 e3); simseqs j;
      try (complete (repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j);
                     repeat (apply DERIVED_RULE_thin_last_true; simseqs j);
                     inst_hyp e4 st)).

    { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }

    { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }

    { apply (DERIVED_RULE_it_owns_tgens_implies_at_true t1); simseqs j.
      { norm_with "x"; apply (PRIMITIVE_RULE_hypothesis_true "x"); simseqs j. }
      inst_hyp e4 st.
      apply (PRIMITIVE_RULE_has_owner_change_event_true _ e1); simseqs j.
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j).
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }

    { apply (DERIVED_RULE_it_owns_tgens_implies_at_true t2); simseqs j.
      { norm_with "y"; apply (PRIMITIVE_RULE_hypothesis_true "y"); simseqs j. }
      inst_hyp e4 st.
      apply (PRIMITIVE_RULE_has_owner_change_event_true _ e1); simseqs j.
      repeat (apply DERIVED_RULE_remove_first_causal_true; simseqs j).
      repeat (apply DERIVED_RULE_thin_last_true; simseqs j). }
  Qed.

  Definition DERIVED_RULE_trusted_knowledge_unique2_ex
             {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen         @ e',
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity                               @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex                           @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique                         @ e',
          ⟬R⟭ H ⊢ KE_TKNOWS t1           @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p     @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2           @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p     @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e2,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2         @ e,
          ⟬R⟭ H ⊢ KE_GEN_FOR d1 t1       @ e,
          ⟬R⟭ H ⊢ KE_GEN_FOR d2 t2       @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2  @ e])
      (⟬R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique2_ex_true :
    forall (eo : EventOrdering) e1 e2 e R H p t1 t2 c1 c2 d1 d2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique2_ex e1 e2 e R H p t1 t2 c1 c2 d1 d2).
  Proof.
    introv st; simpl in *.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TRUST_EQ t1 t2 @ e)); simseqs j.
    { apply (DERIVED_RULE_trusted_knowledge_unique_ex_true p c1 c2 e1 e2); simseqs j;inst_hyp e0 st. }

    apply (PRIMITIVE_RULE_collision_resistant_true t1 t2); simseqs j; try LOCKauto;
      norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j;
        inst_hyp e st.
  Qed.

  Definition DERIVED_RULE_trusted_knowledge_unique3_ex
             {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2 :=
    MkRule1
      (fun e' =>
         [⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_learns_if_gen         @ e',
          ⟬R⟭ H ⊢ KE_ALL_TRUST ASSUMPTION_trusted_knew_or_learns_or_gen @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_monotonicity                               @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_generates_new_ex                           @ e',
          ⟬R⟭ H ⊢ ASSUMPTION_disseminate_unique                         @ e',
          ⟬R⟭ H ⊢ KE_TKNOWS t1           @ e1,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t1 p     @ e1,
          ⟬R⟭ H ⊢ KE_GEN_FOR d1 t1       @ e1,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t1 c1  @ e1,
          ⟬R⟭ H ⊢ KE_TKNOWS t2           @ e2,
          ⟬R⟭ H ⊢ KE_HAS_TOWNER t2 p     @ e2,
          ⟬R⟭ H ⊢ KE_GEN_FOR d2 t2       @ e2,
          ⟬R⟭ H ⊢ KE_TRUST_HAS_ID t2 c2  @ e2,
          ⟬R⟭ H ⊢ KE_SIMILAR_TRUST t1 t2 @ e,
          ⟬R⟭ H ⊢ KE_SIMILAR_DATA d1 d2  @ e,
          ⟬R⟭ H ⊢ KE_ID_EQ c1 c2         @ e])
      (⟬R⟭ H ⊢ KE_DATA_EQ d1 d2 @ e).

  Lemma DERIVED_RULE_trusted_knowledge_unique3_ex_true :
    forall {eo : EventOrdering} e1 e2 e R H p t1 t2 c1 c2 d1 d2,
      rule_true (DERIVED_RULE_trusted_knowledge_unique3_ex e1 e2 e R H p t1 t2 c1 c2 d1 d2).
  Proof.
    introv st; simpl in *.

    apply (PRIMITIVE_RULE_cut_true "x" (KE_TRUST_EQ t1 t2 @ e)); simseqs j.
    { apply (DERIVED_RULE_trusted_knowledge_unique_ex_true p c1 c2 e1 e2); simseqs j; inst_hyp e0 st. }

    apply (PRIMITIVE_RULE_collision_resistant_true t1 t2); simseqs j; try LOCKauto;
      norm_with "x"; apply (PRIMITIVE_RULE_thin_true "x"); simseqs j;
        inst_hyp e st.
   Qed.

End KnowledgeCalculus.


Hint Resolve implies_ex_node_e_local_pred : kn.
Hint Resolve direct_pred_preserves_ex_node_e : kn.
Hint Resolve local_pred_preserves_ex_node_e : kn.
Hint Resolve local_pred_preserves_ex_node_e_forward : kn.
Hint Resolve local_pred_eq_preserves_ex_node_e : kn.
Hint Resolve knows_after_implies_has_correct_trace_before : kn.
Hint Resolve state_before_implies_state_after_not_first : kn.

Hint Resolve state_before_implies_state_after_first : kn.
Hint Resolve trusted_state_before_implies_trusted_state_after_not_first : kn.
Hint Resolve trusted_state_after_implies_trusted_state_before_not_first : kn.
Hint Resolve trusted_state_before_implies_trusted_state_after_first : kn.
Hint Resolve state_after_eq_state_after_implies_eq_mem : kn.
Hint Resolve state_before_eq_state_before_implies_eq_mem : kn.
Hint Resolve trusted_state_after_implies_eq_mem : kn.
Hint Resolve trusted_state_before_implies_eq_mem : kn.
Hint Resolve id_after_eq_id_after_implies_eq_id : kn.
Hint Resolve id_before_eq_id_before_implies_eq_id : kn.
Hint Resolve same_id_sym : kn.
Hint Resolve interpret_KE_ANDS_implies : kn.
Hint Resolve assume_eo_ASSUMPTION_monotonicity_implies_monotonicity : kn.
Hint Resolve disseminate_trusted_own_implies_data_is_owned : kn.
Hint Resolve same_data_is_owned : kn.
Hint Resolve knows_before_implies_knows_after : kn.
Hint Resolve in_M_output_sys_on_event_implies_disseminate : kn.


Hint Rewrite @data_is_owned_local_pred : kn.
Hint Rewrite @kc_trust_is_owned_local_pred : kn.


Delimit Scope kn with kn.

Open Scope kn.
Notation "a ≪ b" := (kc_id_lt a b) (at level 70) : kn.
Notation "a ⋘ b" := (kc_id_le a b) (at level 70) : kn.
Notation "a ≈ b" := (kc_sim_trust a b) (at level 70) : kn.
Notation "a ≍ b" := (kc_sim_data a b) (at level 70).
Notation "a @ b" := (MkKExpAt a b) (at level 68) : kn.
Notation "a › b" := (MkHyp a b) (at level 69) : kn.
Notation "∅" := emHyps : kn.
Notation "H • h" := (addHyp H h) (at level 70) : kn.
Notation "H » J" := (addHyps H J) (at level 70) : kn.
Notation "e1 ≡ e2" := (causal_rel_eq                 e1 e2) (at level 69) : kn.
Notation "e1 ⋄ e2" := (causal_rel_right_before       e1 e2) (at level 69) : kn.
Notation "e1 □ e2" := (causal_rel_local_before       e1 e2) (at level 69) : kn.
Notation "e1 ■ e2" := (causal_rel_local_before_eq    e1 e2) (at level 69) : kn.
Notation "e1 ▷ e2" := (causal_rel_happened_before    e1 e2) (at level 69) : kn.
Notation "e1 ▶ e2" := (causal_rel_happened_before_eq e1 e2) (at level 69) : kn.
Notation "a ⋈ b" := (MkNamedCausalRel a b) (at level 70) : kn.
Notation "⟬ R ⟭ H ⊢ C" := (MkSeq R H C) (at level 70) : kn.
Close Scope kn.
