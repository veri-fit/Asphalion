Require Export ComponentSM3.
Require Export ComponentSM4.


Section ComponentSM6.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { pd  : @Data }.
  Context { pn  : @Node }.
  Context { pk  : @Key }.
  Context { pat : @AuthTok }.
  Context { paf : @AuthFun pn pk pat pd }.
  Context { pm  : @Msg }.
  Context { pda : @DataAuth pd pn }.
  Context { cad : ContainedAuthData }.
  Context { gms : MsgStatus }.
  Context { dtc : @DTimeContext }.
  Context { qc  : @Quorum_context pn}.
  Context { iot : @IOTrusted }.

  Context { base_fun_io       : baseFunIO }.
  Context { base_state_fun    : baseStateFun }.
  Context { trusted_state_fun : trustedStateFun }.


  Lemma decr_n_procs_1 :
    forall (l : n_procs 1),
      decr_n_procs l = [].
  Proof.
    induction l; auto.
    unfold decr_n_procs in *; simpl in *.
    rewrite IHl.
    destruct a as [cn p]; simpl in *.
    destruct p; simpl in *; tcsp.
  Qed.
  Hint Rewrite decr_n_procs_1 : comp.

  Fixpoint in_subs {n:nat} (cn : CompName) (l : n_procs n) : bool :=
    match l with
    | [] => false
    | MkPProc m q :: rest =>
      if CompNameDeq m cn then true
      else in_subs cn rest
    end.

  Lemma compname_proof_irrelevance :
    forall {cn : CompName} (x y : cn = cn),
      x = y.
  Proof.
    introv.
    apply UIP_dec.
    apply CompNameDeq.
  Qed.

  Lemma state_of_subcomponents_replace_name :
    forall {n} {cn} (p : n_proc n cn) subs,
      in_subs cn subs = true
      -> state_of_subcomponents (replace_name p subs) cn = Some (sm2state p).
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [cm q]; simpl in *; dest_cases w; subst; GC.
    { unfold state_of_subcomponents; simpl; dest_cases w.
      simpl.
      rewrite (compname_proof_irrelevance w eq_refl); simpl; auto. }
    { unfold state_of_subcomponents; simpl; dest_cases w. }
  Qed.
  Hint Resolve state_of_subcomponents_replace_name : comp.

  Lemma implies_in_subs_replace_name :
    forall {n} {cn1 cn2} (p : n_proc n cn1) subs,
      in_subs cn2 subs = true
      -> in_subs cn2 (replace_name p subs) = true.
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [cm q]; repeat (simpl in *; dest_cases w; subst; GC).
  Qed.
  Hint Resolve implies_in_subs_replace_name : comp.

  Lemma implies_in_subs_replace_sub :
    forall {n} {cn cn'} (subs : n_procs n) (p : n_proc _ cn'),
      in_subs cn subs = true
      -> in_subs cn (replace_sub subs p) = true.
  Proof.
    induction subs; introv i; simpl; tcsp.
    destruct a as [cm q]; repeat (simpl in *; dest_cases w; subst; GC).
  Qed.
  Hint Resolve implies_in_subs_replace_sub : comp.

  Lemma implies_in_subs_replace_subs :
    forall {n} {cn} l (subs : n_procs n),
      in_subs cn subs = true
      -> in_subs cn (replace_subs subs l) = true.
  Proof.
    induction l; introv i; simpl; tcsp.
    destruct a as [cm q]; repeat (simpl in *; dest_cases w; subst; GC).
    apply IHl; eauto 3 with comp.
  Qed.
  Hint Resolve implies_in_subs_replace_subs : comp.

  Lemma find_name_replace_name_same :
    forall {m} {cn} (p : n_proc m cn) subs,
      in_subs cn subs = true
      -> find_name cn (replace_name p subs) = Some p.
  Proof.
    induction subs; introv i; simpl in *; tcsp.
    destruct a as [n r]; repeat (dest_cases w; subst; simpl in *; tcsp).
    ginv.
    rewrite (compname_proof_irrelevance w eq_refl); simpl; auto.
  Qed.

  Lemma find_name_replace_name_implies_eq :
    forall {m} {cn} (p q : n_proc m cn) subs,
      in_subs cn subs = true
      -> find_name cn (replace_name p subs) = Some q
      -> q = p.
  Proof.
    introv i f.
    rewrite find_name_replace_name_same in f; ginv.
  Qed.

  Lemma find_name_replace_name_none_implies :
    forall {m} {cn} (p : n_proc m cn) subs,
      in_subs cn subs = true
      -> find_name cn (replace_name p subs) = None
      -> False.
  Proof.
    introv i f.
    rewrite find_name_replace_name_same in f; ginv.
  Qed.

  Lemma find_name_replace_name_implies_diff_eq :
    forall {n} {cn1 cn2} (p : n_proc n cn1) subs,
      cn1 <> cn2
      -> find_name cn2 (replace_name p subs) = find_name cn2 subs.
  Proof.
    induction subs; introv d; simpl in *; tcsp.
    destruct a as [m r]; repeat (dest_cases w; subst; simpl in *; tcsp).
  Qed.

  Lemma find_name_replace_name_implies_diff_some :
    forall {n} {cn1 cn2} (p : n_proc n cn1) q subs,
      cn1 <> cn2
      -> find_name cn2 (replace_name p subs) = Some q
      -> find_name cn2 subs = Some q.
  Proof.
    introv d f.
    rewrite find_name_replace_name_implies_diff_eq in f; auto.
  Qed.

  Lemma find_name_replace_name_implies_diff_none :
    forall {n} {cn1 cn2} (p : n_proc n cn1) subs,
      cn1 <> cn2
      -> find_name cn2 (replace_name p subs) = None
      -> find_name cn2 subs = None.
  Proof.
    introv d f.
    rewrite find_name_replace_name_implies_diff_eq in f; auto.
  Qed.

  Lemma find_name_replace_name_implies_eq_1 :
    forall {cn} (p q : n_proc 1 cn) subs,
      in_subs cn subs = true
      -> find_name cn (replace_name p subs) = Some q
      -> q = p.
  Proof.
    introv; apply find_name_replace_name_implies_eq.
  Qed.

  Lemma find_name_replace_name_none_implies_1 :
    forall {cn} (p : n_proc 1 cn) subs,
      in_subs cn subs = true
      -> find_name cn (replace_name p subs) = None
      -> False.
  Proof.
    introv; apply find_name_replace_name_none_implies.
  Qed.

  Lemma find_name_replace_name_implies_diff_some_1 :
    forall {cn1 cn2} (p : n_proc 1 cn1) q subs,
      cn1 <> cn2
      -> find_name cn2 (replace_name p subs) = Some q
      -> find_name cn2 subs = Some q.
  Proof.
    introv; apply find_name_replace_name_implies_diff_some.
  Qed.

  Lemma find_name_replace_name_implies_diff_none_1 :
    forall {cn1 cn2} (p : n_proc 1 cn1) subs,
      cn1 <> cn2
      -> find_name cn2 (replace_name p subs) = None
      -> find_name cn2 subs = None.
  Proof.
    introv; apply find_name_replace_name_implies_diff_none.
  Qed.

  Definition proc2at0 {cn} (p : n_proc 1 cn) : n_proc_at 0 cn.
  Proof.
    destruct p; auto.
    inversion b.
  Defined.

  Lemma sm_or_at_proc2at0 : forall {cn} (p : n_proc 1 cn), sm_or_at (proc2at0 p) = p.
  Proof.
    introv; destruct p; tcsp.
    inversion b.
  Qed.
  Hint Rewrite @sm_or_at_proc2at0 : comp.

  Lemma sm_or_at_proc2at0_v2 : forall {cn} (p : sm_or (MP_StateMachine (fun _ => False) cn) False),
      sm_or_at (proc2at0 p) = p.
  Proof.
    introv; destruct p; tcsp.
  Qed.
  Hint Rewrite @sm_or_at_proc2at0_v2 : comp.

End ComponentSM6.


Hint Rewrite @decr_n_procs_1 : comp.
Hint Resolve state_of_subcomponents_replace_name : comp.
Hint Resolve implies_in_subs_replace_name : comp.
Hint Resolve implies_in_subs_replace_sub : comp.
Hint Resolve implies_in_subs_replace_subs : comp.
Hint Rewrite @sm_or_at_proc2at0 : comp.
Hint Rewrite @sm_or_at_proc2at0_v2 : comp.


Ltac in_subs_tac :=
  repeat (first [complete auto
                |apply implies_in_subs_replace_subs
                |apply implies_in_subs_replace_name]).

Ltac simplify_find_name_replace :=
  match goal with
  | [ H : find_name _ _ = Some _ |- _ ] =>
    let h := fresh "h" in
    first
      [apply find_name_replace_name_implies_eq_1 in H;
       [subst
       |in_subs_tac; eauto 2 with comp minbft; fail]
      |apply find_name_replace_name_implies_diff_some_1 in H;
       [|intro h; inversion h;fail]
      ]
  | [ H : find_name _ _ = None |- _ ] =>
    let h := fresh "h" in
    first
      [apply find_name_replace_name_none_implies_1 in H;
       [inversion H;fail|in_subs_tac; eauto 2 with comp minbft; fail]
      |apply find_name_replace_name_implies_diff_none_1 in H;
       [|intro h; inversion h;fail]
      ]
  end.
