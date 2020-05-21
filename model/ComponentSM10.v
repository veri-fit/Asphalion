Require Export ComponentSM9.


Section ComponentSM10.

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
  Context { iot : @IOTrustedFun }.

  Context { base_fun_io       : baseFunIO }.
  Context { base_state_fun    : baseStateFun }.
  Context { trusted_state_fun : trustedStateFun }.


  Lemma on_comp_sing_eq :
    forall {n} {cn} (p : n_proc n cn) {cn'} {A} (F : n_proc n cn' -> A) (a : A),
      on_comp [MkPProc cn p] F a
      = match CompNameDeq cn cn' with
        | left x => F (eq_rect _ _ p _ x)
        | right _ => a
        end.
  Proof.
    introv; unfold on_comp; simpl; repeat dest_cases w.
  Qed.

  Lemma PreCompNameDeq : Deq PreCompName.
  Proof.
    introv; unfold deceq; destruct x as [n1 s1], y as [n2 s2].
    destruct (CompNameKindDeq n1 n2);
      destruct (CompNameSpaceDeq s1 s2);
      prove_dec.
  Defined.

  Lemma M_run_ls_on_input_not_in :
    forall {n} (l : n_procs n) cn (i : cio_I (fio cn)),
      ~In cn (get_names l)
      -> M_run_ls_on_input l cn i = (l, None).
  Proof.
    introv ni.
    unfold M_run_ls_on_input, on_comp; simpl.
    dest_cases w; rev_Some.
    apply find_name_implies_in_get_names in Heqw; tcsp.
  Qed.

  Lemma find_name_incr_n_procs :
    forall cn {n} (l : n_procs n),
      find_name cn (incr_n_procs l)
      = match find_name cn l with
        | Some p => Some (incr_n_proc p)
        | None => None
        end.
  Proof.
    induction l; introv; simpl; tcsp.
    destruct a; simpl in *; tcsp; repeat dest_cases w.
  Qed.

  Lemma decr_n_procs_incr_n_procs :
    forall {n} (subs : n_procs n),
      decr_n_procs (incr_n_procs subs) = subs.
  Proof.
    induction subs; introv; simpl; tcsp.
    unfold decr_n_procs in *; simpl in *.
    rewrite IHsubs.
    destruct a; simpl in *; tcsp.
  Qed.
  Hint Rewrite @decr_n_procs_incr_n_procs : comp.

  Lemma snd_M_run_ls_on_input_incr_n_procs_eq :
    forall {n} (l : n_procs n) cn i,
      snd (M_run_ls_on_input (incr_n_procs l) cn i)
      = snd (M_run_ls_on_input l cn i).
  Proof.
    introv; unfold M_run_ls_on_input, on_comp; simpl.
    rewrite find_name_incr_n_procs.
    repeat dest_cases w; ginv; rev_Some; simpl.
    unfold M_break; simpl.
    remember (M_run_sm_on_input (incr_n_proc w0) i (incr_n_procs l)) as u.
    symmetry in Hequ; repnd; simpl in *.
    remember (M_run_sm_on_input w0 i l) as v.
    symmetry in Heqv; repnd; simpl in *.
    unfold M_run_sm_on_input in *; simpl in *.
    unfold M_on_decr in *; simpl in *.
    autorewrite with comp in *.
    rewrite Heqv in Hequ; ginv.
  Qed.

  Lemma snd_M_run_ls_on_trusted_incr_n_procs_eq :
    forall {n} (l : n_procs n) i,
      snd (M_run_ls_on_trusted (incr_n_procs l) i)
      = snd (M_run_ls_on_trusted l i).
  Proof.
    introv.
    apply snd_M_run_ls_on_input_incr_n_procs_eq.
  Qed.

End ComponentSM10.
