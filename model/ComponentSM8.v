Require Export ComponentSM.


Section ComponentSM8.

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


  Lemma M_run_ls_before_event_implies_has_correct_trace_before :
    forall {eo : EventOrdering} (e : Event) {L S} (ls1 ls2 : LocalSystem L S),
      ~isFirst e
      -> M_run_ls_before_event ls1 e = Some ls2
      -> has_correct_trace_before (local_pred e) (loc e).
  Proof.
    introv nf run.
    rewrite M_run_ls_before_event_unroll_on in run.
    destruct (dec_isFirst e) as [d|d]; ginv; tcsp.
    apply M_run_ls_on_event_implies_has_correct_trace_before in run; autorewrite with eo in *; auto.
  Qed.
  Hint Resolve M_run_ls_before_event_implies_has_correct_trace_before : comp.

  Lemma M_output_sys_on_event_implies_has_correct_trace_before :
    forall {eo : EventOrdering} (e : Event) {F} (sys : M_USystem F) d,
      d ∈ sys ⇝ e
      -> has_correct_trace_before e (loc e).
  Proof.
    introv out.
    apply M_output_ls_on_event_as_run in out; exrepnd.
    destruct (dec_isFirst e) as [isf|isf].

    { apply isCorrect_first_implies_has_correct_trace_before; auto.
      unfold M_output_ls_on_this_one_event in *.
      unfold time_trigger_op, isCorrect in *.
      remember (trigger_op e) as trig; destruct trig; tcsp. }

    apply M_run_ls_before_event_implies_has_correct_trace_before in out1; auto.
    apply has_correct_trace_before_local_pred_implies; auto.
    unfold M_output_ls_on_this_one_event in *.
    unfold time_trigger_op, isCorrect in *.
    remember (trigger_op e) as trig; destruct trig; tcsp.
  Qed.
  Hint Resolve M_output_sys_on_event_implies_has_correct_trace_before : comp.

End ComponentSM8.


Hint Resolve M_run_ls_before_event_implies_has_correct_trace_before : comp.
Hint Resolve M_output_sys_on_event_implies_has_correct_trace_before : comp.
