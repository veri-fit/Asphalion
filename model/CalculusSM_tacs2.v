Require Export CalculusSM.


Local Open Scope kn.


Ltac use_rule rule tac smash :=
  let r := fresh "rule" in
  let h := fresh "hyp" in
  pose proof rule as r;
  unfold rule_true in r;
  simpl in r;
  repeat (autodimp r h); tac ();
  [match goal with
   | [ |- rule_e_t_d_c_n_hypotheses_true 1 0 0 0 0 ?x ] =>
     let ve := fresh "ve" in
     let vt := fresh "vt" in
     let vd := fresh "vd" in
     let vc := fresh "vc" in
     let xx := fresh "xx" in
     let yy := fresh "yy" in
     let zz := fresh "zz" in
     intros ve vt vd vc vn xx yy zz;
     induction ve using Vector.caseS'; simpl in *;
     clear vt vd vc vn ve;
     repndors; subst; unfold seq_concl, seq_event in *;
     simpl in *; introv; simpl in *; tcsp; smash ()
   end
  |unfold sequent_true in r;simpl in r;
   repeat (autodimp r h); tcsp; ginv
  ].
