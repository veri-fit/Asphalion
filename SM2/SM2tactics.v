(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2018 Luxembourg University
  Copyright 2019 Luxembourg University

  This file is part of Velisarios.

  Velisarios is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Velisarios is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Velisarios.  If not, see <http://www.gnu.org/licenses/>.


  Authors: Vincent Rahli
           Ivana Vukotic

*)


Require Export generic_tactics.
Require Export SM2.

Ltac op_st_some m h :=
  match goal with
  | [ H : op_state _ _ _ _ = Some _ |- _ ] =>
    apply op_state_some_iff in H;
    destruct H as [m [h H]]

  | [ H : op_output _ _ _ _ = Some _ |- _ ] =>
    apply op_output_some_iff in H;
    destruct H as [m [h H]]
  end.

Ltac unfold_handler :=
  match goal with
  | [ H : context[SMhandler_initial    _ _ _] |- _ ] => unfold SMhandler_initial    in H
  | [ H : context[SMhandler_alarm      _ _ _] |- _ ] => unfold SMhandler_alarm      in H
  | [ H : context[SMhandler_lieutenant _ _ _] |- _ ] => unfold SMhandler_lieutenant in H
  | [ H : context[SMhandler_result     _ _ _] |- _ ] => unfold SMhandler_result     in H
  end.

Ltac unfold_handler_concl :=
  match goal with
  | [ |- context[SMhandler_initial    _ _ _] ] => unfold SMhandler_initial
  | [ |- context[SMhandler_alarm      _ _ _] ] => unfold SMhandler_alarm
  | [ |- context[SMhandler_lieutenant _ _ _] ] => unfold SMhandler_lieutenant
  | [ |- context[SMhandler_result     _ _ _] ] => unfold SMhandler_result
  end.

Ltac unfold_handlers := repeat unfold_handler.

Ltac conflicting_sends :=
  match goal with
  | [ H : send_sm_msg_commander _ _ = send_sm_msg_lieutenant _ _                  |- _ ] => inversion H;fail
  | [ H : send_sm_msg_commander _ _ = send_sm_msg_result _ _                      |- _ ] => inversion H;fail
  | [ H : send_sm_msg_commander _ _ = send_alarm _                                |- _ ] => inversion H;fail

  | [ H : send_sm_msg_lieutenant _ _ = send_sm_msg_commander _ _                  |- _ ] => inversion H;fail
  | [ H : send_sm_msg_lieutenant _ _ = send_sm_msg_result _ _                     |- _ ] => inversion H;fail
  | [ H : send_sm_msg_lieutenant _ _ = send_alarm _                               |- _ ] => inversion H;fail

  | [ H : send_sm_msg_result _ _ = send_sm_msg_commander _ _                      |- _ ] => inversion H;fail
  | [ H : send_sm_msg_result _ _ = send_sm_msg_lieutenant _ _                     |- _ ] => inversion H;fail
  | [ H : send_sm_msg_result _ _ = send_alarm _                                   |- _ ] => inversion H;fail

  | [ H : send_alarm _ = send_sm_msg_commander _ _                                |- _ ] => inversion H;fail
  | [ H : send_alarm _ = send_sm_msg_lieutenant _ _                               |- _ ] => inversion H;fail
  | [ H : send_alarm _ = send_sm_msg_result _ _                                   |- _ ] => inversion H;fail
  end.


Ltac sm_simplifier_step :=
  match goal with
  | [ H : is_commander _ = true |- _ ] => apply is_commander_true in H

  | [ H : broadcast2not_in_list _ _ = _ |- _ ] =>
    complete (unfold broadcast2not_in_list in H; (*ginv*) conflicting_sends)
  end.

Ltac sm_simplifier :=
  let stac := (fun _ => sm_simplifier_step) in
  simplifier stac.

(* FIX !!!! atac should be autorewrite with sm in *, but then well_formness is broken *)
Ltac smash_sm_tac tac :=
  let stac := fun _ => sm_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  let atac := fun _ => (autorewrite with eo in * ) in
  smash_byzeml_tac
    tac
    stac
    ftac
    atac.

Ltac smash_sm1  := let tac := fun _ => (eauto 1 with sm2) in smash_sm_tac tac.
Ltac smash_sm2  := let tac := fun _ => (eauto 2 with sm2) in smash_sm_tac tac.
Ltac smash_sm3  := let tac := fun _ => (eauto 3 with sm2) in smash_sm_tac tac.
Ltac smash_sm4  := let tac := fun _ => (eauto 4 with sm2) in smash_sm_tac tac.
Ltac smash_sm5  := let tac := fun _ => (eauto 5 with sm2) in smash_sm_tac tac.
Ltac smash_sm6  := let tac := fun _ => (eauto 6 with sm2) in smash_sm_tac tac.
Ltac smash_sm7  := let tac := fun _ => (eauto 7  with sm2) in smash_sm_tac tac.
Ltac smash_sm8  := let tac := fun _ => (eauto 8  with sm2) in smash_sm_tac tac.
Ltac smash_sm9  := let tac := fun _ => (eauto 9  with sm2) in smash_sm_tac tac.
Ltac smash_sm10 := let tac := fun _ => (eauto 10 with sm2) in smash_sm_tac tac.

Ltac smash_sm := smash_sm3.

Ltac smash_handlers1  := unfold_handlers; smash_sm1.
Ltac smash_handlers2  := unfold_handlers; smash_sm2.
Ltac smash_handlers3  := unfold_handlers; smash_sm3.
Ltac smash_handlers4  := unfold_handlers; smash_sm4.
Ltac smash_handlers5  := unfold_handlers; smash_sm5.
Ltac smash_handlers6  := unfold_handlers; smash_sm6.
Ltac smash_handlers7  := unfold_handlers; smash_sm7.
Ltac smash_handlers8  := unfold_handlers; smash_sm8.
Ltac smash_handlers9  := unfold_handlers; smash_sm9.
Ltac smash_handlers10 := unfold_handlers; smash_sm10.

Ltac smash_handlers := smash_handlers3.

Ltac unfold_handlers_concl := repeat unfold_handler_concl.

Ltac smash_handlers_concl1  := unfold_handlers_concl; smash_sm1.
Ltac smash_handlers_concl2  := unfold_handlers_concl; smash_sm2.
Ltac smash_handlers_concl3  := unfold_handlers_concl; smash_sm3.
Ltac smash_handlers_concl4  := unfold_handlers_concl; smash_sm4.
Ltac smash_handlers_concl5  := unfold_handlers_concl; smash_sm5.
Ltac smash_handlers_concl6  := unfold_handlers_concl; smash_sm6.
Ltac smash_handlers_concl7  := unfold_handlers_concl; smash_sm7.
Ltac smash_handlers_concl8  := unfold_handlers_concl; smash_sm8.
Ltac smash_handlers_concl9  := unfold_handlers_concl; smash_sm9.
Ltac smash_handlers_concl10 := unfold_handlers_concl; smash_sm10.

Ltac smash_handlers_concl := smash_handlers_concl3.

Ltac pred_happened_before_ind_local_pred e ind :=
  induction e as [? ind] using predHappenedBeforeInd_local_pred;[].

Ltac intro_state_step h eqst :=
  match goal with
  | [ |- state_sm_before_event _ _ = _ -> _ ] => let eqst' := fresh eqst in intro eqst'
  | [ |- state_sm_on_event _ _ = _ -> _ ] => let eqst' := fresh eqst in intro eqst'
  | [ |- _ -> _ ] => let h' := fresh h in intro h'
  | _ => idtac
  end.

Ltac intro_state h eqst := repeat (intro_state_step h eqst).

Ltac unroll_state_on :=
  match goal with
  | [ H : state_sm_on_event _ _ = _ |- _ ] =>
    rewrite state_sm_on_event_unroll2 in H
  | [ H : state_sm_before_event _ ?e = _ |- _ ] =>
    let d := fresh "d" in
    rewrite state_sm_before_event_unroll in H; simpl in H;
    destruct (dec_isFirst e) as [d|d];
    [ginv; simpl in *; auto; fail|]
  end.

Ltac unroll_state :=
  match goal with
  | [ H : state_sm_before_event _ ?e = _ |- _ ] =>
    let d := fresh "d" in
    rewrite state_sm_before_event_unroll in H; simpl in H;
    destruct (dec_isFirst e) as [d|d];
    [ginv; simpl in *; auto; fail|]
  | [ H : state_sm_on_event _ _ = _ |- _ ] =>
    rewrite state_sm_on_event_unroll2 in H
  end.

Ltac unroll_send :=
  match goal with
  | [ H : In _ (output_system_on_event_ldata ?s _) |- _ ] =>
    eapply in_output_system_on_event_ldata in H; eauto;
    try unfold SMsys in H;
    try match goal with
        | [ K : loc _ = _ |- _ ] => rewrite K in H
        end;
    try rw @loutput_sm_on_event_unroll2 in H
  end.

Ltac destruct_unrolled_state sop p :=
  match goal with
  | [ H : context[map_option _ ?s] |- _ ] =>
    let sop := fresh sop in
    let p := fresh p in
    remember s as sop;
    match goal with
    | [ H : sop = _ |- _ ] =>
      symmetry in H;
      destruct sop as [p|];
      simpl in *;[|ginv;tcsp;fail]
    end

  | [ H : context[option_map _ ?s] |- _ ] =>
    let sop := fresh sop in
    let p := fresh p in
    remember s as sop;
    match goal with
    | [ H : sop = _ |- _ ] =>
      symmetry in H;
      destruct sop as [p|];
      simpl in *;[|ginv;tcsp;fail]
    end
  end.

Ltac simplify_ind ind :=
  let hyp := fresh "hyp" in
  repeat match type of ind with
         | ~ isFirst ?e -> _ =>
           match goal with
           | [ H : notT (isFirst e) |- _ ] => autodimp ind hyp;[]
           end
         | (forall x : _, Some ?y = Some x -> _) =>
           pose proof (ind y) as ind; autodimp ind hyp;[]
         end.

Ltac unfold_update ind trig tac1 tac2 :=
  match goal with
  | [ H : fst (SMupdate _ _ ?t _) = Some _ |- _ ] =>
    let trig := fresh trig in
    unfold SMupdate in H;
    remember t as trig;
    match goal with
    | [ H : trig = _ |- _ ] => symmetry in H
    end;
    destruct trig

  | [ H : snd (SMupdate _ _ ?t _) = _ |- _ ] =>
    let trig := fresh trig in
    unfold SMupdate in H;
    remember t as trig;
    match goal with
    | [ H : trig = _ |- _ ] => symmetry in H
    end;
    destruct trig
  end.

Ltac apply_in_olist2list :=
  match goal with
  | [ H : In _ (olist2list _) |- _ ] =>
    apply in_olist2list in H; exrepnd
  end.

Ltac start_ind ind :=
  match goal with
  | [ |- forall x : _, _ ] =>
    intro x;
    match type of x with
    | Event => pred_happened_before_ind_local_pred x ind
    | _ => start_ind ind
    end
  end.

Ltac prove_by_ind ind h eqst sop p m eqtrig trig tac1 tac2 :=
  start_ind ind;
  introv;
  intro_state h eqst;
  try unroll_state_on;
  try unroll_send;
  try fold (@DirectedMsgs _ _ _) in *;
  simpl in *;
  destruct_unrolled_state sop p;
  try apply_in_olist2list;
  op_st_some m eqtrig;
  simplify_ind ind;
  unfold_update ind trig tac1 tac2;
  simpl in *; ginv; subst; tcsp;
  try tac1;
  try (first [conflicting_sends|tac2 ind]).

Ltac sm_gen_inv :=
  let stac := (fun _ => sm_simplifier_step) in
  gen_inv stac.

Ltac eproves :=
  repeat eexists; eauto; simpl; try eassumption; autorewrite with eo; auto.

Ltac smLR :=
  first [complete auto
        |complete (left;  autorewrite with eo sm2 in *; eauto 2 with eo sm2; smLR)
        |complete (right; autorewrite with eo sm2 in *; eauto 2 with eo sm2; smLR)].

Ltac smash_sm_ind_tac ind base_tac ind_tac :=
  let d   := fresh "d" in
  let hyp := fresh "hyp" in
  match goal with
  | [ H : state_sm_before_event ?sma ?e = Some ?s |- _ ] =>
    let K := fresh H in
    rewrite <- ite_first_state_sm_on_event_as_before in H;
    unfold ite_first in H;
    destruct (dec_isFirst e) as [d|d]; sm_gen_inv;
    (*simpl in *; subst; simpl in *; tcsp*)
    try (complete ((*try clear_current_view; *)
             simpl in *; subst; simpl in *;
             sm_simplifier; base_tac ();
             simpl in *; try iffalse;
             try congruence; try omega));
    first[fail
         |idtac;[];
          repeat (autodimp ind hyp);
          first[fail
               |idtac;[];
                dup H as K;
                try (complete eproves);
                try (eapply ind in K; eauto; clear ind);
                ind_tac ();
                exrepnd;
                repeat (eexists;[]);
                dands; eauto; eauto 3 with eo sm2;
                complete (repndors; tcsp; try smLR; try congruence; try omega)
               ]
         ]
  end.

Ltac smash_sm_ind ind :=
  let base_tac := (fun _ => smash_sm) in
  let ind_tac  := (fun _ => eauto 2 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac prove_left := eauto 2 with sm2; repndors; tcsp; []; left.

Ltac smash_sm_ind2 ind :=
  let base_tac := (fun _ => smash_sm) in
  let ind_tac  := (fun _ => prove_left) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac smash_sm_ind3 ind :=
  let base_tac := (fun _ => smash_sm) in
  let ind_tac  := (fun _ => eauto 3 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac smash_sm_ind4 ind :=
  let base_tac := (fun _ => smash_sm) in
  let ind_tac  := (fun _ => eauto 4 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac smash_sm_ind5 ind :=
  let base_tac := (fun _ => smash_sm) in
  let ind_tac  := (fun _ => eauto 5 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac smash_sm_ind6 ind :=
  let base_tac := (fun _ => smash_sm) in
  let ind_tac  := (fun _ => eauto 6 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac smash_sm_ind6_6 ind :=
  let base_tac := (fun _ => smash_sm6) in
  let ind_tac  := (fun _ => eauto 6 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac smash_sm_ind6_7 ind :=
  let base_tac := (fun _ => smash_sm6) in
  let ind_tac  := (fun _ => eauto 7 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac smash_sm_ind6_8 ind :=
  let base_tac := (fun _ => smash_sm6) in
  let ind_tac  := (fun _ => eauto 8 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac smash_sm_ind6_9 ind :=
  let base_tac := (fun _ => smash_sm6) in
  let ind_tac  := (fun _ => eauto 9 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac smash_sm_ind6_10 ind :=
  let base_tac := (fun _ => smash_sm6) in
  let ind_tac  := (fun _ => eauto 10 with sm2) in
  smash_sm_ind_tac ind base_tac ind_tac.

Ltac rename_hyp_with oldname newname :=
  match goal with
  | [ H : context[oldname] |- _ ] => rename H into newname
  end.
