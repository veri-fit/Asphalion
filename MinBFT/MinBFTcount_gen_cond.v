(* GENERIC *)

Require Export MinBFTcount_gen_tacs.
Require Export MinBFTcount_gen3.


Section MinBFTcount_gen_cond.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  (* old definition *)
  Inductive pres_is_M_break_out {n} {cn} (P : n_proc_at n cn -> Prop) :
    nat -> n_proc_at n cn -> Prop :=
  | pres_cond1 :
      forall p, P p -> pres_is_M_break_out P 0 p
  | pres_cond2 :
      forall k p i q o subs,
        is_M_break_out (lift_M_1 (app_n_proc_at p i)) subs (Some (sm_or_at q), o)
        -> pres_is_M_break_out P k p
        -> pres_is_M_break_out P (S k) q.

  Fixpoint preserves_is_M_break_out
           {n} {cn}
           (j : nat)
           (P : n_proc_at n cn -> Prop)
           (p : n_proc_at n cn) : Prop :=
    match j with
    | 0 => P p
    | S j =>
      forall i q o l,
        is_M_break_out (lift_M_1 (app_n_proc_at p i)) l (Some (sm_or_at q), o)
        -> preserves_is_M_break_out j P q
    end.

  Definition ex_entry (rd : RequestData) (l : LOG_state) : Prop :=
    exists e, find_entry rd l = Some e.

  Definition is_M_break_out_LOGname_implies_ex_entry
             (p : n_proc_at 0 LOGname) :=
    forall c q subs,
      (is_M_break_out
         (lift_M_1 (app_n_proc_at p (is_committed_in c))) subs
         (Some q, log_out true)
       \/ (exists o,
              is_M_break_out
                 (lift_M_1 (app_n_proc_at p (log_new_commit_log_in c))) subs
                (Some q, o))
       \/ is_M_break_out
            (lift_M_1 (app_n_proc_at p (prepare_already_in_log_in (commit2prepare c)))) subs
            (Some q, log_out true)
       \/ (exists o ui,
              is_M_break_out
                (lift_M_1 (app_n_proc_at p (log_new_commit_log_in (mk_my_commit c ui)))) subs
                (Some q, o)))
      -> ex_entry (commit2request_data_i c) (sm2state q).

  Definition preserves_is_M_break_out_LOGname_implies_ex_entry
             (p    : n_proc_at 0 LOGname) :=
    forall k,
      preserves_is_M_break_out
        k
        is_M_break_out_LOGname_implies_ex_entry
        p.

  Definition cond_LOGname_ex_entry
             (subs : n_procs 1) :=
    forall a,
      find_name LOGname subs = Some (sm_or_at a)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry a.

  Lemma implies_cond_LOGname_ex_entry_replace_name_diff :
    forall (p : n_proc 1 USIGname) (subs : n_procs 1),
      in_subs LOGname subs = true
      -> cond_LOGname_ex_entry subs
      -> cond_LOGname_ex_entry (replace_name p subs).
  Proof.
    introv i cond h.
    simplify_find_name_replace; tcsp.
  Qed.

  Lemma implies_cond_LOGname_ex_entry_replace_name_eq :
    forall (p : n_proc 1 LOGname) (subs : n_procs 1),
      in_subs LOGname subs = true
      -> preserves_is_M_break_out_LOGname_implies_ex_entry (proc2at0 p)
      -> cond_LOGname_ex_entry (replace_name p subs).
  Proof.
    introv i cond h.
    simplify_find_name_replace; simpl in *; tcsp.
  Qed.

  Lemma cond_implies_preserves_ex_entry :
    forall (subs : n_procs 1) (p : n_proc_at 0 LOGname) q i o l,
      cond_LOGname_ex_entry subs
      -> find_name LOGname subs = Some (sm_or_at p)
      -> is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) i)) l (Some q, o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry (proc2at0 q).
  Proof.
    introv cond fn h; introv.
    apply cond in fn; clear cond.
    pose proof (fn (S k)) as fn.
    unfold preserves_is_M_break_out_LOGname_implies_ex_entry in *; simpl in *.
    unfold sm2p0 in *; simpl in *.
    destruct q; simpl in *; tcsp.
    pose proof (fn i a o l) as fn; tcsp.
  Qed.

  Lemma is_M_break_out_preserves_ex_entry :
    forall (p : n_proc_at 0 LOGname) q i o l,
      is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) i)) l (Some q, o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> preserves_is_M_break_out_LOGname_implies_ex_entry (proc2at0 q).
  Proof.
    introv h w.
    destruct q; simpl in *; tcsp.
    introv.
    pose proof (w (S k)) as w; simpl in *.
    apply w in h; auto.
  Qed.
  Hint Resolve is_M_break_out_preserves_ex_entry : minbft.

  Lemma is_M_break_out_preserves_ex_entry_2 :
    forall (p : n_proc_at 0 LOGname) q i o l,
      is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) i)) l (Some (sm_or_at q), o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> preserves_is_M_break_out_LOGname_implies_ex_entry q.
  Proof.
    introv h w.
    introv.
    pose proof (w (S k)) as w; simpl in *.
    apply w in h; auto.
  Qed.
  Hint Resolve is_M_break_out_preserves_ex_entry_2 : minbft.

  Lemma invalid_commit_false_implies_eq_commit2view :
    forall R ks v c b s,
      invalid_commit R ks v c b s = false
      -> commit2view c = v.
  Proof.
    introv h.
    unfold invalid_commit, valid_commit in h.
    repeat dest_cases w.
  Qed.
  Hint Resolve invalid_commit_false_implies_eq_commit2view : minbft.

  Hint Rewrite ui2counter_commit2ui_i_as_commit2counter_i : minbft.

  Lemma invalid_commit_false_implies_eq_commit2sender_i :
    forall R ks v c b s,
      invalid_commit R ks v c b s = false
      -> commit2sender_i c = MinBFTprimary v.
  Proof.
    introv h.
    unfold invalid_commit, valid_commit, is_primary in h.
    repeat dest_cases w.
  Qed.
  Hint Resolve invalid_commit_false_implies_eq_commit2sender_i : minbft.

  Lemma cond_LOGname_ex_entry_implies_preserves :
    forall (subs : n_procs 1) (p : n_proc_at 0 LOGname),
      cond_LOGname_ex_entry subs
      -> find_name LOGname subs = Some (sm_or_at p)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p.
  Proof.
    introv cond fn; introv; tcsp.
    apply cond in fn; clear cond; tcsp.
  Qed.
  Hint Resolve cond_LOGname_ex_entry_implies_preserves : minbft.

  Lemma preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry :
    forall (p : MP_StateMachine (fun _ => False) LOGname) c q l,
      is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) (is_committed_in c))) l (Some q, log_out true)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> ex_entry (commit2request_data_i c) (sm2state q).
  Proof.
    introv h w.
    pose proof (w 0 c q l) as w; simpl in w; tcsp.
  Qed.
  Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry : minbft.

  Lemma mk_my_commit_commit2ui_j :
    forall c,
      mk_my_commit c (commit2ui_j c) = c.
  Proof.
    introv.
    destruct c as [b uij], b as [v r uii]; simpl; tcsp.
  Qed.
  Hint Rewrite mk_my_commit_commit2ui_j : minbft.

  Lemma preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log :
    forall (p : MP_StateMachine (fun _ => False) LOGname) c q o l,
      is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) (log_new_commit_log_in c))) l (Some q, o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> ex_entry (commit2request_data_i c) (sm2state q).
  Proof.
    introv h w.
    pose proof (w 0 c q l) as w; simpl in w; tcsp.
    apply w; clear w.
    right; right; right; eauto.
    exists o (commit2ui_j c).
    autorewrite with minbft; auto.
  Qed.
  Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log : minbft.

  Lemma preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log_my :
    forall (p : MP_StateMachine (fun _ => False) LOGname) c q o ui l,
      is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) (log_new_commit_log_in (mk_my_commit c ui)))) l (Some q, o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> ex_entry (commit2request_data_i c) (sm2state q).
  Proof.
    introv h w.
    pose proof (w 0 c q l) as w; simpl in w; tcsp.
    apply w; right; eauto.
  Qed.
  Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log_my : minbft.

  Lemma preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_prep :
    forall (p : MP_StateMachine (fun _ => False) LOGname) c q l,
      is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) (prepare_already_in_log_in (commit2prepare c)))) l (Some q, log_out true)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> ex_entry (commit2request_data_i c) (sm2state q).
  Proof.
    introv h w.
    pose proof (w 0 c q l) as w; simpl in w; tcsp.
  Qed.
  Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_prep : minbft.

  Lemma is_M_break_out_preserves_ex_entry2 :
    forall p q i o l,
      is_M_break_out (lift_M_1 (app_n_proc_at (sm2p0 p) i)) l (Some (at2sm q), o)
      -> preserves_is_M_break_out_LOGname_implies_ex_entry p
      -> preserves_is_M_break_out_LOGname_implies_ex_entry (sm2p0 q).
  Proof.
    introv a b.
    pose proof (is_M_break_out_preserves_ex_entry p (at2sm q) i o l) as h.
    apply h; auto.
  Qed.
  Hint Resolve is_M_break_out_preserves_ex_entry2 : minbft.

  (* Move to some ComponentSM file *)
  Lemma has_comp_implies_in_subs :
    forall {n} cn (l : n_procs n),
      has_comp cn l -> in_subs cn l = true.
  Proof.
    induction l; introv h; unfold has_comp in *; exrepnd; simpl in *; tcsp.
    destruct a; simpl in *; tcsp; dest_cases w; eauto.
  Qed.
  Hint Resolve has_comp_implies_in_subs : comp.

  (* Move to some ComponentSM file *)
  Lemma in_subs_implies_has_comp :
    forall {n} cn (l : n_procs n),
      in_subs cn l = true -> has_comp cn l.
  Proof.
    induction l; introv h; unfold has_comp in *; exrepnd; simpl in *; tcsp.
    destruct a; simpl in *; tcsp; dest_cases w; eauto.
  Qed.
  Hint Resolve in_subs_implies_has_comp : comp.

  (* Move to some ComponentSM file *)
  Lemma proc2at0_at2sm :
    forall {cn} (p : n_proc_at 0 cn),
      proc2at0 (at2sm p) = sm2p0 p.
  Proof.
    tcsp.
  Qed.
  Hint Rewrite @proc2at0_at2sm : comp.

End MinBFTcount_gen_cond.


Hint Resolve in_subs_implies_has_comp : comp.
(*Hint Resolve has_comp_implies_in_subs : comp.*)
Hint Rewrite @proc2at0_at2sm : comp.


Hint Resolve is_M_break_out_preserves_ex_entry : minbft.
Hint Resolve is_M_break_out_preserves_ex_entry_2 : minbft.
Hint Resolve invalid_commit_false_implies_eq_commit2view : minbft.
Hint Resolve invalid_commit_false_implies_eq_commit2sender_i : minbft.
Hint Resolve cond_LOGname_ex_entry_implies_preserves : minbft.
Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry : minbft.
Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log : minbft.
Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_log_my : minbft.
Hint Resolve preserves_is_M_break_out_LOGname_implies_ex_entry_implies_ex_entry_prep : minbft.
Hint Resolve is_M_break_out_preserves_ex_entry2 : minbft.


Hint Rewrite @mk_my_commit_commit2ui_j : minbft.
Hint Rewrite @ui2counter_commit2ui_i_as_commit2counter_i : minbft.



Definition break_something (P:Type) (e:P) := e.

Notation "'BREAK'" :=
  (@break_something _ _).

Lemma break_something_eq : forall (e:Type),
  e = (@break_something _ e).
Proof. auto. Qed.

Lemma break_something_hide : forall (e:Type),
  e -> (@break_something _ e).
Proof. auto. Qed.

Lemma break_something_show : forall (e:Type),
  (@break_something _ e) -> e.
Proof. auto. Qed.

Ltac show_break_something H :=
  apply break_something_show in H.

Ltac hide_break_something H :=
  apply break_something_hide in H.

Ltac show_all_break_something :=
  repeat (match goal with
          | [ H : @break_something _ _  |- _ ] => show_break_something H
          end).

Ltac hbreak2sim :=
  match goal with
  | [ H : is_M_break_mon _ _ _ |- _ ] =>
    let H' := fresh H in
    dup H as H'; hide_break_something H';
    apply @is_M_break_mon_preserves_subs in H;
    simpl; eauto 3 with comp minbft; pwf;[]

  | [ H : is_M_break_out _ _ _ |- _ ] =>
    let q  := fresh "q" in
    let h1 := fresh H in
    let h2 := fresh H in
    let H' := fresh H in
    dup H as H'; hide_break_something H';
    apply @is_M_break_out_preserves_subs in H;
    eauto 3 with comp minbft;
    destruct H as [q [h1 h2] ]; repnd; subst; simpl in *;pwf;[];
    try (apply similar_sms_at2sm_sm2p0 in h2; exrepnd; subst);
    simpl in *; tcsp;[]
  end.

Ltac hbreak2sims := repeat hbreak2sim.

Ltac prove_in_subs :=
  apply has_comp_implies_in_subs; repeat prove_has_comp.
