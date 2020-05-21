Require Export ComponentSM3.


Section ComponentSMlift.

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

  Definition n_proc_at_default (lvl : nat) (cn : CompName) (s : sf cn) : n_proc_at lvl cn :=
    MkMPSM
      true
      (fun s i => ret _ (None, cio_default_O (fio cn)))
      s.

  Definition ls_default (lvl : nat) (cn : CompName) (s : sf cn) : LocalSystem lvl cn :=
    MkLocalSystem (n_proc_at_default lvl cn s) [].

  (* extract the sub-system with main component [cn2] within the system [ls]
     the state [s], is a default state to use in case we cannot build that system *)
  Definition extract_ls
             {L1 cn1}
             (L2 : nat) (cn2 : CompName)
             (s  : sf cn2)
             (ls : LocalSystem L1 cn1) : LocalSystem L2 cn2 :=
    match find_name cn2 (ls_subs ls) with
    | Some sm => (* a [n_proc L1 cn2] *)
      let pr := sm2at sm in (* a [n_proc_at (sm2level sm) cn2] *)
      match deq_nat (sm2level sm) L2 with
      | left q =>
        let pr' : n_proc_at L2 cn2 := eq_rect _ (fun n => n_proc_at n cn2) pr _ q in (* a [n_proc_at L2 cn2] *)
        MkLocalSystem pr' (select_n_procs L2 (ls_subs ls))
      | right q => ls_default L2 cn2 s
      end
    | None => ls_default L2 cn2 s
    end.

  Definition M_byz_run_ls_on_inputs
             {L cn}
             (ls  : LocalSystem L cn)
             (ins : list (trigger_info (cio_I (fio cn)))) : option (M_trusted (LocalSystem L cn)) :=
    M_break
      (M_byz_run_sm_on_list (at2sm (ls_main ls)) ins)
      (ls_subs ls)
      (fun subs' out =>
         map_op_untrusted
           out
           (fun s => upd_ls_main_state_and_subs ls s subs')).

  Definition cn2level {L S} (ls : LocalSystem L S) (cn : CompName) : nat :=
    match find_sub cn ls with
    | Some sm => sm2level sm
    | None => 0
    end.

  (* How can we have such "lifting" properties for higher-level components since
     we cannot access the state of the (non-trusted) sub-components if the machine
     has been compromised? *)
  Lemma M_byz_compose_step_trusted :
    forall {eo : EventOrdering} (e : Event)
           {L S}
           (ls : MLocalSystem L S)
           {cn}
           (sm : n_proc L cn)
           (ds : sf cn),
      are_procs_ls ls
      -> wf_ls ls
      -> find_sub cn ls = Some sm
      (* Regarding [sm2level sm = 0], see comments above [run_subs] *)
      -> sm2level sm = 0
      -> is_trusted_ls cn ls
      ->
      exists (ls1 ls2 : LocalSystem (cn2level cn) (l : list (cio_I (fio cn))),
        M_byz_state_ls_before_event_of_trusted ls e = Some s1
        /\ M_byz_state_ls_on_event_of_trusted ls e = Some s2
        /\ M_byz_run_ls_on_inputs (extract_ls (cn2level cn) ds ls) (map trigger_info_data l) = Some (M_nt ls').
  Proof.
  Qed.

End ComponentSMlift.
