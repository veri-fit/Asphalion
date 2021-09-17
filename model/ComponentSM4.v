Require Export ComponentSM.


Section ComponentSM4.

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


  Definition op_state_o cn (S : Type) := option (option S * cio_O (fio cn)).
  Definition op_st_o cn := option (option (sf cn) * cio_O (fio cn)).

  (*Definition M_run_update_on_inputs {S} {n} {cn}
             (s    : S)
             (upd  : M_Update n cn S)
             (l    : list (cio_I (fio cn)))
             (i    : cio_I (fio cn))
    : M_n n (op_state_o cn S) :=
    (M_run_update_on_list s upd (map Some l))
      >>o= fun s => M_op_update upd s (Some i).*)

  (*Definition M_run_sm_on_inputs {n} {cn}
             (sm : n_proc n cn)
             (l  : list (cio_I (fio cn)))
             (i  : cio_I (fio cn))
    : M_n (sm2level sm) (op_st_o cn) :=
    M_run_update_on_inputs (sm2state sm) (sm2update sm) l i.*)

  (*Definition M_output_sm_on_inputs {n} {cn}
             (sm : n_proc n cn)
             (l  : list (cio_I (fio cn)))
             (i  : cio_I (fio cn))
    : M_n (sm2level sm) (option (cio_O (fio cn))) :=
    (M_run_sm_on_inputs sm l i)
      >>o= fun x => ret _ (Some (snd x)).*)

  Definition M_simple_break {n} {S} {O}
             (sm   : M_n n S)
             (subs : n_procs n)
             (F    : S -> O) : O :=
    F (snd (sm subs)).

  Definition M_break_nil {n} {S} (sm : M_n n S) : S :=
    snd (sm []).

  Fixpoint call_procs
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             (cn : CompName)
             (l  : list (PosDTime * cio_I (fio cn)))
    : LocalSystem Lv Sp :=
    match l with
    | [] => ls
    | (t,i) :: l =>
      let ls' := fst (call_proc cn t i ls) in
      call_procs ls' cn l
    end.

  Definition call_procs_out
             {Lv Sp}
             (ls : LocalSystem Lv Sp)
             (cn : CompName)
             (l  : list (PosDTime * cio_I (fio cn)))
             (t  : PosDTime)
             (i  : cio_I (fio cn))
    : cio_O (fio cn) :=
    let ls' := call_procs ls cn l in
    snd (call_proc cn t i ls').


  (* None is for the halted process *)
  CoInductive Process (I O : Type) : Type :=
  | proc (f : option (PosDTime -> I -> (Process I O * O))).
  Arguments proc [I] [O] _.

  Definition haltedProc {I O} : Process I O := proc None.

  CoFixpoint build_process {n} {cn}
             (upd : M_Update n cn (sf cn))
             (s   : sf cn) : Process (cio_I (fio cn)) (cio_O (fio cn)) :=
    proc (Some
            (fun (t : PosDTime) (i : cio_I (fio cn)) =>
               match M_break_nil (upd s t i) with
               | (hsome s', out) => (build_process upd s', out)
               | (halt_local, out) => (haltedProc, out)
               | (halt_global, out) => (haltedProc, out)
               end)).

  Definition n_proc_at2process {n} {cn}
             (sm : n_proc_at n cn) : Process (cio_I (fio cn)) (cio_O (fio cn)) :=
    build_process (sm_update sm) (sm_state sm).

  Definition n_proc2process {n} {cn}
             (sm : n_proc n cn) : Process (cio_I (fio cn)) (cio_O (fio cn)) :=
    build_process (sm2update sm) (sm2state sm).

  Record NProcess :=
    MkNProcess
      {
        np_name    : CompName;
        np_process : Process (cio_I (fio np_name)) (cio_O (fio np_name));
      }.

  Definition n_nproc2process {n}
             (sm : n_nproc n) : NProcess :=
    let (cn,p) := sm in
    MkNProcess cn (build_process (sm2update p) (sm2state p)).

  Record LocalProcess cn :=
    MkLocalProcess
      {
        lp_main :> Process (cio_I (fio cn)) (cio_O (fio cn));
        lp_subs : list NProcess;
      }.
  Global Arguments MkLocalProcess [cn] _ _.
  Global Arguments lp_main [cn] _.
  Global Arguments lp_subs [cn] _.

End ComponentSM4.
