Require Export ComponentSM.

Require Import Program.
Require Import Coq.Init.Wf.


(* Adapted from Simulator.v *)

Section RunSM.

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

  Context { base_fun_io : @baseFunIO }.
  Context { base_state_fun : @baseStateFun }.
  Context { trusted_state_fun : @trustedStateFun }.

  Class Time :=
    {
      Time_type     : Type;
      Time_get_time : unit -> Time_type;
      Time_sub      : Time_type -> Time_type -> Time_type;
      Time_2string  : Time_type -> String.string;
    }.

  Context { time : Time }.

  (* DirectedMsg with timestamps *)
  Record TimedDirectedMsg :=
    MkTimedDMsg
    {
      tdm_dmsg : DirectedMsg;
      tdm_time : Time_type;
    }.

  Definition TimedDirectedMsgs := list TimedDirectedMsg.

  Record SimState :=
    MkSimState
      {
        (* system *)
        ss_fls          : funLevelSpace;
        ss_sys          : M_USystem ss_fls;

        (* the number indicates how many messages have been sent so far *)
        ss_step         : nat;

        (* messages in flight from the outside (clients) *)
        ss_out_inflight : DirectedMsgs;

        (* messages in flight from the inside (replicas) *)
        ss_in_inflight   : DirectedMsgs;

        (* log of messages delivered so far *)
        ss_delivered    : TimedDirectedMsgs;
      }.

  Definition replace_out_inflight (s : SimState) (l : DirectedMsgs) : SimState :=
    MkSimState
      (ss_fls s)
      (ss_sys s)
      (ss_step s)
      l
      (ss_in_inflight s)
      (ss_delivered s).

  Definition replace_in_inflight (s : SimState) (l : DirectedMsgs) : SimState :=
    MkSimState
      (ss_fls s)
      (ss_sys s)
      (ss_step s)
      (ss_out_inflight s)
      l
      (ss_delivered s).

  Definition MkInitSimState
             {F    : funLevelSpace}
             (sys  : M_USystem F)
             (msgs : DirectedMsgs) : SimState :=
    MkSimState F sys 0 msgs [] [].

  Definition M_run_ls_on_this_one_msg
             {L S}
             (ls : LocalSystem L S)
             (m  : msg) : LocalSystem L S * DirectedMsgs :=
    match M_run_ls_on_input ls (msg_comp_name S) m with
    | (ls,Some msgs) => (ls, msgs)
    | (ls,None) => (ls,[])
    end.

  Definition run_ls_with_time {L S}
             (ls : LocalSystem L S)
             (m  : msg)
             (t  : PosDTime) : LocalSystem L S * DirectedMsgs * Time_type :=
    let t1 := Time_get_time tt in
    let (ls',msgs) := M_run_ls_on_this_one_msg ls m in
    let t2 := Time_get_time tt in
    (ls', msgs, t2).

  Definition dmsg2one_dst (dm : DirectedMsg) d : DirectedMsg :=
    MkDMsg (dmMsg dm) [d] (dmDelay dm).

  (* run MonoSimulationState on the in flight messages that came from the client *)
  Definition run_sim_on_nth_out (s : SimState) (n : nat) : SimState :=
    match decomp_nth (ss_out_inflight s) n with
    | None => s
    | Some (iseg, dmsg, fseg) =>
      (* dmDst is list of destination msgs (defined in model/Msg.v) *)
      match dmDst dmsg with
      | [] => replace_out_inflight s (iseg ++ fseg)
      | dst :: dsts =>
        match run_ls_with_time (ss_sys s dst) (dmMsg dmsg) ('0) with
        | (ls', outs, time) =>
          MkSimState
            (ss_fls s)
            (fun name=>
               match name_dec dst name return LocalSystem (fls_level (ss_fls s) name) (fls_space (ss_fls s) name) with
               | left q => eq_rect _ (fun dst => LocalSystem (fls_level (ss_fls s) dst) (fls_space (ss_fls s) dst)) ls' _ q
               | _ => ss_sys s name
               end)
            (S (ss_step s))
            (* outside system: *)
            (if nullb dsts
             then iseg ++ fseg
             else iseg ++ MkDMsg (dmMsg dmsg) dsts ('0) :: fseg)
            (* inside system: *)
            (outs ++ ss_in_inflight s)
            (* delivered messages*)
            (MkTimedDMsg (dmsg2one_dst dmsg dst) time :: ss_delivered s)
        end
      end
    end.

  Definition run_sim_on_nth_in (s : SimState) (n : nat) (b : bool) : SimState :=
    match decomp_nth (ss_in_inflight s) n with
    | None => run_sim_on_nth_out s n

    | Some (iseg, dmsg, fseg) =>
      match dmDst dmsg with
      | [] => replace_in_inflight s (iseg ++ fseg)
      | dst :: dsts =>
        match run_ls_with_time (ss_sys s dst) (dmMsg dmsg) ('0) with
        | (ls', outs, time) =>
          MkSimState
            (ss_fls s)
            (fun name=>
               match name_dec dst name return LocalSystem (fls_level (ss_fls s) name) (fls_space (ss_fls s) name) with
               | left q => eq_rect _ (fun dst => LocalSystem (fls_level (ss_fls s) dst) (fls_space (ss_fls s) dst)) ls' _ q
               | _ => ss_sys s name
               end)
            (S (ss_step s))
            (* outside system: *)
            (ss_out_inflight s)
            (* inside system: *)
            (if b
             then if nullb dsts
                  then iseg ++ outs ++ fseg
                  else iseg ++ outs ++ MkDMsg (dmMsg dmsg) dsts ('0) :: fseg
             else if nullb dsts
                  then iseg ++ fseg ++ outs
                  else iseg ++ MkDMsg (dmMsg dmsg) dsts ('0) :: fseg ++ outs)
            (* delivered messages*)
            (MkTimedDMsg (dmsg2one_dst dmsg dst) time :: ss_delivered s)
        end
      end
    end.

  Definition run_sim_out (s : SimState) : SimState :=
    run_sim_on_nth_out s 0.

  Definition run_sim_in (s : SimState) : SimState :=
    run_sim_on_nth_in s 0 false (* false means append outputs *).

  Record Round :=
    MkRound
      {
        round_pos : nat; (* the position of the message we want to send *)
        round_num : nat; (* the number of times we want to send a message at this position *)
      }.

  Definition Rounds := list Round.

  Record Switch :=
    MkSwitch
      {
        switch_step : nat; (* the step at which we want to switch between internal/external messages *)
        switch_pos  : nat; (* the position of the message we want to switch *)
      }.

  Definition Switches := list Switch.

  Fixpoint find_switch (step : nat) (L : Switches) : option nat :=
    match L with
    | [] => None
    | MkSwitch s p :: L => if eq_nat_dec step s then Some p else find_switch step L
    end.


  Fixpoint rounds_size (l : Rounds) : nat :=
    match l with
    | [] => 0
    | MkRound pos n :: rounds => S n + rounds_size rounds
    end.

  Lemma rounds_lt1 :
    forall pos rounds,
      rounds_size rounds < rounds_size (MkRound pos 0 :: rounds).
  Proof.
    introv; simpl; omega.
  Qed.

  Lemma rounds_lt2 :
    forall pos m rounds,
      rounds_size (MkRound pos m :: rounds) < rounds_size (MkRound pos (S m) :: rounds).
  Proof.
    introv; simpl; omega.
  Qed.

  Definition iterate_n_steps
             (rounds : Rounds)
             (switch : Switches)
             (s : SimState) : SimState :=
    @Fix
      Rounds
      (fun a b => lt (rounds_size a) (rounds_size b))
      (measure_wf lt_wf rounds_size)
      (fun rounds => list Switch -> SimState -> SimState)
      (fun rounds =>
         match rounds with
         | [] => fun F switch s => s
         | MkRound pos 0 :: rounds =>
           fun F switch s =>
             F rounds (rounds_lt1 pos rounds) switch s
         | MkRound pos (S m) :: rounds =>
           fun F switch s =>
             match find_switch (ss_step s) switch with
             | Some p =>

               let s1 := run_sim_on_nth_out s p in
               F (MkRound pos m :: rounds) (rounds_lt2 pos m rounds) switch s1

             | None =>

               let s1 := run_sim_on_nth_in s pos false in
               F (MkRound pos m :: rounds) (rounds_lt2 pos m rounds) switch s1

             end
         end) rounds switch s.

  Definition run_n_steps
             (l : list nat)
             (s : SimState) : SimState :=
    iterate_n_steps (map (fun p => MkRound p 1) l) [] s.

End RunSM.
