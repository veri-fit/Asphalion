Require Export ComponentSM2.
Require Export ComponentSM4.
Require Export DTimeN.


Inductive exmsg :=
| ADD1 (n : nat)
| ADD2 (n : nat)
| TOT  (n : nat).

Global Instance EX1Node : Node := MkNode nat deq_nat.
Global Instance EX1Key : Key := MkKey nat nat.
Global Instance EX1Msg : Msg := MkMsg exmsg.

Definition bstatefun (cn : CompName) : Type :=
  if String.string_dec (comp_name_kind cn) "STATE" then nat else unit.

Global Instance EX1baseFunIO : baseFunIO := MkBaseFunIO (fun _ => CIOnat).
Global Instance EX1baseStateFun : baseStateFun := MkBaseStateFun bstatefun.
Global Instance EX1IOTrustedFun : IOTrustedFun := MkIOTrustedFun (fun _ => MkIOTrusted nat nat 0).
Global Instance EX1trustedStateFun : trustedStateFun := MkTrustedStateFun (fun _ => nat).


(* ====== STATE ====== *)

Definition STATEname : CompName := MkCN "STATE" 0 true.

Definition STATEupdate : M_Update 0 STATEname _ :=
  fun (s : nat) i =>
    interp_s_proc
      ([R] (s + i, s + i)).

Definition STATE : n_proc _ _ :=
  build_m_sm STATEupdate 0.


(* ====== OP1 ====== *)

Definition OP1name : CompName := MkCN "OP" 1 false.

Definition OP1update : M_Update 1 OP1name _ :=
  fun s i =>
    interp_s_proc
      ((STATEname [C] i)
       [>>=] fun out =>
       [R] (tt, out)).

Definition OP1 : n_proc _ _ :=
  build_m_sm OP1update tt.


(* ====== OP2 ====== *)

Definition OP2name : CompName := MkCN "OP" 2 false.

Definition OP2update : M_Update 1 OP2name _ :=
  fun s i =>
    interp_s_proc
      ((STATEname [C] i)
       [>>=] fun _ =>
       (STATEname [C] i)
       [>>=] fun out =>
       [R] (tt, out)).

Definition OP2 : n_proc _ _ :=
  build_m_sm OP2update tt.


(* ====== Main ====== *)

Definition MAINname := msg_comp_name 0.

Definition MAINupdate : M_Update 2 MAINname _ :=
  fun s i =>
    interp_s_proc
      ((match i with
        | ADD1 n => (OP1name [C] n)
        | ADD2 n => (OP2name [C] n)
        | TOT  n => [R] n
        end) [>>=] (fun out => [R] (tt, [MkDMsg (TOT out) [] ('0)]))).

Definition MAIN : n_proc _ _ :=
  build_m_sm MAINupdate tt.


(* ====== Local System ====== *)

Definition progs : n_procs _ :=
  [
    MkPProc _ MAIN,
    MkPProc _ (lift_n_proc 1 OP1),
    MkPProc _ (lift_n_proc 1 OP2),
    MkPProc _ (lift_n_proc 2 STATE)
  ].

Definition ls : LocalSystem 3 0 := progs.


Definition test1 := call_procs_out ls MAINname [ADD1 2, ADD2 3] (ADD1 1).
Eval compute in test1.
