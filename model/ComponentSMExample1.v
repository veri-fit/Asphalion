Require Export ComponentSM2.
Require Export ComponentSM4.
Require Export DTimeQ.
Require Export Ref.


Global Instance EX1Node : Node := MkNode nat deq_nat.
Global Instance EX1Key : Key := MkKey nat nat.
Global Instance EX1Msg : Msg := MkMsg nat.

Global Instance EX1baseFunIO : baseFunIO := MkBaseFunIO (fun _ => CIOnat).
Global Instance EX1baseStateFun : baseStateFun := MkBaseStateFun (fun _ => nat).
Global Instance EX1IOTrusted : IOTrusted := Build_IOTrusted nat nat 0.
Global Instance EX1trustedStateFun : trustedStateFun := MkTrustedStateFun nat.



(* =========================== *)
(* ====== GENERIC STUFF ====== *)
Module Type SM.
  Parameter level : nat.
  Parameter name  : CompName.
  Parameter sm    : n_proc level name.
End SM.

Module Type SMat.
  Parameter level : nat.
  Parameter name  : CompName.
  Parameter sm    : n_proc_at level name.
End SMat.

Module Msm (sm : SM).
  Definition state : ref (sf sm.name) := ref_cons (sm2state sm.sm).

  Definition update (i : cio_I (fio sm.name)) : unit * cio_O (fio sm.name) :=
    let (sop,o) := M_break_nil (sm2update sm.sm (get_ref state) i) in
    let u := match sop with | Some s => update_ref state s| None => tt end in
    (u,o).

  Fixpoint run (l : list (cio_I (fio sm.name))) : list (cio_O (fio sm.name)) :=
    match l with
    | [] => []
    | i :: rest => snd (update i) :: run rest
    end.

  Definition upd_lkup := update_lookup sm.level sm.name update.
End Msm.

Module Msmat (sm : SMat).
  Definition state : ref (sf sm.name) := ref_cons (sm_state sm.sm).

  Definition update (i : cio_I (fio sm.name)) : unit * cio_O (fio sm.name) :=
    let (sop,o) := M_break_nil (sm_update sm.sm (get_ref state) i) in
    let u := match sop with | Some s => update_ref state s | None => tt end in
    (u,o).

  Fixpoint run (l : list (cio_I (fio sm.name))) : list (cio_O (fio sm.name)) :=
    match l with
    | [] => []
    | i :: rest => snd (update i) :: run rest
    end.

  Definition upd_lkup := update_lookup sm.level sm.name update.
End Msmat.

(* =========================== *)



(* ====== A ====== *)

Definition Aname : CompName := MkCN "A" 0 true.

Definition A_update : M_Update 0 Aname _ :=
  fun (s : nat) i =>
    interp_s_proc
      ([R] (s + i, s + i)).

Definition A : n_proc 1 _ :=
  build_m_sm A_update 0.

Module SMA <: SM.
  Definition level := 1.
  Definition name  := Aname.
  Definition sm    := A.
End SMA.

Module MA := Msm (SMA).


(* ====== B ====== *)

Definition Bname : CompName := MkCN "B" 1 true.

Definition B_update : M_Update 1 Bname _ :=
  fun s i =>
    interp_s_proc
      ((Aname [C] i)
         [>>=] fun out =>
                 [R] (s + out + 1, s + out + 1)).

Definition B : n_proc _ _ :=
  build_m_sm B_update 0.

Module SMB <: SM.
  Definition level := 2.
  Definition name  := Bname.
  Definition sm    := B.
End SMB.

Module MB := Msm (SMB).


(* ====== C ====== *)

Definition Cname : CompName := MkCN "C" 2 true.

Definition C_update : M_Update 2 Cname _ :=
  fun s i =>
    interp_s_proc
      ((Bname [C] i)
         [>>=] fun out1 =>
                 (Bname [C] i)
                   [>>=] fun out2 =>
                           [R] (s + out1 + out2 + 2, s + out1 + out2 + 2)).

Definition C : n_proc _ _ :=
  build_m_sm C_update 0.

Module SMC <: SM.
  Definition level := 3.
  Definition name  := Cname.
  Definition sm    := C.
End SMC.

Module MC := Msm (SMC).


(* ====== Main ====== *)

Definition Mname := msg_comp_name 0.

Definition M_update : M_Update 3 Mname nat :=
  fun s i =>
    interp_s_proc
      ((Cname [C] i)
         [>>=] (fun out => [R] (s, [MkDMsg out [] ('0)]))).

Definition M : n_proc_at _ _ :=
  build_mp_sm M_update 0.

Module SMM <: SMat.
  Definition level := 3.
  Definition name  := Mname.
  Definition sm    := M.
End SMM.

Module MM := Msmat (SMM).


(* ====== Local System ====== *)

Definition progs : n_procs _ :=
  [
    MkPProc _ (incr_n_proc (incr_n_proc A)),
    MkPProc _ (incr_n_proc B),
    MkPProc _ C
  ].

Definition ls : _ := MkLocalSystem M progs.


Definition test1 := M_output_ls_on_inputs ls [17] 17.
Eval compute in test1.

Definition test2 := MM.run [17, 17].
Eval compute in test2.


(* =========================================================== *)
(* === EXTRACTION *)
(* =========================================================== *)


Extraction Language Ocaml.


Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.


Extract Inductive ref => "ref" ["ref"].
Extract Inlined Constant get_ref => "!".
Extract Inlined Constant update_ref => "(:=)".


Extract Inductive sigT => "(*)" [""].
Extract Inductive Proc => "'a" ["Prelude.SM.ret"
                                  "Prelude.SM.bind"
                                  "Prelude.SM.call_proc lookup_table"].

Extract Constant n_proc => "unit mP_StateMachine".
Extract Constant M_n "'a" => "'a".
Extract Constant M_p "'a" "'b" => "'b".

Extract Constant bind => "fun _ _ _ _ _ _ _ _ _ m f -> Prelude.SM.bind (m,f)".
Extract Constant ret => "fun _ _ _ _ _ _ _ _ _ a -> Prelude.SM.ret a".
Extract Constant M_on_pred => "fun _ _ _ _ _ _ _ _ _ x -> x".
Extract Constant M_simple_break => "fun _ _ _ _ _ _ _ _ _ sm subs f -> f sm".
Extract Constant M_break_nil => "fun _ _ _ _ _ _ _ _ _ sm -> sm".

Extraction Inline interp_s_proc.
Extraction Inline proc_bind_pair.
Extraction Inline to_proc_some_state.

Extract Inlined Constant interp_proc => "(fun _ _ _ _ _ _ _ _ _ x -> x)".
Extract Inlined Constant M_StateMachine => "n_proc".
Extract Inlined Constant n_proc_at => "n_proc".
Extract Inlined Constant n_procs => "((unit mP_StateMachine) p_nproc) list".


Extraction "test1.ml" (*MP_SM*) lookup_table MA MB MC MM test1.

(*
  Then:
    (1) fix [m_run_update_on_list] by removing the extra x/x0 arguments
    (2) Add this after the test to print the output:

let _ =
  match Obj.magic test1 with
   | {dmMsg = m; dmDst = d; dmDelay = t} :: _ ->
      print_endline (string_of_int (Obj.magic m))
   | _ -> ()

    (3) Compile using:
          ocamlbuild -tag thread -use-ocamlfind -package batteries test.native
 *)


Extraction "test2.ml" (*MP_SM*) lookup_table MA MB MC MM test2.


(*
  For test2, add:

let _ =
  let outs = Obj.magic test2 in
  List.iter (fun o ->
      match o with
      | ({dmMsg = m; dmDst = d; dmDelay = t} :: _) ->
         print_endline (string_of_int (Obj.magic m))
      | [] -> ())
      outs
*)



(* XXXXXXXXXXXXXXXXXXX *)

Inductive xxx :=
| XXX (a : nat) (b : nat).

Definition yyy : xxx := XXX 1 2.

Definition fnat := nat -> nat.

Fixpoint foo (d : nat) (n : nat) : fnat :=
  match n with
  | 0 => fun x => x
  | S m => fun x => foo d m x
  end.

Extraction Implicit foo [1].

Fixpoint bar (n : nat) : fnat := fun x => x.

Extraction "foo.ml" xxx yyy foo bar.
