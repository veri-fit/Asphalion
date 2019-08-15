Require Export Ascii String.

Require Import QArith.
Require Export DTimeQ.

Require Export MinBFT.
Require Export RunSM.

Require Export ComponentSM2.
Require Export ComponentSM4.





(* ================== MINBFT CONTEXT ================== *)

Definition minbft_digest : Set := list nat.

Definition minbft_digest_def : minbft_digest := [].

Lemma minbft_digest_deq : Deq minbft_digest.
Proof.
  introv; apply list_eq_dec.
  apply deq_nat.
Defined.

Inductive sending_key_stub : Set :=
| minbft_sending_key_stub.

Inductive receiving_key_stub : Set :=
| minbft_receiving_key_stub.

Definition minbft_sending_key   : Set := sending_key_stub.
Definition minbft_receiving_key : Set := receiving_key_stub.

(*Definition F : nat := 1.*)
Definition nreps (F : nat) : nat := 2 * F + 1.

Definition replica (F : nat) : Set := nat_n (nreps F).

Lemma replica_deq (F : nat) : Deq (replica F).
Proof.
  apply nat_n_deq.
Defined.

Definition reps2nat (F : nat) : replica F -> nat_n (nreps F) := fun n => n.

Lemma bijective_reps2nat (F : nat) : bijective (reps2nat F).
Proof.
  exists (fun n : nat_n (nreps F) => n); introv; unfold reps2nat; auto.
Defined.

Definition replica0 (F : nat) : replica F.
Proof.
  exists 0.
  apply leb_correct.
  unfold nreps.
  omega.
Defined.

Definition replica1 : replica 1.
Proof.
  exists 1.
  apply leb_correct.
  unfold nreps.
  omega.
Defined.

Definition replica2 : replica 1.
Proof.
  exists 2.
  apply leb_correct.
  unfold nreps.
  omega.
Defined.

Definition nclients (C : nat) : nat := S C.

Definition client (C : nat) : Set := nat_n (nclients C).

Definition client0 (C : nat) : client C.
Proof.
  exists 0.
  apply leb_correct.
  unfold nclients.
  omega.
Defined.

Lemma client_deq (C : nat) : Deq (client C).
Proof.
  apply nat_n_deq.
Defined.

Definition clients2nat (C : nat) : client C -> nat_n (nclients C) := fun n => n.

Lemma bijective_clients2nat (C : nat) : bijective (clients2nat C).
Proof.
  exists (fun n : nat_n (nclients C) => n); introv; unfold clients2nat; auto.
Defined.

Inductive minbft_data_message :=
| minbft_data_message_plus (n : nat)
| minbft_data_message_minus (n : nat).

Lemma minbft_data_message_deq : Deq minbft_data_message.
Proof.
  introv; destruct x as [x|x], y as [y|y];
    destruct (deq_nat x y); prove_dec.
Defined.

Definition minbft_result := nat.

Lemma minbft_result_deq : Deq minbft_result.
Proof.
  introv; apply deq_nat.
Defined.

Definition minbft_sm_state := nat.

Definition minbft_sm_initial_state : minbft_sm_state := 0.

Definition minbft_sm_update
           (C : nat)
           (c : client C)
           (s : minbft_sm_state)
           (m : minbft_data_message) : minbft_result * minbft_sm_state :=
  match m with
  | minbft_data_message_plus  n => let x := s + n in (x,x)
  | minbft_data_message_minus n => let x := s - n in (x,x)
  end.

Definition F := 1.
Definition C := 0.

Global Instance MinBFT_I_context : MinBFT_context :=
  Build_MinBFT_context
    minbft_digest
    minbft_digest_deq
    minbft_sending_key
    minbft_receiving_key
    F
    (replica F)
    (replica_deq F)
    (reps2nat F)
    (bijective_reps2nat F)
    (nclients C)
    (client C)
    (client_deq C)
    (clients2nat C)
    (bijective_clients2nat C)
    minbft_data_message
    minbft_data_message_deq
    minbft_result
    minbft_result_deq
    minbft_sm_state
    minbft_sm_initial_state
    (minbft_sm_update C).




(* =========================== *)
(* ====== GENERIC STUFF ====== *)

(* Replace during extraction *)
Inductive ref_stub (T : Type) :=
| ref_stub_cons (t : T).
Global Arguments ref_stub_cons [T] _.

(* Replace during extraction *)
Definition ref_stub_get {T : Type} (t : ref_stub T) : T :=
  match t with
  | ref_stub_cons t => t
  end.

(* Replace during extraction *)
Definition ref_stub_update {T : Type} (r : ref_stub T) (t : T) : unit := tt.

Definition lookup_table : ref_stub (list {cn : CompName & {n : nat & cio_I (fio cn) -> (unit * cio_O (fio cn))}}) :=
  ref_stub_cons [].

Definition update_lookup (level : nat) (name : CompName) (sm : cio_I (fio name) -> (unit * cio_O (fio name))) :=
  ref_stub_update
    lookup_table
    ((existT _ name (existT _ level sm)) :: ref_stub_get lookup_table).

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
  Definition state : ref_stub (sf sm.name) := ref_stub_cons (sm2state sm.sm).

  Definition update (i : cio_I (fio sm.name)) : unit * cio_O (fio sm.name) :=
    let (sop,o) := M_break_nil (sm2update sm.sm (ref_stub_get state) i) in
    let u := match sop with | Some s => ref_stub_update state s| None => tt end in
    (u,o).

  Fixpoint run (l : list (cio_I (fio sm.name))) : list (cio_O (fio sm.name)) :=
    match l with
    | [] => []
    | i :: rest => snd (update i) :: run rest
    end.

  Definition upd_lkup := update_lookup sm.level sm.name update.
End Msm.

Module Msmat (sm : SMat).
  Definition state : ref_stub (sf sm.name) := ref_stub_cons (ComponentSM.sm_state sm.sm).

  Definition update (i : cio_I (fio sm.name)) : unit * cio_O (fio sm.name) :=
    let (sop,o) := M_break_nil (sm_update sm.sm (ref_stub_get state) i) in
    let u := match sop with | Some s => ref_stub_update state s | None => tt end in
    (u,o).

  Fixpoint run (l : list (cio_I (fio sm.name))) : list (cio_O (fio sm.name)) :=
    match l with
    | [] => []
    | i :: rest => snd (update i) :: run rest
    end.

  Definition upd_lkup := update_lookup sm.level sm.name update.
End Msmat.

(* =========================== *)




(* ================== SIGNATURE ================== *)

Definition minbft_create_signature
           (m  : MinBFT_Bare_Msg)
           (ks : sending_keys) : list MinBFT_digest := [minbft_digest_def].

Definition minbft_verify_signature
           (m : MinBFT_Bare_Msg)
           (n : name)
           (k : receiving_key)
           (a : MinBFT_digest) : bool := true.

Global Instance MinBFT_I_auth : MinBFT_auth :=
  MkMinBFT_auth minbft_create_signature minbft_verify_signature.


Definition minbft_lookup_replica_sending_key   (src : Rep)    : minbft_sending_key   := minbft_sending_key_stub.
Definition minbft_lookup_replica_receiving_key (dst : Rep)    : minbft_receiving_key := minbft_receiving_key_stub.
Definition minbft_lookup_client_sending_key    (c   : Client) : minbft_sending_key   := minbft_sending_key_stub.
Definition minbft_lookup_client_receiving_key  (c   : Client) : minbft_receiving_key := minbft_receiving_key_stub.

Definition initial_minbft_local_key_map_replicas (src : name) : local_key_map :=
  match src with
  | MinBFT_replica i =>
    MkLocalKeyMap
      (map (fun c => MkDSKey [MinBFT_client c] (minbft_lookup_client_sending_key c)) clients)
      (map (fun c => MkDRKey [MinBFT_client c] (minbft_lookup_client_receiving_key c)) clients)
  | MinBFT_client _ => MkLocalKeyMap [] []
  end.

Global Instance MinBFT_I_keys : MinBFT_initial_keys :=
  MkMinBFT_initial_keys initial_minbft_local_key_map_replicas.



(* ================== USIG HASH ================== *)

Definition minbft_create_hash_usig
           (hd : HashData)
           (lk : local_key_map) : MinBFT_digest := [].

Definition minbft_verify_hash_usig
           (hd : HashData)
           (d  : MinBFT_digest)
           (lk : local_key_map) : bool := true.

Lemma minbft_verify_create_hash_usig :
  forall (hd : HashData) (keys : local_key_map),
    minbft_verify_hash_usig hd (minbft_create_hash_usig hd keys) keys = true.
Proof.
  tcsp.
Qed.

Global Instance MinBFT_I_usig_hash : USIG_hash :=
  MkMinBFThash
    minbft_create_hash_usig
    minbft_verify_hash_usig
    minbft_verify_create_hash_usig.



(* ================== TIME ================== *)

Definition time_I_type : Set := unit.

Definition time_I_get_time : unit -> time_I_type := fun _ => tt.

Definition time_I_sub : time_I_type -> time_I_type -> time_I_type := fun _ _ => tt.

Definition time_I_2string : time_I_type -> string := fun _ => "".

Global Instance TIME_I : Time.
Proof.
  exists time_I_type.
  { exact time_I_get_time. }
  { exact time_I_sub. }
  { exact time_I_2string. }
Defined.



(* ================== PRETTY PRINTING ================== *)

(* Fix: to finish *)
Definition tokens2string (toks : Tokens) : string := "-".

(* Fix: to finish *)
Definition minbft_digest2string (d : minbft_digest) : string := "-".

(* Fix: to finish *)
Definition minbft_result2string (r : minbft_result) : string := nat2string r.

(* Fix: there's only one client anyway *)
Definition client2string (c : client C) : string := "-".

Definition timestamp2string (ts : Timestamp) : string :=
  match ts with
  | time_stamp n => nat2string n
  end.

Definition view2string (v : View) : string :=
  match v with
  | view n => nat2string n
  end.

Definition seq2string (s : SeqNum) : string :=
  match s with
  | seq_num n => nat2string n
  end.

Definition minbft_data_message2string (opr : minbft_data_message) : string :=
  match opr with
  | minbft_data_message_plus  n => str_concat ["+", nat2string n]
  | minbft_data_message_minus n => str_concat ["-", nat2string n]
  end.

Definition nat_n2string {m} (n : nat_n m) : string := nat2string (proj1_sig n).

Definition replica2string (r : replica F) : string := nat_n2string r.

Definition bare_request2string (br : Bare_Request) : string :=
  match br with
  | bare_request c ts m =>
    str_concat [client2string c,
                ",",
                timestamp2string ts,
                ",",
                minbft_data_message2string m]
  end.

Definition request2string (r : Request) : string :=
  match r with
  | request br a => str_concat ["REQUEST(", bare_request2string br, ",", tokens2string a, ")"]
  end.

Definition bare_prepare2string (bp : Bare_Prepare) : string :=
  match bp with
  | bare_prepare v m =>
    str_concat [view2string v,
                ",",
                request2string m]
  end.

Definition pre_ui2string (pui : preUI) : string :=
  match pui with
  | Build_preUI id counter =>
    str_concat [replica2string id,
                ",",
                nat2string counter]
  end.

Definition ui2string (ui : UI) : string :=
  match ui with
  | Build_UI pui d =>
    str_concat [pre_ui2string pui,
                ",",
                minbft_digest2string d]
  end.

Definition bare_commit2string (bc : Bare_Commit) : string :=
  match bc with
  | bare_commit v m ui =>
    str_concat [view2string v,
                ",",
                request2string m,
                ",",
                ui2string ui]
  end.

Definition prepare2string (p : Prepare) : string :=
  match p with
  | prepare bp a => str_concat ["PREPARE(", bare_prepare2string bp, ",", ui2string a, ")"]
  end.

Definition commit2string (c : Commit) : string :=
  match c with
  | commit bc a => str_concat ["COMMIT(", bare_commit2string bc, ",", ui2string a, ")"]
  end.

Definition accept2string (r : Accept) : string :=
  match r with
  | accept r c => str_concat ["ACCEPT(", request2string r, ",", nat2string c, ")"]
  end.

Definition bare_reply2string (br : Bare_Reply) : string :=
  match br with
  | bare_reply req res i v => str_concat [request2string req, ",", nat2string res, ",", replica2string i, ",", view2string v]
  end.

Definition reply2string (r : Reply) : string :=
  match r with
  | reply br a => str_concat ["REPLY(", bare_reply2string br, ",", tokens2string a, ")"]
  end.


Definition msg2string (m : MinBFT_msg) : string :=
  match m with
  | MinBFT_request r => request2string r
  | MinBFT_reply r   => reply2string r
  | MinBFT_prepare p => prepare2string p
  | MinBFT_commit  c => commit2string  c
  | MinBFT_accept  a => accept2string  a
  | MinBFT_debug   s => s
  end.

Definition name2string (n : name) : string :=
  match n with
  | MinBFT_replica r => replica2string r
  | MinBFT_client c => client2string c
  end.

Fixpoint names2string (l : list name) : string :=
  match l with
  | [] => ""
  | [n] => name2string n
  | n :: ns => str_concat [name2string n, ",", names2string ns]
  end.

Definition delay2string (delay : nat) : string := nat2string delay.

Definition z2string (z : Z) : string := "".
Definition pos2string (p : positive) : string := "".

Definition q2string (q : Q) : string :=
  str_concat ["(" ,
              z2string (Qnum q),
              "/",
              pos2string (Qden q),
              ")"].

Definition posdtime2string (p : PosDTime) : string :=
  q2string (pos_dt_t p).

Definition DirectedMsg2string (dm : DirectedMsg) : string :=
  match dm with
  | MkDMsg msg dst delay =>
    str_concat [msg2string msg, ":", "[", names2string dst, "]", ":", posdtime2string delay]
  end.

Fixpoint DirectedMsgs2string (l : DirectedMsgs) : string :=
  match l with
  | [] => ""
  | [dm] => DirectedMsg2string dm
  | dm :: dmsgs => str_concat [DirectedMsg2string dm, CR, DirectedMsgs2string dmsgs]
  end.

Definition TimedDirectedMsg2string (m : TimedDirectedMsg) : string :=
  match m with
  | MkTimedDMsg dm time => str_concat [DirectedMsg2string dm, ":", time_I_2string time]
  end.

Fixpoint TimedDirectedMsgs2string (l : TimedDirectedMsgs) : string :=
  match l with
  | [] => ""
  | [dm] => TimedDirectedMsg2string dm
  | dm :: dmsgs => str_concat [TimedDirectedMsg2string dm, CR, TimedDirectedMsgs2string dmsgs]
  end.

Definition SimState2string (s : SimState) : string :=
  match s with
  | MkSimState fls sys step out_inflight in_inflight delivered =>
    str_concat
      [CR,
       "====== STEP ======",
       CR,
       nat2string step,
       CR,
       "====== IN FLIGHT (from outside the system) ======",
       CR,
       DirectedMsgs2string out_inflight,
       CR,
       "====== IN FLIGHT (from inside the system) ======",
       CR,
       DirectedMsgs2string in_inflight,
       CR,
       "====== DELIVERED ======",
       CR,
       TimedDirectedMsgs2string delivered,
       CR]
  end.

  (* ================== SYSTEM ================== *)

  (* FIX: do we need this one? *)
  Definition dummy_usig_initial_state : USIG_state :=
    Build_USIG
      replica1
      0
      (MkLocalKeyMap [] []).

  (* do we need this one? *)
  Definition dummy_log_initial_state : LOG_state := [].

  (* do we need this one? *)
  Definition dummy_initial_state : MAIN_state :=
    Build_State
      (MkLocalKeyMap [] [])
      initial_view
      MinBFT_sm_initial_state
      initial_latest_executed_counter
      initial_latest_executed_request
      initial_highest_received_counter_value
      None.

  Definition dummy_LocalSystem : MLocalSystem 0 1 :=
    MkLocalSystem
      (MP_haltedSM munit_comp_name 0 tt)
      [].

  Definition MinBFT_instance_sys : M_USystem MinBFTfunLevelSpace :=
    fun name =>
      match name with
      | MinBFT_replica n => MinBFTlocalSys n
      | _ =>  MkLocalSystem (MP_haltedSM munit_comp_name 0 tt) []
      end.

(* ================== STATE ================== *)

Definition mk_request
           (c  : Client)
           (ts : Timestamp)
           (m  : MinBFT_data_message) : msg :=
  MinBFT_request (request (bare_request c ts m) [minbft_digest_def]).

Definition send_request
           (c  : Client)
           (ts : Timestamp)
           (m  : MinBFT_data_message) :=
  MkDMsg
    (mk_request c ts m)
    [MinBFT_replica (MinBFTprimary (view 0))]
    ('0).

Definition minbft_init_sim_state : SimState :=
  let c  := client0 C in
  let ts := time_stamp 0 in
  let m  := minbft_data_message_plus 17 in
  MkInitSimState
    MinBFTsys
    [send_request c ts m].

Definition minbft_sim_state1 : SimState :=
  run_n_steps [0,0] minbft_init_sim_state.

Eval compute in (let p0  := replica0 F in
                 let km  := initial_minbft_local_key_map_replicas (MinBFT_replica p0) in
                 let c   := client0 C in
                 let ts  := time_stamp 0 in
                 let m   := minbft_data_message_plus 17 in
                 let r   := request (bare_request c ts m) [minbft_digest_def] in
                 let s   := initial_state p0 in
                 valid_request p0 km r s).

Eval compute in (let v   := view 0 in
                 let p0  := replica0 F in
                 let p1  := replica1 in
                 let km  := initial_minbft_local_key_map_replicas (MinBFT_replica p1) in
                 let c   := client0 C in
                 let ts  := time_stamp 0 in
                 let m   := minbft_data_message_plus 17 in
                 let r   := request (bare_request c ts m) [minbft_digest_def] in
                 let ui  := snd (create_UI v r (USIG_initial p0)) in
                 let p   := prepare (bare_prepare v r) ui in
                 let s   := initial_state p1 in
                 valid_prepare p1 km v p s).




(* ================== EXTRACTION ================== *)


Extraction Language Ocaml.


(* printing stuff *)
Extract Inlined Constant print_endline => "Prelude.print_coq_endline".
Extract Inlined Constant nat2string    => "Prelude.char_list_of_int".
Extract Inlined Constant CR            => "['\n']".

(* numbers *)
Extract Inlined Constant Nat.modulo    => "(mod)".

(* lists *)
Extract Inlined Constant forallb => "List.for_all".
Extract Inlined Constant existsb => "List.exists".
Extract Inlined Constant length  => "List.length".
Extract Inlined Constant app     => "List.append".
Extract Inlined Constant map     => "List.map".
Extract Inlined Constant filter  => "List.filter".

(* timing stuff *)
Extract Inlined Constant time_I_type     => "float".
Extract Inlined Constant time_I_get_time => "Prelude.Time.get_time".
Extract Inlined Constant time_I_sub      => "Prelude.Time.sub_time".
Extract Inlined Constant time_I_2string  => "Prelude.Time.time2string".


Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.


(* do we still need this one?
Definition MinBFT_sim_state_pp : unit :=
  print_endline (SimState2string minbft_sim_state1).

Extraction "MinBFTtest.ml" MinBFT_sim_state_pp.
*)

Definition local_system:=
  @MinBFTlocalSys.



(* ================== MODULES ================== *)

Parameter self : Rep.

(* ====== USIG ====== *)

Module SMUSIG <: SM.
  Definition level := 1.
  Definition name  := USIGname.
  Definition sm    := USIG_comp self.
End SMUSIG.

Module MUSIG := Msm (SMUSIG).


(* ====== LOG ====== *)

Module SMLOG <: SM.
  Definition level := 1.
  Definition name  := LOGname.
  Definition sm    := LOG_comp.
End SMLOG.

Module MLOG := Msm (SMLOG).


(* ====== Main ====== *)

Module SMMAIN <: SMat.
  Definition level := 1.
  Definition name  := MAINname.
  Definition sm    := MAIN_comp self.
End SMMAIN.

Module MMAIN := Msmat (SMMAIN).


Definition mtest : unit :=
  let c  := client0 C in
  let ts := time_stamp 0 in
  let m  := minbft_data_message_plus 17 in
  print_endline (DirectedMsgs2string (snd (MMAIN.update (mk_request c ts m)))).

(* =========================== *)
(* =========================== *)



Extract Inductive ref_stub => "ref" ["ref"].
Extract Inlined Constant ref_stub_get => "!".
Extract Inlined Constant ref_stub_update => "(:=)".

Extract Inductive sigT => "(*)" [""].

Extract Inductive Proc => "Prelude.SM.id" ["Prelude.SM.ret"
                                             "Prelude.SM.bind"
                                             "Prelude.SM.call_proc lookup_table"].
(*Extract Inductive MP_StateMachine => "MP_SM" ["Prelude.SM.mk_sm"].*)

(*Extract Constant MP_SM "'p" => "n_proc".*)
Extract Constant n_proc => "unit mP_StateMachine".
Extract Constant M_n "'a" => "'a".
Extract Constant M_p "'a" "'b" => "'b".
Extract Constant UProc "'s" => "'s -> cio_I -> ('s * cio_O) m_n".


Extract Constant bind => "fun _ _ _ _ _ _ _ _ _ m f -> Prelude.SM.bind (m,f)".
Extract Constant ret => "fun _ _ _ _ _ _ _ _ _ a -> Prelude.SM.ret a".
Extract Constant M_on_pred => "fun _ _ _ _ _ _ _ _ _ x -> x".
Extract Constant M_simple_break => "fun _ _ _ _ _ _ _ _ _ sm subs f -> f sm".
Extract Constant M_break_nil => "fun _ _ _ _ _ _ _ _ _ sm -> sm".


Extraction Inline interp_s_proc.
Extraction Inline proc_bind_pair.
Extraction Inline to_proc_some_state.



Extract Inlined Constant interp_proc => "(fun _ _ _ _ _ _ _ _ _ x -> x)".
(*Extract Inlined Constant interp_s_proc => "".
Extract Inlined Constant incr_n_proc => "".
Extract Inlined Constant incr_n_nproc => "".
Extract Inlined Constant incr_n_procs => "".
Extract Inlined Constant incr_pred_n_proc => "".
Extract Inlined Constant incr_pred_n_nproc => "".
Extract Inlined Constant incr_pred_n_procs => "".*)


Extract Inlined Constant M_StateMachine => "n_proc".
Extract Inlined Constant n_proc_at => "n_proc".
Extract Inlined Constant n_procs => "((unit mP_StateMachine) p_nproc) list".
(*Extract Inlined Constant sm_halted => "Prelude.SM.sm_halted".
Extract Inlined Constant sm_update => "Prelude.SM.sm_update".
Extract Inlined Constant sm_state => "Prelude.SM.sm_state".*)

(*Extraction Implicit lift_M_O [1].*)


(*Extract Constant M_Update "'a" => "'a -> cio_I -> option 'a * cio_O".*)
(*Extract Constant n_nproc => "unit MP_StateMachine".*)
(*Extract Constant n_proc_at => "unit MP_StateMachine".*)


Extraction "MinbftReplica.ml" lookup_table MUSIG MLOG MMAIN mtest.

(*
Then:
    (1) Move [lookup_table] to just above its first use (I'll fix that later)
    (2) change the definition of self into [Obj.magic 0]
    (3) Compile using: ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix MinbftReplica.native
*)
