Require Export Ascii String.

Require Import QArith.
Require Export DTimeQ.

Require Export MinBFT.
Require Export RunSM.
Require Export Ref.

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
    minbft_digest_def
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
  Definition state : ref (sf sm.name) := ref_cons (ComponentSM.sm_state sm.sm).

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



(* ================== MINBFT SIGNATURE ================== *)

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


(*Definition minbft_lookup_replica_sending_key   (src : Rep)    : minbft_sending_key   := minbft_sending_key_stub.
Definition minbft_lookup_replica_receiving_key (dst : Rep)    : minbft_receiving_key := minbft_receiving_key_stub.*)
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


Definition usig_lookup_replica_sending_key   (i : Rep) (src : Rep) : minbft_sending_key   := minbft_sending_key_stub.
Definition usig_lookup_replica_receiving_key (i : Rep) (dst : Rep) : minbft_receiving_key := minbft_receiving_key_stub.

Definition initial_usig_local_key_map_replicas (src : name) : local_key_map :=
  match src with
  | MinBFT_replica i =>
    MkLocalKeyMap
      (map (fun r => MkDSKey [MinBFT_replica r] (usig_lookup_replica_sending_key   i r)) reps)
      (map (fun r => MkDRKey [MinBFT_replica r] (usig_lookup_replica_receiving_key i r)) reps)
  | MinBFT_client _ => MkLocalKeyMap [] []
  end.

Global Instance USIG_I_keys : USIG_initial_keys :=
  MkUSIG_initial_keys initial_usig_local_key_map_replicas.

Definition minbft_create_hash_usig_stub (hd : HashData) (k : minbft_sending_key) : MinBFT_digest := [].
Definition minbft_verify_hash_usig_stub (hd : HashData) (r : Rep) (k : minbft_receiving_key) (d : MinBFT_digest) : bool := true.

Definition rep0 : Rep := nat2rep 0.

Definition minbft_create_hash_usig0
           (hd : HashData)
           (lk : local_key_map) : MinBFT_digest :=
  let rep := pre_ui_rid (hd_pre hd) in
  (* 1st [rep0] should be [rep] and 2nd should be recipient *)
  let key := usig_lookup_replica_sending_key rep0 rep0 in
  minbft_create_hash_usig_stub hd key.

Definition minbft_create_hash_usig
           (hd : HashData)
           (lk : local_key_map) : MinBFT_digest :=
  match lookup_dskeys lk rep0 with
  | MkDSKey _ key :: _ => minbft_create_hash_usig_stub hd key
  | _ => []
  end.

Definition minbft_verify_hash_usig0
           (hd : HashData)
           (d  : MinBFT_digest)
           (lk : local_key_map) : bool :=
  let rep := pre_ui_rid (hd_pre hd) in
  (* 1st [rep0] should be the replica doing the call and 2nd should be [rep] *)
  let key := usig_lookup_replica_receiving_key rep0 rep0 in
  (* [rep0] here because we don't have access to the replica name doing the call---it's not used anyway *)
  minbft_verify_hash_usig_stub hd rep0 key d.

Definition minbft_verify_hash_usig
           (hd : HashData)
           (d  : MinBFT_digest)
           (lk : local_key_map) : bool :=
  match lookup_drkeys lk rep0 with
  | MkDRKey _ key :: _ => minbft_verify_hash_usig_stub hd rep0 key d
  | _ => true
  end.

Lemma minbft_verify_create_hash_usig :
  forall (hd : HashData) (keys : local_key_map),
    minbft_verify_hash_usig hd (minbft_create_hash_usig hd keys) keys = true.
Proof.
  introv.
  unfold minbft_verify_hash_usig, minbft_create_hash_usig.
  remember (lookup_drkeys keys (MinBFT_replica rep0)) as w; destruct w; auto;
    try (complete (destruct d;destruct w; auto)).
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

Definition print_endline : string -> unit := fun _ => tt.
Definition nat2string (n : nat) : string := "-".

Definition CR : string := String (ascii_of_nat 13) "".

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

Fixpoint str_concat (l : list String.string) : String.string :=
  match l with
  | [] => ""
  | s :: ss => String.append s (str_concat ss)
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
  | Build_preUI rid cid counter =>
    str_concat [replica2string rid,
                ",",
                nat2string cid,
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
  | bare_reply req res i v => str_concat [request2string req, ",", nat2string res, ",", replica2string i]
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



(* ================== EXTRACTION ================== *)


Extraction Language OCaml.

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


(* == crypto stuff == *)
(* === COMMENT OUT THIS PART IF YOU DON'T WANT TO USE KEYS ===*)
Extract Inlined Constant minbft_digest => "Cstruct.t".
Extract Inlined Constant minbft_digest_deq => "(=)".
Extract Inlined Constant minbft_digest_def => "Cstruct.empty".

Extract Inlined Constant minbft_sending_key   => "Nocrypto.Rsa.priv".
Extract Inlined Constant minbft_receiving_key => "Nocrypto.Rsa.pub".
(*Extract Inlined Constant minbft_lookup_replica_sending_key   => "RsaKeyFun.lookup_replica_sending_key".
Extract Inlined Constant minbft_lookup_replica_receiving_key => "RsaKeyFun.lookup_replica_receiving_key".*)
Extract Inlined Constant minbft_lookup_client_receiving_key  => "RsaKeyFun.lookup_client_receiving_key".
Extract Inlined Constant minbft_lookup_client_sending_key    => "RsaKeyFun.lookup_client_sending_key".

Extract Inlined Constant minbft_create_signature => "RsaKeyFun.sign_list".
Extract Inlined Constant minbft_verify_signature => "RsaKeyFun.verify_one".

Extract Inlined Constant usig_lookup_replica_sending_key   => "MacKeyFun.lookup_replica_key".
Extract Inlined Constant usig_lookup_replica_receiving_key => "MacKeyFun.lookup_replica_key".

(*Extract Inlined Constant minbft_create_hash_usig => "Obj.magic (Hash.create_hash_object)".
Extract Inlined Constant minbft_verify_hash_usig => "Obj.magic (Hash.verify_hash_object)".*)
Extract Inlined Constant minbft_create_hash_usig_stub => "Obj.magic (MacKeyFun.sign_one)".
Extract Inlined Constant minbft_verify_hash_usig_stub => "Obj.magic (MacKeyFun.verify_one)".
(* === --- === *)


Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.


Definition local_system:=
  @MinBFTlocalSys.




(* ================== MODULES ================== *)

Definition self : Rep := (replica0 F).


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


Definition mk_request
           (c   : Client)
           (ts  : Timestamp)
           (m   : MinBFT_data_message)
           (tok : Tokens) : Request :=
  request (bare_request c ts m) tok.

Definition mk_minbft_request
           (c   : Client)
           (ts  : Timestamp)
           (m   : MinBFT_data_message)
           (tok : Tokens) : msg :=
  MinBFT_request (mk_request c ts m tok).

Definition mtest : unit :=
  let c   := client0 C in
  let ts  := time_stamp 0 in
  let m   := minbft_data_message_plus 17 in
  let tok := [minbft_digest_def] in
  print_endline (DirectedMsgs2string (snd (MMAIN.update (mk_minbft_request c ts m tok)))).

Definition mk_ui r c d : UI := Build_UI (Build_preUI r cid0 c) d.

Definition mk_create_ui_out r c d : USIG_output_interface :=
  create_ui_out (Some (mk_ui r c d)).

Definition mk_verify_ui_out b : USIG_output_interface :=
  verify_ui_out b.

Definition mk_create_ui_in view client timestamp op toks : USIG_input_interface :=
  create_ui_in (view, mk_request client timestamp op toks, cid0, cid0).

Definition mk_verify_ui_in view client timestamp op toks rep digest count :=
  verify_ui_in (view, mk_request client timestamp op toks, mk_ui rep digest count).

Definition execute_request (i : USIG_input_interface) : USIG_output_interface :=
  snd (MUSIG.update i).



(* ====== To run USIG inside SGX ====== *)
Parameter register : forall {A: Type}, String.string -> A -> unit.

Definition u1 : unit := register "execute_request" execute_request.
Definition u2 : unit := register "mk_create_ui_in" mk_create_ui_in.
Definition u3 : unit := register "mk_verify_ui_in" mk_verify_ui_in.
Definition u4 : unit := register "mk_create_ui_out" mk_create_ui_out.
Definition u5 : unit := register "mk_verify_ui_out" mk_verify_ui_out.
(* =========================== *)



(* =========================== *)
(* =========================== *)




Extract Inductive ref => "ref" ["ref"].
Extract Inlined Constant get_ref => "!".
Extract Inlined Constant update_ref => "(:=)".


Extract Inlined Constant register => "(fun l -> Callback.register (Batteries.String.of_list l))".


Extract Inductive sigT => "(*)" [""].


Extract Inductive Proc => "Prelude.SM.id" ["Prelude.SM.ret"
                                             "Prelude.SM.bind"
                                             "Prelude.SM.call_proc (lookup_table __)"].


Extract Constant self => "Obj.magic 0".


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


Extract Inlined Constant M_StateMachine => "n_proc".
Extract Inlined Constant n_proc_at => "n_proc".
Extract Inlined Constant n_procs => "((unit mP_StateMachine) p_nproc) list".



(* =========================== *)
(* =========================== *)

(* ***
   Add this only if you want to GC the log for a fair evaluation
   It *shouldn't* be ON by default!
   *** *)
(*Extract Inlined Constant log_new_prepare => "log_new_prepare_gc2".*)



(* =========================== *)
(* =========================== *)

(* ***
   To remove debug messages
   *** *)
Extract Inlined Constant send_debugs => "(fun _ _ _ _ -> [])".



(* =========================== *)
(* =========================== *)

(* TODO: Why can't we get rid of the last argument? *)
Extraction Implicit lookup_table [1 2 3 4 5].


Extraction "MinbftReplica.ml"
           log_new_prepare_gc1 log_new_prepare_gc2 (* this is only used when we want to GC the log for a fair evaluation *)
           lookup_table MUSIG MLOG MMAIN (*mtest*)
           DirectedMsgs2string
           mk_create_ui_in mk_verify_ui_in
           mk_create_ui_out mk_verify_ui_out
           execute_request
           (*u1 u2 u3 u4 u5*).

(*
  Compile using: ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix MinbftReplica.native
 *)
