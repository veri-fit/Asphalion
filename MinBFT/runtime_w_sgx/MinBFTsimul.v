Require Export Ascii String.

Require Import QArith.
Require Export DTimeQ.

Require Export MinBFT.
Require Export RunSM.


Section MinBFTinstance.



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



  (* ================== SIGNATURE ================== *)
(*
  Inductive MinBFTtoken_stub : Set :=
  | minbft_token_stub.

  Definition minbft_token : Set := MinBFTtoken_stub.

  Lemma minbft_token_deq : Deq minbft_token.
  Proof.
    introv; destruct x, y; simpl; prove_dec.
  Defined.

*)

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

(* this def + def below same as send_request (see below); the only difference is the client is not parameter *)
   Definition mk_request_to (rep : Rep) (ts : nat) (m : MinBFT_data_message) : DirectedMsg :=
    let ts   := time_stamp ts in
    let breq := bare_request (client0 C)  ts m in
    let dst  := MinBFT_replica rep in (* the leader *)
    let toks := [ minbft_digest_def ] in (* we just send empty lists here to authenticate messages *)
    let req  := request breq toks in
    let msg  := MinBFT_request req in
    MkDMsg msg [dst] (nat2pdt 0).


  Definition mk_request (ts : nat) (opr : MinBFT_data_message) : DirectedMsg :=
     mk_request_to (MinBFTprimary initial_view) ts opr.

  (* n request starting with number start *)
  Fixpoint mk_requests_start (n start : nat) (opr : MinBFT_data_message) : DirectedMsgs :=
    match n with
    | 0 => []
    | S m => List.app (mk_requests_start m start opr) [mk_request (n + start) opr]
    end.

  Definition mk_requests (n : nat) (opr : MinBFT_data_message) : DirectedMsgs :=
    mk_requests_start n 0 opr.

  Record InitRequests :=
    MkInitRequests
      {
        num_requests     : nat;
        starting_seq_num : nat;
        req_operation    : MinBFT_data_message;
      }.

  (* same as  minbft_init_sim_state (see below) *)
  Definition MinBFT_init_msgs (msgs : DirectedMsgs) : SimState :=
    MkInitSimState MinBFT_instance_sys msgs.

  Definition MinBFT_init (init : InitRequests) : SimState :=
    MinBFT_init_msgs
      (mk_requests_start
         (num_requests init)
         (starting_seq_num init)
         (req_operation init)).

  Definition MinBFT_simul_list (init : InitRequests) (L : list nat) : SimState :=
    run_n_steps L (MinBFT_init init).

  Definition MinBFT_simul_list_msgs (msgs : DirectedMsgs) (L : list nat) : SimState :=
    run_n_steps L (MinBFT_init_msgs msgs).

  (* [switch] is the list of steps at which we want to switch to sending messages
   coming from the outside (from clients) instead of keeping on sending messages
   coming from the inside (from replicas). *)
  Definition MinBFT_simul_n
             (init     : InitRequests) (* This is to generate an initial list of requests *)
             (rounds   : Rounds)
             (switches : Switches) : SimState :=
    iterate_n_steps rounds switches (MinBFT_init init).

  Definition MinBFT_simul_n_msgs
             (msgs     : DirectedMsgs)
             (rounds   : Rounds)
             (switches : Switches) : SimState :=
    iterate_n_steps rounds switches (MinBFT_init_msgs msgs).

(*
  (* ================== STATE ================== *)

 (* same as mk_request_to
  Definition send_request
             (c  : Client)
             (ts : Timestamp)
             (m  : MinBFT_data_message) :=
    MkDMsg
      (MinBFT_request (request (bare_request c ts m) [minbft_digest_def]))
      [MinBFT_replica (MinBFTprimary (view 0))]
      ('0).
 *)

(* same as MinBFT_init_msgs
  Definition minbft_init_sim_state : SimState :=
    let c  := client0 C in
    let ts := time_stamp 0 in
    let m  := minbft_data_message_plus 17 in
    MkInitSimState
      MinBFTsys
      [send_request c ts m]. *)

(* similar to  MinBFT_simul_list_msgs (no parameters required here *)
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
 *)

End MinBFTinstance.


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


(* == crypto stuff ==
(* === COMMENT OUT THIS PART IF YOU DON'T WANT TO USE KEYS ===*)

Extract Inlined Constant minbft_sending_key   => "Nocrypto.Rsa.priv".
Extract Inlined Constant minbft_receiving_key => "Nocrypto.Rsa.pub".
Extract Inlined Constant minbft_lookup_replica_sending_key   => "RsaKeyFun.lookup_replica_sending_key".
Extract Inlined Constant minbft_lookup_replica_receiving_key => "RsaKeyFun.lookup_replica_receiving_key".
Extract Inlined Constant minbft_lookup_client_receiving_key  => "RsaKeyFun.lookup_client_receiving_key".
Extract Inlined Constant minbft_lookup_client_sending_key  => "RsaKeyFun.lookup_client_sending_key".


Extract Inlined Constant minbft_create_signature => "RsaKeyFun.sign_list".
Extract Inlined Constant minbft_verify_signature => "RsaKeyFun.verify_one".


Extract Inlined Constant minbft_digest => "Cstruct.t".
Extract Inlined Constant minbft_digest_deq => "(=)".
(* === --- === *)

(* == hashing stuff == *)
Extract Inlined Constant minbft_create_hash_usig => "Obj.magic (Hash.create_hash_objects)".
Extract Inlined Constant minbft_verify_hash_usig => "Obj.magic (Hash.verify_hash_objects)".
(* === --- === *)


(* Cstruct.t is the most logical choice *)
Extract Inlined Constant minbft_digest_def => "Cstruct.empty".
*)

Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.


Definition local_system:=
  @MinBFTlocalSys.


(*
Extraction "MinbftReplica.ml" (* minbft_state2string *) run_sm SimState2string dummy_LocalSystem local_system.
*)


Definition MinBFT_simul : SimState :=
  let num_requests     := 2  in
  let starting_seq_num := 0  in
  let req_operation    := minbft_data_message_plus 17 in
  let rounds   := [MkRound 0(*pos*) 22(*num steps*)(*, MkRound 3 25, MkRound 0 36*)] in
  let switches := [(*MkSwitch 1 0*)] in
  MinBFT_simul_n
    (MkInitRequests num_requests starting_seq_num req_operation)
    rounds
    switches.

Definition MinBFT_simul_pp : unit :=
  print_endline (SimState2string MinBFT_simul).

Extraction "minbft_simul.ml" MinBFT_simul_pp.

