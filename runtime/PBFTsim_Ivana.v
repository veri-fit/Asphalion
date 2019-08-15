(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University

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


Require Export Simulator.
Require Export PBFT.
Require Import Ascii String.
(*Require Import SHA256. *)
Require Import functional_prog.
Require Export PBFTtactics.
(*
    We'll define here an instance of PBFT so that we can simulate it.
 *)



(* ================== INSTANCE OF PBFT ================== *)


Definition digest : Type := list nat.

Lemma digest_deq : Deq digest.
Proof.
  introv; apply list_eq_dec.
  apply deq_nat.
Defined.

Definition token : Type := list nat.

Lemma token_deq : Deq token.
Proof.
  introv; apply list_eq_dec.
  apply deq_nat.
Defined.

Definition key : Type := list nat.

Definition F : nat := 1.
Definition nreps : nat := 3 * F + 1.

Definition replica (F : nat) : Type := nat_n nreps.

Lemma replica_deq (F : nat) : Deq (replica F).
Proof.
  apply nat_n_deq.
Defined.

Definition reps2nat (F : nat) : replica F -> nat_n nreps := fun n => n.

Lemma bijective_reps2nat (F : nat) : bijective (reps2nat F).
Proof.
  exists (fun n : nat_n nreps => n); introv; unfold reps2nat; auto.
Defined.

(* we'll have a single client here *)
Definition client : Type := unit.

Definition client0 : client := tt.

Lemma natn1 : nat_n 1.
Proof.
  exists 0; simpl; auto.
Defined.

Definition clients2nat : client -> nat_n 1 := fun n => natn1.

Lemma bijective_clients2nat : bijective clients2nat.
Proof.
  exists (fun (n : nat_n 1) => client0); introv; unfold clients2nat; auto.
  { destruct x; auto. }
  { destruct y; auto.
    dup e as c.
    apply Nat.ltb_lt in c.
    destruct x; try omega.
    clear c.
    unfold natn1.
    f_equal.
    apply UIP_dec; apply bool_dec. }
Defined.

Inductive operation :=
| opr_add (n : nat)
| opr_sub (n : nat).

Lemma operation_deq : Deq operation.
Proof.
  introv; destruct x as [n|n], y as [m|m]; prove_dec;
    destruct (deq_nat n m); subst; prove_dec.
Defined.

Definition smState : Type := nat.
Definition result : Type := nat.

Definition operation_upd (c : client) (state : smState) (opr : operation) : result * smState :=
  match opr with
  | opr_add m => let k := state + m in (k,k)
  | opr_sub m => let k := state - m in (k,k)
  end.

Global Instance PBFT_I_context : PBFTcontext.
Proof.
  eexists.

  - (* max in progress *)
    exact 10.

  - (* water mark range *)
    exact 40.

  - (* checkpoint period *)
    exact 2.

  - (* digest decider *)
    exact digest_deq.

  - (* key type *)
    exact key.

  - (* Replica decider *)
    exact (replica_deq 1).

  - (* proof that reps2nat is bijective *)
    exact (bijective_reps2nat 1).

  - (* client decider *)
    exact Deq_unit.

  - (* proof that clients2nat is bijective *)
    exact bijective_clients2nat.

  - (* operation decider *)
    exact operation_deq.

  - (* result decider *)
    exact deq_nat.

  - (* initial state *)
    exact 0.

  - (* update function *)
    exact operation_upd.
Defined.

Global Instance PBFT_I_auth : PBFTauth.
Proof.
  eexists; simpl.

  - (* create function *)
    exact (fun msg key => []).

  - (* verify function *)
    exact (fun msg key digest => true).
Defined.

Definition reps_local_key_map : local_key_map :=
  map (fun (m : replica 1) => MkDKey (PBFTreplica m) ([] : key)) reps.

Global Instance PBFT_I_keys : PBFTkeys.
Proof.
  eexists; simpl.
  exact (fun (src : name) => MkDKey (PBFTclient client0) [] :: reps_local_key_map).
Defined.

(* XXXXXXXXXXXXXX *)

Definition nat2Z (n : nat) : Z := Z_of_nat n.
Definition Z2nat (z : Z) : nat := Coqlib.nat_of_Z z.

Fixpoint Z_list2nat (l : list Z)  : list nat :=
  match l with
  | [] => []
  | h :: t => (Z2nat h) :: (Z_list2nat t)
  end.

(* sum  ? *)
Fixpoint list_nat2Z (l : list nat) : Z :=
  match l with
  | [] => 0
  | h :: t => (Z_of_nat h) + (list_nat2Z t)
  end.

Definition digest2Z (d : digest) : Z := list_nat2Z d.

Definition Z_list2digest (l : list Z) : digest := Z_list2nat l.

Definition token2Z (d : token) : Z := list_nat2Z d.

Fixpoint tokens2Z (l : list token) : Z :=
  match l with
  | [] => 0
  | h :: t => (list_nat2Z h) + (tokens2Z t)
  end.

Definition result2Z (r : result) : Z := nat2Z r.

Definition timestamp2Z (ts : Timestamp) : Z :=
  match ts with
  | time_stamp n => Z_of_nat n
  end.

Definition view2Z (v : View) : Z :=
  match v with
  | view n => Z_of_nat n
  end.

Definition seq2Z (s : SeqNum) : Z :=
  match s with
  | seq_num n => Z_of_nat n
  end.

Definition operation2Z (opr : operation) (n1 n2 : nat ): Z :=
  match opr with
  | opr_add n => (nat2Z n1) * 0 + Z_of_nat n * (nat2Z n2)
  | opr_sub n => (nat2Z n1) * 1 + Z_of_nat n * (nat2Z n2)
  end.

(*  we have only one client so far *)
Definition client2Z (c : Client) : Z := 1.

Definition replica2Z (F : nat) (r : replica F) : Z := nat2Z (proj1_sig r).

Definition bare_request2Z (r : Bare_Request) : Z :=
  match r with
  | null_req => 0
  | bare_req o t c => (operation2Z o 13 17) * 3 + (timestamp2Z t)  * 5 + (client2Z c) * 7
  end.

Definition request2Z (r : Request) : Z :=
  match r with
  | req b a => (bare_request2Z b) + (tokens2Z a) * 11
  end.

Fixpoint requests2Z (l : list Request) : Z :=
  match l with
  | [] => 0
  | h :: t => (request2Z h) + (requests2Z t)
  end.

Definition bare_pre_prepare2Z (p : Bare_Pre_prepare) : Z :=
  match p with
  | bare_pre_prepare v n d => (view2Z v) * 3  + (seq2Z n) * 5 + (requests2Z d) * 7
  end.

Definition pre_prepare2Z (p : Pre_prepare) : Z :=
  match p with
  | pre_prepare b a => (bare_pre_prepare2Z b) + (tokens2Z a) * 11
  end.

Fixpoint pre_prepares2Z (l : list Pre_prepare) : Z :=
  match l with
  | [] => 0
  | h :: t => (pre_prepare2Z h) + (pre_prepares2Z t)
  end.

Definition bare_prepare2Z (p : Bare_Prepare) : Z :=
  match p with
  | bare_prepare v n d i => (view2Z v) * 3  + (seq2Z n) * 5 + (digest2Z d) * 7  + (replica2Z 1 i) * 11
  end.

Definition prepare2Z (p : Prepare) : Z :=
  match p with
  | prepare b a => (bare_prepare2Z b) + (tokens2Z a) * 13
  end.

Fixpoint prepares2Z (l : list Prepare) : Z :=
  match l with
  | [] => 0
  | h :: t => (prepare2Z h) + (prepares2Z t)
  end.

Definition bare_commit2Z (c : Bare_Commit) : Z :=
  match c with
  | bare_commit v n d i => (view2Z v) * 3  + (seq2Z n) * 5 + (digest2Z d) * 7  + (replica2Z 1 i) * 11
  end.

Definition commit2Z (c : Commit) : Z :=
  match c with
  | commit b a => (bare_commit2Z b) + (tokens2Z a) * 13
  end.

Definition bare_checkpoint2Z (c : Bare_Checkpoint) : Z :=
  match c with
  | bare_checkpoint v n d i => (view2Z v) * 3 + (seq2Z n) * 5  + (digest2Z d) * 7 + (replica2Z 1 i) * 11
  end.

Definition checkpoint2Z (c : Checkpoint) : Z :=
  match c with
  | checkpoint b a => (bare_checkpoint2Z b) + (tokens2Z a) * 13
  end.

Definition last_reply_entry2Z (e: LastReplyEntry) (n1 n2 n3 : nat ) : Z :=
  match lre_reply e with
  | Some r => client2Z (lre_client e) * (nat2Z n1) +  timestamp2Z (lre_timestamp e) * (nat2Z n2) + result2Z r * (nat2Z n3)
  | None => client2Z (lre_client e) * (nat2Z n1) +  timestamp2Z (lre_timestamp e) * (nat2Z n2)
  end.

Fixpoint last_reply_state2Z (l : LastReplyState) (n1 n2 n3 : nat ) : Z :=
  match l with
  | [] => 0
  | h :: t => (last_reply_entry2Z h n1 n2 n3) + (last_reply_state2Z t n1 n2 n3)
  end.

Definition stable_ch2Z (s : StableChkPt) (n1 n2 n3 : nat ) : Z :=
  last_reply_state2Z (si_lastr s) n1 n2 n3.

Fixpoint checkpoint_cert2Z (C : CheckpointCert) : Z :=
  match C with
  | [] => 0
  | h :: t => (checkpoint2Z h) + (checkpoint_cert2Z t)
  end.

Definition prepared_info2Z (p : PreparedInfo) (n1 n2 n3 : nat ) : Z :=
  pre_prepare2Z (prepared_info_pre_prepare p) * (nat2Z n1)
  + digest2Z (prepared_info_digest p) * (nat2Z n2)
  + prepares2Z (prepared_info_prepares p) * (nat2Z n3).


Fixpoint prepared_infos2Z (P : list PreparedInfo) (n1 n2 n3 : nat ) : Z :=
  match P with
  | [] => 0
  | h :: t => (prepared_info2Z h n1 n2 n3) + (prepared_infos2Z t n1 n2 n3)
  end.

Definition bare_view_change2Z (v : Bare_ViewChange) :  Z :=
  match v with
  | bare_view_change v n s C P i => (view2Z v) * 3
                                    + (seq2Z n) * 5
                                    + (stable_ch2Z s 19 23 29) * 7
                                    + (checkpoint_cert2Z C) * 11
                                    + (prepared_infos2Z P 31 37 41)  *13
                                    + (replica2Z 1 i) * 17
  end.

Definition view_change2Z (v : ViewChange) : Z :=
  match v with
  | view_change bv a => (bare_view_change2Z bv) + (tokens2Z a) * 43
  end.

Fixpoint view_changes2Z (l : list ViewChange) : Z :=
  match l with
  | [] => 0
  | h :: t => (view_change2Z h) + (view_changes2Z t)
  end.

Definition bare_new_view2Z (b : Bare_NewView) : Z :=
  match b with
  | bare_new_view v V OP NP => (view2Z v) * 3 + (view_changes2Z V) * 5 + (pre_prepares2Z OP) * 7 + (pre_prepares2Z NP) * 11
  end.

Definition new_view2Z (v : NewView) : Z :=
  match v with
  | new_view b a => (bare_new_view2Z b) + (tokens2Z a) * 13
  end.

Definition bare_reply2Z (r : Bare_Reply) :  Z :=
  match r with
  | bare_reply v t c i r => (view2Z v) * 3 + (timestamp2Z t) * 5 + (client2Z c) * 7 + (result2Z r)  * 11 + (replica2Z 1 i) * 13
  end.

Definition reply2Z(r : Reply) :  Z :=
  match r with
  | reply b a => (bare_reply2Z b) + (tokens2Z a) * 17
  end.

(*
  1st prime number is to distinguish between the different kinds of messages
 *)
Definition PBFTbare_msg2Z (m : PBFTBare_Msg) : Z :=
  match m with
  | PBFTmsg_bare_request              r => 2 * 0  + bare_request2Z r
  | PBFTmsg_bare_pre_prepare          p => 2 * 1  + bare_pre_prepare2Z p
  | PBFTmsg_bare_prepare              p => 2 * 2  + bare_prepare2Z p
  | PBFTmsg_bare_commit               c => 2 * 3  + bare_commit2Z c
  | PBFTmsg_bare_checkpoint           c => 2 * 4  + bare_checkpoint2Z c
  | PBFTmsg_bare_reply                r => 2 * 5  + bare_reply2Z r
  | PBFTmsg_bare_check_ready          c => 2 * 6
  | PBFTmsg_bare_check_bcast_new_view c => 2 * 7
  | PBFTmsg_bare_start_timer          t => 2 * 8
  | PBFTmsg_bare_expired_timer        t => 2 * 9
  | PBFTmsg_bare_view_change          v => 2 * 10 + bare_view_change2Z v
  | PBFTmsg_bare_new_view             v => 2 * 11 + bare_new_view2Z v
    end.

Fixpoint PBFTbare_msgs2Z (msgs : list PBFTBare_Msg) : list Z :=
  match msgs with
  | [] => [Z.zero]
  | h :: t => (PBFTbare_msg2Z h) :: (PBFTbare_msgs2Z t)
  end.


Definition PBFTmsg2Z (m : PBFTmsg) : Z :=
  match m with
  | PBFTrequest              r => 2 * 0  + request2Z r
  | PBFTpre_prepare          p => 2 * 1  + pre_prepare2Z p
  | PBFTprepare              p => 2 * 2  + prepare2Z p
  | PBFTcommit               c => 2 * 3  + commit2Z c
  | PBFTcheckpoint           c => 2 * 4  + checkpoint2Z c
  | PBFTreply                r => 2 * 5  + reply2Z r
  | PBFTcheck_ready          c => 2 * 6
  | PBFTcheck_bcast_new_view c => 2 * 7
  | PBFTstart_timer          t => 2 * 8
  | PBFTexpired_timer        t => 2 * 9
  | PBFTview_change          v => 2 * 10 + view_change2Z v
  | PBFTnew_view              v => 2 * 11 + new_view2Z v
  | PBFTdebug                d => 2 * 12
    end.

Fixpoint PBFTmsgs2Z (msgs : list PBFTmsg) : list Z :=
  match msgs with
  | [] => [Z.zero]
  | h :: t => (PBFTmsg2Z h) :: (PBFTmsgs2Z t)
  end.

  (* use SHA_256' because messages can be longer than 256 bits*)
  (* should SHA_256 use intlist_to_Zlist (l: list int) : list Z := *)

Definition simple_create_hash_messages (msgs : list PBFTmsg) : PBFTdigest := Z_list2digest (SHA_256' (PBFTmsgs2Z msgs)).
Definition simple_verify_hash_messages (msgs : list PBFTmsg) (d : PBFTdigest) := true.
Definition simple_create_hash_state_last_reply (smst : PBFTsm_state) (lastr : LastReplyState) : PBFTdigest := [].
Definition simple_verify_hash_state_last_reply (smst : PBFTsm_state) (lastr : LastReplyState) (d : PBFTdigest) := true.


Lemma simple_create_hash_messages_collision_resistant :
  forall msgs1 msgs2,
    simple_create_hash_messages msgs1 = simple_create_hash_messages msgs2
    -> msgs1 = msgs2.
Proof.
  induction msgs2; introv h; simpl in *; unfold simple_create_hash_messages in *;
  unfold Z_list2digest in *.

  {
    destruct msgs1. simpl in *. ginv. tcsp.
    inversion h.
  

  unfold Z_list2digest in *.
  unfold Z_list2nat in *.
  induction msgs2. simpl in *


  
  induction (PBFTmsgs2Z msgs2). simpl in *. ginv. tcsp.





Admitted.

Lemma simple_create_hash_state_last_reply_collision_resistant :
  forall sm1 sm2 last1 last2,
    simple_create_hash_state_last_reply sm1 last1 = simple_create_hash_state_last_reply sm2 last2
    -> sm1 = sm2 /\ last1 = last2.
Proof.
  introv h.
Admitted.

Global Instance PBFT_I_hash : PBFThash.
Proof.
  exact (Build_PBFThash
           (* create function *)
           (fun msgs => [])

           (* verify function *)
           (fun msgs digest => true)

           (* create hash state *)
           (fun state lastr => [])

           (* verify hash state *)
           (fun state lastr digest => true)

           (* create_hash_message is collision resistant *)
           simple_create_hash_messages_collision_resistant

           (* create_hash_state_last_reply is collision resistant *)
           simple_create_hash_state_last_reply_collision_resistant
        ).
Defined.



(* ================== TIME ================== *)


Definition time_I_type : Type := unit.

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


(* FIX: to replace when extracting *)
Definition print_endline : string -> unit := fun _ => tt.
Definition nat2string (n : nat) : string := "-".

Definition CR : string := String (ascii_of_nat 13) "".

(* Fix: to finish *)
Definition tokens2string (toks : Tokens) : string := "-".

(* Fix: to finish *)
Definition digest2string (d : digest) : string := "-".

(* Fix: to finish *)
Definition result2string (r : result) : string := "-".

(* Fix: there's only one client anyway *)
Definition client2string (c : client) : string := "-".

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

Definition operation2string (opr : operation) : string :=
  match opr with
  | opr_add n => str_concat ["+", nat2string n]
  | opr_sub n => str_concat ["-", nat2string n]
  end.

Definition nat_n2string {m} (n : nat_n m) : string := nat2string (proj1_sig n).

Definition replica2string (r : replica F) : string := nat_n2string r.

Definition bare_request2string (br : Bare_Request) : string :=
  match br with
  | null_req => str_concat [ "null_req"]
  | bare_req opr ts c => str_concat [operation2string opr, ",", timestamp2string ts, ",", client2string c]
  end.

Definition request2string (r : Request) : string :=
  match r with
  | req br a => str_concat ["REQUEST(", bare_request2string br, ",", tokens2string a, ")"]
  end.

Fixpoint requests2string (rs : list Request) : string :=
  match rs with
  | [] => ""
  | [r] => request2string r
  | r :: rs => str_concat [request2string r, ",", requests2string rs]
  end.

Definition bare_pre_prepare2string (bpp : Bare_Pre_prepare) : string :=
  match bpp with
  | bare_pre_prepare v s reqs => str_concat [view2string v, ",", seq2string s, ",", requests2string reqs]
  end.

Definition bare_prepare2string (bp : Bare_Prepare) : string :=
  match bp with
  | bare_prepare v s d i => str_concat [view2string v, ",", seq2string s, ",", digest2string d, ",", replica2string i]
  end.

Definition bare_commit2string (bc : Bare_Commit) : string :=
  match bc with
  | bare_commit v s d i => str_concat [view2string v, ",", seq2string s, ",", digest2string d, ",", replica2string i]
  end.

Definition bare_reply2string (br : Bare_Reply) : string :=
  match br with
  | bare_reply v ts c i res => str_concat [view2string v, ",", timestamp2string ts, ",", client2string c, ",", replica2string i, ",", result2string res]
  end.

Definition pre_prepare2string (pp : Pre_prepare) : string :=
  match pp with
  | pre_prepare b a => str_concat ["PRE_PREPARE(",bare_pre_prepare2string b, ",", tokens2string a, ")"]
  end.

Definition prepare2string (p : Prepare) : string :=
  match p with
  | prepare bp a => str_concat ["PREPARE(", bare_prepare2string bp, ",", tokens2string a, ")"]
  end.

Definition commit2string (c : Commit) : string :=
  match c with
  | commit bc a => str_concat ["COMMIT(", bare_commit2string bc, ",", tokens2string a, ")"]
  end.

Definition reply2string (r : Reply) : string :=
  match r with
  | reply br a => str_concat ["REPLY(", bare_reply2string br, ",", tokens2string a, ")"]
  end.

Definition debug2string (d : Debug) : string :=
  match d with
  | debug r s => str_concat ["DEBUG(", replica2string r, ",", s, ")"]
  end.

Definition bare_checkpoint2string (bc : Bare_Checkpoint) : string :=
  match bc with
  | bare_checkpoint v n d i => str_concat [view2string v, ",", seq2string n, ",", digest2string d, ",", replica2string i]
  end.

Definition checkpoint2string (c : Checkpoint) : string :=
  match c with
  | checkpoint bc a => str_concat ["CHECKPOINT(", bare_checkpoint2string bc, ",", tokens2string a, ")"]
  end.

Definition check_ready2string (c : CheckReady) : string := "CHECK-READY()".

Definition start_timer2string (t : StartTimer) : string :=
  match t with
  | start_timer r v => str_concat ["START-TIMER(", bare_request2string r, "," , view2string v, ")"]
  end.

Definition expired_timer2string (t : ExpiredTimer) : string :=
  match t with
  | expired_timer r v => str_concat ["EXPIRED-TIMER(", bare_request2string r, "," , view2string v, ")"]
  end.

(* FIX *)
Definition view_change2string (vc : ViewChange) : string := "-".

(* FIX *)
Definition new_view2string (nv : NewView) : string := "-".

(* FIX *)
Definition check_bcast_new_view2string (nv : CheckBCastNewView) : string := "-".

Definition msg2string (m : PBFTmsg) : string :=
  match m with
  | PBFTrequest r              => request2string r
  | PBFTpre_prepare pp         => pre_prepare2string pp
  | PBFTprepare p              => prepare2string p
  | PBFTcommit c               => commit2string c
  | PBFTcheckpoint c           => checkpoint2string c
  | PBFTcheck_ready c          => check_ready2string c
  | PBFTcheck_bcast_new_view c => check_bcast_new_view2string c
  | PBFTstart_timer t          => start_timer2string t
  | PBFTexpired_timer t        => expired_timer2string t
  | PBFTview_change v          => view_change2string v
  | PBFTnew_view v             => new_view2string v
  | PBFTdebug d                => debug2string d
  | PBFTreply r                => reply2string r
  end.

Definition name2string (n : name) : string :=
  match n with
  | PBFTreplica r => replica2string r
  | PBFTclient c => client2string c
  end.

Fixpoint names2string (l : list name) : string :=
  match l with
  | [] => ""
  | [n] => name2string n
  | n :: ns => str_concat [name2string n, ",", names2string ns]
  end.

Definition DirectedMsg2string (dm : DirectedMsg) : string :=
  match dm with
  | MkDMsg msg dst => str_concat [msg2string msg, ":", "[", names2string dst, "]"]
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

Definition MonoSimulationState2string (s : MonoSimulationState) : string :=
  match s with
  | MkMonoSimState ty sys step out_inflight in_inflight delivered =>
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


Definition dummy_initial_state : PBFTstate :=
  Build_State
    []
    initial_view
    []
    initial_checkpoint_state
    PBFTsm_initial_state
    initial_next_to_execute
    initial_ready
    initial_last_reply
    initial_view_change_state
    initial_primary_state.

Definition PBFTmono_sys : NMStateMachine PBFTstate :=
  fun name =>
    match name with
    | PBFTreplica n => PBFTreplicaSM n
    | _ => MhaltedSM dummy_initial_state
    end.

Definition mk_request_to (rep : Rep) (ts : nat) (opr : nat) : DirectedMsg :=
  let ts   := time_stamp ts in
  let breq := bare_req (opr_add opr) ts client0 in
  let dst  := PBFTreplica rep in (* the leader *)
  let toks := [ [] ] : Tokens in (* we just send empty lists here to authenticate messages *)
  let req  := req breq toks in
  let msg  := PBFTrequest req in
  MkDMsg msg [dst].

Definition mk_request (ts : nat) (opr : nat) : DirectedMsg :=
  mk_request_to (PBFTprimary initial_view) ts opr.

(* n request starting with number start *)
Fixpoint mk_requests_start (n start opr : nat) : DirectedMsgs :=
  match n with
  | 0 => []
  | S m => List.app (mk_requests_start m start opr) [mk_request (n + start) opr]
  end.

Definition mk_requests (n opr : nat) : DirectedMsgs :=
  mk_requests_start n 0 opr.

Record InitRequests :=
  MkInitRequests
    {
      num_requests     : nat;
      starting_seq_num : nat;
      req_operation    : nat;
    }.

Definition PBFTinit_msgs (msgs : DirectedMsgs) : MonoSimulationState :=
  MkInitMonoSimState PBFTmono_sys msgs.

Definition PBFTinit (init : InitRequests) : MonoSimulationState :=
  PBFTinit_msgs
    (mk_requests_start
       (num_requests init)
       (starting_seq_num init)
       (req_operation init)).

Definition PBFTsimul_list (init : InitRequests) (L : list nat) : MonoSimulationState :=
  mono_run_n_steps L (PBFTinit init).

Definition PBFTsimul_list_msgs (msgs : DirectedMsgs) (L : list nat) : MonoSimulationState :=
  mono_run_n_steps L (PBFTinit_msgs msgs).

(* [switch] is the list of steps at which we want to switch to sending messages
   coming from the outside (from clients) instead of keeping on sending messages
   coming from the inside (from replicas). *)
Definition PBFTsimul_n
           (init     : InitRequests) (* This is to generate an initial list of requests *)
           (rounds   : Rounds)
           (switches : Switches) : MonoSimulationState :=
  mono_iterate_n_steps rounds switches (PBFTinit init).

Definition PBFTsimul_n_msgs
           (msgs     : DirectedMsgs)
           (rounds   : Rounds)
           (switches : Switches) : MonoSimulationState :=
  mono_iterate_n_steps rounds switches (PBFTinit_msgs msgs).




(* ================== EXTRACTION ================== *)


Extraction Language Ocaml.

Extract Inlined Constant print_endline => "print_coq_endline".
Extract Inlined Constant nat2string    => "char_list_of_int".
Extract Inlined Constant CR            => "['\n']".

Extract Inlined Constant time_I_type     => "float".
Extract Inlined Constant time_I_get_time => "Time.get_time".
Extract Inlined Constant time_I_sub      => "Time.sub_time".
Extract Inlined Constant time_I_2string  => "Time.time2string".

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.
