Require Export Quorum.
Require Export Process.


Section MinBFT_header.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : @DTimeContext }.

 (* ===============================================================
    Parameters
    =============================================================== *)


  Class MinBFT_context :=
    {
       MinBFT_digest         : Set;
       MinBFT_digest_default : MinBFT_digest;
       MinBFT_digestdeq      : Deq MinBFT_digest;

       MinBFT_sending_key   : Set;
       MinBFT_receiving_key : Set;

       (* number of faults *)
       F : nat;

       (* ++++++++ Nodes (Replicas & Clients) ++++++++ *)

       (* We have 2F+1 replicas *)
       num_replicas := (2 * F) + 1;

       Rep : Set;
       rep_deq : Deq Rep;
       reps2nat : Rep -> nat_n num_replicas;
       reps_bij : bijective reps2nat;

       num_clients : nat;

       Client : Set;
       client_deq : Deq Client;
       clients2nat : Client -> nat_n num_clients;
       clients_bij : bijective clients2nat;

       (* ++++++++ replicated service ++++++++ *)
       MinBFT_data_message : Set;  (* in PBFT this is operation *)
       MinBFT_data_message_deq : Deq MinBFT_data_message;

       MinBFT_result : Set;
       MinBFT_resdeq : Deq MinBFT_result;

       MinBFT_sm_state : Set;
       MinBFT_sm_initial_state : MinBFT_sm_state;
       MinBFT_sm_update : Client -> MinBFT_sm_state -> MinBFT_data_message -> MinBFT_result * MinBFT_sm_state;
    }.

  Context { MinBFT_context : MinBFT_context }.


  (* ===============================================================
     Nodes
     =============================================================== *)

  Inductive MinBFT_node :=
  | MinBFT_replica (n : Rep)
  | MinBFT_client (n : Client).

  Coercion MinBFT_replica : Rep >-> MinBFT_node.

  Definition node2rep (n : MinBFT_node) : option Rep :=
    match n with
    | MinBFT_replica n => Some n
    | _ => None
    end.

  Definition node2client (n : MinBFT_node) : option Client :=
    match n with
    |MinBFT_client nn => Some nn
    | _ => None
    end.

  Lemma MinBFT_nodeDeq : Deq MinBFT_node.
  Proof.
    introv; destruct x as [r1|c1], y as [r2|c2];
    try (complete( right; intro xx; inversion xx; subst; tcsp)).
    - destruct (rep_deq r1 r2);[left|right]; subst; auto.
      intro xx; inversion xx; subst; tcsp.
    - destruct (client_deq c1 c2);[left|right]; subst; auto.
      intro xx; inversion xx; subst; tcsp.
  Defined.

  Global Instance MinBFT_I_Node : Node := MkNode MinBFT_node MinBFT_nodeDeq.


  (* ===============================================================
     Quorum
     =============================================================== *)

  Lemma MinBFT_replica_inj : injective MinBFT_replica.
  Proof.
    introv h; ginv; auto.
  Qed.

  Definition name2rep : name -> option Rep.
  Proof.
    introv n.
    destruct n.
    { exact (Some n). }
    { exact None. }
  Defined.

  Lemma node_cond1 : forall n : Rep, name2rep (MinBFT_replica n) = Some n.
  Proof.
    tcsp.
  Qed.

  Lemma node_cond2 : forall (n : Rep) (m : name), name2rep m = Some n -> MinBFT_replica n = m.
  Proof.
    introv h.
    destruct m; simpl in *; ginv; auto.
  Qed.

  Global Instance MinBFT_I_Quorum : Quorum_context :=
    MkQuorumContext
      Rep
      num_replicas
      rep_deq
      reps2nat
      reps_bij
      MinBFT_replica
      name2rep
      node_cond1
      node_cond2
      MinBFT_replica_inj.


  (* ===============================================================
     More about Nodes
     =============================================================== *)

  (* 0 is less than F+1 *)
  Definition nat_n_Fp1_0 : nat_n num_replicas.
  Proof.
    exists 0.
    apply leb_correct.
    unfold num_replicas.
    omega.
  Defined.

  Definition replica0 : Rep := bij_inv reps_bij nat_n_Fp1_0.

  (* We'll return the node as given by our bijection if n < num_nodes,
     otherwise we return a default value (replica0)
   *)
  Definition nat2rep (n : nat) : Rep.
  Proof.
    destruct reps_bij as [f a b].
    destruct (lt_dec n num_replicas) as [d|d].
    - exact (f (mk_nat_n d)). (* here we now that n < num_replicas so we can use our bijection *)
    - exact replica0. (* here num_replicas <= n, so we return a default value: replica0 *)
  Defined.


  Definition reps : list Rep := nodes.

  Definition nreps : list name := map MinBFT_replica reps.

  Lemma reps_prop : forall (x : Rep), In x reps.
  Proof.
    exact nodes_prop.
  Qed.

  Definition clients : list Client :=
    mapin
      (seq 0 num_clients)
      (fun n i => bij_inv clients_bij (mk_nat_n (seq_0_lt i))).

  Definition nclients : list name := map MinBFT_client clients.

  Lemma clients_prop : forall (x : Client), In x clients.
  Proof.
    introv.
    unfold clients.
    apply in_mapin.

    remember (clients2nat x) as nx.
    destruct nx as [nx condnx].

    pose proof (leb_complete _ _ condnx) as c.

    assert (In nx (seq O num_clients)) as i.
    { apply in_seq; omega. }

    exists nx i; simpl.

    unfold mk_nat_n.
    unfold bij_inv.
    destruct clients_bij.
    pose proof (bij_id1 x) as h.
    rewrite <- Heqnx in h; subst; simpl.

    f_equal; f_equal.
    apply UIP_dec; apply bool_dec.
  Qed.


  (* ===============================================================
     Views
     =============================================================== *)

  Inductive View :=
  | view (n : nat).

  Definition view2nat (v : View) : nat :=
    match v with
    | view n => n
    end.
  Coercion view2nat : View >-> nat.

  Definition next_view (v : View): View := view (S v).

  Definition pred_view (v : View): View := view (pred v).

  Lemma ViewDeq : Deq View.
  Proof.
    introv; destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Defined.

  Definition initial_view := view 0.


  Definition ViewLe (vn1 vn2 : View) : bool :=
    view2nat vn1 <=? view2nat vn2.

  Definition ViewLt (vn1 vn2 : View) : bool :=
    view2nat vn1 <? view2nat vn2.

  Definition max_view (v1 v2 : View) : View :=
    if ViewLe v1 v2 then v2 else v1.


  (* ===============================================================
     Sequence numbers
     =============================================================== *)

  Inductive SeqNum :=
  | seq_num (n : nat).
  Coercion seq_num : nat >-> SeqNum.

  Definition seqnum2nat (s : SeqNum) : nat :=
    match s with
    | seq_num n => n
    end.
  Coercion seqnum2nat : SeqNum >-> nat.

  Definition SeqNumLe (sn1 sn2 : SeqNum) : bool :=
    seqnum2nat sn1 <=? seqnum2nat sn2.

  Definition SeqNumLt (sn1 sn2 : SeqNum) : bool :=
    seqnum2nat sn1 <? seqnum2nat sn2.

  Definition next_seq (n : SeqNum): SeqNum := seq_num (S n).

  Lemma SeqNumDeq : Deq SeqNum.
  Proof.
    introv; destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Defined.

  Definition initial_sequence_number : SeqNum := seq_num 0.

  Definition min_seq_num (s1 s2 : SeqNum) : SeqNum :=
    if SeqNumLe s1 s2 then s1 else s2.

  Definition max_seq_num (s1 s2 : SeqNum) : SeqNum :=
    if SeqNumLe s1 s2 then s2 else s1.


  (* ===============================================================
     Authentication
     =============================================================== *)

  Definition MinBFT_tokens := MinBFT_digest.

  Global Instance MinBFT_I_AuthTok : AuthTok :=
    MkAuthTok
      MinBFT_digest
      MinBFT_digestdeq.

  (* ===============================================================
     Crypto
     =============================================================== *)

  Global Instance MinBFT_I_Key : Key := MkKey MinBFT_sending_key MinBFT_receiving_key.

  Class MinBFT_initial_keys :=
    MkMinBFT_initial_keys {
        minbft_initial_keys : key_map;
      }.
  Context { m_initial_keys : MinBFT_initial_keys }.

  Class USIG_initial_keys :=
    MkUSIG_initial_keys {
        usig_initial_keys : key_map;
      }.
  Context { u_initial_keys : USIG_initial_keys }.

  (* ===============================================================
     Primary
     =============================================================== *)

  (* @Ivnote: mod is already part of Coq standard library, and it's used as follows: a mod b *)
  (* primary p = v mod R, where v is number of current view and |R| is 2f+1 *)
  Definition MinBFTprimary_nat (v : View) : nat := v mod num_replicas. (* here we should return replica, not nat!!!*)

  Definition MinBFTprimary (v : View) : Rep := nat2rep (MinBFTprimary_nat v).

  Definition is_primary (v : View) (r : Rep) : bool :=
    if rep_deq r (MinBFTprimary v) then true else false.

  Definition not_primary (v : View) (r : Rep) : bool :=
    negb (is_primary v r).


  (* ===============================================================
     Timestamps
     =============================================================== *)

  Inductive Timestamp :=
  | time_stamp (q : nat).
  Coercion time_stamp : nat >-> Timestamp.

  Definition timestamp2nat (t : Timestamp) : nat :=
    match t with
    | time_stamp n => n
    end.
  Coercion timestamp2nat : Timestamp >-> nat.

  Definition timestamp0 := time_stamp 0.


  (* ===============================================================
     Bare messages
     =============================================================== *)

  (* FIX : Do we need here a null request? *)
  Record Bare_Request :=
    bare_request
      {
        bare_request_c : Client;
        bare_request_t : Timestamp;
        bare_request_m : MinBFT_data_message; (* this filed is called op in the paper, and m in the CRM *)
      }.

  Record Request :=
    request
      {
        request_b : Bare_Request;
        request_a : Tokens  (* [a] authenticate the client *)
      }.

  Record Bare_Reply :=
    bare_reply
      {
        bare_reply_r      : Request;
        bare_reply_result : nat;
        bare_reply_rep    : Rep;
        bare_reply_view   : View
      }.

  Record Reply :=
    reply
      {
        reply_b : Bare_Reply;
        reply_a : Tokens  (* [a] authenticate the replica *)
      }.


  Record Bare_Prepare :=
    bare_prepare
      {
        bare_prepare_v  : View;
        bare_prepare_m  : Request;
      }.

  Record Accept :=
    accept
      {
        accept_r : Request;
        accept_c : nat;
      }.


End MinBFT_header.
