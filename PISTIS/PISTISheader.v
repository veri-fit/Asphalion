Require Export Quorum.
Require Export Process.


Section PISTIS_header.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : @DTimeContext }.

 (* ===============================================================
    Parameters
    =============================================================== *)


  Class PISTIS_context :=
    {
       PISTIS_digest         : Set;
       PISTIS_digest_default : PISTIS_digest;
       PISTIS_digestdeq      : Deq PISTIS_digest;

       PISTIS_sending_key   : Set;
       PISTIS_receiving_key : Set;

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
       Value : Set;
       ValueDeq : Deq Value;

(*       PISTIS_result : Set;
       PISTIS_resdeq : Deq PISTIS_result;

       PISTIS_sm_state : Set;
       PISTIS_sm_initial_state : PISTIS_sm_state;
       PISTIS_sm_update : Client -> PISTIS_sm_state -> PISTIS_data_message -> PISTIS_result * PISTIS_sm_state;*)
    }.

  Context { PISTIS_context : PISTIS_context }.


  (* ===============================================================
     Nodes
     =============================================================== *)

  Inductive PISTIS_node :=
  | PISTIS_replica (n : Rep)
  | PISTIS_client (n : Client).

  Coercion PISTIS_replica : Rep >-> PISTIS_node.

  Definition node2rep (n : PISTIS_node) : option Rep :=
    match n with
    | PISTIS_replica n => Some n
    | _ => None
    end.

  Definition node2client (n : PISTIS_node) : option Client :=
    match n with
    |PISTIS_client nn => Some nn
    | _ => None
    end.

  Lemma PISTIS_nodeDeq : Deq PISTIS_node.
  Proof.
    introv; destruct x as [r1|c1], y as [r2|c2];
    try (complete( right; intro xx; inversion xx; subst; tcsp)).
    - destruct (rep_deq r1 r2);[left|right]; subst; auto.
      intro xx; inversion xx; subst; tcsp.
    - destruct (client_deq c1 c2);[left|right]; subst; auto.
      intro xx; inversion xx; subst; tcsp.
  Defined.

  Global Instance PISTIS_I_Node : Node := MkNode PISTIS_node PISTIS_nodeDeq.


  (* ===============================================================
     Quorum
     =============================================================== *)

  Lemma PISTIS_replica_inj : injective PISTIS_replica.
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

  Lemma node_cond1 : forall n : Rep, name2rep (PISTIS_replica n) = Some n.
  Proof.
    tcsp.
  Qed.

  Lemma node_cond2 : forall (n : Rep) (m : name), name2rep m = Some n -> PISTIS_replica n = m.
  Proof.
    introv h.
    destruct m; simpl in *; ginv; auto.
  Qed.

  Global Instance PISTIS_I_Quorum : Quorum_context :=
    MkQuorumContext
      Rep
      num_replicas
      rep_deq
      reps2nat
      reps_bij
      PISTIS_replica
      name2rep
      node_cond1
      node_cond2
      PISTIS_replica_inj.


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

  Definition nreps : list name := map PISTIS_replica reps.

  Lemma reps_prop : forall (x : Rep), In x reps.
  Proof.
    exact nodes_prop.
  Qed.

  Definition clients : list Client :=
    mapin
      (seq 0 num_clients)
      (fun n i => bij_inv clients_bij (mk_nat_n (seq_0_lt i))).

  Definition nclients : list name := map PISTIS_client clients.

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

  Global Instance PISTIS_I_AuthTok : AuthTok :=
    MkAuthTok
      PISTIS_digest
      PISTIS_digestdeq.

  (* ===============================================================
     Crypto
     =============================================================== *)

  Global Instance PISTIS_I_Key : Key := MkKey PISTIS_sending_key PISTIS_receiving_key.

  Class PISTIS_initial_keys :=
    MkPISTIS_initial_keys {
        pistis_initial_keys : key_map;
      }.
  Context { m_initial_keys : PISTIS_initial_keys }.


(*
  (* ===============================================================
     Signatures
     =============================================================== *)

  Record Sign := MkSign {sign_r : Rep; sign_s : Tokens}.
  Definition Signs := list Sign.


  (* ===============================================================
     Bare messages
     =============================================================== *)

  Record Bare_Echo :=
    bare_echo
      {
        echo_r : Rep;
        echo_s : SeqNum;
        echo_v : Value;
      }.

  Record Echo :=
    echo
      {
        echo_b :> Bare_Echo;
        echo_a : Signs;
      }.

  Record Deliver :=
    deliver
      {
        reply_e :> Echo;
        reply_a : Signs;
      }.


  Record Bare_HB :=
    bare_hb
      {
        hb_r : Rep;
        hb_s : SeqNum;
      }.

  Record HB :=
    hb
      {
        hb_b :> Bare_HB;
        hb_a : Signs;
      }.
*)

End PISTIS_header.
