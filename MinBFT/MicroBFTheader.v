Require Export Quorum.
Require Export Process.


Section MicroBFT_header.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : @DTimeContext }.

 (* ===============================================================
    Parameters
    =============================================================== *)


  Class MicroBFT_context :=
    {
       MicroBFT_digest : Set;
       MicroBFT_digestdeq : Deq MicroBFT_digest;

       MicroBFT_sending_key   : Set;
       MicroBFT_receiving_key : Set;
    }.

  Context { MicroBFT_context : MicroBFT_context }.


  (* ===============================================================
     Nodes
     =============================================================== *)

  Inductive MicroBFT_node :=
  | MicroBFT_primary
  | MicroBFT_backup1
  | MicroBFT_backup2.

  Lemma MicroBFT_nodeDeq : Deq MicroBFT_node.
  Proof.
    introv; destruct x as [a1|b1|c1], y as [a2|b2|c2]; prove_dec.
  Defined.

  Global Instance MicroBFT_I_Node : Node := MkNode MicroBFT_node MicroBFT_nodeDeq.


  (* ===============================================================
     Quorum
     =============================================================== *)

  Lemma MicroBFT_replica_inj : injective (fun (x : MicroBFT_node) => x).
  Proof.
    introv h; ginv; auto.
  Qed.

  Definition nat_3_0 : nat_n 3.
  Proof.
    exists 0; reflexivity.
  Defined.

  Definition nat_3_1 : nat_n 3.
  Proof.
    exists 1; reflexivity.
  Defined.

  Definition nat_3_2 : nat_n 3.
  Proof.
    exists 2; reflexivity.
  Defined.

  Definition node2nat (n : MicroBFT_node) : nat_n 3 :=
    match n with
    | MicroBFT_primary => nat_3_0
    | MicroBFT_backup1 => nat_3_1
    | MicroBFT_backup2 => nat_3_2
    end.

  Definition nat2node (n : nat_n 3) : MicroBFT_node.
  Proof.
    destruct n as [n p].
    apply Nat.ltb_lt in p.
    destruct n;[exact MicroBFT_primary|].
    destruct n;[exact MicroBFT_backup1|].
    destruct n;[exact MicroBFT_backup2|omega].
  Defined.

  Lemma node2nat_bij : bijective node2nat.
  Proof.
    exists nat2node; introv; simpl; auto.
    { destruct x; simpl; auto. }
    { destruct y as [y p].
      destruct y;[rewrite (UIP_refl_bool _ p); auto|];[].
      destruct y;[rewrite (UIP_refl_bool _ p); auto|];[].
      destruct y;[rewrite (UIP_refl_bool _ p); auto|];[].
      assert False; tcsp. }
  Qed.

  Definition name2node : name -> option MicroBFT_node := fun n => Some n.
  Definition node2name : MicroBFT_node -> name := fun n => n.

  Lemma node_cond1 : forall n : MicroBFT_node, name2node (node2name n) = Some n.
  Proof.
    tcsp.
  Qed.

  Lemma node_cond2 : forall (n : MicroBFT_node) (m : name), name2node m = Some n -> node2name n = m.
  Proof.
    introv h; simpl in *.
    unfold name2node in h; ginv; auto.
  Qed.

  Global Instance MicroBFT_I_Quorum : Quorum_context :=
    MkQuorumContext
      MicroBFT_node
      3
      MicroBFT_nodeDeq
      node2nat
      node2nat_bij
      node2name
      name2node
      node_cond1
      node_cond2
      MicroBFT_replica_inj.


  (* ===============================================================
     More about Nodes
     =============================================================== *)


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

  Definition MicroBFT_tokens := MicroBFT_digest.

  Global Instance MicroBFT_I_AuthTok : AuthTok :=
    MkAuthTok
      MicroBFT_digest
      MicroBFT_digestdeq.


  (* ===============================================================
     Crypto
     =============================================================== *)

  Global Instance MicroBFT_I_Key : Key := MkKey MicroBFT_sending_key MicroBFT_receiving_key.

  Class MicroBFT_initial_keys :=
    MkMicroBFT_initial_keys {
        microbft_initial_keys : key_map;
      }.
  Context { m_initial_keys : MicroBFT_initial_keys }.

  Class USIG_initial_keys :=
    MkUSIG_initial_keys {
        usig_initial_keys : key_map;
      }.
  Context { u_initial_keys : USIG_initial_keys }.

End MicroBFT_header.
