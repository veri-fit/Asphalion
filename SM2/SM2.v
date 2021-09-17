(*

  Copyright 2016 Luxembourg University
  Copyright 2017 Luxembourg University
  Copyright 2018 Luxembourg University
  Copyright 2019 Luxembourg University

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


Require Export Quorum.
Require Export Process.


Section SM2.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc : @DTimeContext }.
  Context { pt  : @TimeConstraint dtc }.

  Class SMcontext :=
    MkSMcontext
      {
        (* number of faults *)
        F : nat;

        (* ++++++++ Nodes ++++++++ *)
        num_generals : nat;
        num_generals_non_empty : 0 < num_generals;
        num_generals_constraint : F <= num_generals;

        Gen : Set; (* same as in paper, replica 0 is commander *)
        gen_deq : Deq Gen;
        gens2nat : Gen -> nat_n num_generals;
        gens_bij : bijective gens2nat;

        SMtoken    : Set;
        SMtokendeq : Deq SMtoken;

        sm_value : Set;
        sm_default_value : sm_value;
        sm_value_deq : Deq sm_value;
        sm_choice : list sm_value -> sm_value;
        sm_choice_cond1 : forall v, sm_choice [v] = v;
        sm_choice_cond2 : sm_choice [] = sm_default_value;
        sm_choice_cond3 : forall l1 l2, eqset l1 l2 -> sm_choice l1 = sm_choice l2;

        sm_initial_values : Gen -> sm_value;

        SMsending_key   : Set;
        SMreceiving_key : Set;
      }.

  Context { sm_context : SMcontext }.


  Lemma sm_choice_diff :
    forall l1 l2,
      sm_choice l1 <> sm_choice l2
      ->
      exists v,
        (In v l1 /\ ~ In v l2)
        \/
        (In v l2 /\ ~ In v l1).
  Proof.
    introv h.
    destruct (eqset_dec l1 l2 sm_value_deq) as [d|d].
    { apply sm_choice_cond3 in d; rewrite d in *; tcsp. }
    apply not_eqset_implies; auto.
    apply sm_value_deq.
  Qed.


  (* ===============================================================
     No trusted component
     =============================================================== *)

  Global Instance SM_I_IOTrustedFun : IOTrustedFun := MkIOTrustedFun (fun _ => MkIOTrusted unit unit tt).


  Inductive General :=
  | general (n : Gen).

  Coercion general : Gen >-> General.

  Definition General2Gen (g : General) : Gen :=
    match g with
    | general n => n
    end.

  Coercion General2Gen : General >-> Gen.

  Lemma GeneralDeq : Deq General.
  Proof.
    introv; destruct x as [g1], y as [g2].
    destruct (gen_deq g1 g2);[left|right]; subst; auto.
    intro xx; inversion xx; subst; tcsp.
  Defined.

  Global Instance SM_I_Node : Node := MkNode General GeneralDeq.

  Lemma general_inj : injective general.
  Proof.
    introv h; ginv; auto.
  Qed.

  Definition General2GenOp (g : General) : option Gen :=
    Some (General2Gen g).

  Lemma Gen2General_cond : forall n, General2GenOp (general n) = Some n.
  Proof.
    tcsp.
  Qed.

  Lemma General2Gen_cond : forall n m, General2GenOp m = Some n -> general n = m.
  Proof.
    introv h.
    unfold General2GenOp in h; ginv; simpl; destruct m; auto.
  Qed.

  Global Instance SM_I_Quorum : Quorum_context :=
    MkQuorumContext
      Gen
      num_generals
      gen_deq
      gens2nat
      gens_bij
      _
      _
      Gen2General_cond
      General2Gen_cond
      general_inj.

  Definition SMtokens := list SMtoken.

  Global Instance SM_I_AuthTok : AuthTok :=
    MkAuthTok
      SMtoken
      SMtokendeq.


  (* 0 is less than F+2 *)
  Definition nat_n_Fp2_0 : nat_n num_generals.
  Proof.
    exists 0.
    apply leb_correct.
    apply num_generals_non_empty.
  Defined.

  Definition general0 : Gen := bij_inv gens_bij nat_n_Fp2_0.

  Definition nat2gen (n : nat) : Gen.
  Proof.
    destruct gens_bij as [f a b].
    destruct (lt_dec n num_generals) as [d|d].
    - exact (f (mk_nat_n d)).
    - exact general0.
  Defined.

  Definition SMcommander : Gen := nat2gen 0.

  Definition is_commander (g : Gen) : bool :=
    if gen_deq g SMcommander then true else false.

  Definition is_lieutenant (g : Gen) : bool := negb (is_commander g).

  Lemma is_commander_false :
    forall n, is_commander n = false <-> n <> SMcommander.
  Proof.
    introv.
    unfold is_commander.
    dest_cases w; split; intro h; tcsp.
  Qed.

  Lemma is_commander_true :
    forall n, is_commander n = true <-> n = SMcommander.
  Proof.
    introv.
    unfold is_commander.
    dest_cases w; split; intro h; tcsp.
  Qed.

(*  Record sm_sign :=
    MkSmSign
      {
        sm_sign_id : General;
        sm_sign_sign : SMtokens;
      }.*)

  Definition sm_signs := list Sign.

  (* here message contains a Set of generals who already saw this value *)
  Record sm_signed_msg :=
    MkSmSignedMsg
      { sm_signed_msg_value : sm_value;
        sm_signed_msg_signs : list Sign;
        sm_signed_msg_sign  : Sign}.

  (* FIX: should we also add timestamps here so that we can make difference
       between different values that commanders proposed *)
  (* V: [sm_order] is abstract.  Is it enough to instantiate it with pairs
       of values and a timestamp? *)

  Inductive SMmsg : Type :=
  | sm_msg_init
  | sm_msg_alarm
  | sm_msg_signed (v : sm_signed_msg)
  | sm_msg_result (v : sm_value).

  Global Instance SM_I_Msg : Msg := MkMsg SMmsg sm_msg_init.

  (* FIX : Is this correct? *)
  Definition SMmsg2status (m : SMmsg) : msg_status :=
    match m with
    | sm_msg_init     => MSG_STATUS_INTERNAL
    | sm_msg_alarm    => MSG_STATUS_INTERNAL
    | sm_msg_signed _ => MSG_STATUS_PROTOCOL
    | sm_msg_result _ => MSG_STATUS_INTERNAL (* sent to itself *)
    end.

  Global Instance SM_I_get_msg_status : MsgStatus := MkMsgStatus SMmsg2status.

  Record sm_bare_signed_msg :=
    MkSmBareSignedMsg
      { sm_bare_signed_msg_value : sm_value;
(*        sm_bare_signed_msg_gens  : list General;  *)
        sm_bare_signed_msg_gen   : Gen }.

  Inductive SMbare_msg : Type :=
  | sm_bare_msg_signed (v : sm_bare_signed_msg)
  | sm_bare_msg_result (v : sm_value).

  Global Instance SM_I_Data : Data := MkData SMbare_msg.

  (* extraxt value and auth *)

  Definition sm_signed_msg2value (m : sm_signed_msg) : sm_value :=
    sm_signed_msg_value m.

  Definition SMmsg2value (m : SMmsg) : option sm_value :=
    match m with
    | sm_msg_init     => None
    | sm_msg_alarm    => None
    | sm_msg_signed v => Some (sm_signed_msg2value v)
    | sm_msg_result v => Some v
    end.

  Definition sm_signed_msg2sign (m : sm_signed_msg) : Sign :=
    match m with
    | MkSmSignedMsg v l a => a
    end.

  Definition sm_signed_msg2auth (m : sm_signed_msg) : SMtokens :=
    sign_token (sm_signed_msg2sign m).

  Definition sm_signed_msg2sender (m : sm_signed_msg) : Gen :=
    sign_name (sm_signed_msg2sign m).

  (* Note: add the last signature at the beginning of the list *)
  Definition sm_signed_msg2signs_old (m : sm_signed_msg) : list Sign :=
    match m with
    | MkSmSignedMsg _ l a => [a] ++ l
    end.

  Fixpoint sm_signed_msg2signs_temp
           (v   : sm_value)
           (l   : list Sign)
           (a   : Sign) : list Sign :=
    match l with
    | [] => [a]
    | el :: l' => snoc (sm_signed_msg2signs_temp v l' el) a
    end.

  Definition sm_signed_msg2signs (m : sm_signed_msg) : list Sign :=
    match m with
    | MkSmSignedMsg v l a => sm_signed_msg2signs_temp v l a
    end.


  (* only the last sender *)
  Definition SMmsg2sender (m : SMmsg) : option Gen :=
    match m with
    | sm_msg_init     => None
    | sm_msg_alarm    => None
    | sm_msg_signed v => Some (sm_signed_msg2sender v)
    | sm_msg_result v => None
    end.

  Definition sm_signed_msg2senders_old (m : sm_signed_msg) : list Gen :=
    match m with
    | MkSmSignedMsg v l a => snoc (rev (map sign_name l))  (sign_name a)
    end.

  Fixpoint sm_signed_msg2senders_temp
           (v  : sm_value)
           (l  : list Sign)
           (a  : Sign)  : list Gen :=
    match l with
    | [] => [(sign_name a)]
    | el :: l' => snoc (sm_signed_msg2senders_temp v l' el) (sign_name a)
    end.

  Definition sm_signed_msg2senders (m : sm_signed_msg) : list Gen :=
    match m with
    | MkSmSignedMsg v l a => sm_signed_msg2senders_temp v l a
    end.

  (* all senders; correct order *)
  Definition SMmsg2senders (m : SMmsg) : list Gen :=
    match m with
    | sm_msg_init     => []
    | sm_msg_alarm    => []
    | sm_msg_signed v => sm_signed_msg2senders v
    | sm_msg_result v => []
    end.

(*  Definition sm_signed_msg2msgs (m : sm_signed_msg) : list sm_signed_msg :=
    match m with
    | MkSmSignedMsg v l a => [m]
    end.*)

(*  (* all signed messages; correct order *)
  Fixpoint SMmsg2signed_messages (m : SMmsg) : list SMmsg :=
    match m with
    | sm_msg_init     => []
    | sm_msg_alarm    => []
    | sm_msg_signed v => map sm_msg_signed (sm_signed_msg2msgs v)
    | sm_msg_result v => []
    end.*)


  (* only the last signature *)
  Definition SMmsg2sign (m : SMmsg) : option SMtokens :=
    match m with
    | sm_msg_init     => None
    | sm_msg_alarm    => None
    | sm_msg_signed v => Some (sign_token (sm_signed_msg2sign v))
    | sm_msg_result v => None
    end.

  (* all signatures; correct order *)
  Fixpoint SMmsg2signs (m : SMmsg) : list SMtokens :=
    match m with
    | sm_msg_init     => []
    | sm_msg_alarm    => []
    | sm_msg_signed v => map sign_token (sm_signed_msg2signs v)
    | sm_msg_result v => []
    end.

  Definition gens : list Gen := nodes.
  Definition ngens : list name := map general gens.

  Lemma gens_prop : forall (x : Gen), In x gens.
  Proof.
    exact nodes_prop.
  Qed.
  Hint Resolve gens_prop : sm2.

  Global Instance SM_I_Key : Key := MkKey SMsending_key SMreceiving_key.

  Class SMauth :=
    MkSMauth
      {
        SMcreate : data -> sending_keys -> SMtokens;
        SMverify : data -> name -> receiving_key -> SMtoken -> bool
      }.
  Context { sm_auth : SMauth }.

  Global Instance SM_I_AuthFun : AuthFun :=
    MkAuthFun
      SMcreate
      SMverify.

  Class SMinitial_keys :=
    MkSMinitial_keys {
        initial_keys : key_map;
      }.

  Context { sm_initial_keys : SMinitial_keys }.

  (*Record value_and_senders :=
    Build_ValueAndSenders
      {
        (* None means that we have no messages so far, and sm_value_default means that we received message with empty value *)
        v         : option sm_value;
        senders   : list Gen;
      }.*)

  Definition sm_values := list sm_value.

  Record SMstate :=
    Build_SMstate
      {
        (* some initial value *)
        init          : sm_value;

        (* the values we received *)
        V             : sm_values;

        (* The keys that we're holding to communicate with the other replicas *)
        local_keys    : local_key_map;
      }.


  Definition SMinitial_state (g : Gen) (init : sm_value) : SMstate :=
    Build_SMstate
      init
      []
      (initial_keys (general g)).


  (****************************************************************************************)

  Definition sm_bare_signed_msg2general (m : sm_bare_signed_msg) : General :=
    match m with
    | MkSmBareSignedMsg v g => general g
    end.

  Definition SMdata_auth (n : name) (m : data) : option name :=
    match m with
    | sm_bare_msg_signed v => Some (sm_bare_signed_msg2general v)
    | sm_bare_msg_result v => Some n
    end.

  Global Instance SM_I_DataAuth : DataAuth := MkDataAuth SMdata_auth.

  Definition sm_signed_msg2bare (m : sm_signed_msg) : sm_bare_signed_msg :=
    match m with
    | MkSmSignedMsg v l a => MkSmBareSignedMsg v (node2name (sign_name a))
    end.

  (* I also tried this version. But I believe that it is same as one above
  Definition sm_signed_msg2bare (m : sm_signed_msg) : sm_bare_signed_msg :=
    match m with
    | MkSmSignedMsg v l a => match l with
                             | [] => MkSmBareSignedMsg v [] (node2name (sign_name a))
                             | _ => MkSmBareSignedMsg v (map general (sm_signed_msg2senders (MkSmSignedMsg v l a))) (node2name (sign_name a))
                             end
    end.
   *)


  Definition sm_signed_msg2top_auth_data (m : sm_signed_msg) : AuthenticatedData :=
    MkAuthData (sm_bare_msg_signed (sm_signed_msg2bare m)) (sm_signed_msg2auth m).

  Definition sm_signed_msg2main_auth_data (m : sm_bare_signed_msg) (t  : SMtokens) : AuthenticatedData :=
    MkAuthData (sm_bare_msg_signed m) t.

  Fixpoint sm_signed_msg2list_auth_data_temp
             (v    : sm_value)
             (l    : list Sign)
             (a    : Sign) : list AuthenticatedData :=
    let m := MkSmBareSignedMsg v (sign_name a) in
    match l with
    | [] => [sm_signed_msg2main_auth_data m (sign_token a)]
    | el :: ol =>  let m' := MkSmBareSignedMsg v (sign_name a) in
                   snoc (sm_signed_msg2list_auth_data_temp v ol el) (sm_signed_msg2main_auth_data m (sign_token a))
    end.

  (* FIX: check this one!  *)
  Definition sm_signed_msg2list_auth_data (m : sm_signed_msg) : list AuthenticatedData :=
    match m with
    | MkSmSignedMsg v l a => sm_signed_msg2list_auth_data_temp v l a
    end.

  Definition SMget_contained_auth_data (m : SMmsg) : list AuthenticatedData :=
    match m with
    | sm_msg_init     => []
    | sm_msg_alarm    => []
    | sm_msg_signed v => sm_signed_msg2list_auth_data v
    | sm_msg_result v => [] (* these are not signed *)
    end.

  Global Instance SM_I_ContainedAuthData : ContainedAuthData :=
    MkContainedAuthData SMget_contained_auth_data.

  (* Here, we check that all signatures are correct *)
  Definition verify_signed_msg_sign (slf : Gen) (lkm : local_key_map) (m : sm_signed_msg) : bool :=
    forallb
      (fun a => verify_authenticated_data (general slf) a lkm)
      (sm_signed_msg2list_auth_data m).

  (*(* Here, we check that all signatures are correct *)
  Definition verify_msg_sign (slf : Gen) (lkm : local_key_map) (m : SMmsg) : bool :=
    forallb
      (fun a => verify_authenticated_data (general slf) a lkm)
      (SMget_contained_auth_data m).*)

    Fixpoint sm_signed_msg2sing_temp (v : sm_value) (l : list Sign) (a : Sign) : sm_value * Sign :=
    match l with
    | [] => (v, a)
    | el :: ol => sm_signed_msg2sing_temp v ol el
    end.

  Definition sm_signed_msg2sing (m : sm_signed_msg) : sm_value * Sign :=
    match m with
    | MkSmSignedMsg v l a => sm_signed_msg2sing_temp v l a
    end.

  (* Here, we check that the first one to sign was the commander *)
  Definition verify_msg_commander (m : SMmsg) : bool :=
    match m with
    | sm_msg_init  => false
    | sm_msg_alarm => false
    | sm_msg_signed v =>
      let (_,a) := sm_signed_msg2sing v in
      is_commander (sign_name a)
    | sm_msg_result _ => false
    end.

  (* Here, we check that the first one to sign was the commander *)
  Definition verify_signed_msg_commander (m : sm_signed_msg) : bool :=
    is_commander (sign_name (snd (sm_signed_msg2sing m))).

  Definition is_sm_signed_msg2directly_from_commander (m : sm_signed_msg) : bool :=
    match m with
    | MkSmSignedMsg v l a  => match l with
                              | [] => is_commander (sign_name a)
                              | _ => false
                              end
    end.

  Definition verify_signed_msg (slf : Gen) (lkm : local_key_map) (m : sm_signed_msg) : bool :=
    (* all signatures have to be correct *)
    (verify_signed_msg_sign slf lkm m)
      (* the first signer has to be the commander *)
      && (verify_signed_msg_commander m)
      (* the senders have to be different from each other *)
      && (norepeatsb gen_deq (sm_signed_msg2senders m))
      (* the receiver should not be in the list of signers *)
      && (not_inb gen_deq slf (sm_signed_msg2senders m)).

  (*Definition verify_msg (slf : Gen) (lkm : local_key_map) (m : SMmsg) : bool :=
    verify_msg_sign slf lkm m && verify_msg_commander m.*)

(* Fixpoint verify_msg_form_list_senders_signatures
             (signed_messages  : list SMmsg)
             (senders          : list Gen)
             (signatures       : list SMtokens)
             (lkm              : local_key_map) : bool :=
    (* here we take care of only properly structure messages *)
    match signed_messages, senders, signatures with
    | [] , [], [] => true
    | m :: l_signed_messages, g :: l_senders, a :: l_signatures =>
      if verify_authenticated_data (general g) (sm_msg_lieutenant2auth_data m g a) lkm then
        verify_msg_form_list_senders_signatures l_signed_messages l_senders l_signatures lkm
      else false
    | _ , _ , _ => false (* this should never happened *)
    end.

  Definition remove_first_element {A} (l : list A) : list A :=
    match l with
    | [] => []
    | h :: t => t
    end.

    Definition first_element {A} (l : list A) :  option A :=
    match l with
    | [] => None
    | h :: t =>  Some h
    end.

  Definition verify_msg (lkm : local_key_map) (m : SMmsg) : bool :=
    let value                := SMmsg2value m in
    let list_senders         := SMmsg2senders m in
    let list_signatures      := SMmsg2signs m in
    let list_signed_messages := app (SMmsg2signed_messages m) [m] in

  (* here we check only if the message that commander signed was correct,
   and forward the rest to the verify_msg_form_list_senders_signatures *)
    let c := first_element list_senders in
    let a := first_element list_signatures in

    match c, a with
    | Some c, Some a =>
      if verify_authenticated_data (general c) (sm_msg_commander2auth_data value c a) lkm then

        (* check if all other messages are signed properly *)
        let list_senders'    := remove_first_element list_senders in
        let list_signatures' := remove_first_element list_signatures in

        verify_msg_form_list_senders_signatures list_signed_messages list_senders' list_signatures' lkm

      else false

    |_,_ => false (* this should never happened *)
    end.*)

  Definition check_new_value
             (V : sm_values (*value_and_senders*))
             (m : sm_signed_msg) : bool :=
    if in_dec sm_value_deq (sm_signed_msg2value m) V then false
    else true.

(*  Fixpoint check_new_value
           (slf : Gen)
           (V   : list value_and_senders)
           (m   : SMmsg) : bool :=
    match V with
    | [] => true
    | entry :: entries =>
      match entry with
      | Build_ValueAndSenders v senders =>
        match v with
        | None => false (* this means that message was missing the value! *)
        | Some value => if sm_value_deq (SMmsg2value m) value then false
                        else check_new_value slf entries m
        end
      end
    end.*)

(*  Fixpoint occurrences (e : sm_value) (l : list sm_value) : nat :=
    match l with
    | [] => 0
    | entry :: entries =>
      if sm_value_deq e entry then 1 + occurrences e entries
      else occurrences e entries
    end.*)

  (* median value is return -- see pg. 391
  Fixpoint choice_V_ (l : list value_and_senders) : (option sm_value * nat) :=
    match l with
    | [] => (None, 0)
    | entry :: entries => match entry with
                          | Build_ValueAndSenders val senders =>
                            match val with
                            | None => (Some sm_value_default,0) (* pg. 391 retreat is default value *)
                            | Some v =>
                              let (sum_val, num) := choice_V entries in
                               , num + 1)

                              (Some v, 1)
                              (* we should have a median value here *)
(*                              let med :=  choice_V entries *)
                            end
                          end
                              end.
   *)

(*  Fixpoint all_sm_values (l : list value_and_senders) : list sm_value :=
    match l with
    | [] => []
    | entry :: entries =>
      match entry with
      | Build_ValueAndSenders val senders =>
        match val with
        | None => [sm_default_value] (* pg. 391 retreat is default value *)
        | Some v =>
          let l' := all_sm_values entries in
          match l' with
          | [] => [v]
          | _ => v :: l'
          end
        end
      end
    end.

  Fixpoint number_of_diff_values (l : list value_and_senders) : nat :=
    match l with
    | [] => 0
    | entry :: entries => match entry with
                          | Build_ValueAndSenders val senders =>
                            match val with
                            | None => 1 (* pg. 391 retreat is default value *)
                            | Some v => (number_of_diff_values entries) + 1
                            end
                          end
    end.


  (* median value is return -- see pg. 391 *)
  Definition choice_V (l : list value_and_senders) : sm_value :=
    let nb_val  := number_of_diff_values l in
    let all_val := all_sm_values l in
    sm_choice all_val (*nb_val*).*)


  (* message has the form (v:0) *)
  Definition commander_message (m : SMmsg) : bool := verify_msg_commander m.

  (* message has the form (v:0:j1:...jk) *)
  Definition commander_lieutenant (m : SMmsg) : bool := negb (verify_msg_commander m).

  (* general have not received any order yet *)
  Definition no_order_yet (V : sm_values (*value_and_senders*)) : bool := nullb V.

(*  (* add value v to the V; no order received so far *)
  Definition add_value_to_V_no_order_yet (v : sm_value) (V : sm_values) :=
    match V with
    | [] => [v]
    | l => l (* this should never happened!!! *)
    end.*)

  (*Definition update_state_V (s : SMstate) (V : sm_values) : SMstate :=
    Build_SMstate
      (init       s)
      V
      (local_keys s)
      (bp         s).*)

  Definition add_to_V (s : SMstate) (v : sm_value) : SMstate :=
    Build_SMstate
      (init          s)
      (v ::        V s)
      (local_keys    s).


  (* FIX: check *)
  Definition extend_signed_msg
             (m    : sm_signed_msg)
             (g    : General)
             (keys : local_key_map) : sm_signed_msg :=
    match m with
    | MkSmSignedMsg v ls a =>  let ls' := [a] ++ ls in
                               let b  := MkSmBareSignedMsg v g in
                               let a' := authenticate (sm_bare_msg_signed b) keys in
                               MkSmSignedMsg v ls' (MkSign (General2Gen g) a')
    end.


  Definition extend_msg
             (m    : SMmsg)
             (g    : General)
             (keys : local_key_map) : SMmsg :=
    match m with
    | sm_msg_init     => m
    | sm_msg_alarm    => m
    | sm_msg_signed v => sm_msg_signed (extend_signed_msg v g keys)
    | sm_msg_result v => m
    end.

  Definition send_sm_msg_commander (m : SMmsg) (n : list name) : DirectedMsg :=
    MkDMsg m n ('0).

  Definition send_sm_msg_lieutenant (m : SMmsg) (n : list name) : DirectedMsg :=
    MkDMsg m n ('0).

  Definition gens_not_in_list (l : list Gen) : list Gen :=
    diff gen_deq l gens.

  Definition names_not_in_list (l : list Gen) : list name :=
    map general (gens_not_in_list l).

  Definition broadcast2not_in_list (l : list Gen) F : DirectedMsg :=
    F (names_not_in_list l).

  Definition create_new_sm_signed_msg
             (v    : sm_value)
             (keys : local_key_map) : sm_signed_msg :=
    let b  := MkSmBareSignedMsg v (general SMcommander) in
    let a := authenticate (sm_bare_msg_signed b) keys in
    MkSmSignedMsg v [] (MkSign SMcommander a).

  Definition create_new_msg_commander
             (v    : sm_value)
             (keys : local_key_map) : SMmsg :=
    sm_msg_signed (create_new_sm_signed_msg v keys).

  Definition create_new_msg_result (v : sm_value) : SMmsg:=
    let b := sm_bare_msg_result v in
    sm_msg_result v.

  (* FIX: the paper is not clear what lieutenants do with their decision at the end.
      We send the final decision to ourselves. *)
  Definition send_sm_msg_result (slf : Gen) (m : sm_value) : DirectedMsg :=
    MkDMsg (sm_msg_result m) [general slf] ('0).


  (* FIX: correct delay?  [F] or [F+1]? *)
  Definition send_alarm (slf : Gen) : DirectedMsg :=
    MkDMsg sm_msg_alarm [general slf] (pdt_mult ('(S F)) (pdt_plus mu tau)).


  (* handler of initial message sent to commander to start it *)
  Definition SMhandler_initial (slf : Gen) : Update SMstate unit DirectedMsgs :=
    fun state v t =>
      let keys   := local_keys state in
      let V_list := V state in

      if dt_eq_dec t (nat2pdt 0) then

        if is_commander slf then
          let new_msg := create_new_msg_commander (init state) keys in
          let new_state1 := add_to_V state (init state) in

          (* commander broadcasts new message to all replicas *)
          (Some new_state1, [broadcast2not_in_list [SMcommander] (send_sm_msg_commander new_msg)])

        else
          (Some state, [send_alarm slf])

      else (* initial messages are supposed to be received at time 0 *)
        (Some state, []).



  Definition message_is_on_time (m : sm_signed_msg) (t : PosDTime) : bool :=
    let signs := sm_signed_msg2signs m in
    if dt_le_lt_dec t (nat2pdt (length signs) * (mu + tau))%dtime then
      (* We don't care about messages with more than F+1 signatures,
         we're not supposed to send any: *)
      if le_dec (length signs) (S F) then true else false
    else false.


  Definition SMhandler_lieutenant (slf : Gen) : Update SMstate sm_signed_msg DirectedMsgs :=
    fun state m time =>
      let keys := local_keys state in
      let Vs   := V state in

      if is_lieutenant slf then

        if verify_signed_msg slf keys m then

          if message_is_on_time m time then

            (* is message of the form (v:0), i.e., commander message *)
            if is_sm_signed_msg2directly_from_commander m then

              (* lieutenant have not received any order yet *)
              if no_order_yet Vs then

                (* add value (received with msg m) to the V, assuming that general have not received any order yet *)
                let new_state1 := add_to_V state (sm_signed_msg2value m) in

                if 1 <=? F then

                  (* create new message v:0:i *)
                  let new_signed_msg := extend_signed_msg m (general slf) keys in
                  let new_msg := sm_msg_signed new_signed_msg in

                  (* we broadcast new message to all replicas that are not in the message i.e. commander in this case *)
                  (Some new_state1, [broadcast2not_in_list [slf,SMcommander] (send_sm_msg_lieutenant new_msg)])

                else
                  (Some new_state1, [])

              else (* message has the form (v:0), but lieutenant has some order already received *)
                (Some state, [])

            else (* message is not of the form (v:0), i.e., commander message
              i.e., message has the form (v:0:j1:..:jk *)

              (* if this is the value that was not received before *)
              if check_new_value Vs m then

                (* add value (received with msg m) to the V, assuming that general already received some value *)
                let new_state1 := add_to_V state (sm_signed_msg2value m) in

                (* if k < m , i.e., (if number of senders is less than number of faults) then broadcast the message *)
                (* NOTE : F + 1 because commander is one of the senders *)
                if length (sm_signed_msg2senders m) <=? F then

                  (* create new message v:0:j1:...:jk:i *)
                  let new_signed_msg := extend_signed_msg m (general slf) keys in
                  let new_msg := sm_msg_signed new_signed_msg in

                  let ls := sm_signed_msg2senders m in

                  (* we broadcast new message to all replicas that were not in the message *)
                  (Some new_state1, [broadcast2not_in_list (slf :: ls) (send_sm_msg_lieutenant new_msg)])

                else (* number of senders is not less than number of faults,
                  i.e., in this case lieutenant obeys the order determined with choice(V) *)
                  (Some new_state1, [])

              else (* this value was received before *)
                (Some state, [])

          else (* message is not on time *)
            (Some state, [])

        else (* message is not signed properly *)
          (Some state, [])

      else (* not a lieutenant *)
        (Some state, []).


  Definition SMhandler_result (slf : Gen) : Update SMstate sm_value DirectedMsgs :=
    fun state _ _ => (Some state, []).


  Definition SMhandler_alarm (slf : Gen) : Update SMstate unit DirectedMsgs :=
    fun state _ t =>
      if is_lieutenant slf then
        if dt_le_lt_dec t (pdt_mult ('(S F)) (pdt_plus mu tau))
        then (Some state, []) (* this shouldn't happen because the alarm was set to [(F+1)*(mu+tau)] *)
        else
          let choice := sm_choice (V state) in
          (* we send the signed msg that contains choice to all other replicas *)
(*          let new_msg := create_new_msg_result choice in *)
          (Some state, [send_sm_msg_result slf choice])
      else (Some state, []).


  (*
     NOTE:

     - The init message has to be sent to the commander at time T0
     - Alarms have to be sent to the lieutenants at time T0, and have to be
       set as in [send_alarm].
   *)
  Definition SMupdate (slf : Gen) : MUpdate SMstate :=
    fun state m =>
      match m with
      | sm_msg_init     => SMhandler_initial    slf state tt
      | sm_msg_alarm    => SMhandler_alarm      slf state tt
      | sm_msg_signed v => SMhandler_lieutenant slf state v
      | sm_msg_result v => SMhandler_result     slf state v
      end.

  Definition SMreplicaSM (slf : Gen) : MStateMachine _ :=
    mkSM
      (SMupdate slf)
      (SMinitial_state slf (sm_initial_values slf)).

  Definition SMsys : MUSystem (fun n => SMstate) := SMreplicaSM.

  (*Definition initial_conditions (eo : EventOrdering) :=
    forall (e : Event) g,
      has_correct_trace_before e (loc e)
      -> loc e = general g
      -> isFirst e
      -> (time e = 0 /\ trigger e = Some sm_msg_init).*)

End SM2.


Hint Resolve gens_prop : sm2.
