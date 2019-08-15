Require Export MinBFT.
(* Require Export CorrectKeys. *)


Section MinBFT_at_most_f_byz.

  (*  Context { pk  : @Key }.    if I add this one MinBFT_at_most_f_byz1 complains, but it still does not solve my problem *)
  Local Open Scope eo.
  Local Open Scope proc.

  Context { minbft_context      : MinBFT_context }.
  Context { minbft_initial_keys : MinBFT_initial_keys }.
(*  Context { dm                  : DataMessage }. *)
  Context { minbft_auth         : MinBFT_auth }.
  Context { usig_hash : USIG_hash }.


  (* This says that all the events [e] _at all time_ that happen
      at non-faulty locations (not in the [faulty] list are indeed non-faulty *)
  Definition MinBFT_at_most_f_byz1 (eo : EventOrdering) :=
    exists (faulty : list Rep),
      length faulty <= F
      /\
      forall (e : Event),
        ~ In (loc e) (map MinBFT_replica faulty)
        -> isCorrect e.

  Lemma MinBFT_at_most_f_byz1_implies :
    forall (eo : EventOrdering) L,
      MinBFT_at_most_f_byz1 eo -> AXIOM_exists_at_most_f_faulty L F.
  Proof.
    introv atmost.
    unfold MinBFT_at_most_f_byz1 in *.
    exrepnd.
    exists faulty.
    repnd; dands; auto.
    introv i j k eqn w.
    apply atmost0.
    introv xx; allrw in_map_iff; exrepnd; subst.
    assert (loc e' = loc e1) as eqloc by eauto with eo.
    rewrite k in eqloc; rewrite <- xx1 in eqloc; simpl in eqloc; ginv.
  Qed.
  Hint Resolve MinBFT_at_most_f_byz1_implies : pbft.

(*  Check (fun i => @M_state_sm_before_event
                    MinBFT_I_Node
                    MinBFT_I_Key
                    MinBFT_I_Msg
                    baseFunIOusig
                    2
                    (MinBFT_replicaSM i)).
*)

  Definition AXIOM_MinBFT_correct_keys (eo : EventOrdering) :=
    forall (e : Event) (i : Rep) st,
      node_has_correct_trace_before e i
      -> M_state_sm_before_event (MinBFT_replicaSM i) e = st
      -> st >p>= (fun sop => match sop with
                            | Some s => ret _ (keys e = local_keys s)
                            | None => ret _ True
                            end).

  Definition default_local_key_map : local_key_map :=
    MkLocalKeyMap [] [].

  Definition MinBFT_get_keys0 (i : name) : MinBFT_nstate i -> local_key_map :=
    match i with
    | MinBFT_replica i => fun s => local_keys s
    | MinBFT_client _  => fun _ => default_local_key_map
    end.

  Definition MinBFT_get_keys (i : name) : sm2S (MinBFTsys i) -> local_key_map :=
    match i with
    | MinBFT_replica i => fun s => local_keys s
    | MinBFT_client _  => fun _ => default_local_key_map
    end.


 Lemma correct_keys_implies_MinBFT_correct_keys :
   forall {eo : EventOrdering} (e : Event),
     AXIOM_M_correct_keys
       (fun name => system2main_local e MinBFTsys)
       (fun name => MinBFT_get_keys name)
       eo
     -> AXIOM_MinBFT_correct_keys eo.
  Proof.
    introv cor ctrace eqst.
    apply (cor e (MinBFT_replica i) st); auto.
  Qed.


  Lemma correct_keys_implies_MinBFT_correct_keys_sys :
  forall (eo : EventOrdering) (e : Event),
    AXIOM_M_correct_keys_sys MinBFTsys  e (MinBFT_get_keys name) eo
    -> AXIOM_MinBFT_correct_keys eo.
  Proof.
    introv cor ctrace eqst.
    apply (cor e (MinBFT_replica i) st); auto.
  Qed.




  XXXXXXXXXXXXXXXXXXXx


End MinBFT_at_most_f_byz.


Hint Resolve MinBFT_at_most_f_byz1_implies : pbft.


(***************** old code to be checked ************************

(*  CHECK this one
 Definition AXIOM_M_correct_keys_new
             {eo   : EventOrdering}
             (sys  : M_USystem)
             (K    : forall (e : Event), sm2S (system2main_local e sys) -> local_key_map)
              : Prop :=
    forall (e : Event) (i : name) st,
      has_correct_trace_before e i
      -> M_state_sm_before_event (system2main_local e sys)  e = st
      -> st >p>= (fun sop => match sop with
                             | Some s => ret _ (keys e = K e s)
                             | None => ret _ True
                             end).
 *)

  (*  CHECK this one
  Definition AXIOM_M_correct_keys_new2
             {eo   : EventOrdering}
             (sys  : M_USystem)
             (K  : forall (i : name), sm2S (sys i) -> local_key_map)
              : Prop :=
    forall (e : Event) (i : name) st,
      has_correct_trace_before e i
      -> M_state_sm_before_event (system2main_local e sys)  e = st
      -> st >p>= (fun sop => match sop with
                             | Some s => ret _ (keys e = K i  (sm2S (sys i)))
                             | None => ret _ True
                             end).
*)
*******************************************************)