Require Export toString.
Require Export CalculusSM.

From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype choice tuple finfun.

Require Import Reals (*Fourier FunctionalExtensionality*).

From infotheo
Require Import fdist proba (*pproba*) (*ssrR*) Reals_ext (*logb ssr_ext ssralg_ext bigop_ext*) Rbigop.


(* We assume that if a message is not lost, it gets received by some time [R+1] *)
Class ProbaParams :=
  MkProbaParams {
      (* probability that a message gets lots *)
      LostDist : prob;

      (* probability distribution that messages are received over a finite event
         set of size R+1 (i.e., R+1 discrete time points *)
      RcvdDist : forall (R : nat), fdist [finType of 'I_R.+1];
    }.

Class BoundsParams :=
  MkBoundsParams {
      (* time by which a message is considered lost *)
      maxRound : nat;

      (* To get finite types we can only reason up to so maximal time *)
      maxTime  : nat;

      (* To get finite types again: *)
      maxMsgs  : nat;
    }.

Class ProcParams :=
  MkProcParams {
      numNodes : nat;
      message  : finType;
      state    : finType;
  }.


(* Inspired by probachain *)
Section Comp.

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.
  Context { pProc   : ProcParams   }.


  Inductive Comp : finType -> Type :=
  | Ret  : forall (A : finType) (a : A), Comp A
  | Bind : forall (A B : finType), Comp B -> (B -> Comp A) -> Comp A
  | Pick : forall (n : nat), Comp [finType of 'I_n.+1]
  | Lost : Comp [finType of bool].

  (* from probachain *)
  Lemma size_enum_equiv :
    forall n: nat, size(enum (ordinal n.+1)) = n.+1 -> #|ordinal_finType n.+1| = n.+1.
  Proof.
    move=> n H.
      by rewrite unlock H.
  Qed.

  Definition pickRound : Comp [finType of 'I_(maxRound.+1)] :=
    Pick maxRound.

  Fixpoint getSupport {A : finType} (c : Comp A) : list A :=
    match c with
    | Ret _ a => [a]
    | Bind _ _ c1 c2 =>
      flat_map
        (fun b => (getSupport (c2 b)))
        (getSupport c1)
    | Pick n => ord_enum n.+1
    | Lost => [true, false]
    end.

  Fixpoint evalDist {A : finType} (c : Comp A) : fdist A :=
    match c with
    | Ret _ a => FDist1.d a
    | Bind _ _ c f => FDistBind.d (evalDist c) (fun b => evalDist (f b))
    | Pick n => RcvdDist n
    | Lost => Binary.d card_bool LostDist true (* i.e., LostDist if true and 1-LostDist if false *)
    end.

  Definition distRound : fdist [finType of 'I_(maxRound.+1)] := RcvdDist maxRound.

End Comp.

Arguments Ret [A] _.
Arguments Bind [A] [B] _ _.


Section finList.

  Variables (n : nat) (T : finType).

  Structure finList_of : Type := FinList {fLval :> seq T; _ : length fLval <= n}.
  Canonical finList_subType := Eval hnf in [subType for fLval].

  Definition finList_eqMixin  := Eval hnf in [eqMixin of finList_of by <:].
  Canonical finList_eqType    := Eval hnf in EqType finList_of finList_eqMixin.
  Canonical finList_of_eqType := Eval hnf in [eqType of finList_of].

  Definition finList_choiceMixin  := [choiceMixin of finList_of by <:].
  Canonical finList_choiceType    := Eval hnf in ChoiceType finList_of finList_choiceMixin.
  Canonical finList_of_choiceType := Eval hnf in [choiceType of finList_of].

  Definition finList_countMixin  := [countMixin of finList_of by <:].
  Canonical finList_countType    := Eval hnf in CountType finList_of finList_countMixin.
  Canonical finList_subCountType := Eval hnf in [subCountType of finList_of].
  Canonical finList_of_countType := Eval hnf in [countType of finList_of].

  Definition enumN (n : nat) : seq finList_of :=
    let extend e := flatten (codom (fun (x : T) => map (List.cons x) e)) in
    pmap insub (iter n extend [::[::]]).

  Fixpoint enumUpToN (n : nat) : seq finList_of :=
    match n with
    | 0 => enumN n
    | S m => enumN n ++ enumN m
    end.

  Definition enum : seq finList_of := enumUpToN n.

  Lemma enumFL : Finite.axiom enum.
  Proof.
    case=> /= l l_n.
    (* TODO *)
  Admitted.

  Definition finList_finMixin  := Eval hnf in FinMixin enumFL.
  Canonical finList_finType    := Eval hnf in FinType finList_of finList_finMixin.
  Canonical finList_subFinType := Eval hnf in [subFinType of finList_of].
  Canonical finList_of_finType := Eval hnf in [finType of finList_of].

  Implicit Type l : finList_of.

  Definition sizeFL l  := length l.

  Lemma splitFL_cond :
    forall (hd : T) (tl : seq T) (p : length (hd :: tl) <= n),
      length tl <= n.
  Proof.
    auto.
  Qed.

  Definition splitFL l : option T * finList_of :=
    match l with
    | FinList [] p => (None, l)
    | FinList (hd :: tl) p => (Some hd, FinList tl (splitFL_cond hd tl p))
    end.

  Lemma rotateFL_cond :
    forall (hd : T) (tl : seq T) (p : length (hd :: tl) <= n),
      length (snoc tl hd) <= n.
  Proof.
    introv h; simpl in *; rewrite length_snoc; auto.
  Qed.

  Definition rotateFL l : finList_of :=
    match l with
    | FinList [] p => l
    | FinList (hd :: tl) p => FinList (snoc tl hd) (rotateFL_cond hd tl p)
    end.

  Definition emFL : finList_of := FinList [] is_true_true.

End finList.

Notation "n .-finList" := (finList_of n)
  (at level 2, format "n .-finList") : type_scope.


Section Msg.

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.
  Context { pProc   : ProcParams   }.

  Definition location := 'I_numNodes.
  Definition time     := 'I_maxTime.+1.


  Record DMsg :=
    MkDMsg
      {
        dmsg_src : location;   (* sender *)
        dmsg_dst : location;   (* receiver *)
        dmsg_snd : time; (* time it was sent *)
(*        dmsg_rcv : 'I_maxTime; (* time it is received *)*)
        dmsg_msg : message;    (* payload message *)
      }.

  Definition DMsg_prod (d : DMsg) :=
    (dmsg_src d,
     dmsg_dst d,
     dmsg_snd d,
(*     dmsg_rcv d,*)
     dmsg_msg d).

  Definition prod_DMsg prod :=
    let: (dmsg_src,
          dmsg_dst,
          dmsg_snd,
(*          dmsg_rcv,*)
          dmsg_msg) := prod in
    MkDMsg
      dmsg_src
      dmsg_dst
      dmsg_snd
(*      dmsg_rcv*)
      dmsg_msg.

  Lemma DMsg_cancel : cancel DMsg_prod prod_DMsg .
  Proof.
      by case.
  Qed.

  Definition DMsg_eqMixin      := CanEqMixin DMsg_cancel.
  Canonical DMsg_eqType        := Eval hnf in EqType (DMsg) DMsg_eqMixin.
  Canonical dmsg_of_eqType     := Eval hnf in [eqType of DMsg].
  Definition DMsg_choiceMixin  := CanChoiceMixin DMsg_cancel.
  Canonical DMsg_choiceType    := Eval hnf in ChoiceType (DMsg) DMsg_choiceMixin.
  Canonical dmsg_of_choiceType := Eval hnf in [choiceType of DMsg].
  Definition DMsg_countMixin   := CanCountMixin DMsg_cancel.
  Canonical DMsg_countType     := Eval hnf in CountType (DMsg) DMsg_countMixin.
  Canonical dmsg_of_countType  := Eval hnf in [countType of DMsg].
  Definition DMsg_finMixin     := CanFinMixin DMsg_cancel.
  Canonical DMsg_finType       := Eval hnf in FinType (DMsg) DMsg_finMixin.
  Canonical dmsg_of_finType    := Eval hnf in [finType of DMsg].

End Msg.


Section Status.

  Inductive Status :=
  | StCorrect
  | StFaulty.

  Definition leSt (s1 s2 : Status) : bool :=
    match s1,s2 with
    | StCorrect,_ => true
    | StFaulty,StFaulty => true
    | StFault,StCorrect => false
    end.

  Definition isCorrectStatus (s : Status) :=
    match s with
    | StCorrect => true
    | StFaulty => false
    end.

  Definition Status_bool (s : Status) :=
    match s with
    | StCorrect => true
    | StFaulty => false
    end.

  Definition bool_Status b :=
    match b with
    | true => StCorrect
    | false => StFaulty
    end.

  Lemma Status_cancel : cancel Status_bool bool_Status .
  Proof.
      by case.
  Qed.

  Definition Status_eqMixin      := CanEqMixin Status_cancel.
  Canonical Status_eqType        := Eval hnf in EqType (Status) Status_eqMixin.
  Canonical status_of_eqType     := Eval hnf in [eqType of Status].
  Definition Status_choiceMixin  := CanChoiceMixin Status_cancel.
  Canonical Status_choiceType    := Eval hnf in ChoiceType (Status) Status_choiceMixin.
  Canonical status_of_choiceType := Eval hnf in [choiceType of Status].
  Definition Status_countMixin   := CanCountMixin Status_cancel.
  Canonical Status_countType     := Eval hnf in CountType (Status) Status_countMixin.
  Canonical status_of_countType  := Eval hnf in [countType of Status].
  Definition Status_finMixin     := CanFinMixin Status_cancel.
  Canonical Status_finType       := Eval hnf in FinType (Status) Status_finMixin.
  Canonical status_of_finType    := Eval hnf in [finType of Status].

End Status.


Section Point.

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.
  Context { pProc   : ProcParams   }.

  (* Points *)
  Record Point :=
    MkPoint
      {
        point_state  : state;
        point_status : Status;
      }.

  Definition update_state (p : Point) (s : state) :=
    MkPoint
      s
      (point_status p).

  Definition Point_prod (p : Point) :=
    (point_state p,
     point_status p).

  Definition prod_Point prod :=
    let: (point_state,
          point_status) := prod in
    MkPoint
      point_state
      point_status.

  Lemma Point_cancel : cancel Point_prod prod_Point .
  Proof.
      by case.
  Qed.

  Definition Point_eqMixin      := CanEqMixin Point_cancel.
  Canonical Point_eqType        := Eval hnf in EqType (Point) Point_eqMixin.
  Canonical point_of_eqType     := Eval hnf in [eqType of Point].
  Definition Point_choiceMixin  := CanChoiceMixin Point_cancel.
  Canonical Point_choiceType    := Eval hnf in ChoiceType (Point) Point_choiceMixin.
  Canonical point_of_choiceType := Eval hnf in [choiceType of Point].
  Definition Point_countMixin   := CanCountMixin Point_cancel.
  Canonical Point_countType     := Eval hnf in CountType (Point) Point_countMixin.
  Canonical point_of_countType  := Eval hnf in [countType of Point].
  Definition Point_finMixin     := CanFinMixin Point_cancel.
  Canonical Point_finType       := Eval hnf in FinType (Point) Point_finMixin.
  Canonical point_of_finType    := Eval hnf in [finType of Point].

End Point.


Section History.

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.
  Context { pProc   : ProcParams   }.

  (* a global state is a tuple of 1 point per node *)
  Definition Global : finType := [finType of {ffun location -> Point}].
  (* A history is a mapping from timestamps to global states - None if not assigned yet *)
  Definition History : finType := [finType of {ffun time -> option Global}].

End History.


Section Queue.

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.
  Context { pProc   : ProcParams   }.

  (* a queue is a list of messages *)
  Definition Queue : finType := [finType of maxMsgs.-finList [finType of DMsg]].
  (* 1 queue per node -- messages are sorted by receiver and are tagged with the time they should be delivered *)
  Definition Queues : finType := [finType of {ffun location -> Queue}].
  (* In Transit messages *)
  Definition InTransit : finType := [finType of {ffun time -> Queues}].


  (* truncates the sequence to maxMsgs *)
  Definition seq2queue (s : seq DMsg) : Queue :=
    FinList
      _ _
      (firstn maxMsgs s)
      ([eta introTF (c:=true) leP] (firstn_le_length maxMsgs s)).

  Definition app_queue (q1 q2 : Queue) : Queue := seq2queue (q1 ++ q2).
  Definition snoc_queue (m : DMsg) (q : Queue) : Queue := seq2queue (snoc q m).

End Queue.


Section World.

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.
  Context { pProc   : ProcParams   }.

  Definition StateFun := location -> state.
  Definition MsgFun   := location -> Queue.
  Definition UpdFun   := forall (t : time) (l : location) (m : message) (s : state), state ## Queue.

  Class SMParams :=
    MkSMParams {
        InitStates   : StateFun;
        InitMessages : MsgFun;
        Upd          : UpdFun;
      }.

  Context { pSM  : SMParams  }.


  Record World :=
    MkWorld
      {
        (* current "real" time *)
        world_time : time;

        (* history *)
        world_history : History;

        (* messages in transit *)
        world_intransit : InTransit;
        (* The way we compute those in the [step] function is that those are the delivered messages *)
      }.

  (* ********* *)
  (* initial world *)
  Definition initGlobal : Global :=
    finfun (fun l => MkPoint (InitStates l) StCorrect).

  (* Initially only the first world is set *)
  Definition initHistory : History :=
    finfun (fun t => if t == ord0 then Some initGlobal else None).

  Definition emQueue : Queue := emFL _ _.

  Definition emQueues : Queues :=
    finfun (fun _ => emQueue).

  Definition initInTransit : InTransit :=
    finfun (fun t => if t == ord0 then finfun InitMessages else emQueues).

  Definition initWorld : World :=
    MkWorld
      ord0
      initHistory
      initInTransit.
  (* ********* *)

  Definition inc {n} (i : 'I_n) : option 'I_n :=
    match lt_dec i.+1 n with
    | left h => Some ([eta Ordinal (n:=n) (m:=i.+1)] (introT ltP h))
    | right h => None
    end.

  Definition inck {n} (i : 'I_n) (k : nat) : option 'I_n :=
    match lt_dec (k+i) n with
    | left h => Some ([eta Ordinal (n:=n) (m:=k+i)] (introT ltP h))
    | right h => None
    end.

  Definition toI {i n} (h : i < n) : 'I_n :=
    [eta Ordinal (n:=n) (m:=i)] h.

  Definition increment_time (w : World) : option World :=
    option_map
      (fun t =>
         MkWorld
           t
           (world_history w)
           (world_intransit w))
      (inc (world_time w)).

(*  Definition upd_intransit (w : World) (l : maxPoints.-finList [finType of DMsg]) :=
    MkWorld
      (world_global  w)
      (world_history w)
      l.*)

  Definition World_prod w :=
    (world_time w,
     world_history w,
     world_intransit w).

  Definition prod_World prod :=
    let: (world_time,
          world_history,
          world_intransit) := prod in
    MkWorld
      world_time
      world_history
      world_intransit.

  Lemma World_cancel : cancel World_prod prod_World .
  Proof.
      by case.
  Qed.

  Definition World_eqMixin      := CanEqMixin World_cancel.
  Canonical World_eqType        := Eval hnf in EqType (World) World_eqMixin.
  Canonical world_of_eqType     := Eval hnf in [eqType of World].
  Definition World_choiceMixin  := CanChoiceMixin World_cancel.
  Canonical World_choiceType    := Eval hnf in ChoiceType (World) World_choiceMixin.
  Canonical world_of_choiceType := Eval hnf in [choiceType of World].
  Definition World_countMixin   := CanCountMixin World_cancel.
  Canonical World_countType     := Eval hnf in CountType (World) World_countMixin.
  Canonical world_of_countType  := Eval hnf in [countType of World].
  Definition World_finMixin     := CanFinMixin World_cancel.
  Canonical World_finType       := Eval hnf in FinType (World) World_finMixin.
  Canonical world_of_finType    := Eval hnf in [finType of World].


  Fixpoint run_point (t : time) (l : location) (s : state) (q : seq DMsg) : state ## seq DMsg :=
    match q with
    | [] => (s, [])
    | msg :: msgs =>
    let (s1,q1) := Upd t l (dmsg_msg msg) s in
    let (s2,q2) := run_point t l s1 msgs in
    (s2, q1 ++ q2)
    end.

  Definition zip_global
             (t  : time)
             (ps : Global)
             (qs : Queues)
    : {ffun location -> (Point ## Queue)} :=
    finfun
      (fun i =>
         let (s,o) := run_point t i (point_state (ps i)) (qs i) in
         (update_state (ps i) s, seq2queue o)).

  Definition get_msgs_to_in_queue (i : location) (t : Queue) : Queue :=
    seq2queue (filter (fun m => (dmsg_dst m) == i) t).

  Fixpoint get_msgs_to (i : location) (t : seq Queue) : Queue :=
    match t with
    | [] => seq2queue []
    | q :: qs => app_queue (get_msgs_to_in_queue i q) (get_msgs_to i qs)
    end.

  (* the function [f] is organized by senders, while we want it organized by receivers *)
  Definition senders2receivers (f : Queues) : Queues :=
    finfun (fun i => get_msgs_to i (fgraph f)).

  Fixpoint flat_seq_flist {m T} (t : seq (m.-finList T)) : seq T :=
    match t with
    | [] => []
    | x :: xs => x ++ flat_seq_flist xs
    end.

  Definition flatten_queues (qs : Queues) : seq DMsg :=
    flat_seq_flist (fgraph qs).

  Definition run_global
             (t  : time)
             (ps : Global)
             (qs : Queues)
    : Global ## seq DMsg :=
    let f := zip_global t ps qs in
    let points := finfun (fun i => fst (f i)) in
    (* Queues of outgoing messages *)
    let out := flatten_queues (finfun (fun i => snd (f i))) in
    (points,out).

  Definition upd_finfun {A B : finType} (f : {ffun A -> B}) (c : A) (u : B -> B) :=
    finfun (fun a => if a == c then u (f a) else f a).

  (* Adds a message to the queues by adding it to the queue for the recipient of the message *)
  Definition add_to_queues (d : DMsg) (qs : Queues) : Queues :=
    upd_finfun qs (dmsg_dst d) (snoc_queue d).

  (* This is used when messages are produced.
     - Messages can either get lost or be delayed or arrive on time
     - Messages are stored in the in-transit list under the time they should be delivered
     - Messages are stored under the location of the recipient
   *)
  Fixpoint deliver_messages (t : time) (s : seq DMsg) (I : InTransit) : Comp [finType of option InTransit] :=
    match s with
    | [] => Ret (Some I)
    | m :: ms =>
      Bind Lost
           (fun b =>
              if b (* lost *)
              then deliver_messages t ms I
              else (* message is received by t+maxRound *)
                Bind pickRound
                     (fun (r : 'I_(maxRound.+1)) =>
                        (* messages is supposed to be delivered by t+r *)
                        match inck t r with
                        | Some t' => deliver_messages t ms (upd_finfun I t' (add_to_queues m))
                        (* we stop when the time bound is not large enough to deliver a message *)
                        | None => Ret None
                        end))
    end.

  Definition step (w : World) : Comp [finType of option World] :=
    (* current time *)
    let t := world_time w in
    let H := world_history w in
    let I := world_intransit w in
    match H t with
    | Some ps => (* [ps] is the world at the current time [t] *)
      (* we compute the messages that need to be computed at time [t] *)
      let qs := I t in
      (* We now apply the points in [ps] to the queues in [qs].
         We obtain new points and outgoing messages *)
      let (ps',out) := run_global t ps qs in
      match inc t with
      | Some t' =>
        (* we compute the new history *)
        let H' := upd_finfun H t' (fun _ => Some ps') in
        (* we compute the new messages in transit *)
        Bind (deliver_messages t out I)
             (fun o => Ret (option_map (fun I' => MkWorld t' H' I') o))
      | None => Ret None
      end

    (* No world recorded at time [t] *)
    | None => Ret (increment_time w)
    end.

  Fixpoint steps (n : nat) (w : World) : Comp [finType of option World] :=
    match n with
    | 0 => Ret (Some w)
    | S m =>
      Bind (step w)
           (fun o => match o with
                     | Some w' => steps m w'
                     | None => Ret None
                     end)
    end.

  (* [false] if we want the probabilities of faulty executions to not count *)
  Definition steps2dist (n : nat) (F : World -> bool) : fdist [finType of bool] :=
    evalDist (Bind (steps n initWorld)
                   (fun o => match o with
                             | Some w => Ret (F w)
                             | None => Ret false
                             end)).

  (* [true] when proving lower bounds, to set the probability of halted executions to 1 *)
  Definition steps2dist' (n : nat) (F : World -> bool) : fdist [finType of bool] :=
    evalDist (Bind (steps n initWorld)
                   (fun o => match o with
                             | Some w => Ret (F w)
                             | None => Ret true
                             end)).

End World.


(* A simple example with only one initial message (could be a broadcast)
   sent by one node, and all the other nodes, simply relay that message. *)
Section Ex1.

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.

  Definition p_numNodes : nat := 4.

  Inductive p_message :=
  | MsgStart
  | MsgBcast (l : 'I_p_numNodes)
  | MsgEcho  (l : 'I_p_numNodes).

  Definition p_message_nat (s : p_message) : 'I_3 * 'I_p_numNodes :=
    match s with
    | MsgStart => (@Ordinal 3 0 is_true_true, ord0)
    | MsgBcast l => (@Ordinal 3 1 is_true_true, l)
    | MsgEcho  l => (@Ordinal 3 2 is_true_true, l)
    end.

  Definition nat_p_message (n : 'I_3 * 'I_p_numNodes) :=
    let (i,j) := n in
    if nat_of_ord i == 0 then MsgStart else
    if nat_of_ord i == 1 then MsgBcast j
    else MsgEcho j.

  Lemma p_message_cancel : cancel p_message_nat nat_p_message .
  Proof.
      by case.
  Qed.

  Definition p_message_eqMixin      := CanEqMixin p_message_cancel.
  Canonical p_message_eqType        := Eval hnf in EqType (p_message) p_message_eqMixin.
  Canonical p_message_of_eqType     := Eval hnf in [eqType of p_message].
  Definition p_message_choiceMixin  := CanChoiceMixin p_message_cancel.
  Canonical p_message_choiceType    := Eval hnf in ChoiceType (p_message) p_message_choiceMixin.
  Canonical p_message_of_choiceType := Eval hnf in [choiceType of p_message].
  Definition p_message_countMixin   := CanCountMixin p_message_cancel.
  Canonical p_message_countType     := Eval hnf in CountType (p_message) p_message_countMixin.
  Canonical p_message_of_countType  := Eval hnf in [countType of p_message].
  Definition p_message_finMixin     := CanFinMixin p_message_cancel.
  Canonical p_message_finType       := Eval hnf in FinType (p_message) p_message_finMixin.
  Canonical p_message_of_finType    := Eval hnf in [finType of p_message].

  Inductive p_state :=
  (* records the number of received echos *)
  | StateEchos (n : 'I_p_numNodes).

  Definition num_echos (s : p_state) :=
    match s with
    | StateEchos n => n
    end.

  Definition inc_state (s : p_state) : p_state :=
    match inc (num_echos s) with
    | Some m => StateEchos m
    | None => s
    end.

  Definition p_state_nat (s : p_state) : 'I_p_numNodes := num_echos s.

  Definition nat_p_state (n : 'I_p_numNodes) := StateEchos n.

  Lemma p_state_cancel : cancel p_state_nat nat_p_state .
  Proof.
      by case.
  Qed.

  Definition p_state_eqMixin      := CanEqMixin p_state_cancel.
  Canonical p_state_eqType        := Eval hnf in EqType (p_state) p_state_eqMixin.
  Canonical p_state_of_eqType     := Eval hnf in [eqType of p_state].
  Definition p_state_choiceMixin  := CanChoiceMixin p_state_cancel.
  Canonical p_state_choiceType    := Eval hnf in ChoiceType (p_state) p_state_choiceMixin.
  Canonical p_state_of_choiceType := Eval hnf in [choiceType of p_state].
  Definition p_state_countMixin   := CanCountMixin p_state_cancel.
  Canonical p_state_countType     := Eval hnf in CountType (p_state) p_state_countMixin.
  Canonical p_state_of_countType  := Eval hnf in [countType of p_state].
  Definition p_state_finMixin     := CanFinMixin p_state_cancel.
  Canonical p_state_finType       := Eval hnf in FinType (p_state) p_state_finMixin.
  Canonical p_state_of_finType    := Eval hnf in [finType of p_state].

  Global Instance ProcParamsEx1 : ProcParams :=
    MkProcParams
      p_numNodes
      [finType of p_message]
      [finType of p_state].


  (* 0 echos *)
  Definition e0 := @Ordinal p_numNodes 0 is_true_true.
  (* 1 echo *)
  Definition e1 := @Ordinal p_numNodes 1 is_true_true.

  Definition p_InitStates : StateFun :=
    fun l => StateEchos e0.

  Definition loc0  : location := ord0.
  Definition time0 : time := ord0.

  Definition start : DMsg := MkDMsg loc0 loc0 time0 MsgStart.

  Definition p_InitMessages : MsgFun :=
    fun l => seq2queue (if l == loc0 then [start] else []).

  Definition p_Upd : UpdFun :=
    fun t l m s =>
      match m with
      | MsgStart =>
        (* send a bcast to everyone *)
        (s, seq2queue (fgraph (finfun (fun i => MkDMsg l i t (MsgBcast l)))))
      | MsgBcast i =>
        (* send an echo to bcast's sender *)
        (s, seq2queue [MkDMsg l i t (MsgEcho l)])
      | MsgEcho j =>
        (* count echos *)
        (inc_state s, emQueue)
      end.

  Global Instance SMParamsEx1 : SMParams :=
    MkSMParams
      p_InitStates
      p_InitMessages
      p_Upd.

  Definition received_1_echo (w : World) : bool :=
    let t := world_time w in
    match world_history w t with
    | Some g =>
      (* [loc0]'s state (the sender of the broadcast) *)
      let st := point_state (g loc0) in
      num_echos st == e1
    | None => false
    end.

  Lemma ex1 :
    exists (s : nat),
      forall (n : nat),
        (maxTime > n)%nat ->
        (n > s)%nat ->
        ((\sum_(i in 'I_p_numNodes) (1-LostDist) * (1-LostDist))%R
                         < Pr (steps2dist' n received_1_echo) (finset.set1 true))%R.
  Proof.
    exists (2 * (maxRound + 1))%nat; introv gtn ltn.
    destruct n; simpl in *.
    { assert False; tcsp. }

    { unfold steps2dist'; simpl.
      unfold Pr.
      rewrite finset.big_set1; simpl.
      rewrite FDistBindA; simpl.
      unfold step; simpl; unfold initHistory; simpl.
      rewrite ffunE; simpl.


  Abort.

  (* TODO: probability to receive 1 echo by some time *)
  Lemma ex2 :
    forall n,
      Pr (steps2dist'(*?*) n received_1_echo) (finset.set1 true)
      = (\sum_(t in 'I_maxRound.+1) (distRound t) * R1)%R.
  Proof.
  Abort.

(*  Lemma ex1 :
    forall n,
      Reals_ext.pos_ff (FDist.f (prb n received_1_echo)) true = R0.*)

End Ex1.


Section Ex2.

  (* ------------------------------------- *)
  (* Let us now prove properties of Pistis *)

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.
  Context { pSM     : SMParams     }.
  (* Instead of defining a concrete state machine, we assume one,
     and we will add constraints on its behavior *)


  Definition msgObs := message -> bool.

  (* True if a message satisfying [c] is sent at time [t] by node [n] in world [w]
   *)
  Definition disseminate (w : World) (n : location) (t : time) (c : msgObs) : Prop :=
    let H := world_history w in
    let I := world_intransit w in
    match H t with
    | Some ps => (* [ps] is the world at the current time [t] *)
      (* we compute the messages that need to be computed at time [t] *)
      let qs := I t in
      (* We now apply the points in [ps] to the queues in [qs].
         We obtain new points and outgoing messages *)
      let (ps',out) := run_global t ps qs in
      Exists (fun d => dmsg_src d = n /\ c (dmsg_msg d)) out
    | None => False
    end.

  Definition startDisseminate (w : World) (n : location) (t : time) (c : msgObs) : Prop :=
    disseminate w n t c
    /\ forall (u : time), u < t -> ~disseminate w n u c.

  Definition startDisseminateBetween (w : World) (n : location) (t T : time) (c : msgObs) : Prop :=
    exists (u : time),
      t <= u
      /\ u <= t + T
      /\ startDisseminate w n u c.

  Lemma startDisseminate_implies_disseminate :
    forall w n t c,
      startDisseminate w n t c
      -> disseminate w n t c.
  Proof.
    introv diss; destruct diss; auto.
  Qed.
  Hint Resolve startDisseminate_implies_disseminate : pistis.

  (* n disseminates [del] [K] times every [d] starting from [t] *)
  Fixpoint disseminateFor (w : World) (t : time) (n : location) (K d : nat) (c : msgObs) :=
    match K with
    | 0 => disseminate w n t c
    | S k =>
      disseminate w n t c
      /\ match inck t d with
         | Some u => disseminateFor w u n k d c
         | None => True (* if we ran out of time, we just assume that the predicate is true afterwards *)
         end
    end.

  (* [n] receives [c] as time [t] *)
  Definition receiveAt (w : World) (n : location) (t : time) (c : msgObs) : Prop :=
    Exists (fun m => c (dmsg_msg m)) (world_intransit w t n).

  (* [n] receives [c] between [t] and [t+T] *)
  Definition receiveBetween (w : World) (n : location) (t T : time) (c : msgObs) : Prop :=
    exists (u : time),
      t < u
      /\ u <= t + T
      /\ receiveAt w n u c.

  Definition isCorrectAt (w : World) (n : location) (t : time) : bool :=
    let H := world_history w in
    match H t with
    | Some G => isCorrectStatus (point_status (G n))
    (* [G n] is cthe point at space time coordinate [n]/[t] *)
    | None => true
    end.

  Definition isCorrect (w : World) (n : location) : Prop :=
    forall (t : time), isCorrectAt w n t.

  (*Definition isQuorum (l : list location) (Q : nat) :=
    length l = Q
    /\ no_repeats l.*)

  Definition Quorum (F : nat) := [finType of ((2*F)+1).-finList [finType of location]].

  (* [Q] is the size of quorums
     [K] is the number of times nodes disseminate [del] every [d] *)
  Definition IntersectingQuorum (w : World) (F K d : nat) (del : msgObs) :=
    forall (t : time) (n : location),
      isCorrect w n
      -> startDisseminate w n t del
      -> exists (Q : Quorum F) (u : time),
          u <= t + (K * d)
          /\ forall m,
            List.In m Q
            -> isCorrect w m
            -> disseminateFor w u m K d del.

  (* This is a property of the PISTIS's proof-of-connectivity component, where
     nodes become passive (considered faulty), when they don't receive answers
     back from a quorum of nodes, when sending a message.  Therefore, it must
     be that a Quorum received a message sent by a correct node by the time it
     was sent [t] plus [T], where [T] is the time bound by which a message is
     supposed to be received
   *)
  Definition proof_of_connectivity_condition (F : nat) (T : time) :=
    forall (w : World) (n : location) (t : time) (c : msgObs),
      isCorrect w n
      -> startDisseminate w n t c
      -> exists (A : Quorum F),
          forall (m : location),
            List.In m A
            -> receiveBetween w m t T c.

  Definition exStartDisseminateBefore (w : World) (t : time) (c : msgObs) :=
    exists (n : location) (u : time),
      (u < t)%coq_nat
      /\ isCorrect w n
      /\ startDisseminate w n u c
      /\ isCorrect w n.

  Lemma ex_node_start_del_dec :
    forall (w : World) (t : time) (c : msgObs),
      decidable (exStartDisseminateBefore w t c).
  Proof.
  Admitted.

  (* If a correct node receives a deliver it should start delivering
     if it hasn't started already doing so *)
  Definition mustStartDelivering (del : msgObs) :=
    forall (w : World) (n : location) (t : time),
      isCorrect w n
      -> receiveAt w n t del
      -> exists (u : time),
          u <= t
          /\ startDisseminate w n u del.

  (* If a node starts disseminating a message [c] at time [t]
     then it must do so until [t+(K*d)] *)
  Definition startDisseminateUntil (c : msgObs) (K d : nat) :=
    forall (w : World) (n : location) (t : time),
      isCorrect w n
      -> startDisseminate w n t c
      -> disseminateFor w t n K d c.

  (* This is one of main properties required to prove timeliness.
   *)
  Lemma IntersectingQuorum_true (del : msgObs) :
    forall (w : World) (F K d : nat) (p : K*d < maxTime.+1),
      numNodes = (3*F)+1
      -> proof_of_connectivity_condition F (toI(p))
      -> mustStartDelivering del
      (* deliver messages are delivered twice as long as the PoC *)
      -> startDisseminateUntil del (2*K) d
      -> IntersectingQuorum w F K d del.
  Proof.
    introv nnodes poc startD dissU.
    introv.
    destruct t as [t ct].
    revert dependent n.
    induction t as [? ind] using comp_ind; introv cor diss.
    destruct (ex_node_start_del_dec w (toI ct) del) as [z|z].

    { unfold exStartDisseminateBefore in z; exrepnd.
      pose proof (ind u) as ind; simpl in *.
      autodimp ind hyp.
      destruct u as [u cu].
      pose proof (ind cu n0) as ind.
      repeat (autodimp ind hyp; auto).

      exrepnd.
      exists Q u0; dands; auto.
      eapply leq_trans; eauto.
      apply leq_add; auto.
      apply/leP; apply Nat.lt_le_incl; auto. }

    assert (forall (n : location) (u : time),
               (u < t)%coq_nat -> isCorrect w n -> ~startDisseminate w n u del) as z'.
    { introv ltu corn dis; destruct z; exists n0 u; auto. }
    clear z; rename z' into z.

    pose proof (poc w n (toI ct) del) as poc; simpl in *.
    repeat (autodimp poc hyp); eauto 3 with pistis.
    exrepnd.

    (* since no correct nodes start disseminating before [t] it must be that
       all correct nodes in A start disseminating starting from [t]
     *)

    assert (forall (n : location),
               isCorrect w n
               -> List.In n A
               -> startDisseminateBetween w n (toI ct) (toI p) del) as z'.
    { introv isc i.
      pose proof (poc0 _ i) as poc0.
      unfold receiveBetween in poc0; exrepnd.
      pose proof (startD w n0 u) as startD.
      repeat (autodimp startD hyp); exrepnd.
      destruct (lt_dec u0 t) as [ltu|ltu].
      { pose proof (z _ _ ltu isc) as z; tcsp. }
      assert (~(u0 < t)) as ltu' by (intro xx; destruct ltu; apply/ltP; auto).
      assert (t <= u0) as leu by (rewrite leqNgt; apply/negP; auto).
      clear ltu ltu'.
      exists u0.
      dands; auto.
      eapply leq_trans; eauto. }

(*
    exists A (toI ct); dands; simpl; auto; try apply leq_addr.
    introv i isc.

    pose proof (z' _ isc i) as z'.
    pose proof (dissU w m) as dissU.
*)
  Qed.

End Ex2.


(*
  (* combine loose and deliver and use a binary probability *)
  (* Also combine rotate?  Where we rotate randomly? *)
  Inductive Action :=
  (* loose 1st message in transit *)
  | act_loose (*(n : 'I_maxPoints)*)

  (* rotates the in transit messages *)
  | act_rotate

  (* deliver in transit message*)
  | act_deliver.

  Definition step (w : World) (a : Action) : Comp [finType of (option World)] :=
    match a with
    | act_loose => (* loose the first message in transit *)
      let itr := world_intransit w in
      let (op,k) := splitFL _ _ itr in
      let w' := upd_intransit w k in
      Ret (Some w')

    | act_rotate => (* rotates in transit messages *)
      let itr := world_intransit w in
      let k := rotateFL _ _ itr in
      let w' := upd_intransit w k in
      Ret (Some w')

    | act_deliver => (* deliver 1st message in transit *)
      let itr := world_intransit w in
      let (op,k) := splitFL _ _ itr in
      let w' := upd_intransit w k in
      match op with
      | Some m =>
        Bind pickRound
             (fun (n : 'I_(maxRound.+1)) =>
                let dst := dmsg_dst m in
                Ret (Some w'))
      | None => Ret (Some w')
      end
    end.
*)



  (*Definition maxPoints : nat := maxTime * numNodes.*)

(*
  (* Triggers of points *)
  Inductive Trigger :=
  | TriggerMsg (m : message)
  | TriggerArbitrary.

  Definition Trigger_opt (t : Trigger) :=
    match t with
    | TriggerMsg m => Some m
    | TriggerArbitrary => None
    end.

  Definition opt_Trigger o :=
    match o with
    | Some m => TriggerMsg m
    | None => TriggerArbitrary
    end.

  Lemma Trigger_cancel : cancel Trigger_opt opt_Trigger .
  Proof.
      by case.
  Qed.

  Definition Trigger_eqMixin      := CanEqMixin Trigger_cancel.
  Canonical Trigger_eqType        := Eval hnf in EqType (Trigger) Trigger_eqMixin.
  Canonical trigger_of_eqType     := Eval hnf in [eqType of Trigger].
  Definition Trigger_choiceMixin  := CanChoiceMixin Trigger_cancel.
  Canonical Trigger_choiceType    := Eval hnf in ChoiceType (Trigger) Trigger_choiceMixin.
  Canonical trigger_of_choiceType := Eval hnf in [choiceType of Trigger].
  Definition Trigger_countMixin   := CanCountMixin Trigger_cancel.
  Canonical Trigger_countType     := Eval hnf in CountType (Trigger) Trigger_countMixin.
  Canonical trigger_of_countType  := Eval hnf in [countType of Trigger].
  Definition Trigger_finMixin     := CanFinMixin Trigger_cancel.
  Canonical Trigger_finType       := Eval hnf in FinType (Trigger) Trigger_finMixin.
  Canonical trigger_of_finType    := Eval hnf in [finType of Trigger].
*)


(*
  Record TGlobal :=
    MkTGlobal
      {
        (* global time *)
        tglobal_time : 'I_maxTime;

        (* current state of the nodes *)
        tglobal_points : Global;
      }.

  Definition TGlobal_prod (g : TGlobal) :=
    (tglobal_time g,
     tglobal_points g).

  Definition prod_TGlobal prod :=
    let: (tglobal_time,
          tglobal_points) := prod in
    MkTGlobal
      tglobal_time
      tglobal_points.

  Lemma TGlobal_cancel : cancel TGlobal_prod prod_TGlobal .
  Proof.
      by case.
  Qed.

  Definition TGlobal_eqMixin      := CanEqMixin TGlobal_cancel.
  Canonical TGlobal_eqType        := Eval hnf in EqType (TGlobal) TGlobal_eqMixin.
  Canonical tglobal_of_eqType     := Eval hnf in [eqType of TGlobal].
  Definition TGlobal_choiceMixin  := CanChoiceMixin TGlobal_cancel.
  Canonical TGlobal_choiceType    := Eval hnf in ChoiceType (TGlobal) TGlobal_choiceMixin.
  Canonical tglobal_of_choiceType := Eval hnf in [choiceType of TGlobal].
  Definition TGlobal_countMixin   := CanCountMixin TGlobal_cancel.
  Canonical TGlobal_countType     := Eval hnf in CountType (TGlobal) TGlobal_countMixin.
  Canonical tglobal_of_countType  := Eval hnf in [countType of TGlobal].
  Definition TGlobal_finMixin     := CanFinMixin TGlobal_cancel.
  Canonical TGlobal_finType       := Eval hnf in FinType (TGlobal) TGlobal_finMixin.
  Canonical tglobal_of_finType    := Eval hnf in [finType of TGlobal].
*)



(* TODO:

- Allow external messages
- Separate worlds from computations?

*)
