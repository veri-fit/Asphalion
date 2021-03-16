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
      LostProb : prob;

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

      (* To get finite types we can only store a finite number of messages in queues *)
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

  Definition round : finType := [finType of 'I_(maxRound.+1)].

  Definition pickRound : Comp [finType of round] :=
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
    | Lost => Binary.d card_bool LostProb false (* i.e., 1-LostProb if true and LostProb if false *)
    end.

  Definition distRound : fdist [finType of round] := RcvdDist maxRound.

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

  Lemma eq_FinList :
    forall s1 s2 p1 p2,
      s1 = s2
      -> FinList s1 p1 = FinList s2 p2.
  Proof.
    introv h; subst.
    f_equal.
    apply UIP_dec; apply bool_dec.
  Qed.
End finList.

Notation "n .-finList" := (finList_of n)
  (at level 2, format "n .-finList") : type_scope.


Section finList2.
  Definition extendN {T : finType} (e : seq (seq T)) := flatten (codom (fun (x : T) => map (List.cons x) e)).

  Definition seqN (T : finType) (n : nat) : seq (seq T) :=
    iter n extendN [::[::]].

  Definition enumN (T : finType) (n : nat) : seq (finList_of n T) :=
    pmap insub (seqN T n).

  Definition toFL {T n s} (h : length s <= n) : finList_of n T :=
    FinList _ _ s h.

  Lemma seqN_prop :
    forall T n s,
      s \in (seqN T n)
      -> length s = n.
  Proof.
    induction n; introv i; simpl in *.

    { destruct s; simpl in *; auto.
      unfold in_mem in *; simpl in *; inversion i. }

    unfold extendN, codom in i.
    move/flatten_imageP in i.
    destruct i as [t x i j].
    move/mapP in i.
    destruct i as [z w i]; subst; simpl in *.
    f_equal; apply IHn; auto.
  Qed.

  Lemma enumN_prop :
    forall T n s,
      s \in (enumN T n)
      -> length s = n.
  Proof.
    introv i.
    rewrite mem_pmap_sub in i; simpl in *.
    apply seqN_prop in i; auto.
  Qed.

  Definition incFinList {T : finType} {n : nat} (s : finList_of n T) : finList_of (S n) T.
  Proof.
    destruct s as [s c].
    exists s; auto.
  Defined.

  Definition incFinListSeq {T : finType} {n : nat} (s : seq (finList_of n T)) : seq (finList_of (S n) T).
  Proof.
    exact (map incFinList s).
  Defined.

  Fixpoint enumUpToN (T : finType) (n : nat) : seq (finList_of n T) :=
    match n with
    | 0 => enumN T 0
    | S m => enumN T (S m) ++ incFinListSeq (enumUpToN T m)
    end.

  Lemma enumUpToN_prop :
    forall T n s,
      s \in (enumUpToN T n)
      -> length s <= n.
  Proof.
    induction n; introv i; simpl in *.

    { apply enumN_prop in i; rewrite i; auto. }

    rewrite mem_cat in i.
    move/orP in i; destruct i as [i|i].
    { apply enumN_prop in i; rewrite i; auto. }
    move/mapP in i.
    destruct i as [x w i]; subst; simpl in *.
    apply IHn in w.
    destruct x as [x c]; simpl in *; auto.
  Qed.

  Lemma leq_eq_or :
    forall (a b : nat),
      a <= b
      = (a < b) || (a == b).
  Proof.
    induction a; introv; simpl;
      unfold leq in *; simpl; rewrite <- minusE in *; simpl;
        destruct b; simpl; auto.
    rewrite IHa; simpl; auto.
  Qed.

  (* must be proved already *)
  Lemma implies_notin :
    forall (T : eqType) (x : T) (l : seq T),
      ~(x \in l)
       -> (x \notin l).
  Proof.
    introv i; destruct (x \in l); auto.
  Qed.

  Lemma eqFinList_eq :
    forall (T : finType) n (s1 s2 : seq T) i1 i2,
      (FinList n T s1 i1 == FinList n T s2 i2) = (s1 == s2).
  Proof.
    introv; remember (s1 == s2) as b; symmetry in Heqb; destruct b.
    { move/eqP in Heqb; subst; apply/eqP.
      apply eq_FinList; auto. }

    { allrw <- not_true_iff_false; intro xx; destruct Heqb.
      move/eqP in xx; apply/eqP.
      inversion xx; auto. }
  Qed.

  Lemma count_incFinListSeq_enumUptoN_eq :
    forall T n x (c : Datatypes.length x <= n.+1) (d : Datatypes.length x < n.+1),
      count_mem (FinList n.+1 T x c) (incFinListSeq (enumUpToN T n))
      = count_mem (FinList n T x d) (enumUpToN T n).
  Proof.
    introv.
    unfold incFinListSeq.
    rewrite count_map.
    unfold preim,SimplPred; auto.
    apply eq_in_count; introv i; simpl.
    destruct x0 as [s z]; simpl in *.
    repeat rewrite eqFinList_eq; auto.
  Qed.

  Lemma count_mem_smaller :
    forall T n (x : finList_of n.+1 T),
      length x < n.+1
      -> count_mem x (enumN T n.+1) = 0.
  Proof.
    introv i.
    apply/count_memPn.
    apply implies_notin; intro j.
    apply enumN_prop in j; rewrite j in i.
    rewrite ltnn in i; inversion i.
  Qed.

  Lemma count_incFinListSeq_0 :
    forall T n (x : finList_of n.+1 T) (c : Datatypes.length x == n.+1),
      count_mem x (incFinListSeq (enumUpToN T n))
      = 0.
  Proof.
    introv c.
    apply/count_memPn.
    apply implies_notin; intro j.
    unfold incFinListSeq in j.
    move/mapP in j.
    destruct j as [s w i]; subst.
    apply enumUpToN_prop in w.
    unfold incFinList in *; simpl in *.
    destruct s as [s cs]; simpl in *.
    move/eqP in c; rewrite c in w.
    rewrite ltnn in w; inversion w.
  Qed.

  Lemma pmap_flatten :
    forall A B (f : A -> option B) (s : seq (seq A)),
      pmap f (flatten s) = flatten (map (pmap f) s).
  Proof.
    induction s; introv; simpl; auto.
    rewrite pmap_cat; rewrite IHs; auto.
  Qed.

  Lemma count_enumN_as_count_seqN :
    forall T n (x : finList_of T n),
      count_mem x (enumN n T)
      = count (pred1 (fLval _ _ x)) (seqN n T).
  Proof.
    introv.
    unfold enumN.
    repeat rewrite <- size_filter.
    pose proof (seqN_prop n T) as p.
    remember (seqN n T) as l; clear Heql.
    induction l; simpl in *; auto.
    unfold oapp; simpl.
    pose proof (p a) as q; autodimp q hyp; tcsp; try apply mem_head.
    autodimp IHl hyp.
    { introv i; apply p; rewrite in_cons; apply/orP; auto. }
    unfold insub at 1; destruct idP; tcsp;[|rewrite q in n0; destruct n0; auto];[].
    simpl.
    destruct x as [x c]; simpl in *.
    rewrite eqFinList_eq.
    destruct (a == x); simpl; auto.
  Qed.

  Lemma notin_cons :
    forall (T : eqType) t a (l : seq T),
      (t \notin a :: l) = ((t != a) && (t \notin l)).
  Proof.
    introv.
    unfold in_mem; simpl.
    rewrite negb_orb; tcsp.
  Qed.

  Lemma notin_app :
    forall (T : eqType) t (l k : seq T),
      (t \notin l ++ k) = ((t \notin l) && (t \notin k)).
  Proof.
    introv.
    rewrite mem_cat.
    rewrite negb_orb; tcsp.
  Qed.

  Lemma in_uniq_decompose :
    forall (T : eqType) t (l : seq T),
      (t \in l)
      -> uniq l
      -> exists a b, l = a ++ t :: b /\ (t \notin a) /\ (t \notin b).
  Proof.
    induction l; introv i u; simpl in *.
    { inversion i. }
    rewrite in_cons in i.
    move/andP in u; repnd.
    move/orP in i; destruct i as [i|i].

    { move/eqP in i; subst.
      exists ([] : seq T) l; simpl; dands; auto. }

    repeat (autodimp IHl hyp); exrepnd; subst.
    exists (a :: a0) b; simpl; dands; auto.
    rewrite notin_cons.
    rewrite notin_app in u0.
    rewrite notin_cons in u0.
    repeat (move/andP in u0; repnd).
    apply/andP; dands; auto.
    apply/eqP; intro xx; subst.
    move/eqP in u2; tcsp.
  Qed.

  Lemma count_cons_flatten_codom :
    forall (T : finType) (t : T) l K,
      count_mem (t :: l) (flatten (codom (fun z => [seq z :: i | i <- K])))
      = count_mem l K.
  Proof.
    introv.
    rewrite count_flatten.
    rewrite codomE; simpl.
    rewrite <- map_comp.
    unfold ssrfun.comp; simpl.

    rewrite <- deprecated_filter_index_enum.
    pose proof (mem_index_enum t) as i.
    pose proof (index_enum_uniq T) as u.
    apply in_uniq_decompose in i; auto; exrepnd.
    rewrite i0.
    rewrite filter_cat; simpl.
    rewrite map_cat; simpl.
    rewrite sumn_cat; simpl.

    assert (sumn [seq count_mem (t :: l) [seq x :: i | i <- K] | x <- a & T x] = 0) as ha.
    { rewrite map_comp; simpl.
      rewrite <- count_flatten.
      apply/count_memPn.
      apply/negP.
      introv i.
      move/flattenP in i.
      destruct i as [s i z]; simpl in *.
      move/mapP in i.
      destruct i as [w i v]; subst.
      rewrite mem_filter in i; move/andP in i; repnd.
      move/mapP in z.
      destruct z as [s j k]; subst; ginv.
      move/negP in i2; tcsp. }

    assert (sumn [seq count_mem (t :: l) [seq x :: i | i <- K] | x <- b & T x] = 0) as hb.
    { rewrite map_comp; simpl.
      rewrite <- count_flatten.
      apply/count_memPn.
      apply/negP.
      introv i.
      move/flattenP in i.
      destruct i as [s i z]; simpl in *.
      move/mapP in i.
      destruct i as [w i v]; subst.
      rewrite mem_filter in i; move/andP in i; repnd.
      move/mapP in z.
      destruct z as [s j k]; subst; ginv.
      move/negP in i1; tcsp. }

    rewrite ha hb; clear ha hb; simpl; autorewrite with nat.
    rewrite <- plusE; rewrite Nat.add_0_l.

    rewrite count_map; simpl.
    unfold preim; simpl.
    unfold pred1, SimplPred; simpl.
    apply eq_in_count; introv i; simpl.
    rewrite eqseq_cons; simpl.
    apply/andP.
    destruct (x == l); auto.
    intro xx; repnd; inversion xx.
  Qed.

  Lemma count_enumN_1 :
    forall T n (x : finList_of n T),
      length x == n
      -> count_mem x (enumN T n) = 1.
  Proof.
    introv len.
    rewrite count_enumN_as_count_seqN.
    destruct x as [x c]; simpl in *; clear c.
    revert dependent x.
    induction n; introv len; simpl.

    { destruct x; simpl in *; tcsp; inversion len. }

    unfold extendN; simpl.
    destruct x as [|t x]; simpl in *.
    { inversion len. }
    pose proof (IHn x) as IHn; autodimp IHn hyp.
    rewrite count_cons_flatten_codom; auto.
  Qed.

  Lemma enumUpToNFL : forall T n, Finite.axiom (enumUpToN T n).
  Proof.
    induction n; repeat introv; simpl in *.

    { unfold enumN; simpl; unfold oapp, insub; simpl.
      destruct idP; simpl; introv.

      { destruct x as [s c].
        destruct s; simpl in *; auto.
        rewrite ltn0 in c; inversion c. }

      destruct n; auto. }

    unfold enum; simpl.
    rewrite count_cat.
    assert (length x <= n.+1) as len by (destruct x as [x c]; simpl in *; auto).
    rewrite leq_eq_or in len.
    move/orP in len; destruct len as [len|len].

    { rewrite count_mem_smaller; auto.
      unfold Finite.axiom in IHn.
      destruct x as [x c]; simpl in *.
      pose proof (IHn (FinList _ _ x len)) as IHn.
      unfold enum in IHn.
      rewrite count_incFinListSeq_enumUptoN_eq; auto. }

    { rewrite count_incFinListSeq_0; auto; simpl.
      rewrite count_enumN_1; auto. }
  Qed.

  Variables (T : finType) (n : nat).

  Definition enum : seq (finList_of n T) := enumUpToN T n.

  Lemma enumFL : Finite.axiom enum.
  Proof.
    apply enumUpToNFL.
  Qed.

  Definition finList_finMixin  := Eval hnf in FinMixin enumFL.
  Canonical finList_finType    := Eval hnf in FinType (finList_of n T) finList_finMixin.
  Canonical finList_subFinType := Eval hnf in [subFinType of finList_of n T].
  Canonical finList_of_finType := Eval hnf in [finType of finList_of n T].

  Implicit Type l : finList_of n T.

  Definition sizeFL l  := length l.

  Lemma splitFL_cond :
    forall (hd : T) (tl : seq T) (p : length (hd :: tl) <= n),
      length tl <= n.
  Proof.
    auto.
  Qed.

  Definition splitFL l : option T * finList_of n T :=
    match l with
    | FinList [] p => (None, l)
    | FinList (hd :: tl) p => (Some hd, FinList _ _ tl (splitFL_cond hd tl p))
    end.

  Lemma rotateFL_cond :
    forall (hd : T) (tl : seq T) (p : length (hd :: tl) <= n),
      length (snoc tl hd) <= n.
  Proof.
    introv h; simpl in *; rewrite length_snoc; auto.
  Qed.

  Definition rotateFL l : finList_of n T :=
    match l with
    | FinList [] p => l
    | FinList (hd :: tl) p => FinList _ _ (snoc tl hd) (rotateFL_cond hd tl p)
    end.

  Definition emFL : finList_of n T := FinList _ _ [] is_true_true.

End finList2.


Section Msg.

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.
  Context { pProc   : ProcParams   }.

  Definition location : finType := [finType of 'I_numNodes].
  Definition time     : finType := [finType of 'I_maxTime.+1].

  Definition msgObs := message -> bool.

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

  Definition MkCPoint (s : state) := MkPoint s StCorrect.
  Definition MkFPoint (s : state) := MkPoint s StFaulty.

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
  Definition OpInTransit : finType := [finType of option InTransit].


  (* truncates the sequence to maxMsgs *)
  Definition seq2queue (s : seq DMsg) : Queue :=
    FinList
      _ _
      (firstn maxMsgs s)
      ([eta introTF (c:=true) leP] (firstn_le_length maxMsgs s)).

  Definition app_queue (q1 q2 : Queue) : Queue := seq2queue (q1 ++ q2).
  Definition snoc_queue (m : DMsg) (q : Queue) : Queue := seq2queue (snoc q m).

  Lemma fLval_seq2queue :
    forall (s : seq DMsg),
      length s <= maxMsgs
      -> fLval _ _ (seq2queue s) = s.
  Proof.
    introv len; simpl.
    rewrite firstn_all2; auto.
    apply/leP; auto.
  Qed.

  Lemma eq_flattens :
    forall {T} (s1 s2 : seq (seq T)),
      s1 = s2
      -> flatten s1 = flatten s2.
  Proof.
    introv i; subst; auto.
  Qed.

  Lemma eq_maps :
    forall {A B : eqType} (f1 f2 : A -> B) (s1 s2 : seq A),
      s1 = s2
      -> {in s1, f1 =1 f2}
      -> map f1 s1 = map f2 s2.
  Proof.
    introv i j; subst; auto.
    apply eq_in_map; auto.
  Qed.

  Lemma length_as_size :
    forall T (s : seq T),
      Datatypes.length s = size s.
  Proof.
    induction s; simpl; auto.
  Qed.

  Lemma flatten_queue_not_in :
    forall (n : location) (F : location -> list DMsg) (l : list location),
      (n \notin l)
      -> flatten
           [seq (fLval _ _ ([ffun i => seq2queue (if i == n then F i else [])] x))
           | x <- l] = [].
  Proof.
    induction l; introv i; simpl in *; auto.

    rewrite notin_cons in i; move/andP in i; repnd.
    rewrite IHl; auto.
    rewrite ffunE; simpl.
    rewrite eq_sym in i0.
    remember (a == n) as b; symmetry in Heqb; rewrite Heqb; destruct b; try rewrite firstn_nil; auto.
    inversion i0.
  Qed.

  Lemma flatten_single_queue :
    forall (n : location) (F : location -> list DMsg) (l : list location),
      uniq l
      -> (n \in l)
      -> length (F n) <= maxMsgs
      -> flatten
           [seq (fLval _ _ ([ffun i => seq2queue (if i == n then F i else [])] x))
           | x <- l] = F n.
  Proof.
    induction l; introv u i len; simpl in *; auto.

    { rewrite in_nil in i; inversion i. }

    move/andP in u; repnd.

    rewrite ffunE; simpl.
    rewrite in_cons in i; move/orP in i; repndors.

    { rewrite eq_sym in i.
      rewrite i.
      move/eqP in i; subst.
      rewrite firstn_all2; auto;[|apply/leP; auto].
      rewrite flatten_queue_not_in; auto.
      rewrite cats0; auto. }

    repeat (autodimp IHl hyp).
    rewrite IHl.
    remember (a == n) as b; symmetry in Heqb; rewrite Heqb; destruct b; simpl; try rewrite firstn_nil; auto.
    move/eqP in Heqb; subst; tcsp.
    rewrite i in u0; inversion u0.
  Qed.

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
    [ffun l => MkPoint (InitStates l) StCorrect].

  (* Initially only the first world is set *)
  Definition initHistory : History :=
    [ffun t => if t == ord0 then Some initGlobal else None].

  Definition emQueue : Queue := emFL _ _.

  Definition emQueues : Queues :=
    [ffun _ => emQueue].

  Definition initInTransit : InTransit :=
    [ffun t => if t == ord0 then finfun InitMessages else emQueues].

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
    [ffun i =>
     let (s,o) := run_point t i (point_state (ps i)) (qs i) in
     (update_state (ps i) s, seq2queue o)].

  Definition get_msgs_to_in_queue (i : location) (t : Queue) : Queue :=
    seq2queue (filter (fun m => (dmsg_dst m) == i) t).

  Fixpoint get_msgs_to (i : location) (t : seq Queue) : Queue :=
    match t with
    | [] => emQueue
    | q :: qs => app_queue (get_msgs_to_in_queue i q) (get_msgs_to i qs)
    end.

  (* the function [f] is organized by senders, while we want it organized by receivers *)
  Definition senders2receivers (f : Queues) : Queues :=
    [ffun i => get_msgs_to i (codom f)].
  Definition flatten_queues (qs : Queues) : seq DMsg :=
    flatten (map (fLval _ _) (codom qs)).

  Definition run_global
             (t  : time)
             (ps : Global)
             (qs : Queues)
    : Global ## seq DMsg :=
    let f := zip_global t ps qs in
    let points := [ffun i => fst (f i)] in
    (* Queues of outgoing messages *)
    let out := flatten_queues [ffun i => snd (f i)] in
    (points,out).

  Definition upd_finfun {A B : finType} (f : {ffun A -> B}) (c : A) (u : B -> B) :=
    [ffun a => if a == c then u (f a) else f a].

  (* Adds a message to the queues by adding it to the queue for the recipient of the message *)
  Definition add_to_queues (d : DMsg) (qs : Queues) : Queues :=
    upd_finfun qs (dmsg_dst d) (snoc_queue d).

  (* This is used when messages are produced.
     - Messages can either get lost or be delayed or arrive on time
     - Messages are stored in the in-transit list under the time they should be delivered
     - Messages are stored under the location of the recipient
   *)
  Fixpoint deliver_messages (t : time) (s : seq DMsg) (I : InTransit) : Comp [finType of OpInTransit] :=
    match s with
    | [] => Ret (Some I)
    | m :: ms =>
      Bind Lost
           (fun b =>
              if b (* lost *)
              then deliver_messages t ms I
              else (* message is received by t+maxRound *)
                Bind pickRound
                     (fun (r : round) =>
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
        (* we compute the new history -- we set up the new states (for the next time) *)
        let H' := upd_finfun H t' (fun _ => Some ps') in
        (* we compute the new messages in transit *)
        Bind (deliver_messages t' out I)
             (fun o => Ret (option_map (fun I' => MkWorld t' H' I') o))
      | None => Ret None
      end

    (* No world recorded at time [t] *)
    | None => Ret (increment_time w)
    end.

  Definition liftN {A : finType} (f : A -> Comp [finType of option A]) (o : option A) : Comp [finType of option A] :=
    match o with
    | Some w' => f w'
    | None => Ret None
    end.

  Fixpoint iterate {A : finType} (n : nat) (f : A -> Comp [finType of option A]) (a : A) : Comp [finType of option A] :=
    match n with
    | 0 => Ret (Some a)
    | S m => Bind (f a) (liftN (iterate m f))
    end.

  Definition steps (n : nat) (w : World) : Comp [finType of option World] :=
    iterate n step w.

  Definition liftF {A : finType} (f : A -> bool) (o : option A) : Comp [finType of bool] :=
    match o with
    | Some w' => Ret (f w')
    | None => Ret false
    end.

  Definition liftT {A : finType} (f : A -> bool) (o : option A) : Comp [finType of bool] :=
    match o with
    | Some w' => Ret (f w')
    | None => Ret true
    end.

  (* [false] if we want the probabilities of faulty executions to not count *)
  Definition steps2dist (n : nat) (F : World -> bool) : fdist [finType of bool] :=
    evalDist (Bind (steps n initWorld) (liftF F)).

  (* [true] when proving lower bounds, to set the probability of halted executions to 1 *)
  Definition steps2dist' (n : nat) (F : World -> bool) : fdist [finType of bool] :=
    evalDist (Bind (steps n initWorld) (liftT F)).


  (* Here is variant of [steps2dist] where instead of requiring exactly [n] steps, we require at most [n] steps *)
  Definition liftNUpTo {A : finType} (f : A -> Comp [finType of bool]) (g : A -> bool) (o : option A) : Comp [finType of bool] :=
    match o with
    | Some a => if g a then Ret true else f a
    | None => Ret false
    end.

  Fixpoint iterateUpTo {A : finType} (n : nat) (f : A -> Comp [finType of option A]) (g : A -> bool) (a : A) : Comp [finType of bool] :=
    match n with
    | 0 => Ret (g a)
    | S m => Bind (f a) (liftNUpTo (iterateUpTo m f g) g)
    end.

  Definition stepsUpTo (n : nat) (w : World) (F : World -> bool) : Comp [finType of bool] :=
    iterateUpTo n step F w.

  Definition stepsUpTo2dist (n : nat) (F : World -> bool) : fdist [finType of bool] :=
    evalDist (stepsUpTo n initWorld F).


  (* Counting messages in a world *)
  Fixpoint num_msgs_in_queue (o : msgObs) (ms : seq DMsg) : nat :=
    match ms with
    | [] => 0
    | m :: ms =>
      if o (dmsg_msg m) then S (num_msgs_in_queue o ms)
      else num_msgs_in_queue o ms
    end.

  Fixpoint num_msgs_in_queues (o : msgObs) (qs : seq Queue) : nat :=
    match qs with
    | [] => 0
    | q :: qs => num_msgs_in_queue o q + num_msgs_in_queues o qs
    end.

  Fixpoint num_msgs_intransit (o : msgObs) (i : seq Queues) : nat :=
    match i with
    | [] => 0
    | qs :: i => num_msgs_in_queues o (fgraph qs) + num_msgs_intransit o i
    end.

  Definition obs_intransit (n : nat) (o : msgObs) (w : World) : bool :=
    num_msgs_intransit o (fgraph (world_intransit w)) == n.

  Definition num_intransit_at (o : msgObs) (w : World) (t : time) : nat :=
    num_msgs_in_queues o (fgraph (world_intransit w t)).


  (* Non-halted worlds are worlds that are set to [Some] up to the current time *)
  Definition non_halted_world (w : World) :=
    forall t' : time, t' <= world_time w -> isSome (world_history w t').

End World.


(* Properties about probabilities, distributions, and worlds *)
Section Props.

  Context { pProba  : ProbaParams  }.
  Context { pBounds : BoundsParams }.
  Context { pProc   : ProcParams   }.
  Context { pSM     : SMParams     }.

  Lemma eq_fdists :
    forall (A : finType) (a b : fdist A),
      (forall x, pos_ff (FDist.f a) x = pos_ff (FDist.f b) x)
      -> a = b.
  Proof.
    introv h.
    destruct a as [a ha].
    destruct b as [b hb].
    assert (a = b) as z; subst;[|f_equal;apply UIP_dec;apply bool_dec].
    simpl in *.
    destruct a as [a haa].
    destruct b as [b hbb].
    simpl in *.
    assert (a = b) as z; subst;[|f_equal;apply UIP_dec;apply bool_dec].
    apply ffunP; auto.
  Qed.

  (* TODO : prove without using functional extensionality *)
  Lemma FDistBind_d_equal :
    forall (A B : finType) (a b : fdist A) (f g : A -> fdist B),
      a = b
      -> (forall x, f x = g x)
      -> FDistBind.d a f = FDistBind.d b g.
  Proof.
    introv h q; subst.
    apply eq_fdists; introv.
    unfold FDistBind.d.
    repeat rewrite <- lock; simpl.
    unfold FDistBind.f.
    repeat rewrite ffunE; simpl.
    f_equal; simpl.
    apply functional_extensionality; introv.
    rewrite q; auto.
  Qed.

  Lemma FDistBind_d_equal2 :
    forall (A B : finType) (a b : fdist A) (f g : A -> fdist B) x,
      a = b
      -> (forall x, f x = g x)
      -> FDistBind.d a f x = FDistBind.d b g x.
  Proof.
    introv h q; subst.
    erewrite FDistBind_d_equal; eauto.
  Qed.

  Definition notOp {A} (C : A -> bool) (wop : option A) : bool :=
    match wop with
    | Some w => ~~(C w)
    | None => false
    end.

  (* This can be used to propagate properties to earlier states:
     if [C] is an invariant that implies [~~F], then we might as well assume [~~C] on the current state
   *)
  Lemma addConstraint :
    forall {A : finType} (F C : A -> bool) (G : A -> Comp [finType of option A]) (n : nat) (aop : option A),
      (forall a, C a -> ~~(F a))
      -> (forall a, C a -> forall b, evalDist (G a) (Some b) <> 0%R -> C b)
      -> FDistBind.d
           (evalDist (liftN (iterate n G) aop))
           (fun b : option A => evalDist (liftF F b))
           true
         = if notOp C aop
           then
             FDistBind.d
               (evalDist (liftN (iterate n G) aop))
               (fun b : option A => evalDist (liftF F b)) true
           else R0.
  Proof.
    introv cond1 cond2.
    destruct aop; simpl;[|rewrite FDistBind1f; rewrite FDist1.dE; simpl; auto];[].
    remember (C s) as b; symmetry in Heqb; destruct b; simpl; auto;[].

    revert s Heqb.

    induction n; introv cond3; simpl.

    { rewrite FDistBind1f; simpl; auto.
      apply cond1 in cond3.
      remember (F s) as b; destruct b; tcsp; inversion cond3.
      rewrite FDist1.dE; simpl; auto. }

    rewrite FDistBindA; simpl.
    rewrite FDistBind.dE; simpl.
    pose proof (cond2 _ cond3) as cond2.
    apply prsumr_eq0P; simpl; introv i.

    { apply ssrR.mulR_ge0.
      { remember (evalDist (G s)) as d; symmetry in Heqd; rewrite Heqd; clear Heqd.
        destruct d as [d ca].
        destruct d as [d cb].
        simpl in *.
        move/forallP in cb.
        pose proof (cb a) as cb; auto.
        move/ssrR.leRP in cb; auto. }

      { remember (FDistBind.d (evalDist (liftN (iterate n G) a)) (fun b : option A => evalDist (liftF F b))) as d.
        symmetry in Heqd; rewrite Heqd; clear Heqd.
        destruct d as [d ca].
        destruct d as [d cb].
        simpl in *.
        move/forallP in cb.
        pose proof (cb true) as cb; auto.
        move/ssrR.leRP in cb; auto. } }

    destruct a; simpl.

    { destruct (Req_dec (evalDist (G s) (Some s0)) 0%R) as [eqd|eqd].

      { rewrite eqd; rewrite Rmult_0_l; auto. }

      apply Rmult_eq_0_compat; right.
      apply IHn.
      apply cond2; auto. }

    rewrite FDistBind1f; simpl.
    rewrite FDist1.dE; simpl.
    rewrite Rmult_0_r; auto.
  Qed.

  Lemma FDistBind_bin :
    forall (B : finType) (g : bool -> fdist B) (x : B) (p : prob),
      FDistBind.d (Binary.d card_bool p false) g x
      = ((p * g true x) + ((1-p) * g false x))%R.
  Proof.
    introv.
    rewrite FDistBind.dE; simpl.
    rewrite BigOp.bigopE; simpl.
    unfold in_mem; simpl.
    unfold index_enum; simpl.
    rewrite Finite.EnumDef.enumDef; simpl.
    repeat rewrite Binary.dE; simpl.
    rewrite Rplus_0_r; auto.
  Qed.

  Lemma evalDist_match_inck :
    forall {n} {A : finType} (i : 'I_n) (k : nat) (F : 'I_n -> Comp A) G a,
      evalDist
        match inck i k with
        | Some j => F j
        | None => G
        end a
      = match inck i k with
        | Some j => evalDist (F j) a
        | None => evalDist G a
        end.
  Proof.
    introv.
    destruct (inck i k); auto.
  Qed.

  Lemma R_plus_eq_compat :
    forall r1 r2 r3 r4 : R,
      r1 = r2 -> r3 = r4 -> (r1 + r3)%R = (r2 + r4)%R.
  Proof.
    introv a b; subst; auto.
  Qed.

  Lemma R_mult_eq_compat :
    forall r1 r2 r3 r4 : R,
      r1 = r2 -> r3 = r4 -> (r1 * r3)%R = (r2 * r4)%R.
  Proof.
    introv a b; subst; auto.
  Qed.

  Lemma eq_match_inck :
    forall {n} {A} (i : 'I_n) (k : nat) (F G : 'I_n -> A) H K,
      (forall j, F j = G j)
      -> H = K
      -> match inck i k with
         | Some j => F j
         | None => H
         end
         = match inck i k with
           | Some j => G j
           | None => K
           end.
  Proof.
    introv h q; subst.
    destruct (inck i k); auto.
  Qed.

  Lemma Rle_trans_eq_r :
    forall (r r1 r2 : R),
      (r1 = r2)%R
      -> (r <= r2)%R
      -> (r <= r1)%R.
  Proof.
    introv h q; subst; auto.
  Qed.

  Lemma Rlt_trans_eq_r :
    forall (r r1 r2 : R),
      (r1 = r2)%R
      -> (r < r2)%R
      -> (r < r1)%R.
  Proof.
    introv h q; subst; auto.
  Qed.

  Lemma one1_m_prob_pos :
    forall (p : prob), (0%R <= 1 - p)%R.
  Proof.
    introv.
    apply ssrR.subR_ge0; auto.
    apply prob_le1.
  Qed.
  Hint Resolve one1_m_prob_pos : prob.

  Lemma ex_inck_is_some :
    forall (t : time) (i : round),
      (t + maxRound.+1) < maxTime.+1
      -> {j : time & inck t i = Some j}.
  Proof.
    introv ltm.
    unfold inck.
    remember (lt_dec (i + t) maxTime.+1) as b; symmetry in Heqb; destruct b; simpl in *.
    { eexists; eauto. }
    destruct n.
    eapply lt_trans;[|apply/ltP;eauto].
    rewrite <- plusE.
    rewrite Nat.add_comm.
    apply plus_lt_compat_l; auto.
    destruct i; simpl in *.
    apply/ltP; auto.
  Defined.

  Lemma inck_is_some :
    forall {t : time} {i : round} (p : t + maxRound.+1 < maxTime.+1),
      inck t i = Some (projT1 (ex_inck_is_some t i p)).
  Proof.
    introv.
    remember (ex_inck_is_some t i p) as b; symmetry in Heqb; exrepnd; simpl in *; auto.
  Qed.

  Lemma sum_distrr I (a : R) (a0 : (0 <= a)%R) r (P : pred I) F :
    ((a * \sum_(i <- r | P i) F i)%R = \sum_(i <- r | P i) (a * F i)%R)%R.
  Proof.
    elim: r => [| h t IH].
      by rewrite 2!big_nil ssrR.mulR0.
      rewrite 2!big_cons.
      case: ifP => Qh //.
        by rewrite -IH Rmult_plus_distr_l.
  Qed.

  Lemma Rmult_INR_subst :
    forall {A : eqType} (a b : A) (F : A -> R),
      (INR (a == b) * F a)%R = (INR (a == b) * F b)%R.
  Proof.
    introv.
    remember (a == b) as w; symmetry in Heqw; destruct w; simpl.
    { move/eqP in Heqw; subst; auto. }
    repeat rewrite Rmult_0_l; auto.
  Qed.

  Lemma swap_sums :
    forall {A B : finType} (F : A -> B -> R),
      (\sum_(a in A) \sum_(b in B) F a b
       = \sum_(b in B) \sum_(a in A) F a b)%R.
  Proof.
    introv.
    rewrite BigOp.bigopE; simpl.
    unfold reducebig, ssrfun.comp, applybig; simpl.
    remember (index_enum B) as lb.
    remember (index_enum A) as la.
    clear Heqla Heqlb.
    revert lb.
    induction la; introv; simpl.

    { induction lb; simpl; auto.
      rewrite <- IHlb; simpl; auto.
      rewrite Rplus_0_r; auto. }

    induction lb; simpl.

    { rewrite Rplus_0_l; auto.
      clear IHla.
      induction la; simpl; auto.
      rewrite IHla; simpl; auto.
      rewrite Rplus_0_r; auto. }

    repeat rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    rewrite <- IHlb; clear IHlb.
    rewrite <- Rplus_assoc.
    rewrite (Rplus_comm (foldr (fun x : A => [eta Rplus (F x a0)]) R0 la)).
    rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    pose proof (IHla (a0 :: lb)) as IHla'; simpl in *.
    rewrite IHla'.
    apply Rplus_eq_compat_l; auto.
  Qed.

  Lemma foldr_of_sum_not_in_0 :
    forall {A : finType} (a : A) F l,
      (a \notin l)
      -> (foldr (fun x => [eta Rplus (INR (x == a) * F x)]) R0 l)%R = 0%R.
  Proof.
    induction l; introv i; simpl in *; auto.
    rewrite notin_cons in i.
    move/andP in i; repnd.
    rewrite IHl; auto.
    remember (a0 == a) as b; symmetry in Heqb; destruct b; simpl; auto.
    { move/eqP in Heqb; subst; move/negP in i0; destruct i0; auto. }
    rewrite Rmult_0_l.
    rewrite Rplus_0_l; auto.
  Qed.

  Lemma sum_Rmult_INR_subst :
    forall {A : finType} (b : A) (F : A -> R),
      (\sum_(a in A) INR (a == b) * F a)%R = F b.
  Proof.
    introv.
    rewrite BigOp.bigopE; simpl.
    unfold reducebig, ssrfun.comp, applybig; simpl.
    pose proof (index_enum_uniq A) as u.
    pose proof (mem_index_enum b) as i.
    remember (index_enum A) as l; clear Heql.

    induction l; simpl in *.
    { inversion i. }

    move/andP in u; repnd.
    rewrite in_cons in i; move/orP in i; repndors.

    { move/eqP in i; subst.
      rewrite foldr_of_sum_not_in_0; auto.
      rewrite Rplus_0_r; auto.
      remember (a == a) as b; symmetry in Heqb; destruct b; simpl; auto.
      { rewrite Rmult_1_l; auto. }
      move/eqP in Heqb; tcsp. }

    remember (a == b) as x; symmetry in Heqx; destruct x; simpl; auto.
    { move/eqP in Heqx; subst.
      move/negP in u0; tcsp. }
    rewrite Rmult_0_l; auto.
    rewrite IHl; auto.
    rewrite Rplus_0_l; auto.
  Qed.

  Lemma sum_option :
    forall (T : finType) (F : option T -> R),
      ((\sum_(a in [finType of option T]) (F a))
       = F None + (\sum_(a in T) (F (Some a))))%R.
  Proof.
    introv.
    rewrite BigOp.bigopE; simpl.
    unfold reducebig, ssrfun.comp, applybig; simpl.
    unfold index_enum; simpl.
    repeat (rewrite Finite.EnumDef.enumDef; simpl).
    rewrite foldr_map; auto.
  Qed.

  (* An alternative definition of [deliver_messages] and [step]
     that threads the computation in [deliver_messages] instead
     of calling [Bind] *)
  Fixpoint deliver_messages'
           (t : time)
           {T : finType}
           (F : option InTransit -> Comp T)
           (s : seq DMsg)
           (I : InTransit) : Comp T :=
    match s with
    | [] => F (Some I)
    | m :: ms =>
      Bind Lost
           (fun b =>
              if b (* lost *)
              then deliver_messages' t F ms I
              else (* message is received by t+maxRound *)
                Bind pickRound
                     (fun (r : round) =>
                        (* messages is supposed to be delivered by t+r *)
                        match inck t r with
                        | Some t' => deliver_messages' t F ms (upd_finfun I t' (add_to_queues m))
                        (* we stop when the time bound is not large enough to deliver a message *)
                        | None => F None
                        end))
    end.

  Definition step' (w : World) : Comp [finType of option World] :=
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
        (* we compute the new history -- we set up the new states (for the next time) *)
        let H' := upd_finfun H t' (fun _ => Some ps') in
        (* we compute the new messages in transit *)
        deliver_messages' t' (fun o => Ret (option_map (fun i => MkWorld t' H' i) o)) out I
      | None => Ret None
      end

    (* No world recorded at time [t] *)
    | None => Ret (increment_time w)
    end.

  Lemma step_as_step' :
    forall w,
      evalDist (step w)
      = evalDist (step' w).
  Proof.
    introv.
    apply eq_fdists; introv.
    unfold step, step'.
    destruct w as [t H I]; simpl.
    remember (H t) as h; symmetry in Heqh; rewrite Heqh; simpl in *.
    destruct h; simpl; auto;[].
    remember (inc t) as i; symmetry in Heqi; destruct i; simpl in *; auto.
    remember (flatten_queues [ffun i => (zip_global t f (I t) i).2]) as l; symmetry in Heql.
    rewrite Heql; clear Heql.

    match goal with
    | [ |- context[upd_finfun ?a ?b ?c] ] => remember c as k; clear Heqk
    end.
    revert x I.
    induction l; introv; simpl; auto.

    { rewrite FDistBind1f; auto. }

    rewrite FDistBindA.
    apply FDistBind_d_equal2; auto;[].
    introv.
    destruct x0; simpl in *; auto.

    { apply eq_fdists; introv; auto. }

    rewrite FDistBindA; simpl.
    apply FDistBind_d_equal; auto;[].
    introv.
    destruct (inck o x0); simpl in *; auto;[|rewrite FDistBind1f; auto].
    apply eq_fdists; introv; auto.
  Qed.

  Lemma bind_eval_dist_deliver_messages'_eq :
    forall (t : time)
           {T : finType}
           (F : InTransit -> T)
           (s : seq DMsg)
           (I : InTransit)
           {U : finType}
           (G : option T -> Comp [finType of option U]),
      FDistBind.d
        (evalDist (deliver_messages' t (fun o => Ret (option_map F o)) s I))
        (fun o => evalDist (G o))
      = evalDist (deliver_messages' t (fun o => G (option_map F o)) s I).
  Proof.
    introv.
    apply eq_fdists; introv.
    revert x I.
    induction s; introv; simpl; auto.
    { rewrite FDistBind1f; auto. }
    rewrite FDistBindA.
    apply FDistBind_d_equal2; auto;[].
    introv.
    destruct x0; simpl; auto.
    { apply eq_fdists; introv; auto. }
    rewrite FDistBindA; auto.
    apply FDistBind_d_equal; auto;[].
    introv; simpl in *.
    destruct (inck t x0); simpl in *; auto;[|rewrite FDistBind1f; auto];[].
    apply eq_fdists; introv; auto.
  Qed.

  Lemma bind_eval_dist_deliver_messages'_eq2 :
    forall (t : time)
           {T : finType}
           (F : option InTransit -> Comp T)
           (s : seq DMsg)
           (I : InTransit)
           {U : finType}
           (G : T -> Comp U),
      FDistBind.d
        (evalDist (deliver_messages' t F s I))
        (fun o => evalDist (G o))
      = evalDist (deliver_messages' t (fun i => Bind (F i) G) s I).
  Proof.
    introv.
    apply eq_fdists; introv.
    revert x I.
    induction s; introv; simpl; auto;[].
    rewrite FDistBindA.
    apply FDistBind_d_equal2; auto;[].
    introv.
    destruct x0; simpl; auto.
    { apply eq_fdists; introv; auto. }
    rewrite FDistBindA; auto.
    apply FDistBind_d_equal; auto;[].
    introv; simpl in *.
    destruct (inck t x0); simpl in *; auto.
    apply eq_fdists; introv; auto.
  Qed.

End Props.


Hint Resolve one1_m_prob_pos : prob.
Hint Resolve FDist.ge0 : prob.


(* A simple example with only one initial message (could be a broadcast)
   sent by one node, and all the other nodes, simply relay that message. *)
Section Ex1.

  Context { pProba    : ProbaParams  }.
  Context { pMaxRound : nat }.
  Context { pMaxTime  : nat }.

  Definition pMaxMsgs := 2.

  Global Instance BoundsParamsEx1 : BoundsParams :=
    MkBoundsParams
      pMaxRound
      pMaxTime
      pMaxMsgs.

  Definition p_numNodes : nat := 2.

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
  | StateEchos (n : 'I_p_numNodes.+1).

  Definition num_echos (s : p_state) : 'I_p_numNodes.+1 :=
    match s with
    | StateEchos n => n
    end.

  Definition inc_state (s : p_state) : p_state :=
    match inc (num_echos s) with
    | Some m => StateEchos m
    | None => s
    end.

  Definition p_state_nat (s : p_state) : 'I_p_numNodes.+1 := num_echos s.

  Definition nat_p_state (n : 'I_p_numNodes.+1) := StateEchos n.

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


  Definition isStart : msgObs :=
    fun m : message =>
      match m with
      | MsgStart => true
      | _ => false
      end.

  Definition isBcast : msgObs :=
    fun m : message =>
      match m with
      | MsgBcast _ => true
      | _ => false
      end.

  Definition isEcho : msgObs :=
    fun m : message =>
      match m with
      | MsgEcho _ => true
      | _ => false
      end.


  (* 0 echos *)
  Definition e0 := @Ordinal p_numNodes.+1 0 is_true_true.
  (* 1 echo *)
  Definition e1 := @Ordinal p_numNodes.+1 1 is_true_true.
  (* 2 echo *)
  Definition e2 := @Ordinal p_numNodes.+1 2 is_true_true.

  Definition p_InitStates : StateFun :=
    fun l => StateEchos e0.

  Definition loc0  : location := @Ordinal p_numNodes 0 is_true_true.
  Definition loc1  : location := @Ordinal p_numNodes 1 is_true_true.

  Definition time0  : time := ord0.
  Definition round0 : round := ord0.

  Definition timen {n} (p : (n < maxTime.+1)%coq_nat) : time := Ordinal (n:=maxTime.+1) (m:=n) (introT ltP p).

  Definition start : DMsg := MkDMsg loc0 loc0 time0 MsgStart.

  Definition p_InitMessages : MsgFun :=
    fun l => seq2queue (if l == loc0 then [start] else []).

  Definition p_Upd : UpdFun :=
    fun t l m s =>
      match m with
      | MsgStart =>
        (* send a bcast to everyone *)
        (s, seq2queue (codom [ffun i => MkDMsg l i t (MsgBcast l)]))
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

  Lemma compute_initial_messages :
    flatten_queues [ffun i => (zip_global ord0 initGlobal (initInTransit ord0) i).2]
    = codom [ffun i => MkDMsg loc0 i ord0 (MsgBcast loc0)].
  Proof.
    unfold flatten_queues.
    unfold initInTransit.
    unfold zip_global; simpl.
    unfold p_InitMessages; simpl.
    rewrite ffunE; simpl.

    assert ([ffun i => ([ffun i0 =>
                         let (s, o) :=
                             run_point
                               ord0 i0 (point_state (initGlobal i0))
                               ([ffun l => seq2queue (if l == loc0 then [:: start] else [])] i0) in
                         (update_state (initGlobal i0) s, seq2queue o)] i).2]
            = [ffun i => seq2queue (if i == loc0 then codom [ffun x => MkDMsg loc0 x ord0 (MsgBcast loc0)] else [])]) as h.
    { apply eq_ffun; introv; simpl.
      repeat (rewrite ffunE; simpl).
      rewrite (surjective_pairing (run_point ord0 x (p_InitStates x) (seq2queue (if x == loc0 then [:: start] else [])))); simpl.
      remember (x == loc0) as b; symmetry in Heqb; destruct b;[|apply eq_FinList; auto].
      move/eqP in Heqb; subst.
      Opaque firstn.
      simpl; rewrite firstn_all2; simpl; try rewrite cats0; auto.
      Transparent firstn.
      rewrite length_as_size.
      rewrite size_codom; simpl; auto.
      rewrite card_ord; auto. }

    rewrite h; clear h; simpl.
    simpl.
    repeat rewrite codomE.
    repeat rewrite <- map_comp.
    unfold ssrfun.comp; simpl.
    repeat rewrite codomE.
    simpl.
    rewrite flatten_single_queue; auto.

    { apply enum_uniq. }

    { apply/mapP; simpl.
      exists loc0; auto.
      apply mem_index_enum. }

    rewrite length_as_size.
    rewrite size_map; simpl.
    rewrite size_enum_ord; auto.
  Qed.

  (* We provide a lower bound so that we can manually discard probabilities that we know will end up begin 0 *)
  Lemma evalDist_deliver_initial_messages :
    forall (t : time)
           (ct : t + maxRound.+1 < maxTime.+1)
           (F : location -> DMsg) (I : InTransit) (a : OpInTransit),
      (((1-LostProb)^2 *
        \sum_(i in round)
         \sum_(j in round)
         RcvdDist maxRound i *
        RcvdDist maxRound j *
        INR
          (a ==
           Some
             (upd_finfun
                (upd_finfun I (projT1 (ex_inck_is_some t i ct)) (add_to_queues (F loc0)))
                (projT1 (ex_inck_is_some t j ct))
                (add_to_queues (F loc1)))))%R
       <= evalDist (deliver_messages t (codom [ffun i => F i]) I) a)%R.
  Proof.
    introv.
    assert (codom [ffun i => F i] = [F loc0, F loc1]) as h.
    { unfold codom; simpl; auto.
      unfold image_mem; simpl.
      rewrite ssr_ext.enum_inord; simpl.
      repeat rewrite ffunE; simpl; auto.
      repeat f_equal; unfold inord, insubd, insub; simpl; destruct idP; simpl; auto; tcsp;
        try (complete (destruct n; auto));
        unfold loc0, loc1;
        f_equal; apply UIP_dec; apply bool_dec. }

    rewrite h; clear h.
    simpl.
    repeat (rewrite FDistBind_bin; simpl).
    repeat (rewrite FDist1.dE; simpl).
    repeat (rewrite FDistBind.dE; simpl).

    eapply Rle_trans_eq_r.
    { apply R_plus_eq_compat.
      { apply R_mult_eq_compat;[reflexivity|].
        apply R_plus_eq_compat;[reflexivity|].
        apply R_mult_eq_compat;[reflexivity|].
        apply eq_bigr; introv j.
        rewrite (inck_is_some ct); simpl.
        apply R_mult_eq_compat;[reflexivity|].
        rewrite FDist1.dE; simpl; reflexivity. }
      apply R_mult_eq_compat;[reflexivity|].
      apply eq_bigr; introv j.
      apply R_mult_eq_compat;[reflexivity|].
      rewrite (inck_is_some ct); simpl.
      rewrite FDistBind_bin; simpl.
      rewrite FDist1.dE; simpl.
      apply R_plus_eq_compat;[reflexivity|].
      apply R_mult_eq_compat;[reflexivity|].
      rewrite FDistBind.dE; simpl.
      apply eq_bigr; introv k.
      apply R_mult_eq_compat;[reflexivity|].
      rewrite (inck_is_some ct); simpl.
      rewrite FDist1.dE; simpl; reflexivity. }

    simpl.
    rewrite Rmult_1_r.

    match goal with
    | [ |- (?x <= _)%R] => rewrite <- (Rplus_0_l x)
    end.
    apply Rplus_le_compat.

    { repeat (first [apply ssrR.mulR_ge0; auto
                    |apply one1_m_prob_pos; auto
                    |apply ssrR.addR_ge0; auto
                    |apply ssrR.leR0n]).
      apply rsumr_ge0; introv j.
      apply ssrR.mulR_ge0; auto.
      { apply FDist.ge0. }
      apply ssrR.leR0n. }

    rewrite Rmult_assoc.
    apply Rmult_le_compat_l;[apply one1_m_prob_pos; auto|].
    rewrite sum_distrr; eauto 3 with prob.

    apply ler_rsum; introv j.
    rewrite Rmult_plus_distr_l.

    match goal with
    | [ |- (?x <= _)%R] => rewrite <- (Rplus_0_l x)
    end.
    apply Rplus_le_compat.

    { repeat (first [apply ssrR.mulR_ge0; auto
                    |apply one1_m_prob_pos; auto
                    |apply ssrR.addR_ge0; auto
                    |apply ssrR.leR0n]).
      apply FDist.ge0. }

    repeat (rewrite sum_distrr; eauto 3 with prob; try apply FDist.ge0).
    apply ler_rsum; introv k.
    rewrite <- Rmult_assoc.
    rewrite <- Rmult_assoc.
    rewrite (Rmult_comm (1-LostProb)).
    repeat (rewrite Rmult_assoc).
    apply Rle_refl.
  Qed.

  (* TODO: we could easily generalize this to multiple updates for later rounds *)
  Lemma empty_queue_in_two_upd :
    forall (ia ib : round)
           (p1 : (1 < maxTime.+1)%coq_nat)
           (ct : 1 + pMaxRound.+1 < pMaxTime.+1)
           (r  : nat)
           (c0 : 0 < r)
           (cr : r <= ia <= ib \/ r <= ib <= ia)
           (pr1 : (r < maxTime.+1)%coq_nat),
      upd_finfun
        (upd_finfun initInTransit (projT1 (ex_inck_is_some (timen p1) ia ct))
                    (add_to_queues (MkDMsg loc0 loc0 ord0 (MsgBcast loc0))))
        (projT1 (ex_inck_is_some (timen p1) ib ct))
        (add_to_queues (MkDMsg loc0 loc1 ord0 (MsgBcast loc0)))
        (timen pr1)
      = emQueues.
  Proof.
    introv lr0 lr; introv.
    unfold upd_finfun.
    repeat (rewrite ffunE; simpl).

    remember (ex_inck_is_some (timen p1) ia ct) as k; exrepnd; simpl in *; clear Heqk.
    unfold inck in *; simpl in *.
    remember (lt_dec (ia + 1) pMaxTime.+1) as z; destruct z; simpl in *; clear Heqz; ginv; simpl in *.
    remember (timen pr1 == Ordinal (n:=pMaxTime.+1) (m:=ia + 1) (introT ltP l)) as k; symmetry in Heqk.
    destruct k; simpl in *.

    { move/eqP in Heqk.
      inversion Heqk; subst; tcsp.
      rewrite addn1 in lr.
      repndors; move/andP in lr; repnd.
      { move/ltP in lr1; apply Nat.lt_irrefl in lr1; tcsp. }
      assert (ia < ia) as xx by (move/ltP in lr1; move/leP in lr; apply/ltP; eapply lt_le_trans; eauto).
      move/ltP in xx; apply Nat.lt_irrefl in xx; tcsp. }
    clear Heqk.

    remember (ex_inck_is_some (timen p1) ib ct) as k; exrepnd; simpl in *; clear Heqk.
    unfold inck in *; simpl in *.
    remember (lt_dec (ib + 1) pMaxTime.+1) as z; destruct z; simpl in *; clear Heqz; ginv; simpl in *.
    remember (timen pr1 == Ordinal (n:=pMaxTime.+1) (m:=ib + 1) (introT ltP l0)) as k; symmetry in Heqk.
    destruct k; simpl in *.

    { move/eqP in Heqk.
      inversion Heqk; subst; tcsp.
      assert (ib + 1 <= ib) as xx.
      { repndors;move/andP in lr; repnd; auto.
        eapply leq_trans; eauto. }
      rewrite addn1 in xx.
      move/ltP in xx; apply Nat.lt_irrefl in xx; tcsp. }
    clear Heqk.

    remember (timen pr1 == ord0) as b; symmetry in Heqb; rewrite Heqb; destruct b; simpl; auto.
    move/eqP in Heqb; simpl in *.
    inversion Heqb; subst.
    inversion lr0.
  Qed.

  Lemma flatten_queues_zip_global_emqQueues :
    forall (t : time),
      flatten_queues [ffun i => (zip_global t initGlobal emQueues i).2] = [].
  Proof.
    introv; unfold flatten_queues; simpl.
    unfold zip_global, emQueues; simpl.
    eapply transitivity.
    { apply eq_flattens.
      apply eq_maps;[|introv i; reflexivity].
      apply eq_codom; introv.
      repeat (rewrite ffunE; simpl); reflexivity. }

    unfold codom; simpl.
    unfold image_mem; simpl.
    rewrite <- map_comp.
    unfold ssrfun.comp; simpl.

    remember (fintype.enum 'I_p_numNodes) as l; symmetry in Heql; rewrite Heql; clear Heql.
    induction l; simpl; auto.
  Qed.

  (* As they are no messages in transit between [1] and [ia], we can advance there.
     We just have to fill in the states.
   *)
  Lemma advance_state1 :
    forall (F : option World -> fdist [finType of bool])
           (n : nat)
           (ia ib : round)
           (p1 : (1 < maxTime.+1)%coq_nat)
           (ct : 1 + pMaxRound.+1 < pMaxTime.+1)
           (r  : nat)
           (cr : r <= ia <= ib \/ r <= ib <= ia)
           (cn : r <= n)
           (pr : (r.+1 < maxTime.+1)%coq_nat),
      (FDistBind.d
         (evalDist
            (steps n
                   (MkWorld
                      (timen p1)
                      [ffun t => if (nat_of_ord t <= 1)%nat then Some initGlobal else None]
                      (upd_finfun
                         (upd_finfun initInTransit (projT1 (ex_inck_is_some (timen p1) ia ct))
                                     (add_to_queues (MkDMsg loc0 loc0 ord0 (MsgBcast loc0))))
                         (projT1 (ex_inck_is_some (timen p1) ib ct))
                         (add_to_queues (MkDMsg loc0 loc1 ord0 (MsgBcast loc0)))))))
         F
         true
       = FDistBind.d
           (evalDist
              (steps (n-r)
                     (MkWorld
                        (timen pr)
                        [ffun t => if (nat_of_ord t <= r.+1)%nat then Some initGlobal else None]
                        (upd_finfun
                           (upd_finfun initInTransit (projT1 (ex_inck_is_some (timen p1) ia ct))
                                       (add_to_queues (MkDMsg loc0 loc0 ord0 (MsgBcast loc0))))
                           (projT1 (ex_inck_is_some (timen p1) ib ct))
                           (add_to_queues (MkDMsg loc0 loc1 ord0 (MsgBcast loc0)))))))
           F
           true)%R.
  Proof.
    induction r; introv cr cn; introv; simpl in *.

    { rewrite <- minusE.
      rewrite minus0.
      assert (p1 = pr) as xx by apply lt_irrelevance; subst; auto. }

    repeat (autodimp IHr hyp).

    { repndors; [left|right]; move/andP in cr; apply/andP; repnd; dands; auto. }

    assert (r.+1 < pMaxTime.+1)%coq_nat as pr1.
    { eapply lt_trans;[|eauto].
      apply Nat.lt_succ_diag_r. }
    pose proof (IHr pr1) as IHr.
    rewrite IHr; clear IHr.

    assert (n - r = (n - r.+1).+1) as xx.
    { rewrite subnS.
      rewrite Nat.succ_pred_pos; auto.
      apply lt_minus_O_lt; apply/ltP; auto. }
    rewrite xx; clear xx.
    simpl.
    rewrite FDistBindA; simpl.

    unfold step at 1; simpl; unfold initHistory; simpl.
    rewrite ffunE; simpl.

    remember (r < r.+1) as b; symmetry in Heqb; destruct b;
      [|move/negP in Heqb; destruct Heqb; auto];[].

    unfold inc; simpl.
    destruct (lt_dec r.+2 (pMaxTime.+1)); simpl;[|destruct n0; auto;apply/ltP; auto];[].
    rewrite empty_queue_in_two_upd; auto;[].
    rewrite flatten_queues_zip_global_emqQueues; simpl.
    rewrite FDistBind1f; simpl.
    rewrite FDistBind1f; simpl.

    assert (pr = l) as xx by apply lt_irrelevance; subst; auto.

    assert (upd_finfun [ffun t => if nat_of_ord t <= r.+1 then Some initGlobal else None]
                       (Ordinal (n:=pMaxTime.+1) (m:=r.+2) (introT ltP l))
                       (fun=> Some [ffun i => (zip_global (timen pr1) initGlobal emQueues i).1])
            = [ffun t => if nat_of_ord t <= r.+2 then Some initGlobal else None]) as xx;[|rewrite xx;auto];[].
    unfold upd_finfun.
    apply eq_ffun; introv; simpl in *.
    repeat (rewrite ffunE; simpl).

    remember (x == Ordinal (n:=pMaxTime.+1) (m:=r.+2) (introT ltP l)) as k; symmetry in Heqk; rewrite Heqk.
    destruct k; auto.

    { move/eqP in Heqk; subst; simpl in *.
      remember (r.+1 < r.+2) as k; symmetry in Heqk; destruct k.

      { f_equal.
        unfold initGlobal.
        apply eq_ffun; introv; simpl in *.
        unfold zip_global, emQueues; simpl.
        repeat (rewrite ffunE; simpl); auto. }

      move/ltP in Heqk; destruct Heqk.
      apply Nat.lt_succ_diag_r. }

    move/eqP in Heqk.
    destruct x as [x cx]; simpl in *.

    remember (x <= r.+1) as z; symmetry in Heqz; destruct z.

    { move/leP in Heqz.
      remember (x <= r.+2) as w; symmetry in Heqw; destruct w; auto.
      move/leP in Heqw; destruct Heqw; auto. }

    move/leP in Heqz.
    remember (x <= r.+2) as w; symmetry in Heqw; destruct w; auto.
    move/leP in Heqw.
    apply Nat.le_succ_r in Heqw; destruct Heqw; tcsp; subst.
    destruct Heqk; f_equal; apply UIP_dec; apply bool_dec.
  Qed.

  Lemma advance_state2 :
    forall (F : option World -> fdist [finType of bool])
           (n : nat)
           (ia ib : round)
           (p1 : (1 < maxTime.+1)%coq_nat)
           (ct : 1 + pMaxRound.+1 < pMaxTime.+1)
           (la : ia <= n)
           (pr : ((min ia ib).+1 < maxTime.+1)%coq_nat),
      (FDistBind.d
         (evalDist
            (steps n
                   (MkWorld
                      (timen p1)
                      [ffun t => if (nat_of_ord t <= 1)%nat then Some initGlobal else None]
                      (upd_finfun
                         (upd_finfun initInTransit (projT1 (ex_inck_is_some (timen p1) ia ct))
                                     (add_to_queues (MkDMsg loc0 loc0 ord0 (MsgBcast loc0))))
                         (projT1 (ex_inck_is_some (timen p1) ib ct))
                         (add_to_queues (MkDMsg loc0 loc1 ord0 (MsgBcast loc0)))))))
         F
         true
       = FDistBind.d
           (evalDist
              (steps (n-(min ia ib))
                     (MkWorld
                        (timen pr)
                        [ffun t => if (nat_of_ord t <= (min ia ib).+1)%nat then Some initGlobal else None]
                        (upd_finfun
                           (upd_finfun initInTransit (projT1 (ex_inck_is_some (timen p1) ia ct))
                                       (add_to_queues (MkDMsg loc0 loc0 ord0 (MsgBcast loc0))))
                           (projT1 (ex_inck_is_some (timen p1) ib ct))
                           (add_to_queues (MkDMsg loc0 loc1 ord0 (MsgBcast loc0)))))))
           F
           true)%R.
  Proof.
    introv la; introv; simpl in *.
    apply advance_state1.
    { destruct (le_dec ia ib) as [u|u].
      { left; apply/andP; dands; auto;[|apply/leP;auto].
        apply/leP; apply Min.le_min_l. }
      apply Nat.nle_gt in u; move/ltP in u.
      right; apply/andP; dands; auto;[].
      apply/leP; apply Min.le_min_r. }
    apply/leP; apply Nat.min_le_iff; left.
    apply/leP; auto.
  Qed.

  Lemma bound_lt_cond1 :
    forall (i : 'I_pMaxRound.+1) {n},
      2 * (pMaxRound + 1) < n.+1
      -> i < n.
  Proof.
    introv ltn.
    destruct i; simpl in *.
    move/ltP in ltn; apply lt_n_Sm_le in ltn.
    apply/ltP; eapply lt_le_trans;[|eauto].
    eapply lt_le_trans;[|apply le_n_2n].
    rewrite addn1; apply/ltP; auto.
  Qed.

  Lemma bound_lt_cond2 :
    forall (i : 'I_pMaxRound.+1) {n},
      2 * (pMaxRound + 1) < n.+1
      -> i <= n.
  Proof.
    introv ltn.
    apply ltnW; auto.
    apply bound_lt_cond1; auto.
  Qed.

  Lemma bound_lt_cond3 :
    forall (i : 'I_pMaxRound.+1) i0 {n},
      2 * (pMaxRound + 1) < n.+1
      -> n.+1 < pMaxTime
      -> ((Init.Nat.min i i0).+1 < maxTime.+1)%coq_nat.
  Proof.
    introv ltn gtn.
    apply lt_n_S.
    eapply le_lt_trans;[apply Nat.le_min_l|].
    pose proof (bound_lt_cond1 i ltn) as u.
    move/ltP in u; eapply lt_trans;[exact u|].
    move/ltP in gtn; eapply lt_trans;[|exact gtn]; auto.
  Qed.


  Definition two_bcasts_intransit (w : World) : bool :=
    obs_intransit 2 isBcast w.

  Lemma in_firstn_implies :
    forall n {A : eqType} a (l : seq A),
      (a \in firstn n l)
      -> (a \in l).
  Proof.
    induction n; introv i; simpl in *.
    { inversion i. }
    destruct l; simpl in *.
    { inversion i. }
    rewrite in_cons;apply/orP.
    rewrite in_cons in i;move/orP in i; repndors; tcsp.
  Qed.

  Lemma time2fin (t : 'I_pMaxTime.+1) : Finite.sort time.
  Proof.
    exact t.
  Defined.

  Lemma loc2fin (i : 'I_numNodes) : Finite.sort location.
  Proof.
    exact i.
  Defined.

  Lemma advance_state3 :
    forall (n  : nat)
           (w  : World)
           (cn : (world_time w)+n < maxTime),
      (* All worlds are set to [Some] up to the current time *)
      non_halted_world w
      (* no [Start] message scheduled in the future *)
      -> (forall t' : time, world_time w <= t' -> obs_intransit 0 isStart w)
      (* if some [Bcast] messages are scheduled then they should before [n-maxRound] so that there is time to [Echo] *)
      -> (forall t' : time, 0 < num_intransit_at isBcast w t' -> t' < n-maxRound)
      (* if some [Echo] messages are scheduled then they should before [n] so that there is time to process them *)
      -> (forall t' : time, 0 < num_intransit_at isBcast w t' -> t' < n)
      (* two [BCast] messages scheduled in total *)
      -> obs_intransit 2 isBcast w
      -> (FDistBind.d
            (evalDist (steps n w))
            (fun b => evalDist (liftF (obs_intransit 2 isBcast) b))
            true
          = R1)%R.
  Proof.
    induction n; introv cn condH condS condB condE condO; simpl.

    { rewrite FDistBind1f; simpl.
      rewrite FDist1.dE; simpl.
      rewrite condO; auto. }

    rewrite step_as_step'.
    unfold step' at 1; simpl.
    destruct w as [t H I]; simpl.

    remember (H t) as h; symmetry in Heqh; rewrite Heqh; simpl in *.
    pose proof (condH t) as condx; simpl in *.
    autodimp condx hyp.
    rewrite Heqh in condx; simpl in *.
    destruct h; simpl in *; tcsp;[|inversion condx];[]; clear condx.

    unfold inc at 1; simpl in *.
    destruct (lt_dec t.+1 pMaxTime.+1) as [d|d];
      [|destruct d; rewrite <- addSnnS in cn; move/ltP in cn;
        eapply le_lt_trans;[apply/leP;apply (leq_addr n)|];
        eapply lt_trans;[eauto|]; apply Nat.lt_succ_diag_r];[].
    simpl.

    rewrite bind_eval_dist_deliver_messages'_eq; simpl.
    rewrite bind_eval_dist_deliver_messages'_eq2; simpl.

    remember (flatten_queues [ffun i => (zip_global (time2fin t) f (I t) i).2]) as L.
    symmetry in HeqL; unfold time2fin in *; simpl in *.
    rewrite HeqL.
    assert (forall m, (m \in L) -> isBcast (dmsg_msg m) \/ isEcho (dmsg_msg m)) as condM.
    { introv i; subst.
      move/flatten_mapP in i.
      destruct i as [l i j]; simpl in *.
      move/codomP in i; exrepnd; subst; simpl in *.
      rewrite ffunE in j; simpl in *.
      unfold zip_global in j; simpl in j.
      rewrite ffunE in j; simpl in *.
      remember (I t x) as k; clear Heqk; simpl in *.

      rewrite (@surjective_pairing state (seq DMsg) (run_point (time2fin t) (loc2fin x) (point_state (f x)) k)) in j.
      Opaque firstn.
      simpl in j; unfold time2fin, loc2fin in j; simpl in *.
      destruct k as [k kc]; simpl in *; clear kc.
      apply in_firstn_implies in j.
      remember (point_state (f x)) as s; clear Heqs; revert dependent s.

      induction k; introv j; simpl in *;[inversion j|].
      unfold p_Upd in j; destruct a as [a b u z]; simpl in *.
      destruct z; simpl in *.

      { rewrite (@surjective_pairing state (seq DMsg) (run_point (time2fin t) (loc2fin x) s k)) in j.
        simpl in j; rewrite mem_cat in j;move/orP in j; repndors.
        { apply in_firstn_implies in j.
          move/codomP in j; exrepnd; subst; simpl in *.
          rewrite ffunE; simpl;tcsp. }
        unfold time2fin, loc2fin in *; simpl in *; eapply IHk; eauto. }

      { rewrite (@surjective_pairing state (seq DMsg) (run_point (time2fin t) (loc2fin x) s k)) in j.
        simpl in j; rewrite mem_cat in j;move/orP in j; repndors.
        { apply in_firstn_implies in j.
          rewrite in_cons in j; move/orP in j; repndors;[|inversion j].
          move/eqP in j; subst; simpl in *; tcsp. }
        unfold time2fin, loc2fin in *; simpl in *; eapply IHk; eauto. }

      { rewrite (@surjective_pairing state (seq DMsg) (run_point (time2fin t) (loc2fin x) (inc_state s) k)) in j.
        simpl in j; eapply IHk; eauto. } }
    clear HeqL.

    induction L; simpl in *.

    { apply IHn; simpl; auto.
      admit.
      admit.
      admit.
      admit.
      admit. }

    rewrite FDistBind_bin.
    SearchAbout FDistBind.d Binary.d.

    XXXXXXXXXX

      rewrite FDistBind.dE; simpl.
    rewrite sum_option; simpl.
    repeat (rewrite FDistBind1f; simpl).
    rewrite FDist1.dE; simpl.
    rewrite Rmult_0_r; rewrite Rplus_0_l.

    eapply transitivity.
    { apply eq_bigr; introv u.
      apply R_mult_eq_compat;[reflexivity|].
      rewrite FDistBind1f; simpl.
      reflexivity. }
    simpl.



  (* Write another version of [step], where the computation on in-transit messages
   is done within deliver messages *)


  Qed.

  (* TODO: We shouldn't need the bounds [lbound] and [n] since [steps2dist'] returns true when time runs out*)
  (* We provide a lower bound so that we can manually discard probabilities that we know will end up begin 0 *)
  Lemma ex1 :
    (* [lbound] is the number of steps that we allow ourselves *)
    exists (lbound : nat),
      (* The property below holds for all all bounds between [lbound] and [maxTime] *)
      forall (n : nat),
        (maxTime > n)%nat ->
        (n > lbound)%nat ->
        ((\sum_(i in 'I_p_numNodes) (1-LostProb)^2)%R (* TODO: update, it will be slightly more complicated than this to take delays into consideration *)
                         < Pr (steps2dist n two_bcasts_intransit) (finset.set1 true))%R.
  Proof.
    exists (2 * (maxRound + 1))%nat; introv gtn ltn.
    unfold Pr.
    rewrite finset.big_set1; simpl.
    unfold steps2dist; simpl.

    destruct n; simpl in *.
    { assert False; tcsp. }

    rewrite FDistBindA; simpl.

    unfold step at 1; simpl; unfold initHistory; simpl.
    rewrite ffunE; simpl.

    unfold inc; simpl.
    assert (0 < maxTime) as mg0 by (eapply ltn_trans;[|eauto]; auto).
    destruct (lt_dec 1 (pMaxTime.+1)); simpl;[|destruct n0; auto;apply/ltP; auto];[].

    rewrite compute_initial_messages.
    rewrite FDistBindA; simpl.

    match goal with
    | [ |- (_ < ?z)%R] =>
      assert (z = FDistBind.d
     (evalDist
        (deliver_messages (timen l)
           (codom [ffun i => MkDMsg loc0 i ord0 (MsgBcast loc0)])
           initInTransit))
     (fun x : OpInTransit =>
        let x0 := option_map
                    [eta MkWorld (Ordinal (n:=pMaxTime.+1) (m:=1) (introT ltP l))
                         (upd_finfun [ffun t => if t == ord0 then Some initGlobal else None]
                                     (Ordinal (n:=pMaxTime.+1) (m:=1) (introT ltP l))
                                     (fun=> Some [ffun i => (zip_global ord0 initGlobal (initInTransit ord0) i).1]))] x
        in FDistBind.d (evalDist (liftN (steps n) x0))
                       (fun b : option World => evalDist (liftF two_bcasts_intransit b))) true) as w
    end;[|rewrite w; clear w].
    { apply FDistBind_d_equal2; auto; introv; simpl.
      rewrite FDistBind1f; auto. }
    simpl.

    assert (timen l + pMaxRound.+1 < pMaxTime.+1) as ct.
    { apply/ltP; apply lt_n_S.
      eapply lt_trans; apply/ltP;[|exact gtn].
      apply/ltP; eapply le_lt_trans;[|apply/ltP;exact ltn].
      rewrite addn1; apply le_n_2n. }

    rewrite FDistBind.dE; simpl.
    eapply Rlt_le_trans.
    2:{ pose proof (@ler_rsum OpInTransit) as w; apply w; clear w; introv j.
        apply Rmult_le_compat_r; eauto 3 with prob.
        apply (evalDist_deliver_initial_messages _ ct). }
    simpl.
    repeat rewrite Rmult_1_r.

    eapply Rlt_trans_eq_r.
    { apply eq_bigr; introv k.
      repeat (rewrite Rmult_assoc); reflexivity. }
    repeat (rewrite <- sum_distrr; eauto 2 with prob;[]).

    eapply Rlt_trans_eq_r.
    { apply R_mult_eq_compat;[reflexivity|].
      apply R_mult_eq_compat;[reflexivity|].
      apply eq_bigr; introv k.
      rewrite Rmult_comm.
      eapply transitivity;[apply sum_distrr|]; eauto 2 with prob; simpl;[].
      apply eq_bigr; introv j.
      eapply transitivity;[apply sum_distrr|]; eauto 2 with prob; simpl;[].
      apply eq_bigr; introv u.
      rewrite Rmult_comm.
      rewrite Rmult_assoc.
      reflexivity. }
    simpl.

    eapply Rlt_trans_eq_r.
    { apply R_mult_eq_compat;[reflexivity|].
      apply R_mult_eq_compat;[reflexivity|].
      rewrite swap_sums.
      apply eq_bigr; introv j.
      rewrite swap_sums.
      apply eq_bigr; introv k.
      rewrite <- sum_distrr;[|apply ssrR.mulR_ge0;apply FDist.ge0].
      reflexivity. }
    simpl.

    eapply Rlt_trans_eq_r.
    { apply R_mult_eq_compat;[reflexivity|].
      apply R_mult_eq_compat;[reflexivity|].
      apply eq_bigr; introv j.
      apply eq_bigr; introv k.
      apply R_mult_eq_compat;[reflexivity|].
      apply sum_Rmult_INR_subst. }
    simpl.

    assert ([ffun i1 => (zip_global ord0 initGlobal (initInTransit ord0) i1).1] = initGlobal) as eqs.
    { apply eq_ffun; introv; simpl.
      unfold zip_global; simpl.
      unfold initInTransit; simpl.
      repeat (rewrite ffunE; simpl).
      remember (x == loc0) as b; symmetry in Heqb; destruct b; simpl in *; auto. }
    rewrite eqs; clear eqs.

    assert (upd_finfun [ffun t => if t == ord0 then Some initGlobal else None]
                       (Ordinal (n:=pMaxTime.+1) (m:=1) (introT ltP l))
                       (fun=> Some initGlobal)
            = [ffun t => if nat_of_ord t <= 1 then Some initGlobal else None]) as eqs.
    { apply eq_ffun; introv; simpl.
      remember (x == timen l) as b; symmetry in Heqb; rewrite Heqb.
      destruct b; simpl in *; move/eqP in Heqb; subst; simpl in *; auto;[].
      repeat (rewrite ffunE; simpl).
      remember (x == ord0) as c; symmetry in Heqc; try rewrite Heqc.
      destruct c; simpl in *; move/eqP in Heqc; subst; simpl in *; auto;[].
      remember (x <= 1) as d; symmetry in Heqd; try rewrite Heqd.
      destruct d; simpl in *; auto.
      move/leP in Heqd; auto.
      destruct x as [x xc]; simpl in *.
      destruct x; simpl in *.
      { destruct Heqc.
        unfold ord0.
        assert (xc = ltn0Sn pMaxTime) as xx by (apply UIP_dec; apply bool_dec); subst; auto. }
      destruct x; simpl in *;[|move/leP in Heqd; inversion Heqd].
      destruct Heqb.
      unfold timen.
      assert (xc = introT ltP l) as xx by (apply UIP_dec; apply bool_dec); subst; auto. }
    rewrite eqs; clear eqs.

    eapply Rlt_trans_eq_r.
    { apply R_mult_eq_compat;[reflexivity|].
      apply R_mult_eq_compat;[reflexivity|].
      apply eq_bigr; introv j.
      apply eq_bigr; introv k.
      apply R_mult_eq_compat;[reflexivity|].
      pose proof (advance_state2 (fun b => evalDist (liftF two_bcasts_intransit b)) n i i0 l ct (bound_lt_cond2 i ltn) (bound_lt_cond3 i i0 ltn gtn)) as w.
      rewrite w; clear w.
      reflexivity. }
    simpl.




(* We're now ready to handle one of the messages in-transit or both (if they're delivered at the same time) *)


XXXXXXXXXXXX

  Abort.


  Definition received_2_echos (w : World) : bool :=
    let t := world_time w in
    match world_history w t with
    | Some g =>
      (* [loc0]'s state (the sender of the broadcast) *)
      let st := point_state (g loc0) in
      num_echos st == e2
    | None => false
    end.

  (* makes use of [ex1] *)
  Lemma ex2 :
    (* [lbound] is the number of steps that we allow ourselves *)
    exists (lbound : nat),
      (* The property below holds for all all bounds between [lbound] and [maxTime] *)
      forall (n : nat),
        (maxTime > n)%nat ->
        (n > lbound)%nat ->
        ((\sum_(i in 'I_p_numNodes) (1-LostProb)^2)%R (* TODO: update, it will be slightly more complicated than this to take delays into consideration *)
                         < Pr (steps2dist n received_2_echos) (finset.set1 true))%R.
  Proof.
  Abort.


  (* TODO: probability to receive 1 echo by some time *)
  Lemma ex3 :
    forall n,
      Pr (steps2dist'(*?*) n received_2_echos) (finset.set1 true)
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


  (* True if a message satisfying [c] is sent at time [t] by node [n] in world [w]
   *)
  Definition disseminate (w : World) (n : location) (t : time) (c : msgObs) : bool :=
    let H := world_history w in
    let I := world_intransit w in
    match H t with
    | Some ps => (* [ps] is the world at the current time [t] *)
      (* we compute the messages that need to be computed at time [t] *)
      let qs := I t in
      (* We now apply the points in [ps] to the queues in [qs].
         We obtain new points and outgoing messages *)
      let (ps',out) := run_global t ps qs in
      existsb (fun d => (dmsg_src d == n) && c (dmsg_msg d)) out
    | None => false
    end.

  Definition startDisseminate (w : World) (n : location) (t : time) (c : msgObs) : Prop :=
    disseminate w n t c
    /\ forall (u : time), u < t -> ~disseminate w n u c.

  Definition startDisseminateDec (w : World) (n : location) (t : time) (c : msgObs) : bool :=
    disseminate w n t c
    && [forall (u : time | u < t), ~~disseminate w n u c].

  Lemma startDisseminateP :
    forall w n t c,
      reflect (startDisseminate w n t c) (startDisseminateDec w n t c).
  Proof.
    introv.
    remember (startDisseminateDec w n t c); symmetry in Heqb; destruct b;[left|right].

    { unfold startDisseminateDec, startDisseminate in *.
      move/andP in Heqb; repnd; dands; auto.
      move/forallP in Heqb; simpl in *.
      introv i.
      pose proof (Heqb u) as Heqb.
      move/implyP in Heqb.
      apply Heqb in i.
      apply/negP; auto. }

    unfold startDisseminateDec, startDisseminate in *.
    move/negP in Heqb.
    intro xx; destruct Heqb; apply/andP; repnd; dands;auto.
    apply/forallP.
    introv; apply/implyP; introv i; apply xx in i.
    apply/negP; auto.
  Qed.

  Definition startDisseminateBetween (w : World) (n : location) (t T : time) (c : msgObs) : Prop :=
    exists (u : time),
      t <= u
      /\ u < t + T
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
      && match inck t d with
         | Some u => disseminateFor w u n k d c
         | None => true (* if we ran out of time, we just assume that the predicate is true afterwards *)
         end
    end.

  (* [n] receives [c] as time [t] *)
  Definition receiveAt (w : World) (n : location) (t : time) (c : msgObs) : Prop :=
    Exists (fun m => c (dmsg_msg m)) (world_intransit w t n).

  (* [n] receives [c] between [t] and [t+T] *)
  Definition receiveBetween (w : World) (n : location) (t T : time) (c : msgObs) : Prop :=
    exists (u : time),
      t < u
      /\ u < t + T
      /\ receiveAt w n u c.

  Definition isCorrectAt (w : World) (n : location) (t : time) : bool :=
    let H := world_history w in
    match H t with
    | Some G => isCorrectStatus (point_status (G n))
    (* [G n] is cthe point at space time coordinate [n]/[t] *)
    | None => true
    end.

  Definition isCorrect (w : World) (n : location) : bool :=
    [forall t, isCorrectAt w n t].

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
            -> exists (v : time),
                u <= v
                /\ v < u + d
                /\ disseminateFor w v m K d del.

  (* This is a property of the PISTIS's proof-of-connectivity component, where
     nodes become passive (considered faulty), when they don't receive answers
     back from a quorum of nodes, when sending a message.  Therefore, it must
     be that a Quorum received a message sent by a correct node by the time it
     was sent [t] plus [T], where [T] is the time bound by which a message is
     supposed to be received
   *)
  Definition proof_of_connectivity_condition (w : World) (F : nat) (T : time) :=
    forall (n : location) (t : time) (c : msgObs),
      isCorrect w n
      -> startDisseminate w n t c
      -> exists (A : Quorum F),
          forall (m : location),
            List.In m A
            -> receiveBetween w m t T c.

  Definition exStartDisseminateBefore (w : World) (t : time) (c : msgObs) : Prop :=
    exists (n : location) (u : time),
      (u < t)%coq_nat
      /\ isCorrect w n
      /\ startDisseminate w n u c.

  Definition exStartDisseminateBeforeDec (w : World) (t : time) (c : msgObs) : bool :=
    [exists n : location, exists u : time,
          (u < t)
          && isCorrect w n
          && startDisseminateDec w n u c].

  Lemma ex_node_start_del_dec :
    forall (w : World) (t : time) (c : msgObs),
      decidable (exStartDisseminateBefore w t c).
  Proof.
    introv.
    apply (@decP _ (exStartDisseminateBeforeDec w t c)).
    remember (exStartDisseminateBeforeDec w t c); symmetry in Heqb.
    destruct b;[left|right].

    { unfold exStartDisseminateBeforeDec, exStartDisseminateBefore in *.
      move/existsP in Heqb; simpl in *; exrepnd.
      exists x.
      move/existsP in Heqb0; simpl in *; exrepnd.
      exists x0.
      move/andP in Heqb1; repnd.
      move/andP in Heqb0; repnd.
      dands; auto.
      { apply/ltP; auto. }
      apply/startDisseminateP; auto. }

    unfold exStartDisseminateBeforeDec, exStartDisseminateBefore in *.
    move/existsP in Heqb.
    intro xx; destruct Heqb; simpl in *; exrepnd.
    exists n.
    apply/existsP; exists u.
    apply/andP; dands; auto.
    { apply/andP; dands; auto.
      apply/ltP; auto. }
    apply/startDisseminateP; auto.
  Qed.

  (* If a correct node receives a deliver it should start delivering
     if it hasn't started already doing so *)
  Definition mustStartDelivering (w : World) (del : msgObs) :=
    forall (n : location) (t : time),
      isCorrect w n
      -> receiveAt w n t del
      -> exists (u : time),
          u <= t
          /\ startDisseminate w n u del.

  (* If a node starts disseminating a message [c] at time [t]
     then it must do so until [t+(K*d)] *)
  Definition startDisseminateUntil (w : World) (c : msgObs) (K d : nat) :=
    forall (n : location) (t : time),
      isCorrect w n
      -> startDisseminate w n t c
      -> disseminateFor w t n K d c.

  (* For simplicity, we assume long enough worlds, where there is still some time
     (namely [T]), after a node starts disseminating
*)
  Definition longEnoughWorld (w : World) (c : msgObs) (T : nat) :=
    forall n t,
      startDisseminate w n t c
      -> t + T <= maxTime.

  Lemma existsNextStep :
    forall (t u : time) (K d : nat),
      d <> 0
      -> t <= u
      -> u < t + (K*d)
      -> exists (J : nat),
          t + (J*d) <= u
          /\ u < t + ((J+1)*d)
          /\ J + 1 <= K.
  Proof.
    introv dd0 h q.
    destruct t as [t ct].
    destruct u as [u cu].
    simpl in *.
    clear ct cu.
    assert (K <> 0) as kd0.
    { destruct K; simpl in *; auto.
      rewrite <- multE in q; simpl in *.
      rewrite <- plusE in q; simpl in *.
      rewrite Nat.add_0_r in q; auto.
      assert (t < t) as z by (eapply leq_ltn_trans; eauto).
      rewrite ltnn in z; tcsp. }

    exists ((u - t)/d); dands.
    { pose proof (Nat.mul_div_le (u - t) d dd0) as p.
      eapply (@leq_trans (t + (u - t)));[|rewrite subnKC; auto].
      rewrite leq_add2l.
      apply/leP; auto.
      rewrite Nat.mul_comm in p; auto. }
    { pose proof (Nat.mul_succ_div_gt (u-t) d dd0) as z; simpl in *.
      eapply (@leq_ltn_trans (t + (u - t)));[rewrite subnKC; auto|].
      rewrite ltn_add2l.
      apply/ltP; auto.
      rewrite Nat.mul_comm in z; auto.
      rewrite addn1; auto. }

    apply (@ltn_sub2r t) in q; auto.

    { rewrite <- addnBAC in q; auto.
      assert (t - t = 0) as w by (apply/eqP; rewrite subn_eq0; auto).
      rewrite w in q; clear w; simpl in q.
      rewrite <- plusE in q.
      rewrite Nat.add_0_l in q.
      rewrite <- multE in q.
      rewrite Nat.mul_comm in q.
      assert (u - t < (d * K)%coq_nat)%coq_nat as z by (apply/ltP; auto).
      apply Nat.div_lt_upper_bound in z; auto; clear q.
      rewrite addn1; apply/leP; auto. }

    remember (t + K *d); rewrite (plus_n_O t); subst.
    rewrite ltn_add2l; auto.
    destruct K, d; auto.
  Qed.

  Lemma eq_nat_of_ord_implies :
    forall (u v : time),
      nat_of_ord u = nat_of_ord v
      -> u = v.
  Proof.
    introv h.
    destruct u, v; simpl in *; subst; auto.
    assert (i = i0) by (apply UIP_dec; apply bool_dec); subst; auto.
  Qed.

  Lemma disseminateForLess :
    forall (w : World) (n : location) (K J d : nat) (u : time) (c : msgObs),
      J <= K
      -> disseminateFor w u n K d c
      -> disseminateFor w u n J d c.
  Proof.
    induction K; introv h diss.
    { assert (J = 0) as j0.
      { destruct J; auto.
        rewrite ltn0 in h; inversion h. }
      subst; simpl in *; auto. }

    simpl in *; move/andP in diss; repnd.
    destruct J; simpl in *; auto; apply/andP; dands; auto.
    remember (inck u d) as iu; destruct iu; symmetry in Heqiu; auto.
  Qed.

  Lemma disseminateForCovered :
    forall (w : World) (n : location) (K : nat) (u v : time) (c : msgObs) (I J d : nat),
      nat_of_ord v = (nat_of_ord u)+(I*d)
      -> I + J <= K
      -> disseminateFor w u n K d c
      -> disseminateFor w v n J d c.
  Proof.
    induction K; introv h q diss.
    { assert (I = 0) as i0.
      { destruct I; auto.
        rewrite <- plusE in q; simpl in q.
        rewrite ltn0 in q; inversion q. }
      assert (J = 0) as j0.
      { destruct J; auto.
        rewrite <- plusE, Nat.add_comm in q; simpl in q.
        rewrite ltn0 in q; inversion q. }
      subst; simpl in *.
      rewrite <- multE, <- plusE in h; simpl in h.
      rewrite Nat.add_0_r in h; subst.
      apply eq_nat_of_ord_implies in h; subst; auto. }

    destruct I.

    { rewrite <- plusE in q; simpl in q.
      rewrite <- plusE, <- multE in h; simpl in h.
      rewrite Nat.add_0_r in h; subst.
      apply eq_nat_of_ord_implies in h; subst; auto.
      eapply disseminateForLess; eauto. }

    simpl in *; move/andP in diss; repnd.
    remember (inck u d) as iu; destruct iu; symmetry in Heqiu.

    { pose proof (IHK o v c I J d) as IHK.
      repeat (autodimp IHK hyp).
      rewrite h.
      unfold inck in Heqiu.
      destruct (lt_dec (d + u) (maxTime.+1)); ginv; simpl in *.
      rewrite <- multE, <- plusE; simpl.
      rewrite <- (plus_comm u d).
      rewrite plus_assoc; auto. }

    unfold inck in *.
    destruct (lt_dec (d + u) (maxTime.+1)); ginv; simpl in *.
    destruct v as [v cv].
    destruct u as [u cu].
    simpl in *; subst.
    destruct n0.
    rewrite <- multE, <- plusE in cv; simpl in cv.
    apply/ltP.
    eapply leq_ltn_trans;[|eauto].
    rewrite <- plusE.
    rewrite plus_assoc.
    rewrite plus_comm.
    apply leq_addr.
  Qed.

  (* This is one of main properties required to prove timeliness.
   *)
  Lemma IntersectingQuorum_true (del : msgObs) :
    forall (w : World) (F K d : nat) (p : K*d < maxTime.+1),
      (* assuming that there are 3F+1 nodes *)
      numNodes = (3*F)+1
      (* the maximum transmission delay [d] is not 0 *)
      -> d <> 0
      (* that the world is long enough to allow for deliveries to end *)
      -> longEnoughWorld w del (2*(K*d))
      (* that we're running proof of connectivity *)
      -> proof_of_connectivity_condition w F (toI(p))
      (* that received nodes are eventually relayed *)
      -> mustStartDelivering w del
      (* that deliver messages are delivered twice as long as the PoC, which is used in 'IntersectingQuorum' *)
      -> startDisseminateUntil w del (2*K) d
      (* then the 'IntersectingQuorum' property holds *)
      -> IntersectingQuorum w F K d del.
  Proof.
    introv nnodes dd0 lw poc startD dissU.
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

    pose proof (poc n (toI ct) del) as poc; simpl in *.
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
      pose proof (startD n0 u) as startD.
      repeat (autodimp startD hyp); exrepnd.
      destruct (lt_dec u0 t) as [ltu|ltu].
      { pose proof (z _ _ ltu isc) as z; tcsp. }
      assert (~(u0 < t)) as ltu' by (intro xx; destruct ltu; apply/ltP; auto).
      assert (t <= u0) as leu by (rewrite leqNgt; apply/negP; auto).
      clear ltu ltu'.
      exists u0.
      dands; auto.
      eapply leq_ltn_trans; eauto. }

    pose proof (lw n (toI ct) diss) as lw0.

    assert (t + (K*d) < maxTime.+1) as ct'.
    { assert (t + (K*d) <= maxTime) as ct'; auto.
      eapply leq_trans;[|eauto]; simpl.
      rewrite leq_add2l.
      apply leq_pmull; auto. }

    exists A (toI ct'); dands; simpl; auto; try apply leq_addr.
    introv i isc.

    pose proof (z' _ isc i) as z'.
    unfold startDisseminateBetween in z'; exrepnd.
    pose proof (dissU _ _ isc z'0) as dissU.

    pose proof (existsNextStep (toI ct) u K d) as ens.
    repeat (autodimp ens hyp); exrepnd.

    pose proof (lw m u z'0) as lw1.
    rewrite addn1 in ens0; auto.

    assert (u + ((K-J)*d) < maxTime.+1) as cu.
    { assert (u + ((K-J)*d) <= maxTime) as cu; auto.
      eapply leq_trans;[|eauto]; simpl.
      rewrite leq_add2l.
      rewrite <- (Nat.mul_1_l ((K-J)*d)).
      apply leq_mul; auto.
      apply leq_mul; auto.
      apply leq_subr. }

    exists (toI cu); simpl in *.
    dands; auto.

    { apply (@leq_add _ ((K-J)*d) _ ((K-J)*d)) in ens1; auto.
      eapply leq_trans;[|eauto].
      rewrite <- plus_assoc.
      rewrite <- multE.
      rewrite <- Nat.mul_add_distr_r.
      rewrite <- minusE.
      rewrite <- le_plus_minus; auto.
      apply/leP; auto. }

    { rewrite <- (ltn_add2r ((K-J)*d)) in ens2.
      rewrite <- plus_assoc in ens2.
      rewrite <- multE, <- plusE, <- minusE in ens2.
      rewrite <- Nat.mul_add_distr_r in ens2.
      rewrite (Nat.add_comm J 1) in ens2.
      rewrite <- plus_assoc in ens2.
      rewrite <- le_plus_minus in ens2; auto.
      { rewrite Nat.mul_add_distr_r in ens2; simpl in ens2.
        rewrite Nat.add_0_r in ens2.
        rewrite (Nat.add_comm d _) in ens2; auto.
        rewrite <- multE, <- plusE, <- minusE; auto.
        rewrite <- plus_assoc; auto. }
      apply/leP; auto. }

    eapply (disseminateForCovered _ _ _ _ _ _ (K-J)); try exact dissU; simpl; auto.
    rewrite addnBAC; auto.
    rewrite <- multE, <- minusE, <- plusE; simpl.
    rewrite Nat.add_0_r.
    apply/leP; apply Nat.le_sub_l.
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
