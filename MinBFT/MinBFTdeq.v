(* GENERIC *)

Require Export MinBFTg.
Require Export ComponentSM10.


Section MinBFTdeq.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma Bare_Reply_Deq : Deq Bare_Reply.
  Proof.
    repeat introv.
    destruct x as [c1 t1 m1 v1], y as [c2 t2 m2 v2].
    destruct (Request_Deq c1 c2); subst; prove_dec.
    destruct (deq_nat t1 t2); subst; prove_dec.
    destruct (rep_deq m1 m2); subst; prove_dec.
    destruct (ViewDeq v1 v2); subst; prove_dec.
  Defined.

  Lemma Reply_Deq : Deq Reply.
  Proof.
    repeat introv.
    destruct x as [r1 a1], y as [r2 a2].
    destruct (Bare_Reply_Deq r1 r2); subst; prove_dec.
    destruct (Tokens_dec a1 a2); subst; prove_dec.
  Defined.

  Lemma Bare_Prepare_Deq : Deq Bare_Prepare.
  Proof.
    repeat introv.
    destruct x as [c1 t1 m1 v1], y as [c2 t2 m2 v2].
    destruct (ViewDeq c1 c2); subst; prove_dec.
    destruct (Request_Deq t1 t2); subst; prove_dec.
  Defined.

  Lemma Prepare_Deq : Deq Prepare.
  Proof.
    repeat introv.
    destruct x as [r1 a1], y as [r2 a2].
    destruct (Bare_Prepare_Deq r1 r2); subst; prove_dec.
    destruct (UI_dec a1 a2); subst; prove_dec.
  Defined.

  Lemma Bare_Commit_Deq : Deq Bare_Commit.
  Proof.
    repeat introv.
    destruct x as [c1 t1 m1 v1], y as [c2 t2 m2 v2].
    destruct (ViewDeq c1 c2); subst; prove_dec.
    destruct (Request_Deq t1 t2); subst; prove_dec.
    destruct (UI_dec m1 m2); subst; prove_dec.
  Defined.

  Lemma Commit_Deq : Deq Commit.
  Proof.
    repeat introv.
    destruct x as [r1 a1], y as [r2 a2].
    destruct (Bare_Commit_Deq r1 r2); subst; prove_dec.
    destruct (UI_dec a1 a2); subst; prove_dec.
  Defined.

  Lemma Accept_Deq : Deq Accept.
  Proof.
    repeat introv.
    destruct x as [c1 t1 m1 v1], y as [c2 t2 m2 v2].
    destruct (Request_Deq c1 c2); subst; prove_dec.
    destruct (deq_nat t1 t2); subst; prove_dec.
  Defined.

  Lemma msg_deq : Deq msg.
  Proof.
    introv.
    destruct x, y; simpl in *; subst; prove_dec.
    { destruct (Request_Deq m m0); subst; prove_dec. }
    { destruct (Reply_Deq m m0); subst; prove_dec. }
    { destruct (Prepare_Deq p p0); subst; prove_dec. }
    { destruct (Commit_Deq c c0); subst; prove_dec. }
    { destruct (Accept_Deq a a0); subst; prove_dec. }
    { destruct (string_dec s s0); subst; prove_dec. }
  Qed.

  Lemma ti_deq : Deq (trigger_info msg).
  Proof.
    introv; destruct x as [u1| |i1], y as [u2| |i2]; subst; prove_dec.
    { destruct (msg_deq u1 u2); subst; prove_dec. }
    { destruct i1 as [cn1 i1], i1 as [x|], i2 as [cn2 i2], i2 as [y|]; simpl in *; repnd; simpl in *;
        destruct (PreCompNameDeq cn1 cn2); subst; prove_dec.
      { destruct (ViewDeq x2 y2); subst; prove_dec.
        destruct (Request_Deq x1 y1); subst; prove_dec.
        destruct (deq_nat x0 y0); subst; prove_dec.
        destruct (deq_nat x y); subst; prove_dec. }
      { destruct (ViewDeq msgui4 msgui2); subst; prove_dec.
        destruct (Request_Deq msgui3 msgui1); subst; prove_dec.
        destruct (UI_dec msgui msgui0); subst; prove_dec. } }
  Qed.

End MinBFTdeq.
