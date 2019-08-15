Require Export MinBFTg.


Create HintDb minbft.
Create HintDb minbft2.
Hint Resolve implies_authenticated_messages_were_sent_non_byz_usys : minbft minbft2.
Hint Rewrite @run_process_on_list_haltedProc : minbft minbft2.


Ltac minbft_simplifier_step :=
  match goal with
  | [ H : true = false |- _ ] => inversion H
  | [ H : false = true |- _ ] => inversion H
  | [ H : broadcast2others _ (send_commit  _) = send_accept _ _ |- _ ] => complete (inversion H)
  | [ H : broadcast2others _ (send_prepare _) = send_accept _ _ |- _ ] => complete (inversion H)
  | [ H : send_debug  _ _ = send_accept _ _ |- _ ] => complete (inversion H)
  | [ H : send_accept _ _ = send_debug  _ _ |- _ ] => complete (inversion H)
  | [ H : send_debug_valid_commit _ _ _ _ _ _ = send_accept _ _ |- _ ] => complete (inversion H)
  | [ H : send_accept _ _ = send_debug_valid_commit _ _ _ _ _ _ |- _ ] => complete (inversion H)

  | [ H : n_procs 0 |- _ ] => rewrite (n_procs_0 H) in *; simpl in *; clear H
  | [ H : ret _ _ _ = (_,_) |- _ ] => unfold ret in H
  | [ H : (_,_) = (_,_) |- _ ] => apply pair_inj in H; repnd
  | [ H : Some _ = Some _ |- _ ] => apply Some_inj in H
  | [ x : _, H : ?x = _ |- _ ] => subst x
  | [ x : _, H : _ = ?x |- _ ] => subst x
  end.

Ltac minbft_simp := repeat (minbft_simplifier_step; simpl in * ).

Ltac unfold_handler :=
  match goal with
  | [ H : context[handle_request] |- _ ] => unfold handle_request in H
  | [ H : context[handle_reply  ] |- _ ] => unfold handle_reply   in H
  | [ H : context[handle_prepare] |- _ ] => unfold handle_prepare in H
  | [ H : context[handle_commit ] |- _ ] => unfold handle_commit  in H
  | [ H : context[handle_accept ] |- _ ] => unfold handle_accept  in H
  | [ H : context[handle_debug  ] |- _ ] => unfold handle_debug   in H
  end.

Ltac unfold_handler_concl :=
  match goal with
  | [ |- context[handle_request] ] => unfold handle_request
  | [ |- context[handle_reply  ] ] => unfold handle_reply
  | [ |- context[handle_prepare] ] => unfold handle_prepare
  | [ |- context[handle_commit ] ] => unfold handle_commit
  | [ |- context[handle_accept ] ] => unfold handle_accept
  | [ |- context[handle_debug  ] ] => unfold handle_debug
  end.

Ltac minbft_simplifier :=
  let stac := (fun _ => minbft_simplifier_step) in
  simplifier stac.

Ltac minbft_dest_all name :=
  let stac := fun _ => minbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  dest_all
    name
    stac
    ftac.

Ltac smash_minbft_tac tac :=
  let stac := fun _ => minbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  let atac := fun _ => repeat (autorewrite with minbft minbft2 comp kn eo proc in *;simpl in * ) in
  smash_byzeml_tac
    tac
    stac
    ftac
    atac.

Ltac smash_minbft_tac_at H tac :=
  let stac := fun _ => minbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  let atac := fun _ => repeat (autorewrite with minbft minbft2 comp kn eo proc in H;simpl in H) in
  smash_byzeml_tac
    tac
    stac
    ftac
    atac.

(* As opposed to the one above, this one doesn't contain minbft2 *)
Ltac smash_minbft_tac_ tac :=
  let stac := fun _ => minbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  let atac := fun _ => repeat (autorewrite with minbft comp kn eo proc in *;simpl in * ) in
  smash_byzeml_tac
    tac
    stac
    ftac
    atac.

Ltac smash_minbft1  := let tac := fun _ => (eauto 1  with minbft) in smash_minbft_tac tac.
Ltac smash_minbft2  := let tac := fun _ => (eauto 2  with minbft) in smash_minbft_tac tac.
Ltac smash_minbft3  := let tac := fun _ => (eauto 3  with minbft) in smash_minbft_tac tac.
Ltac smash_minbft4  := let tac := fun _ => (eauto 4  with minbft) in smash_minbft_tac tac.
Ltac smash_minbft5  := let tac := fun _ => (eauto 5  with minbft) in smash_minbft_tac tac.
Ltac smash_minbft6  := let tac := fun _ => (eauto 6  with minbft) in smash_minbft_tac tac.
Ltac smash_minbft7  := let tac := fun _ => (eauto 7  with minbft) in smash_minbft_tac tac.
Ltac smash_minbft8  := let tac := fun _ => (eauto 8  with minbft) in smash_minbft_tac tac.
Ltac smash_minbft9  := let tac := fun _ => (eauto 9  with minbft) in smash_minbft_tac tac.
Ltac smash_minbft10 := let tac := fun _ => (eauto 10 with minbft) in smash_minbft_tac tac.

Ltac smash_minbft1_at  H := let tac := fun _ => (eauto 1  with minbft) in smash_minbft_tac_at H tac.
Ltac smash_minbft2_at  H := let tac := fun _ => (eauto 2  with minbft) in smash_minbft_tac_at H tac.
Ltac smash_minbft3_at  H := let tac := fun _ => (eauto 3  with minbft) in smash_minbft_tac_at H tac.
Ltac smash_minbft4_at  H := let tac := fun _ => (eauto 4  with minbft) in smash_minbft_tac_at H tac.
Ltac smash_minbft5_at  H := let tac := fun _ => (eauto 5  with minbft) in smash_minbft_tac_at H tac.
Ltac smash_minbft6_at  H := let tac := fun _ => (eauto 6  with minbft) in smash_minbft_tac_at H tac.
Ltac smash_minbft7_at  H := let tac := fun _ => (eauto 7  with minbft) in smash_minbft_tac_at H tac.
Ltac smash_minbft8_at  H := let tac := fun _ => (eauto 8  with minbft) in smash_minbft_tac_at H tac.
Ltac smash_minbft9_at  H := let tac := fun _ => (eauto 9  with minbft) in smash_minbft_tac_at H tac.
Ltac smash_minbft10_at H := let tac := fun _ => (eauto 10 with minbft) in smash_minbft_tac_at H tac.

Ltac smash_minbft_1  := let tac := fun _ => (eauto 1  with minbft) in smash_minbft_tac_ tac.
Ltac smash_minbft_2  := let tac := fun _ => (eauto 2  with minbft) in smash_minbft_tac_ tac.
Ltac smash_minbft_3  := let tac := fun _ => (eauto 3  with minbft) in smash_minbft_tac_ tac.
Ltac smash_minbft_4  := let tac := fun _ => (eauto 4  with minbft) in smash_minbft_tac_ tac.
Ltac smash_minbft_5  := let tac := fun _ => (eauto 5  with minbft) in smash_minbft_tac_ tac.
Ltac smash_minbft_6  := let tac := fun _ => (eauto 6  with minbft) in smash_minbft_tac_ tac.
Ltac smash_minbft_7  := let tac := fun _ => (eauto 7  with minbft) in smash_minbft_tac_ tac.
Ltac smash_minbft_8  := let tac := fun _ => (eauto 8  with minbft) in smash_minbft_tac_ tac.
Ltac smash_minbft_9  := let tac := fun _ => (eauto 9  with minbft) in smash_minbft_tac_ tac.
Ltac smash_minbft_10 := let tac := fun _ => (eauto 10 with minbft) in smash_minbft_tac_ tac.

Ltac smash_minbft := smash_minbft3.

Ltac minbft_dest_msg c :=
  match goal with
  | [ H : MinBFT_msg |- _ ] =>
    destruct H;
    [ Case_aux c "Request"
    | Case_aux c "Reply"
    | Case_aux c "Prepare"
    | Case_aux c "Commit"
    | Case_aux c "Accept"
    | Case_aux c "Debug"
    ];
    simpl in *;
    autorewrite with comp minbft minbft2 in *; simpl in *;
    repeat unfold_handler;
    repeat unfold_handler_concl;
    smash_minbft
  end.

Ltac minbft_finish_eexists :=
  repeat match goal with
         | [ |- ex _ ] => eexists
         end;
  dands; eauto; eauto 3 with eo.

Ltac rename_hyp_with oldname newname :=
  match goal with
  | [ H : context[oldname] |- _ ] => rename H into newname
  end.
