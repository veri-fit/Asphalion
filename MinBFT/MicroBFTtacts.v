Require Export MicroBFT.


Create HintDb microbft.
Create HintDb microbft2.
Hint Resolve implies_authenticated_messages_were_sent_non_byz_usys : microbft microbft2.
Hint Rewrite @run_process_on_list_haltedProc : microbft microbft2.


Ltac microbft_simplifier_step :=
  match goal with
  | [ H : ret _ _ _ = (_,_) |- _ ] => unfold ret in H
  | [ H : (_,_) = (_,_) |- _ ] => apply pair_inj in H; repnd
  | [ H : Some _ = Some _ |- _ ] => apply Some_inj in H
  | [ H : MicroBFTsubs_new _ _ = MicroBFTsubs_new _ _ |- _ ] => apply MicroBFTsubs_new_inj in H; repnd
  | [ H : MicroBFTsubs_new _ _ = _ |- _ ] => apply MicroBFTsubs_new_inj in H; repnd
  | [ H : _ = MicroBFTsubs_new _ _ |- _ ] => apply MicroBFTsubs_new_inj in H; repnd
  | [ H : MicroBFTlocalSys _ = MicroBFTlocalSys_new _ _ _ _ |- _ ] => rewrite MicroBFTlocalSys_as_new in H
  | [ H : _ = MicroBFTlocalSys_new _ _ _ _ |- _ ] => apply MicroBFTlocalSys_new_inj in H; repnd
  | [ H : MicroBFTlocalSys_new _ _ _ _ = _ |- _ ] => apply MicroBFTlocalSys_new_inj in H; repnd
  | [ H : MicroBFTsys _ = MicroBFTlocalSys_new _ _ _ _ |- _ ] => rewrite MicroBFTlocalSys_as_new in H
  | [ H : true = false |- _ ] => inversion H
  | [ H : false = true |- _ ] => inversion H
  | [ x : _, H : ?x = _ |- _ ] => subst x
  | [ x : _, H : _ = ?x |- _ ] => subst x
  | [ H : broadcast2others _ (send_commit _) = send_accept _ _ |- _ ] => complete (inversion H)
  end.

Ltac microbft_simp := repeat (microbft_simplifier_step; simpl in * ).

Ltac unfold_handler :=
  match goal with
  | [ H : context[handle_request] |- _ ] => unfold handle_request in H
  | [ H : context[handle_commit ] |- _ ] => unfold handle_commit  in H
  | [ H : context[handle_accept ] |- _ ] => unfold handle_accept  in H
  end.

Ltac unfold_handler_concl :=
  match goal with
  | [ |- context[handle_request] ] => unfold handle_request
  | [ |- context[handle_commit ] ] => unfold handle_commit
  | [ |- context[handle_accept ] ] => unfold handle_accept
  end.

Ltac microbft_simplifier :=
  let stac := (fun _ => microbft_simplifier_step) in
  simplifier stac.

Ltac microbft_dest_all name :=
  let stac := fun _ => microbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  dest_all
    name
    stac
    ftac.

Ltac smash_microbft_tac tac :=
  let stac := fun _ => microbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  let atac := fun _ => repeat (autorewrite with microbft microbft2 comp kn eo proc in *;simpl in * ) in
  smash_byzeml_tac
    tac
    stac
    ftac
    atac.

(* As opposed to the one above, this one doesn't contain microbft2 *)
Ltac smash_microbft_tac_ tac :=
  let stac := fun _ => microbft_simplifier_step in
  let ftac := fun _ => try (fold DirectedMsgs in * ) in
  let atac := fun _ => repeat (autorewrite with microbft comp kn eo proc in *;simpl in * ) in
  smash_byzeml_tac
    tac
    stac
    ftac
    atac.

Ltac smash_microbft1  := let tac := fun _ => (eauto 1  with microbft) in smash_microbft_tac tac.
Ltac smash_microbft2  := let tac := fun _ => (eauto 2  with microbft) in smash_microbft_tac tac.
Ltac smash_microbft3  := let tac := fun _ => (eauto 3  with microbft) in smash_microbft_tac tac.
Ltac smash_microbft4  := let tac := fun _ => (eauto 4  with microbft) in smash_microbft_tac tac.
Ltac smash_microbft5  := let tac := fun _ => (eauto 5  with microbft) in smash_microbft_tac tac.
Ltac smash_microbft6  := let tac := fun _ => (eauto 6  with microbft) in smash_microbft_tac tac.
Ltac smash_microbft7  := let tac := fun _ => (eauto 7  with microbft) in smash_microbft_tac tac.
Ltac smash_microbft8  := let tac := fun _ => (eauto 8  with microbft) in smash_microbft_tac tac.
Ltac smash_microbft9  := let tac := fun _ => (eauto 9  with microbft) in smash_microbft_tac tac.
Ltac smash_microbft10 := let tac := fun _ => (eauto 10 with microbft) in smash_microbft_tac tac.

Ltac smash_microbft_1  := let tac := fun _ => (eauto 1  with microbft) in smash_microbft_tac_ tac.
Ltac smash_microbft_2  := let tac := fun _ => (eauto 2  with microbft) in smash_microbft_tac_ tac.
Ltac smash_microbft_3  := let tac := fun _ => (eauto 3  with microbft) in smash_microbft_tac_ tac.
Ltac smash_microbft_4  := let tac := fun _ => (eauto 4  with microbft) in smash_microbft_tac_ tac.
Ltac smash_microbft_5  := let tac := fun _ => (eauto 5  with microbft) in smash_microbft_tac_ tac.
Ltac smash_microbft_6  := let tac := fun _ => (eauto 6  with microbft) in smash_microbft_tac_ tac.
Ltac smash_microbft_7  := let tac := fun _ => (eauto 7  with microbft) in smash_microbft_tac_ tac.
Ltac smash_microbft_8  := let tac := fun _ => (eauto 8  with microbft) in smash_microbft_tac_ tac.
Ltac smash_microbft_9  := let tac := fun _ => (eauto 9  with microbft) in smash_microbft_tac_ tac.
Ltac smash_microbft_10 := let tac := fun _ => (eauto 10 with microbft) in smash_microbft_tac_ tac.

Ltac smash_microbft := smash_microbft3.

Ltac microbft_dest_msg c :=
  match goal with
  | [ H : MicroBFT_msg |- _ ] =>
    destruct H;
    [ Case_aux c "Request"
    | Case_aux c "Commit"
    | Case_aux c "Accept"
    ];
    simpl in *;
    autorewrite with comp microbft microbft2 in *; simpl in *;
    repeat unfold_handler;
    repeat unfold_handler_concl;
    smash_microbft
  end.

Ltac microbft_finish_eexists :=
  repeat match goal with
         | [ |- ex _ ] => eexists
         end;
  dands; eauto; eauto 3 with eo.

Ltac rename_hyp_with oldname newname :=
  match goal with
  | [ H : context[oldname] |- _ ] => rename H into newname
  end.
