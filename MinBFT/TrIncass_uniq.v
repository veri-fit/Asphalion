Require Export TrIncprops2.
Require Export TrIncrun.


Section TrIncass_uniq.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Lemma ASSUMPTION_disseminate_unique_true :
    forall (eo : EventOrdering), assume_eo eo ASSUMPTION_disseminate_unique.
  Proof.
    introv h; simpl in *; exrepnd; subst; GC.
    rewrite h0 in h1; ginv.

    unfold disseminate_data in *; simpl in *; exrepnd.
    rewrite h6 in *; ginv.
    unfold M_byz_output_sys_on_event in *; simpl in *.
    unfold M_byz_output_ls_on_event in *; simpl in *.
    revert dependent o; allrw; simpl; introv dout1 out dout2.

    remember (M_byz_run_ls_before_event (MinBFTlocalSys c3) e) as run; symmetry in Heqrun.
    apply M_byz_run_ls_before_event_ls_is_minbft in Heqrun.
    unfold M_byz_run_ls_on_one_event in out; simpl in *.
    unfold M_byz_run_ls_on_input in out.
    unfold data_is_in_out, event2out in *.
    remember (trigger e) as trig; symmetry in Heqtrig.
    destruct trig; repndors; exrepnd; subst; simpl in *; ginv; tcsp;[| |].

    { apply in_flat_map in dout1; exrepnd.
      apply in_flat_map in dout2; exrepnd.
      unfold M_run_ls_on_input in *; simpl in *.
      autorewrite with comp minbft in *; simpl in *.

      Time minbft_dest_msg Case;
        repeat (simpl in *; autorewrite with minbft in *; smash_minbft2);
        repeat (repndors; subst; tcsp; smash_minbft2). }

    { pose proof (snd_M_run_ls_on_trusted_incr_n_procs_eq (USIGlocalSys u) i) as z.
      unfold LocalSystem in *; simpl in *; rewrite z in out; clear z.
      rewrite rw_M_run_ls_on_trusted_USIGlocalSys in out.
      destruct i as [cn i]; simpl in *; dest_cases w;[].
      subst; simpl in *.
      destruct i; repnd; repeat (simpl in *; repndors; ginv; tcsp).
      unfold try_create_trinc_ui in *; simpl in *; smash_minbft2. }

    { pose proof (snd_M_run_ls_on_trusted_incr_n_procs_eq (USIGlocalSys u) i) as z.
      unfold LocalSystem in *; simpl in *; rewrite z in out; clear z.
      rewrite rw_M_run_ls_on_trusted_USIGlocalSys in out.
      destruct i as [cn i]; simpl in *; dest_cases w;[].
      subst; simpl in *.
      destruct i; repnd; repeat (simpl in *; repndors; ginv; tcsp).
      unfold try_create_trinc_ui in *; simpl in *; smash_minbft2. }
  Qed.
  Hint Resolve ASSUMPTION_disseminate_unique_true : minbft.

End TrIncass_uniq.


Hint Resolve ASSUMPTION_disseminate_unique_true : minbft.
