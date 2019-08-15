Require Export MinBFTgen.


Section MinBFTcount_gen1.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma accepted_if_executed_previous_step :
    forall {eo  : EventOrdering}
           (e   : Event)
           (req : Request)
           (i   : nat)
           (l   : list name)
           (r   : Rep)
           (s   : MAIN_state)
           (subs : n_procs _),
      In (send_accept (accept req i) l)
         (M_output_ls_on_this_one_event (MinBFTlocalSys_newP r s subs) e)
      -> i = S (cexec s).
  Proof.
    introv h.
    apply in_M_output_ls_on_this_one_event_implies in h; exrepnd; simpl in *.
    autorewrite with minbft comp in *.
    Time minbft_dest_msg Case; simpl in *; tcsp; ginv; repeat smash_minbft2;
      repndors; tcsp; try (complete (inversion h0; subst; GC; eauto 4 with minbft));
        repeat (gdest; smash_minbft1_at_ h0; repeat hide_break; repnd; simpl in *; repndors; ginv; tcsp; eauto 2 with minbft).
  Qed.

End MinBFTcount_gen1.
