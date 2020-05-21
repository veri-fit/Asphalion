(* GENERIC *)

Require Export ComponentSM7.
Require Export MinBFTgen.


Section MinBFTcount_gen3.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { dtc                 : DTimeContext        }.
  Context { minbft_context      : MinBFT_context      }.
  Context { m_initial_keys      : MinBFT_initial_keys }.
  Context { u_initial_keys      : USIG_initial_keys   }.
  Context { usig_hash           : USIG_hash           }.
  Context { minbft_auth         : MinBFT_auth         }.

  Context { ti : TrustedInfo }.


  Lemma M_run_ls_before_event_minbft_preserves_in_subs :
    forall cn {eo : EventOrdering} (e : Event) R s subs subs',
      ~ In MAINname (get_names subs)
      -> lower_head 1 subs = true
      -> wf_procs subs
      -> are_procs_n_procs subs
      -> M_run_ls_before_event (MinBFTlocalSysP R subs) e
         = Some (MinBFTlocalSys_newP R s subs')
      -> in_subs cn subs = true
      -> in_subs cn subs' = true.
  Proof.
    introv ni low wf aps run i.
    apply M_run_ls_before_event_ls_is_minbftP in run; auto; exrepnd.
    inversion run0 as [xx]; clear run0; apply incr_n_procs_inj in xx; subst; auto; eauto 3 with comp.
  Qed.
  Hint Resolve M_run_ls_before_event_minbft_preserves_in_subs : minbft.

End MinBFTcount_gen3.


Hint Resolve M_run_ls_before_event_minbft_preserves_in_subs : minbft.
