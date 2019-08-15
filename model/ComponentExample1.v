Require Export Component.


Section ComponentExample1.

  Instance CIOnat : ComponentIO :=
    BuildComponentIO nat nat 0.

  Definition m_counter_update : M_Update 0 nat :=
    fun (s : nat) (i : cio_I) => ret _ (Some (s + i), s + i).

  Definition A : M_Process 1 :=
    build_m_process m_counter_update 0.

  Definition B_update : M_Update 1 nat :=
    fun s i =>
      (call_proc "A" i)
        >>= fun out =>
      ret _ (Some (s + out + 1), s + out + 1).

  Definition B : M_Process 2 :=
    build_m_process B_update 0.

  Definition C_update : M_Update 2 nat :=
    fun s i =>
      (call_proc "B" i)
        >>= fun out1 =>
      (call_proc "B" i)
        >>= fun out2 =>
      ret _ (Some (s + out1 + out2 + 2), s + out1 + out2 + 2).

  Definition C : M_Process 3 :=
    build_m_process C_update 0.

  Definition M_update : M_Update 3 unit :=
    fun s i =>
      (call_proc "C" i)
        >>= (fun out => ret _ (Some s, out)).

  Definition M : M_Process 4 :=
    build_m_process M_update tt.

  Definition progs : n_procs 3 :=
    [("A",incr_n_proc (incr_n_proc A)),
     ("B",incr_n_proc B),
     ("C",C)].

  Eval compute in (run_n_proc M [17] progs).

End ComponentExample1.
