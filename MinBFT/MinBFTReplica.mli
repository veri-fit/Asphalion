
type __ = Obj.t

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)



val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont :
    comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val of_succ_nat : int -> positive

  val eq_dec : positive -> positive -> bool
 end

module N :
 sig
  val of_nat : int -> n
 end

val list_eq_dec :
  ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val of_nat : int -> z

  val eq_dec : z -> z -> bool
 end

val z_lt_dec : z -> z -> bool

val z_lt_ge_dec : z -> z -> bool

val z_lt_le_dec : z -> z -> bool

val string_dec : char list -> char list -> bool

val append : char list -> char list -> char list

type q = { qnum : z; qden : positive }

val qnum : q -> z

val qden : q -> positive

val inject_Z : z -> q

val qeq_dec : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qlt_le_dec : q -> q -> bool

type 't deceq = bool

type 't deq = 't -> 't -> 't deceq

type dTimeContext = { dt_0 : __; dt_1 : __;
                      dt_add : (__ -> __ -> __);
                      dt_mul : (__ -> __ -> __);
                      dt_sub : (__ -> __ -> __);
                      dt_opp : (__ -> __);
                      dt_nat_inj : (int -> __);
                      dt_lt_le_dec : (__ -> __ -> bool);
                      dt_eq_dec : (__ -> __ -> bool) }

type dt_T = __

type posDTime =
  dt_T
  (* singleton inductive, whose constructor was MkPosDTime *)

val pos_dt_t : dTimeContext -> posDTime -> dt_T

type q_dt_T = q

val q_dt_0 : q_dt_T

val q_dt_1 : q_dt_T

val q_dt_add : q_dt_T -> q_dt_T -> q_dt_T

val q_dt_mul : q_dt_T -> q_dt_T -> q_dt_T

val q_dt_sub : q_dt_T -> q_dt_T -> q_dt_T

val q_dt_opp : q_dt_T -> q_dt_T

val q_dt_nat_inj : int -> q_dt_T

val q_dt_lt_le_dec : q_dt_T -> q_dt_T -> bool

val q_dt_eq_dec : q_dt_T -> q_dt_T -> bool

val dTimeContextQ : dTimeContext

type node =
  __ deq
  (* singleton inductive, whose constructor was MkNode *)

type name = __

type nat_n = int

type ('a, 'b) bijective =
  'b -> 'a
  (* singleton inductive, whose constructor was Build_bijective *)

val nat_n_deq : int -> nat_n deq

type msg =
| MkMsg

type msg0 = __

type directedMsg = { dmMsg : msg0; dmDst : name list;
                     dmDelay : posDTime }

type directedMsgs = directedMsg list

type key =
| MkKey

type token = __

type tokens = token list

type iOTrusted =
  __
  (* singleton inductive, whose constructor was Build_IOTrusted *)

type iot_output = __

val iot_def_output : iOTrusted -> iot_output

type ('s, 'i, 'o) update = 's -> 'i -> posDTime -> 's option * 'o

type ('s, 'i, 'o) stateMachine = { sm_halted : bool;
                                   sm_update : ('s, 'i, 'o) update;
                                   sm_state : 's }

val sm_halted :
  dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> bool

val sm_update :
  dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> ('a1, 'a2, 'a3)
  update

val sm_state : dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> 'a1

val updState :
  dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> 'a1 -> ('a1,
  'a2, 'a3) stateMachine

val halts :
  dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> ('a1, 'a2, 'a3)
  stateMachine

val force_sm :
  dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> (('a1, 'a2, 'a3)
  stateMachine -> 'a4) -> 'a4

val run_sm :
  dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> 'a2 -> posDTime
  -> (('a1, 'a2, 'a3) stateMachine * 'a3) option

type minBFT_context = { minBFT_digestdeq : __ deq; f : int;
                        rep_deq : __ deq;
                        reps2nat : (__ -> nat_n);
                        reps_bij : (__, nat_n) bijective;
                        num_clients : int; client_deq : __ deq;
                        clients2nat : (__ -> nat_n);
                        clients_bij : (__, nat_n) bijective;
                        minBFT_data_message_deq : __ deq;
                        minBFT_resdeq : __ deq;
                        minBFT_sm_initial_state : __;
                        minBFT_sm_update : (__ -> __ -> __ ->
                                           __ * __) }

type minBFT_digest = __

type rep = __

val rep_deq : minBFT_context -> rep deq

type client = __

val client_deq : minBFT_context -> client deq

type minBFT_data_message = __

type minBFT_node =
| MinBFT_replica of rep
| MinBFT_client of client

val minBFT_nodeDeq : minBFT_context -> minBFT_node deq

val minBFT_I_Node : minBFT_context -> node

type view =
  int
  (* singleton inductive, whose constructor was view *)

val minBFT_I_Key : minBFT_context -> key

type compNameKind = char list

type compNameSpace = int

val compNameKindDeq : compNameKind deq

type compName = { comp_name_kind : compNameKind;
                  comp_name_space : compNameSpace;
                  comp_name_trust : bool }

val comp_name_kind : compName -> compNameKind

val comp_name_trust : compName -> bool

type 'p p_nproc = { pp_name : compName; pp_proc : 'p }

type 'p p_procs = 'p p_nproc list

type ('p, 'pO) m_p = 'p p_procs -> 'p p_procs * 'pO

type ('p, 'i, 'o, 's) mP_Update =
  's -> 'i -> ('p, 's option * 'o) m_p

type componentIO =
  __
  (* singleton inductive, whose constructor was MkComponentIO *)

type cio_I = __

type cio_O = __

val cio_default_O : componentIO -> cio_O

val cIOmsg : node -> msg -> dTimeContext -> componentIO

val cIOtrusted : iOTrusted -> componentIO

val cIOdef : componentIO

type baseFunIO =
  compName -> componentIO
  (* singleton inductive, whose constructor was MkBaseFunIO *)

val bfio : baseFunIO -> compName -> componentIO

type baseStateFun =
| MkBaseStateFun

type trustedStateFun =
| MkTrustedStateFun

type funIO =
  compName -> componentIO
  (* singleton inductive, whose constructor was MkFunIO *)

val fio : funIO -> compName -> componentIO

type sf = __

val msg_comp_name_kind : compNameKind

val msg_comp_name_trust : bool

val msg_comp_name : compNameSpace -> compName

val unit_comp_name_kind : compNameKind

val munit_comp_name : compName

val funIOd_msg_nm :
  node -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  compName -> componentIO

val funIOd_msg :
  node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> funIO

type 'p mP_StateMachine = { sm_halted0 : bool;
                            sm_update0 : ('p, cio_I, cio_O, sf)
                                         mP_Update; sm_state0 : 
                            sf }

type m_StateMachine = __

type n_proc = m_StateMachine

type n_nproc = n_proc p_nproc

type n_procs = n_nproc list

type n_proc_at = m_StateMachine mP_StateMachine

val mP_haltedSM :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> compName -> int -> sf ->
  n_proc mP_StateMachine

type localSystem = { ls_main : n_proc_at; ls_subs : n_procs }

type funLevelSpace = { fls_level : (name -> int);
                       fls_space : (name -> int) }

type m_USystem = name -> localSystem

type preUI = { pre_ui_id : rep; pre_ui_counter : int }

type uI = { ui_pre : preUI; ui_digest : minBFT_digest }

type timestamp =
  int
  (* singleton inductive, whose constructor was time_stamp *)

type bare_Request = { bare_request_c : client;
                      bare_request_t : timestamp;
                      bare_request_m : minBFT_data_message }

type request = { request_b : bare_Request; request_a : tokens }

type bare_Prepare = { bare_prepare_v : view;
                      bare_prepare_m : request }

type prepare = { prepare_b : bare_Prepare; prepare_ui : uI }

type bare_Commit = { bare_commit_v : view;
                     bare_commit_m : request; bare_commit_ui : 
                     uI }

type commit = { commit_b : bare_Commit; commit_uj : uI }

type accept = { accept_r : request; accept_c : int }

type minBFT_msg =
| MinBFT_request of request
| MinBFT_prepare of prepare
| MinBFT_commit of commit
| MinBFT_accept of accept
| MinBFT_debug of char list

val minBFT_I_Msg : minBFT_context -> msg

type uSIG_output_interface =
| Create_ui_out of uI
| Verify_ui_out of bool
| Verify_ui_out_def

val cIOusig : minBFT_context -> componentIO

val cIOlog : minBFT_context -> componentIO

val minBFT_I_baseFunIO : minBFT_context -> baseFunIO

val minBFT_I_baseStateFun : minBFT_context -> baseStateFun

val minBFT_I_IOTrusted : minBFT_context -> iOTrusted

val minBFT_I_trustedStateFun : minBFT_context -> trustedStateFun

val minBFTfunLevelSpace : minBFT_context -> funLevelSpace

type time_type = __

type timedDirectedMsg = { tdm_dmsg : directedMsg;
                          tdm_time : time_type }

type timedDirectedMsgs = timedDirectedMsg list

type simState = { ss_fls : funLevelSpace; ss_sys : m_USystem;
                  ss_step : int; ss_out_inflight : directedMsgs;
                  ss_in_inflight : directedMsgs;
                  ss_delivered : timedDirectedMsgs }

type minbft_digest = int list

val minbft_digest_deq : minbft_digest deq

val nreps : int -> int

type replica = nat_n

val replica_deq : int -> replica deq

val reps2nat0 : int -> replica -> nat_n

val bijective_reps2nat : int -> (replica, nat_n) bijective

val nclients : int -> int

type client0 = nat_n

val client_deq0 : int -> client0 deq

val clients2nat0 : int -> client0 -> nat_n

val bijective_clients2nat : int -> (client0, nat_n) bijective

type minbft_data_message =
| Minbft_data_message_plus of int
| Minbft_data_message_minus of int

val minbft_data_message_deq : minbft_data_message deq

type minbft_result = int

val minbft_result_deq : minbft_result deq

type minbft_sm_state = int

val minbft_sm_initial_state : minbft_sm_state

val minbft_sm_update :
  int -> client0 -> minbft_sm_state -> minbft_data_message ->
  minbft_result * minbft_sm_state

val f0 : int

val c : int

val minBFT_I_context : minBFT_context

val tokens2string : tokens -> char list

val minbft_digest2string : minbft_digest -> char list

val client2string : client0 -> char list

val timestamp2string : timestamp -> char list

val view2string : view -> char list

val str_concat : char list list -> char list

val minbft_data_message2string : minbft_data_message -> char list

val nat_n2string : int -> nat_n -> char list

val replica2string : replica -> char list

val bare_request2string : bare_Request -> char list

val request2string : request -> char list

val bare_prepare2string : bare_Prepare -> char list

val pre_ui2string : preUI -> char list

val ui2string : uI -> char list

val bare_commit2string : bare_Commit -> char list

val prepare2string : prepare -> char list

val commit2string : commit -> char list

val accept2string : accept -> char list

val msg2string : minBFT_msg -> char list

val name2string : name -> char list

val names2string : name list -> char list

val z2string : z -> char list

val pos2string : positive -> char list

val q2string : q -> char list

val posdtime2string : posDTime -> char list

val directedMsg2string : directedMsg -> char list

val directedMsgs2string : directedMsgs -> char list

val timedDirectedMsg2string : timedDirectedMsg -> char list

val timedDirectedMsgs2string : timedDirectedMsgs -> char list

val simState2string : simState -> char list

val dummy_LocalSystem : localSystem

val local_replica : minBFT_context -> funLevelSpace
