
type __ = Obj.t

(* False : logical inductive *)
(* with constructors :  *)


val negb : bool -> bool

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

val bool_dec : bool -> bool -> bool

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
  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int * int
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_succ_nat : int -> positive

  val eq_dec : positive -> positive -> bool
 end

module N :
 sig
  val of_nat : int -> n
 end

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val seq : int -> int -> int list

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

  val abs_nat : z -> int

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

type ('a, 'b) cast = 'a -> 'b

val cast0 : ('a1, 'a2) cast -> 'a1 -> 'a2

type dTimeContext = { dt_0 : __; dt_1 : __; dt_add : (__ -> __ -> __);
                      dt_mul : (__ -> __ -> __); dt_sub : (__ -> __ -> __);
                      dt_opp : (__ -> __); dt_nat_inj : (int -> __);
                      dt_approx : (__ -> int);
                      dt_lt_le_dec : (__ -> __ -> bool);
                      dt_eq_dec : (__ -> __ -> bool) }

type dt_T = __

val dt_nat_inj : dTimeContext -> int -> dt_T

type posDTime =
  dt_T
  (* singleton inductive, whose constructor was MkPosDTime *)

val pos_dt_t : dTimeContext -> posDTime -> dt_T

val nat2pdt : dTimeContext -> int -> posDTime

val n2t : dTimeContext -> (int, posDTime) cast

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

val q_dt_approx : q -> int

val dTimeContextQ : dTimeContext

val remove_elt : 'a1 deq -> 'a1 -> 'a1 list -> 'a1 list

val nullb : 'a1 list -> bool

val mapOption : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val mapin : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list

val decomp_nth : 'a1 list -> int -> (('a1 list * 'a1) * 'a1 list) option

type node = __ deq
  (* singleton inductive, whose constructor was MkNode *)

type name = __

val name_dec : node -> name deq

type nat_n = int

type ('a, 'b) bijective =
  'b -> 'a
  (* singleton inductive, whose constructor was Build_bijective *)

val bij_inv : ('a1 -> 'a2) -> ('a1, 'a2) bijective -> 'a2 -> 'a1

val nat_n_deq : int -> nat_n deq

type quorum_context = { num_nodes : int; node_deq : __ deq;
                        node2nat : (__ -> nat_n);
                        node_bij : (__, nat_n) bijective;
                        node2name : (__ -> name);
                        name2node : (name -> __ option) }

type node_type = __

val num_nodes : node -> quorum_context -> int

val node2nat : node -> quorum_context -> node_type -> nat_n

val node_bij : node -> quorum_context -> (node_type, nat_n) bijective

val mk_nat_n : int -> int -> nat_n

val nodes : node -> quorum_context -> node_type list

type msg =
| MkMsg

type msg0 = __

type directedMsg = { dmMsg : msg0; dmDst : name list; dmDelay : posDTime }

val dmMsg : node -> dTimeContext -> msg -> directedMsg -> msg0

val dmDst : node -> dTimeContext -> msg -> directedMsg -> name list

val dmDelay : node -> dTimeContext -> msg -> directedMsg -> posDTime

type directedMsgs = directedMsg list

type key =
| MkKey

type sending_key = __

type receiving_key = __

type sending_keys = sending_key list

type receiving_keys = receiving_key list

type dSKey = { dsk_dst : name list; dsk_key : sending_key }

val dsk_key : node -> key -> dSKey -> sending_key

type dRKey = { drk_dst : name list; drk_key : receiving_key }

val drk_dst : node -> key -> dRKey -> name list

val drk_key : node -> key -> dRKey -> receiving_key

type local_key_map = { lkm_sending_keys : dSKey list;
                       lkm_receiving_keys : dRKey list }

val lkm_sending_keys : node -> key -> local_key_map -> dSKey list

val lkm_receiving_keys : node -> key -> local_key_map -> dRKey list

type key_map = name -> local_key_map

val lookup_drkeys : node -> key -> local_key_map -> name -> dRKey list

val lookup_receiving_keys :
  node -> key -> local_key_map -> name -> receiving_key list

type authTok =
  __ deq
  (* singleton inductive, whose constructor was MkAuthTok *)

type token = __

val token_dec : authTok -> token deq

type tokens = token list

val tokens_dec : authTok -> tokens deq

type data =
| MkData

type data0 = __

type authFun = { create : (data0 -> sending_keys -> tokens);
                 verify : (data0 -> name -> receiving_key -> token -> bool) }

val create :
  node -> key -> authTok -> data -> authFun -> data0 -> sending_keys -> tokens

val verify :
  node -> key -> authTok -> data -> authFun -> data0 -> name -> receiving_key
  -> token -> bool

val authenticate :
  node -> key -> authTok -> data -> authFun -> data0 -> local_key_map ->
  tokens

type authenticatedData = { am_data : data0; am_auth : tokens }

val am_data : authTok -> data -> authenticatedData -> data0

val am_auth : authTok -> data -> authenticatedData -> tokens

type dataAuth =
  name -> data0 -> name option
  (* singleton inductive, whose constructor was MkDataAuth *)

val data_auth : data -> node -> dataAuth -> name -> data0 -> name option

val verify_authenticated_data_key :
  data -> key -> node -> authTok -> authFun -> name -> authenticatedData ->
  receiving_key -> bool

val verify_authenticated_data_keys :
  data -> key -> node -> authTok -> authFun -> name -> authenticatedData ->
  receiving_keys -> bool

val verify_authenticated_data :
  data -> key -> node -> authTok -> authFun -> dataAuth -> name ->
  authenticatedData -> local_key_map -> bool

type iOTrusted =
  __
  (* singleton inductive, whose constructor was Build_IOTrusted *)

type iot_output = __

val iot_def_output : iOTrusted -> iot_output

type minBFT_context = { minBFT_digestdeq : __ deq; f : int; rep_deq : 
                        __ deq; reps2nat : (__ -> nat_n);
                        reps_bij : (__, nat_n) bijective; num_clients : 
                        int; client_deq : __ deq;
                        clients2nat : (__ -> nat_n);
                        clients_bij : (__, nat_n) bijective;
                        minBFT_data_message_deq : __ deq;
                        minBFT_resdeq : __ deq; minBFT_sm_initial_state : 
                        __; minBFT_sm_update : (__ -> __ -> __ -> __ * __) }

type minBFT_digest = __

val minBFT_digestdeq : minBFT_context -> minBFT_digest deq

val f : minBFT_context -> int

val num_replicas : minBFT_context -> int

type rep = __

val rep_deq : minBFT_context -> rep deq

val reps2nat : minBFT_context -> rep -> nat_n

val reps_bij : minBFT_context -> (rep, nat_n) bijective

val num_clients : minBFT_context -> int

type client = __

val client_deq : minBFT_context -> client deq

val clients2nat : minBFT_context -> client -> nat_n

val clients_bij : minBFT_context -> (client, nat_n) bijective

type minBFT_data_message = __

val minBFT_data_message_deq : minBFT_context -> minBFT_data_message deq

type minBFT_result = __

type minBFT_sm_state = __

val minBFT_sm_initial_state : minBFT_context -> minBFT_sm_state

val minBFT_sm_update :
  minBFT_context -> client -> minBFT_sm_state -> minBFT_data_message ->
  minBFT_result * minBFT_sm_state

type minBFT_node =
| MinBFT_replica of rep
| MinBFT_client of client

val minBFT_nodeDeq : minBFT_context -> minBFT_node deq

val minBFT_I_Node : minBFT_context -> node

val name2rep : minBFT_context -> name -> rep option

val minBFT_I_Quorum : minBFT_context -> quorum_context

val nat_n_Fp1_0 : minBFT_context -> nat_n

val replica0 : minBFT_context -> rep

val nat2rep : minBFT_context -> int -> rep

val reps : minBFT_context -> rep list

val clients : minBFT_context -> client list

type view = int
  (* singleton inductive, whose constructor was view *)

val view2nat : view -> int

val viewDeq : view deq

val initial_view : view

val minBFT_I_AuthTok : minBFT_context -> authTok

val minBFT_I_Key : minBFT_context -> key

type minBFT_initial_keys =
  key_map
  (* singleton inductive, whose constructor was MkMinBFT_initial_keys *)

val initial_keys : minBFT_context -> minBFT_initial_keys -> key_map

val minBFTprimary_nat : minBFT_context -> view -> int

val minBFTprimary : minBFT_context -> view -> rep

val is_primary : minBFT_context -> view -> rep -> bool

val not_primary : minBFT_context -> view -> rep -> bool

type compNameKind = char list

type compNameSpace = int

val compNameKindDeq : compNameKind deq

val compNameSpaceDeq : compNameSpace deq

type compName = { comp_name_kind : compNameKind;
                  comp_name_space : compNameSpace; comp_name_trust : 
                  bool }

val comp_name_kind : compName -> compNameKind

val comp_name_trust : compName -> bool

val compNameDeq : compName deq

type 'p p_nproc = { pp_name : compName; pp_proc : 'p }

type 'p p_procs = 'p p_nproc list

type ('p, 'pO) m_p = 'p p_procs -> 'p p_procs * 'pO

type ('p, 'i, 'o, 's) mP_Update = 's -> 'i -> ('p, 's option * 'o) m_p

type componentIO =
  __
  (* singleton inductive, whose constructor was MkComponentIO *)

type cio_I = __

type cio_O = __

val cio_default_O : componentIO -> cio_O

val cIOmsg : node -> msg -> dTimeContext -> componentIO

val cIOtrusted : iOTrusted -> componentIO

val cIOdef : componentIO

val cIOnat : componentIO

val cIObool : componentIO

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

val nat_comp_name_kind : compNameKind

val bool_comp_name_kind : compNameKind

val munit_comp_name : compName

val funIOd_msg_nm :
  node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> compName ->
  componentIO

val funIOd_msg :
  node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> funIO

type 'p mP_StateMachine = { sm_halted : bool;
                            sm_update : ('p, cio_I, cio_O, sf) mP_Update;
                            sm_state : sf }

val sm_halted :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> compName -> 'a1 mP_StateMachine -> bool

val sm_update :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> compName -> 'a1 mP_StateMachine -> ('a1,
  cio_I, cio_O, sf) mP_Update

val sm_state :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> compName -> 'a1 mP_StateMachine -> sf

type ('a, 'b) sm_or =
| Sm_or_at of 'a
| Sm_or_sm of 'b

type m_StateMachine = __

type n_proc = m_StateMachine

type n_nproc = n_proc p_nproc

type n_procs = n_nproc list

type n_proc_at = n_proc mP_StateMachine

type 'pO m_n = n_procs -> n_procs * 'pO

type 's m_Update = 's -> cio_I -> ('s option * cio_O) m_n

val ret :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> 'a1 -> 'a1 m_n

val bind :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> 'a1 m_n -> ('a1 -> 'a2 m_n) ->
  'a2 m_n

val bind_pair :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> ('a1 * 'a2) m_n -> ('a1 -> 'a2 ->
  'a3 m_n) -> 'a3 m_n

val find_name :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_procs -> n_proc
  option

val replace_name :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> n_procs ->
  n_procs

val at2sm :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_proc_at -> (__
  mP_StateMachine, __) sm_or

val mP_haltedSM :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> compName -> int -> sf -> n_proc_at

val incr_n_proc :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> (__
  mP_StateMachine, __) sm_or

val decr_n_proc :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> n_proc
  option

val decr_n_nproc :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> n_nproc -> n_nproc option

val decr_n_procs :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> n_procs -> n_procs

val incr_pred_n_proc :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> n_proc

val incr_pred_n_nproc :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> n_nproc -> n_nproc

val incr_pred_n_procs :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> n_procs -> n_procs

val update_state :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_proc_at -> sf ->
  n_proc_at

val halt_machine :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_proc_at -> n_proc_at

val sm_s_to_sm :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_proc_at -> (sf
  option * cio_O) m_n -> (n_proc_at * cio_O) m_n

val lift_M_O :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> (n_proc_at * 'a1) m_n
  -> ((__ mP_StateMachine, __) sm_or * 'a1) m_n

val m_on_pred :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> 'a1 m_n -> 'a1 m_n

val lift_M_O2 :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> (n_proc * 'a1) m_n ->
  ((__ mP_StateMachine, __) sm_or * 'a1) m_n

val app_m_proc :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> cio_I ->
  (n_proc * cio_O) m_n

val replace_sub :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> n_procs -> n_proc ->
  n_procs

val replace_subs :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> n_procs -> n_procs -> n_procs

val call_proc :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> cio_I -> cio_O m_n

val build_mp_sm :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> sf m_Update -> sf ->
  n_proc_at

val build_m_sm :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> sf m_Update -> sf ->
  (__ mP_StateMachine, __) sm_or

type localSystem = { ls_main : n_proc_at; ls_subs : n_procs }

val ls_main :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> localSystem ->
  n_proc_at

val ls_subs :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> localSystem -> n_procs

type mLocalSystem = localSystem

val upd_ls_main_state_and_subs :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compName -> localSystem -> sf ->
  n_procs -> localSystem

type funLevelSpace = { fls_level : (name -> int); fls_space : (name -> int) }

val fls_level : node -> funLevelSpace -> name -> int

val fls_space : node -> funLevelSpace -> name -> int

type m_USystem = name -> mLocalSystem

val m_break :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> 'a1 m_n -> n_procs -> (n_procs ->
  'a1 -> 'a2) -> 'a2

type 'o proc =
| PROC_RET of 'o
| PROC_BIND of __ proc * (__ -> 'o proc)
| PROC_CALL of compName * cio_I

val proc_bind_pair :
  node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> ('a1 * 'a2) proc
  -> ('a1 -> 'a2 -> 'a3 proc) -> 'a3 proc

val interp_proc :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> 'a1 proc -> 'a1 m_n

val to_proc_some_state :
  node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> ('a1 * 'a2) proc
  -> ('a1 option * 'a2) proc

val interp_s_proc :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> ('a1 * 'a2) proc -> ('a1
  option * 'a2) m_n

type 's uProc = 's -> cio_I -> ('s * cio_O) proc

val str_concat : char list list -> char list

val bool2string : bool -> char list

val nat2string : int -> char list

val op2string : ('a1 -> char list) -> 'a1 option -> char list

type uSIG_state = { usig_id : rep; usig_counter : int;
                    usig_local_keys : local_key_map }

val usig_id : minBFT_context -> uSIG_state -> rep

val usig_counter : minBFT_context -> uSIG_state -> int

val usig_local_keys : minBFT_context -> uSIG_state -> local_key_map

type preUI = { pre_ui_id : rep; pre_ui_counter : int }

val pre_ui_id : minBFT_context -> preUI -> rep

val pre_ui_counter : minBFT_context -> preUI -> int

type uI = { ui_pre : preUI; ui_digest : minBFT_digest }

val ui_pre : minBFT_context -> uI -> preUI

val ui_digest : minBFT_context -> uI -> minBFT_digest

type uIs = uI list

val ui2rep : minBFT_context -> uI -> rep

val ui2counter : minBFT_context -> uI -> int

val ui2digest : minBFT_context -> uI -> minBFT_digest

type timestamp =
  int
  (* singleton inductive, whose constructor was time_stamp *)

val timestamp2nat : timestamp -> int

type bare_Request = { bare_request_c : client; bare_request_t : timestamp;
                      bare_request_m : minBFT_data_message }

type request = { request_b : bare_Request; request_a : tokens }

val request_b : minBFT_context -> request -> bare_Request

val request_a : minBFT_context -> request -> tokens

type bare_Reply = { bare_reply_r : request; bare_reply_result : int;
                    bare_reply_rep : rep; bare_reply_view : view }

val bare_reply_r : minBFT_context -> bare_Reply -> request

val bare_reply_rep : minBFT_context -> bare_Reply -> rep

type reply = { reply_b : bare_Reply; reply_a : tokens }

val reply_b : minBFT_context -> reply -> bare_Reply

type bare_Prepare = { bare_prepare_v : view; bare_prepare_m : request }

val bare_prepare_v : minBFT_context -> bare_Prepare -> view

val bare_prepare_m : minBFT_context -> bare_Prepare -> request

type prepare = { prepare_b : bare_Prepare; prepare_ui : uI }

val prepare_b : minBFT_context -> prepare -> bare_Prepare

val prepare_ui : minBFT_context -> prepare -> uI

type bare_Commit = { bare_commit_v : view; bare_commit_m : request;
                     bare_commit_ui : uI }

val bare_commit_v : minBFT_context -> bare_Commit -> view

val bare_commit_m : minBFT_context -> bare_Commit -> request

val bare_commit_ui : minBFT_context -> bare_Commit -> uI

type commit = { commit_b : bare_Commit; commit_uj : uI }

val commit_b : minBFT_context -> commit -> bare_Commit

val commit_uj : minBFT_context -> commit -> uI

type accept = { accept_r : request; accept_c : int }

val accept_r : minBFT_context -> accept -> request

val accept_c : minBFT_context -> accept -> int

val prepare2view : minBFT_context -> prepare -> view

val commit2view : minBFT_context -> commit -> view

val bare_request2timestamp : minBFT_context -> bare_Request -> timestamp

val request2timestamp : minBFT_context -> request -> timestamp

val bare_request2sender : minBFT_context -> bare_Request -> client

val request2sender : minBFT_context -> request -> client

val prepare2sender : minBFT_context -> prepare -> rep

val commit2sender_i : minBFT_context -> commit -> rep

val commit2sender_j : minBFT_context -> commit -> rep

val bare_reply2sender : minBFT_context -> bare_Reply -> rep

val bare_reply2request : minBFT_context -> bare_Reply -> request

val bare_reply2client : minBFT_context -> bare_Reply -> client

val reply2client : minBFT_context -> reply -> client

val prepare2ui : minBFT_context -> prepare -> uI

val commit2ui_i : minBFT_context -> commit -> uI

val commit2ui_j : minBFT_context -> commit -> uI

val commit2counter_i : minBFT_context -> commit -> int

val prepare2request : minBFT_context -> prepare -> request

val commit2request : minBFT_context -> commit -> request

val commit2bare_request : minBFT_context -> commit -> bare_Request

val commit2msg : minBFT_context -> commit -> minBFT_data_message

val commit2client : minBFT_context -> commit -> client

type minBFT_Bare_Msg =
| MinBFT_msg_bare_request of bare_Request
| MinBFT_msg_bare_reply of bare_Reply
| MinBFT_msg_bare_prepare of bare_Prepare * preUI
| MinBFT_msg_bare_commit of bare_Commit * preUI

type minBFT_msg =
| MinBFT_request of request
| MinBFT_reply of reply
| MinBFT_prepare of prepare
| MinBFT_commit of commit
| MinBFT_accept of accept
| MinBFT_debug of char list

val minBFT_I_Msg : minBFT_context -> msg

type hashData = { hd_view : view; hd_msg : request; hd_pre : preUI }

type uSIG_hash = { create_hash_usig : (hashData -> local_key_map ->
                                      minBFT_digest);
                   verify_hash_usig : (hashData -> minBFT_digest ->
                                      local_key_map -> bool) }

val create_hash_usig :
  minBFT_context -> uSIG_hash -> hashData -> local_key_map -> minBFT_digest

val verify_hash_usig :
  minBFT_context -> uSIG_hash -> hashData -> minBFT_digest -> local_key_map
  -> bool

val uSIG_initial : minBFT_context -> minBFT_initial_keys -> rep -> uSIG_state

val increment_USIG : minBFT_context -> uSIG_state -> uSIG_state

val create_UI :
  minBFT_context -> uSIG_hash -> view -> request -> uSIG_state ->
  uSIG_state * uI

val verify_UI :
  minBFT_context -> uSIG_hash -> view -> request -> uI -> uSIG_state -> bool

type uSIG_input_interface =
| Create_ui_in of (view * request)
| Verify_ui_in of ((view * request) * uI)

type uSIG_output_interface =
| Create_ui_out of uI
| Verify_ui_out of bool
| Verify_ui_out_def

val cIOusig : minBFT_context -> componentIO

val minBFT_I_Data : minBFT_context -> data

type minBFT_auth = { minBFT_create : (data0 -> sending_keys -> minBFT_digest
                                     list);
                     minBFT_verify : (data0 -> name -> receiving_key ->
                                     minBFT_digest -> bool) }

val minBFT_create :
  minBFT_context -> minBFT_auth -> data0 -> sending_keys -> minBFT_digest list

val minBFT_verify :
  minBFT_context -> minBFT_auth -> data0 -> name -> receiving_key ->
  minBFT_digest -> bool

val minBFT_I_AuthFun : minBFT_context -> minBFT_auth -> authFun

val minBFT_data_auth : minBFT_context -> name -> data0 -> name option

val minBFT_I_DataAuth : minBFT_context -> dataAuth

val other_replicas : minBFT_context -> rep -> rep list

val other_names : minBFT_context -> rep -> name list

val broadcast2others :
  dTimeContext -> minBFT_context -> rep -> (name list -> directedMsg) ->
  directedMsg

val send_prepare :
  dTimeContext -> minBFT_context -> prepare -> name list -> directedMsg

val send_commit :
  dTimeContext -> minBFT_context -> commit -> name list -> directedMsg

val send_reply : dTimeContext -> minBFT_context -> reply -> directedMsg

val send_accept :
  dTimeContext -> minBFT_context -> accept -> name list -> directedMsg

val send_debug :
  dTimeContext -> minBFT_context -> char list -> name -> directedMsg

val mk_auth_prepare : minBFT_context -> view -> request -> uI -> prepare

val mk_auth_commit : minBFT_context -> view -> request -> uI -> uI -> commit

val mk_auth_reply :
  minBFT_context -> minBFT_auth -> request -> int -> rep -> view ->
  local_key_map -> reply

type requestData =
| Request_data of view * request * uI

val request_data2ui : minBFT_context -> requestData -> uI

val request_data2rep : minBFT_context -> requestData -> rep

val timestamp_deq : timestamp deq

val view_deq : view deq

val bare_Request_Deq : minBFT_context -> bare_Request deq

val request_Deq : minBFT_context -> request deq

val requestData_Deq : minBFT_context -> requestData deq

val prepare2request_data : minBFT_context -> prepare -> requestData

val commit2request_data_i : minBFT_context -> commit -> requestData

type lOG_state_entry = { log_entry_request_data : requestData;
                         log_entry_commits : uIs }

val log_entry_request_data : minBFT_context -> lOG_state_entry -> requestData

val log_entry_commits : minBFT_context -> lOG_state_entry -> uIs

type lOG_state = lOG_state_entry list

val lOG_initial : minBFT_context -> lOG_state

val is_committed_entry : minBFT_context -> lOG_state_entry -> bool

val find_entry :
  minBFT_context -> requestData -> lOG_state -> lOG_state_entry option

val is_committed : minBFT_context -> commit -> lOG_state -> bool

val mkNewLogEntryFromPrepare : minBFT_context -> prepare -> lOG_state_entry

val mkNewLogEntryFromCommit : minBFT_context -> commit -> lOG_state_entry

val add_commit2commits : minBFT_context -> uI -> uIs -> uIs

val add_commit2entry :
  minBFT_context -> uI -> lOG_state_entry -> lOG_state_entry

val prepare_already_in_log : minBFT_context -> prepare -> lOG_state -> bool

val log_new_prepare : minBFT_context -> prepare -> lOG_state -> lOG_state

val log_new_commit : minBFT_context -> commit -> lOG_state -> lOG_state

type lOG_input_interface =
| Log_new_prepare_log_in of prepare
| Log_new_commit_log_in of commit
| Prepare_already_in_log_in of prepare
| Is_committed_in of commit

type lOG_output_interface =
  bool
  (* singleton inductive, whose constructor was log_out *)

val cIOlog : minBFT_context -> componentIO

type latest_executed_request = (client * timestamp) list

val initial_latest_executed_request :
  minBFT_context -> latest_executed_request

val update_latest_executed_request :
  minBFT_context -> request -> latest_executed_request ->
  latest_executed_request

type latest_executed_counter = int

val initial_latest_executed_counter : latest_executed_counter

type highest_received_counter_value = (rep * int) list

val initial_highest_received_counter_value :
  minBFT_context -> highest_received_counter_value

val update_highest_received_counter_value :
  minBFT_context -> uI -> highest_received_counter_value ->
  highest_received_counter_value

type mAIN_state = { local_keys : local_key_map; current_view : view;
                    sm_state0 : minBFT_sm_state;
                    cexec : latest_executed_counter;
                    vreq : latest_executed_request;
                    vacc : highest_received_counter_value;
                    current_seq : timestamp option }

val local_keys : minBFT_context -> mAIN_state -> local_key_map

val current_view : minBFT_context -> mAIN_state -> view

val sm_state0 : minBFT_context -> mAIN_state -> minBFT_sm_state

val cexec : minBFT_context -> mAIN_state -> latest_executed_counter

val vreq : minBFT_context -> mAIN_state -> latest_executed_request

val vacc : minBFT_context -> mAIN_state -> highest_received_counter_value

val current_seq : minBFT_context -> mAIN_state -> timestamp option

val initial_state : minBFT_context -> minBFT_initial_keys -> rep -> mAIN_state

val replace_sm_state :
  minBFT_context -> mAIN_state -> minBFT_sm_state -> mAIN_state

val minBFT_I_baseFunIO : minBFT_context -> baseFunIO

val uSIGname : compName

val minBFT_I_baseStateFun : minBFT_context -> baseStateFun

val minBFT_I_IOTrusted : minBFT_context -> iOTrusted

val minBFT_I_trustedStateFun : minBFT_context -> trustedStateFun

val uSIG_update :
  dTimeContext -> minBFT_context -> uSIG_hash -> uSIG_state -> cio_I ->
  n_proc p_nproc list -> n_proc p_nproc list * (uSIG_state option * cio_O)

val uSIG_comp :
  dTimeContext -> minBFT_context -> minBFT_initial_keys -> uSIG_hash -> rep
  -> (n_proc mP_StateMachine, n_proc) sm_or

val lOGname : compName

val lOG_update :
  dTimeContext -> minBFT_context -> lOG_state -> cio_I -> n_proc p_nproc list
  -> n_proc p_nproc list * (lOG_state option * cio_O)

val lOG_comp :
  dTimeContext -> minBFT_context -> (n_proc mP_StateMachine, n_proc) sm_or

val on_create_ui_out :
  minBFT_context -> (uI -> 'a1) -> 'a1 -> uSIG_output_interface -> 'a1

val call_create_ui :
  dTimeContext -> minBFT_context -> (view * request) -> 'a1 proc -> (uI ->
  'a1 proc) -> 'a1 proc

val if_true_verify_ui_out :
  minBFT_context -> 'a1 -> 'a1 -> uSIG_output_interface -> 'a1

val call_verify_ui :
  dTimeContext -> minBFT_context -> ((view * request) * uI) -> 'a1 proc ->
  'a1 proc -> 'a1 proc

val on_log_out : 'a1 -> 'a1 -> lOG_output_interface -> 'a1

val call_prepare_already_in_log :
  dTimeContext -> minBFT_context -> prepare -> 'a1 proc -> 'a1 proc -> 'a1
  proc

val on_log_out_bool : (bool -> 'a1) -> lOG_output_interface -> 'a1

val call_prepare_already_in_log_bool :
  dTimeContext -> minBFT_context -> prepare -> (bool -> 'a1 proc) -> 'a1 proc

val call_is_committed :
  dTimeContext -> minBFT_context -> commit -> 'a1 proc -> 'a1 proc -> 'a1 proc

val call_log_prepare :
  dTimeContext -> minBFT_context -> prepare -> 'a1 proc -> 'a1 proc

val call_log_commit :
  dTimeContext -> minBFT_context -> commit -> 'a1 proc -> 'a1 proc

val on_data_message :
  dTimeContext -> minBFT_context -> minBFT_msg -> 'a1 proc -> (request -> 'a1
  proc) -> 'a1 proc

val on_prepare :
  dTimeContext -> minBFT_context -> minBFT_msg -> 'a1 proc -> (prepare -> 'a1
  proc) -> 'a1 proc

val on_commit :
  dTimeContext -> minBFT_context -> minBFT_msg -> 'a1 proc -> (commit -> 'a1
  proc) -> 'a1 proc

val on_accept :
  dTimeContext -> minBFT_context -> minBFT_msg -> 'a1 proc -> (accept -> 'a1
  proc) -> 'a1 proc

val mAINname : compName

val processing : minBFT_context -> mAIN_state -> bool

val maybe_processing : minBFT_context -> timestamp -> mAIN_state -> bool

val new_request : minBFT_context -> request -> latest_executed_request -> bool

val verify_request :
  minBFT_context -> minBFT_auth -> rep -> local_key_map -> request -> bool

val valid_request :
  minBFT_context -> minBFT_auth -> rep -> local_key_map -> request ->
  mAIN_state -> bool

val invalid_request :
  minBFT_context -> minBFT_auth -> rep -> local_key_map -> request ->
  mAIN_state -> bool

val prepare2timestamp : minBFT_context -> prepare -> timestamp

val commit2timestamp : minBFT_context -> commit -> timestamp

val highest_received_counter :
  minBFT_context -> rep -> highest_received_counter_value -> int option

val highest_received_counter_is :
  minBFT_context -> rep -> int -> highest_received_counter_value -> bool

val received_prior_counter : minBFT_context -> uI -> mAIN_state -> bool

val received_equal_counter : minBFT_context -> uI -> mAIN_state -> bool

val received_prior_or_equal_counter :
  minBFT_context -> uI -> bool -> mAIN_state -> bool

val executed_prior_counter : minBFT_context -> uI -> mAIN_state -> bool

val valid_prepare :
  minBFT_context -> minBFT_auth -> rep -> local_key_map -> view -> prepare ->
  mAIN_state -> bool

val invalid_prepare :
  minBFT_context -> minBFT_auth -> rep -> local_key_map -> view -> prepare ->
  mAIN_state -> bool

val valid_commit :
  minBFT_context -> minBFT_auth -> rep -> local_key_map -> view -> commit ->
  bool -> mAIN_state -> int

val invalid_commit :
  minBFT_context -> minBFT_auth -> rep -> local_key_map -> view -> commit ->
  bool -> mAIN_state -> bool

val start_processing : minBFT_context -> request -> mAIN_state -> mAIN_state

val stop_processing : minBFT_context -> mAIN_state -> mAIN_state

val update_latest_executed :
  minBFT_context -> request -> mAIN_state -> mAIN_state

val update_highest_received_counter :
  minBFT_context -> uI -> mAIN_state -> mAIN_state

val increment_latest_executed_counter :
  minBFT_context -> mAIN_state -> mAIN_state

val handle_request :
  dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state uProc

val handle_prepare :
  dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state uProc

val commit2prepare : minBFT_context -> commit -> prepare

val mk_my_commit : minBFT_context -> commit -> uI -> commit

val send_debug_valid_commit :
  dTimeContext -> minBFT_context -> minBFT_auth -> rep -> local_key_map ->
  view -> commit -> bool -> mAIN_state -> directedMsg

val handle_commit :
  dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state uProc

val handle_accept :
  dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state uProc

val handle_reply : dTimeContext -> minBFT_context -> rep -> mAIN_state uProc

val handle_debug : dTimeContext -> minBFT_context -> rep -> mAIN_state uProc

val mAIN_update :
  dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state -> cio_I
  -> (n_proc mP_StateMachine, n_proc) sm_or p_nproc list -> (n_proc
  mP_StateMachine, n_proc) sm_or p_nproc list * (mAIN_state option * cio_O)

val mAIN_comp :
  dTimeContext -> minBFT_context -> minBFT_initial_keys -> minBFT_auth -> rep
  -> (n_proc mP_StateMachine, n_proc) sm_or mP_StateMachine

val minBFTsubs :
  dTimeContext -> minBFT_context -> minBFT_initial_keys -> uSIG_hash -> rep
  -> (n_proc mP_StateMachine, n_proc) sm_or p_nproc list

type minBFTls = mLocalSystem

val minBFTlocalSys :
  dTimeContext -> minBFT_context -> minBFT_initial_keys -> uSIG_hash ->
  minBFT_auth -> rep -> minBFTls

val minBFTfunLevelSpace : minBFT_context -> funLevelSpace

type time = { time_get_time : (unit -> __); time_sub : (__ -> __ -> __);
              time_2string : (__ -> char list) }

type time_type = __

val time_get_time : time -> unit -> time_type

type timedDirectedMsg = { tdm_dmsg : directedMsg; tdm_time : time_type }

type timedDirectedMsgs = timedDirectedMsg list

type simState = { ss_fls : funLevelSpace; ss_sys : m_USystem; ss_step : 
                  int; ss_out_inflight : directedMsgs;
                  ss_in_inflight : directedMsgs;
                  ss_delivered : timedDirectedMsgs }

val ss_fls :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> funLevelSpace

val ss_sys :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> m_USystem

val ss_step :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> int

val ss_out_inflight :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> directedMsgs

val ss_in_inflight :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> directedMsgs

val ss_delivered :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> timedDirectedMsgs

val replace_out_inflight :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> directedMsgs ->
  simState

val replace_in_inflight :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> directedMsgs ->
  simState

val mkInitSimState :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> funLevelSpace -> m_USystem ->
  directedMsgs -> simState

val m_run_ls_on_this_one_msg :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> int -> compNameSpace -> mLocalSystem ->
  msg0 -> mLocalSystem option * directedMsgs

val run_ls_with_time :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> int -> compNameSpace ->
  mLocalSystem -> msg0 -> posDTime ->
  (mLocalSystem * directedMsgs) * time_type

val dmsg2one_dst :
  node -> msg -> dTimeContext -> directedMsg -> name -> directedMsg

val run_sim_on_nth_out :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> int -> simState

val run_sim_on_nth_in :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> simState -> int -> bool ->
  simState

type round = { round_pos : int; round_num : int }

type rounds = round list

type switch = { switch_step : int; switch_pos : int }

type switches = switch list

val find_switch : int -> switches -> int option

val iterate_n_steps :
  node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
  baseStateFun -> trustedStateFun -> time -> rounds -> switches -> simState
  -> simState

type minbft_digest = int list

val minbft_digest_def : minbft_digest

val minbft_digest_deq : minbft_digest deq

type sending_key_stub =
| Minbft_sending_key_stub

type receiving_key_stub =
| Minbft_receiving_key_stub

type minbft_sending_key = sending_key_stub

type minbft_receiving_key = receiving_key_stub

val nreps : int -> int

type replica = nat_n

val replica_deq : int -> replica deq

val reps2nat0 : int -> replica -> nat_n

val bijective_reps2nat : int -> (replica, nat_n) bijective

val nclients : int -> int

type client0 = nat_n

val client1 : int -> client0

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

val minbft_create_signature :
  minBFT_Bare_Msg -> sending_keys -> minBFT_digest list

val minbft_verify_signature :
  minBFT_Bare_Msg -> name -> receiving_key -> minBFT_digest -> bool

val minBFT_I_auth : minBFT_auth

val minbft_lookup_client_sending_key : client -> minbft_sending_key

val minbft_lookup_client_receiving_key : client -> minbft_receiving_key

val initial_minbft_local_key_map_replicas : name -> local_key_map

val minBFT_I_keys : minBFT_initial_keys

val minbft_create_hash_usig : hashData -> local_key_map -> minBFT_digest

val minbft_verify_hash_usig :
  hashData -> minBFT_digest -> local_key_map -> bool

val minBFT_I_usig_hash : uSIG_hash

val tIME_I : time

val tokens2string : tokens -> char list

val minbft_digest2string : minbft_digest -> char list

val client2string : client0 -> char list

val timestamp2string : timestamp -> char list

val view2string : view -> char list

val str_concat0 : char list list -> char list

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

val bare_reply2string : bare_Reply -> char list

val reply2string : reply -> char list

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

val minBFT_instance_sys : m_USystem

val mk_request_to : rep -> int -> minBFT_data_message -> directedMsg

val mk_request : int -> minBFT_data_message -> directedMsg

val mk_requests_start : int -> int -> minBFT_data_message -> directedMsgs

type initRequests = { num_requests : int; starting_seq_num : int;
                      req_operation : minBFT_data_message }

val num_requests : initRequests -> int

val starting_seq_num : initRequests -> int

val req_operation : initRequests -> minBFT_data_message

val minBFT_init_msgs : directedMsgs -> simState

val minBFT_init : initRequests -> simState

val minBFT_simul_n : initRequests -> rounds -> switches -> simState

val minBFT_simul : simState

val minBFT_simul_pp : unit
