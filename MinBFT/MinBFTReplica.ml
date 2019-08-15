
type __ = Obj.t

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)



(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

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

module Nat =
 struct
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q0 -> XO (succ q0)
       | XO q0 -> XI q0
       | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont :
      comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n0

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> false)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> false)
    | XH -> (match x0 with
             | XH -> true
             | _ -> false)
 end

module N =
 struct
  (** val of_nat : int -> n **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> N0)
      (fun n' -> Npos (Pos.of_succ_nat n'))
      n0
 end

(** val list_eq_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a0 :: l1 ->
       if eq_dec0 y a0 then list_eq_dec eq_dec0 l0 l1 else false)

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Pos.compare x' y'
       | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val of_nat : int -> z **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n1 -> Zpos (Pos.of_succ_nat n1))
      n0

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos x0 ->
      (match y with
       | Zpos p0 -> Pos.eq_dec x0 p0
       | _ -> false)
    | Zneg x0 ->
      (match y with
       | Zneg p0 -> Pos.eq_dec x0 p0
       | _ -> false)
 end

(** val z_lt_dec : z -> z -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_lt_ge_dec : z -> z -> bool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : z -> z -> bool **)

let z_lt_le_dec =
  z_lt_ge_dec

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c0::s1' -> c0::(append s1' s2)

type q = { qnum : z; qden : positive }

(** val qnum : q -> z **)

let qnum x = x.qnum

(** val qden : q -> positive **)

let qden x = x.qden

(** val inject_Z : z -> q **)

let inject_Z x =
  { qnum = x; qden = XH }

(** val qeq_dec : q -> q -> bool **)

let qeq_dec x y =
  Z.eq_dec (Z.mul x.qnum (Zpos y.qden))
    (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum =
    (Z.add (Z.mul x.qnum (Zpos y.qden))
      (Z.mul y.qnum (Zpos x.qden))); qden =
    (Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qlt_le_dec : q -> q -> bool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden))
    (Z.mul y.qnum (Zpos x.qden))

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

(** val pos_dt_t : dTimeContext -> posDTime -> dt_T **)

let pos_dt_t _ p =
  p

type q_dt_T = q

(** val q_dt_0 : q_dt_T **)

let q_dt_0 =
  { qnum = Z0; qden = XH }

(** val q_dt_1 : q_dt_T **)

let q_dt_1 =
  { qnum = (Zpos XH); qden = XH }

(** val q_dt_add : q_dt_T -> q_dt_T -> q_dt_T **)

let q_dt_add =
  qplus

(** val q_dt_mul : q_dt_T -> q_dt_T -> q_dt_T **)

let q_dt_mul =
  qmult

(** val q_dt_sub : q_dt_T -> q_dt_T -> q_dt_T **)

let q_dt_sub =
  qminus

(** val q_dt_opp : q_dt_T -> q_dt_T **)

let q_dt_opp =
  qopp

(** val q_dt_nat_inj : int -> q_dt_T **)

let q_dt_nat_inj n0 =
  inject_Z (Z.of_nat n0)

(** val q_dt_lt_le_dec : q_dt_T -> q_dt_T -> bool **)

let q_dt_lt_le_dec =
  qlt_le_dec

(** val q_dt_eq_dec : q_dt_T -> q_dt_T -> bool **)

let q_dt_eq_dec =
  qeq_dec

(** val dTimeContextQ : dTimeContext **)

let dTimeContextQ =
  { dt_0 = (Obj.magic q_dt_0); dt_1 = (Obj.magic q_dt_1); dt_add =
    (Obj.magic q_dt_add); dt_mul = (Obj.magic q_dt_mul); dt_sub =
    (Obj.magic q_dt_sub); dt_opp = (Obj.magic q_dt_opp);
    dt_nat_inj = (Obj.magic q_dt_nat_inj); dt_lt_le_dec =
    (Obj.magic q_dt_lt_le_dec); dt_eq_dec =
    (Obj.magic q_dt_eq_dec) }

type node =
  __ deq
  (* singleton inductive, whose constructor was MkNode *)

type name = __

type nat_n = int

type ('a, 'b) bijective =
  'b -> 'a
  (* singleton inductive, whose constructor was Build_bijective *)

(** val nat_n_deq : int -> nat_n deq **)

let nat_n_deq _ =
  (=)

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

(** val iot_def_output : iOTrusted -> iot_output **)

let iot_def_output iOTrusted0 =
  iOTrusted0

type ('s, 'i, 'o) update = 's -> 'i -> posDTime -> 's option * 'o

type ('s, 'i, 'o) stateMachine = { sm_halted : bool;
                                   sm_update : ('s, 'i, 'o) update;
                                   sm_state : 's }

(** val sm_halted :
    dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> bool **)

let sm_halted _ x = x.sm_halted

(** val sm_update :
    dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> ('a1, 'a2,
    'a3) update **)

let sm_update _ x = x.sm_update

(** val sm_state :
    dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> 'a1 **)

let sm_state _ x = x.sm_state

(** val updState :
    dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> 'a1 -> ('a1,
    'a2, 'a3) stateMachine **)

let updState _ c0 s =
  { sm_halted = c0.sm_halted; sm_update = c0.sm_update; sm_state =
    s }

(** val halts :
    dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> ('a1, 'a2,
    'a3) stateMachine **)

let halts _ c0 =
  { sm_halted = true; sm_update = c0.sm_update; sm_state =
    c0.sm_state }

(** val force_sm :
    dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> (('a1, 'a2,
    'a3) stateMachine -> 'a4) -> 'a4 **)

let force_sm _ sm f1 =
  f1 sm

(** val run_sm :
    dTimeContext -> ('a1, 'a2, 'a3) stateMachine -> 'a2 ->
    posDTime -> (('a1, 'a2, 'a3) stateMachine * 'a3) option **)

let run_sm dtc c0 i t =
  if c0.sm_halted
  then None
  else let (o0, o) = c0.sm_update c0.sm_state i t in
       (match o0 with
        | Some s ->
          force_sm dtc (updState dtc c0 s) (fun sm -> Some (sm, o))
        | None ->
          force_sm dtc (halts dtc c0) (fun sm -> Some (sm, o)))

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

(** val rep_deq : minBFT_context -> rep deq **)

let rep_deq x = x.rep_deq

type client = __

(** val client_deq : minBFT_context -> client deq **)

let client_deq x = x.client_deq

type minBFT_data_message = __

type minBFT_node =
| MinBFT_replica of rep
| MinBFT_client of client

(** val minBFT_nodeDeq : minBFT_context -> minBFT_node deq **)

let minBFT_nodeDeq minBFT_context0 x y =
  match x with
  | MinBFT_replica r1 ->
    (match y with
     | MinBFT_replica r2 -> minBFT_context0.rep_deq r1 r2
     | MinBFT_client _ -> false)
  | MinBFT_client c1 ->
    (match y with
     | MinBFT_replica _ -> false
     | MinBFT_client c2 -> minBFT_context0.client_deq c1 c2)

(** val minBFT_I_Node : minBFT_context -> node **)

let minBFT_I_Node minBFT_context0 =
  Obj.magic minBFT_nodeDeq minBFT_context0

type view =
  int
  (* singleton inductive, whose constructor was view *)

(** val minBFT_I_Key : minBFT_context -> key **)

let minBFT_I_Key _ =
  MkKey

type compNameKind = char list

type compNameSpace = int

(** val compNameKindDeq : compNameKind deq **)

let compNameKindDeq =
  string_dec

type compName = { comp_name_kind : compNameKind;
                  comp_name_space : compNameSpace;
                  comp_name_trust : bool }

(** val comp_name_kind : compName -> compNameKind **)

let comp_name_kind x = x.comp_name_kind

(** val comp_name_trust : compName -> bool **)

let comp_name_trust x = x.comp_name_trust

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

(** val cio_default_O : componentIO -> cio_O **)

let cio_default_O c0 =
  c0

(** val cIOmsg : node -> msg -> dTimeContext -> componentIO **)

let cIOmsg _ _ _ =
  Obj.magic []

(** val cIOtrusted : iOTrusted -> componentIO **)

let cIOtrusted =
  iot_def_output

(** val cIOdef : componentIO **)

let cIOdef =
  Obj.magic ()

type baseFunIO =
  compName -> componentIO
  (* singleton inductive, whose constructor was MkBaseFunIO *)

(** val bfio : baseFunIO -> compName -> componentIO **)

let bfio baseFunIO0 =
  baseFunIO0

type baseStateFun =
| MkBaseStateFun

type trustedStateFun =
| MkTrustedStateFun

type funIO =
  compName -> componentIO
  (* singleton inductive, whose constructor was MkFunIO *)

(** val fio : funIO -> compName -> componentIO **)

let fio funIO0 =
  funIO0

type sf = __

(** val msg_comp_name_kind : compNameKind **)

let msg_comp_name_kind =
  'M'::('S'::('G'::[]))

(** val msg_comp_name_trust : bool **)

let msg_comp_name_trust =
  false

(** val msg_comp_name : compNameSpace -> compName **)

let msg_comp_name n0 =
  { comp_name_kind = msg_comp_name_kind; comp_name_space = n0;
    comp_name_trust = msg_comp_name_trust }

(** val unit_comp_name_kind : compNameKind **)

let unit_comp_name_kind =
  'U'::('N'::('I'::('T'::[])))

(** val munit_comp_name : compName **)

let munit_comp_name =
  msg_comp_name (Pervasives.succ 0)

(** val funIOd_msg_nm :
    node -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    compName -> componentIO **)

let funIOd_msg_nm pn pm dtc iot base_fun_io nm =
  if nm.comp_name_trust
  then cIOtrusted iot
  else if compNameKindDeq nm.comp_name_kind msg_comp_name_kind
       then cIOmsg pn pm dtc
       else if compNameKindDeq nm.comp_name_kind
                 unit_comp_name_kind
            then cIOdef
            else bfio base_fun_io nm

(** val funIOd_msg :
    node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> funIO **)

let funIOd_msg =
  funIOd_msg_nm

type 'p mP_StateMachine = { sm_halted0 : bool;
                            sm_update0 : ('p, cio_I, cio_O, sf)
                                         mP_Update; sm_state0 : 
                            sf }

type m_StateMachine = __

type n_proc = m_StateMachine

type n_nproc = n_proc p_nproc

type n_procs = n_nproc list

type n_proc_at = m_StateMachine mP_StateMachine

(** val mP_haltedSM :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO
    -> baseStateFun -> trustedStateFun -> compName -> int -> sf ->
    n_proc mP_StateMachine **)

let mP_haltedSM pn _ pm dtc iot base_fun_io _ _ nm _ d =
  { sm_halted0 = true; sm_update0 = (fun _ _ p -> (p, (None,
    (cio_default_O (fio (funIOd_msg pn pm dtc iot base_fun_io) nm)))));
    sm_state0 = d }

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

(** val minBFT_I_Msg : minBFT_context -> msg **)

let minBFT_I_Msg _ =
  MkMsg

type uSIG_output_interface =
| Create_ui_out of uI
| Verify_ui_out of bool
| Verify_ui_out_def

(** val cIOusig : minBFT_context -> componentIO **)

let cIOusig _ =
  Obj.magic Verify_ui_out_def

(** val cIOlog : minBFT_context -> componentIO **)

let cIOlog _ =
  Obj.magic true

(** val minBFT_I_baseFunIO : minBFT_context -> baseFunIO **)

let minBFT_I_baseFunIO minbft_context nm =
  if compNameKindDeq nm.comp_name_kind
       ('U'::('S'::('I'::('G'::[]))))
  then cIOusig minbft_context
  else if compNameKindDeq nm.comp_name_kind ('L'::('O'::('G'::[])))
       then cIOlog minbft_context
       else cIOdef

(** val minBFT_I_baseStateFun : minBFT_context -> baseStateFun **)

let minBFT_I_baseStateFun _ =
  MkBaseStateFun

(** val minBFT_I_IOTrusted : minBFT_context -> iOTrusted **)

let minBFT_I_IOTrusted _ =
  Obj.magic Verify_ui_out_def

(** val minBFT_I_trustedStateFun :
    minBFT_context -> trustedStateFun **)

let minBFT_I_trustedStateFun _ =
  MkTrustedStateFun

(** val minBFTfunLevelSpace : minBFT_context -> funLevelSpace **)

let minBFTfunLevelSpace _ =
  { fls_level = (fun n0 ->
    match Obj.magic n0 with
    | MinBFT_replica _ -> Pervasives.succ 0
    | MinBFT_client _ -> 0); fls_space = (fun n0 ->
    match Obj.magic n0 with
    | MinBFT_replica _ -> 0
    | MinBFT_client _ -> Pervasives.succ 0) }

type time_type = __

type timedDirectedMsg = { tdm_dmsg : directedMsg;
                          tdm_time : time_type }

type timedDirectedMsgs = timedDirectedMsg list

type simState = { ss_fls : funLevelSpace; ss_sys : m_USystem;
                  ss_step : int; ss_out_inflight : directedMsgs;
                  ss_in_inflight : directedMsgs;
                  ss_delivered : timedDirectedMsgs }

type minbft_digest = int list

(** val minbft_digest_deq : minbft_digest deq **)

let minbft_digest_deq x y =
  list_eq_dec (=) x y

(** val nreps : int -> int **)

let nreps f1 =
  add (mul (Pervasives.succ (Pervasives.succ 0)) f1)
    (Pervasives.succ 0)

type replica = nat_n

(** val replica_deq : int -> replica deq **)

let replica_deq f1 =
  nat_n_deq (nreps f1)

(** val reps2nat0 : int -> replica -> nat_n **)

let reps2nat0 _ n0 =
  n0

(** val bijective_reps2nat : int -> (replica, nat_n) bijective **)

let bijective_reps2nat _ n0 =
  n0

(** val nclients : int -> int **)

let nclients c0 =
  Pervasives.succ c0

type client0 = nat_n

(** val client_deq0 : int -> client0 deq **)

let client_deq0 c0 =
  nat_n_deq (nclients c0)

(** val clients2nat0 : int -> client0 -> nat_n **)

let clients2nat0 _ n0 =
  n0

(** val bijective_clients2nat :
    int -> (client0, nat_n) bijective **)

let bijective_clients2nat _ n0 =
  n0

type minbft_data_message =
| Minbft_data_message_plus of int
| Minbft_data_message_minus of int

(** val minbft_data_message_deq : minbft_data_message deq **)

let minbft_data_message_deq x y =
  match x with
  | Minbft_data_message_plus x0 ->
    (match y with
     | Minbft_data_message_plus y0 -> (=) x0 y0
     | Minbft_data_message_minus _ -> false)
  | Minbft_data_message_minus x0 ->
    (match y with
     | Minbft_data_message_plus _ -> false
     | Minbft_data_message_minus y0 -> (=) x0 y0)

type minbft_result = int

(** val minbft_result_deq : minbft_result deq **)

let minbft_result_deq =
  (=)

type minbft_sm_state = int

(** val minbft_sm_initial_state : minbft_sm_state **)

let minbft_sm_initial_state =
  0

(** val minbft_sm_update :
    int -> client0 -> minbft_sm_state -> minbft_data_message ->
    minbft_result * minbft_sm_state **)

let minbft_sm_update _ _ s = function
| Minbft_data_message_plus n0 -> let x = add s n0 in (x, x)
| Minbft_data_message_minus n0 -> let x = sub s n0 in (x, x)

(** val f0 : int **)

let f0 =
  Pervasives.succ 0

(** val c : int **)

let c =
  0

(** val minBFT_I_context : minBFT_context **)

let minBFT_I_context =
  { minBFT_digestdeq = (Obj.magic minbft_digest_deq); f = f0;
    rep_deq = (Obj.magic replica_deq f0); reps2nat =
    (Obj.magic reps2nat0 f0); reps_bij =
    (Obj.magic bijective_reps2nat f0); num_clients = (nclients c);
    client_deq = (Obj.magic client_deq0 c); clients2nat =
    (Obj.magic clients2nat0 c); clients_bij =
    (Obj.magic bijective_clients2nat c); minBFT_data_message_deq =
    (Obj.magic minbft_data_message_deq); minBFT_resdeq =
    (Obj.magic minbft_result_deq); minBFT_sm_initial_state =
    (Obj.magic minbft_sm_initial_state); minBFT_sm_update =
    (Obj.magic minbft_sm_update c) }

(** val tokens2string : tokens -> char list **)

let tokens2string _ =
  '-'::[]

(** val minbft_digest2string : minbft_digest -> char list **)

let minbft_digest2string _ =
  '-'::[]

(** val client2string : client0 -> char list **)

let client2string _ =
  '-'::[]

(** val timestamp2string : timestamp -> char list **)

let timestamp2string =
  Prelude.char_list_of_int

(** val view2string : view -> char list **)

let view2string =
  Prelude.char_list_of_int

(** val str_concat : char list list -> char list **)

let rec str_concat = function
| [] -> []
| s :: ss -> append s (str_concat ss)

(** val minbft_data_message2string :
    minbft_data_message -> char list **)

let minbft_data_message2string = function
| Minbft_data_message_plus n0 ->
  str_concat (('+'::[]) :: ((Prelude.char_list_of_int n0) :: []))
| Minbft_data_message_minus n0 ->
  str_concat (('-'::[]) :: ((Prelude.char_list_of_int n0) :: []))

(** val nat_n2string : int -> nat_n -> char list **)

let nat_n2string _ =
  Prelude.char_list_of_int

(** val replica2string : replica -> char list **)

let replica2string r =
  nat_n2string (nreps f0) r

(** val bare_request2string : bare_Request -> char list **)

let bare_request2string br =
  let { bare_request_c = c0; bare_request_t = ts; bare_request_m =
    m } = br
  in
  str_concat
    ((client2string (Obj.magic c0)) :: ((','::[]) :: ((timestamp2string
                                                        ts) :: ((','::[]) :: (
    (minbft_data_message2string (Obj.magic m)) :: [])))))

(** val request2string : request -> char list **)

let request2string r =
  let { request_b = br; request_a = a } = r in
  str_concat
    (('R'::('E'::('Q'::('U'::('E'::('S'::('T'::('('::[])))))))) :: (
    (bare_request2string br) :: ((','::[]) :: ((tokens2string a) :: ((')'::[]) :: [])))))

(** val bare_prepare2string : bare_Prepare -> char list **)

let bare_prepare2string bp =
  let { bare_prepare_v = v; bare_prepare_m = m } = bp in
  str_concat
    ((view2string v) :: ((','::[]) :: ((request2string m) :: [])))

(** val pre_ui2string : preUI -> char list **)

let pre_ui2string pui =
  let { pre_ui_id = id; pre_ui_counter = counter } = pui in
  str_concat
    ((replica2string (Obj.magic id)) :: ((','::[]) :: ((Prelude.char_list_of_int
                                                         counter) :: [])))

(** val ui2string : uI -> char list **)

let ui2string ui =
  let { ui_pre = pui; ui_digest = d } = ui in
  str_concat
    ((pre_ui2string pui) :: ((','::[]) :: ((minbft_digest2string
                                             (Obj.magic d)) :: [])))

(** val bare_commit2string : bare_Commit -> char list **)

let bare_commit2string bc =
  let { bare_commit_v = v; bare_commit_m = m; bare_commit_ui =
    ui } = bc
  in
  str_concat
    ((view2string v) :: ((','::[]) :: ((request2string m) :: ((','::[]) :: (
    (ui2string ui) :: [])))))

(** val prepare2string : prepare -> char list **)

let prepare2string p =
  let { prepare_b = bp; prepare_ui = a } = p in
  str_concat
    (('P'::('R'::('E'::('P'::('A'::('R'::('E'::('('::[])))))))) :: (
    (bare_prepare2string bp) :: ((','::[]) :: ((ui2string a) :: ((')'::[]) :: [])))))

(** val commit2string : commit -> char list **)

let commit2string c0 =
  let { commit_b = bc; commit_uj = a } = c0 in
  str_concat
    (('C'::('O'::('M'::('M'::('I'::('T'::('('::[]))))))) :: (
    (bare_commit2string bc) :: ((','::[]) :: ((ui2string a) :: ((')'::[]) :: [])))))

(** val accept2string : accept -> char list **)

let accept2string r =
  let { accept_r = r0; accept_c = c0 } = r in
  str_concat
    (('A'::('C'::('C'::('E'::('P'::('T'::('('::[]))))))) :: (
    (request2string r0) :: ((','::[]) :: ((Prelude.char_list_of_int
                                            c0) :: ((')'::[]) :: [])))))

(** val msg2string : minBFT_msg -> char list **)

let msg2string = function
| MinBFT_request r -> request2string r
| MinBFT_prepare p -> prepare2string p
| MinBFT_commit c0 -> commit2string c0
| MinBFT_accept a -> accept2string a
| MinBFT_debug s -> s

(** val name2string : name -> char list **)

let name2string n0 =
  match Obj.magic n0 with
  | MinBFT_replica r -> replica2string (Obj.magic r)
  | MinBFT_client c0 -> client2string (Obj.magic c0)

(** val names2string : name list -> char list **)

let rec names2string = function
| [] -> []
| n0 :: ns ->
  (match ns with
   | [] -> name2string n0
   | _ :: _ ->
     str_concat
       ((name2string n0) :: ((','::[]) :: ((names2string ns) :: []))))

(** val z2string : z -> char list **)

let z2string _ =
  []

(** val pos2string : positive -> char list **)

let pos2string _ =
  []

(** val q2string : q -> char list **)

let q2string q0 =
  str_concat
    (('('::[]) :: ((z2string q0.qnum) :: (('/'::[]) :: ((pos2string
                                                         q0.qden) :: ((')'::[]) :: [])))))

(** val posdtime2string : posDTime -> char list **)

let posdtime2string p =
  q2string (Obj.magic pos_dt_t dTimeContextQ p)

(** val directedMsg2string : directedMsg -> char list **)

let directedMsg2string dm =
  let { dmMsg = msg1; dmDst = dst; dmDelay = delay } = dm in
  str_concat
    ((msg2string (Obj.magic msg1)) :: ((':'::[]) :: (('['::[]) :: (
    (names2string dst) :: ((']'::[]) :: ((':'::[]) :: ((posdtime2string
                                                         delay) :: [])))))))

(** val directedMsgs2string : directedMsgs -> char list **)

let rec directedMsgs2string = function
| [] -> []
| dm :: dmsgs ->
  (match dmsgs with
   | [] -> directedMsg2string dm
   | _ :: _ ->
     str_concat
       ((directedMsg2string dm) :: (['\n'] :: ((directedMsgs2string
                                                 dmsgs) :: []))))

(** val timedDirectedMsg2string : timedDirectedMsg -> char list **)

let timedDirectedMsg2string m =
  let { tdm_dmsg = dm; tdm_time = time } = m in
  str_concat
    ((directedMsg2string dm) :: ((':'::[]) :: ((Prelude.Time.time2string
                                                 (Obj.magic time)) :: [])))

(** val timedDirectedMsgs2string :
    timedDirectedMsgs -> char list **)

let rec timedDirectedMsgs2string = function
| [] -> []
| dm :: dmsgs ->
  (match dmsgs with
   | [] -> timedDirectedMsg2string dm
   | _ :: _ ->
     str_concat
       ((timedDirectedMsg2string dm) :: (['\n'] :: ((timedDirectedMsgs2string
                                                      dmsgs) :: []))))

(** val simState2string : simState -> char list **)

let simState2string s =
  let { ss_fls = _; ss_sys = _; ss_step = step; ss_out_inflight =
    out_inflight; ss_in_inflight = in_inflight; ss_delivered =
    delivered } = s
  in
  str_concat
    (['\n'] :: (('='::('='::('='::('='::('='::('='::(' '::('S'::('T'::('E'::('P'::(' '::('='::('='::('='::('='::('='::('='::[])))))))))))))))))) :: (['\n'] :: (
    (Prelude.char_list_of_int step) :: (['\n'] :: (('='::('='::('='::('='::('='::('='::(' '::('I'::('N'::(' '::('F'::('L'::('I'::('G'::('H'::('T'::(' '::('('::('f'::('r'::('o'::('m'::(' '::('o'::('u'::('t'::('s'::('i'::('d'::('e'::(' '::('t'::('h'::('e'::(' '::('s'::('y'::('s'::('t'::('e'::('m'::(')'::(' '::('='::('='::('='::('='::('='::('='::[]))))))))))))))))))))))))))))))))))))))))))))))))) :: (['\n'] :: (
    (directedMsgs2string out_inflight) :: (['\n'] :: (('='::('='::('='::('='::('='::('='::(' '::('I'::('N'::(' '::('F'::('L'::('I'::('G'::('H'::('T'::(' '::('('::('f'::('r'::('o'::('m'::(' '::('i'::('n'::('s'::('i'::('d'::('e'::(' '::('t'::('h'::('e'::(' '::('s'::('y'::('s'::('t'::('e'::('m'::(')'::(' '::('='::('='::('='::('='::('='::('='::[])))))))))))))))))))))))))))))))))))))))))))))))) :: (['\n'] :: (
    (directedMsgs2string in_inflight) :: (['\n'] :: (('='::('='::('='::('='::('='::('='::(' '::('D'::('E'::('L'::('I'::('V'::('E'::('R'::('E'::('D'::(' '::('='::('='::('='::('='::('='::('='::[]))))))))))))))))))))))) :: (['\n'] :: (
    (timedDirectedMsgs2string delivered) :: (['\n'] :: [])))))))))))))))))

(** val dummy_LocalSystem : localSystem **)

let dummy_LocalSystem =
  { ls_main =
    (mP_haltedSM (minBFT_I_Node minBFT_I_context)
      (minBFT_I_Key minBFT_I_context)
      (minBFT_I_Msg minBFT_I_context) dTimeContextQ
      (minBFT_I_IOTrusted minBFT_I_context)
      (minBFT_I_baseFunIO minBFT_I_context)
      (minBFT_I_baseStateFun minBFT_I_context)
      (minBFT_I_trustedStateFun minBFT_I_context) munit_comp_name
      0 (Obj.magic ())); ls_subs = [] }

(** val local_replica : minBFT_context -> funLevelSpace **)

let local_replica =
  minBFTfunLevelSpace
