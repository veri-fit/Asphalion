
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(* False : logical inductive *)
(* with constructors :  *)


(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f1 = function
| Some a -> Some (f1 a)
| None -> None

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

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
  (** val sub : int -> int -> int **)

  let rec sub n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val ltb : int -> int -> bool **)

  let ltb n0 m =
    (<=) (Pervasives.succ n0) m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q0 u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q0, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Pervasives.succ q0) y)
        (fun u' -> divmod x' y q0 u')
        u)
      x
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
    | XH -> (match y with
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

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

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

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Pervasives.succ 0)

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

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 -> let s = h y a in if s then true else in_dec h a l0

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a0 :: l1 -> if eq_dec0 y a0 then list_eq_dec eq_dec0 l0 l1 else false)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Pervasives.succ start) len0))
    len

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
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val abs_nat : z -> int **)

  let abs_nat = function
  | Z0 -> 0
  | Zpos p -> Pos.to_nat p
  | Zneg p -> Pos.to_nat p

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
    | Zpos x0 -> (match y with
                  | Zpos p0 -> Pos.eq_dec x0 p0
                  | _ -> false)
    | Zneg x0 -> (match y with
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
  Z.eq_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Pos.mul x.qden y.qden) }

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
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

type 't deceq = bool

type 't deq = 't -> 't -> 't deceq

type ('a, 'b) cast = 'a -> 'b

(** val cast0 : ('a1, 'a2) cast -> 'a1 -> 'a2 **)

let cast0 cast1 =
  cast1

type dTimeContext = { dt_0 : __; dt_1 : __; dt_add : (__ -> __ -> __);
                      dt_mul : (__ -> __ -> __); dt_sub : (__ -> __ -> __);
                      dt_opp : (__ -> __); dt_nat_inj : (int -> __);
                      dt_approx : (__ -> int);
                      dt_lt_le_dec : (__ -> __ -> bool);
                      dt_eq_dec : (__ -> __ -> bool) }

type dt_T = __

(** val dt_nat_inj : dTimeContext -> int -> dt_T **)

let dt_nat_inj x = x.dt_nat_inj

type posDTime =
  dt_T
  (* singleton inductive, whose constructor was MkPosDTime *)

(** val pos_dt_t : dTimeContext -> posDTime -> dt_T **)

let pos_dt_t _ p =
  p

(** val nat2pdt : dTimeContext -> int -> posDTime **)

let nat2pdt =
  dt_nat_inj

(** val n2t : dTimeContext -> (int, posDTime) cast **)

let n2t =
  dt_nat_inj

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

(** val q_dt_approx : q -> int **)

let q_dt_approx x =
  Z.abs_nat x.qnum

(** val dTimeContextQ : dTimeContext **)

let dTimeContextQ =
  { dt_0 = (Obj.magic q_dt_0); dt_1 = (Obj.magic q_dt_1); dt_add =
    (Obj.magic q_dt_add); dt_mul = (Obj.magic q_dt_mul); dt_sub =
    (Obj.magic q_dt_sub); dt_opp = (Obj.magic q_dt_opp); dt_nat_inj =
    (Obj.magic q_dt_nat_inj); dt_approx = (Obj.magic q_dt_approx);
    dt_lt_le_dec = (Obj.magic q_dt_lt_le_dec); dt_eq_dec =
    (Obj.magic q_dt_eq_dec) }

(** val remove_elt : 'a1 deq -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove_elt dec z0 = function
| [] -> []
| x :: xs ->
  if dec z0 x then remove_elt dec z0 xs else x :: (remove_elt dec z0 xs)

(** val nullb : 'a1 list -> bool **)

let nullb = function
| [] -> true
| _ :: _ -> false

(** val mapOption : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list **)

let rec mapOption f1 = function
| [] -> []
| x :: xs ->
  (match f1 x with
   | Some y -> y :: (mapOption f1 xs)
   | None -> mapOption f1 xs)

(** val mapin : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list **)

let rec mapin l x =
  match l with
  | [] -> []
  | x0 :: xs -> (x x0 __) :: (mapin xs (fun a _ -> x a __))

(** val decomp_nth :
    'a1 list -> int -> (('a1 list * 'a1) * 'a1 list) option **)

let rec decomp_nth l n0 =
  match l with
  | [] -> None
  | x :: xs ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Some (([], x), xs))
       (fun n1 ->
       match decomp_nth xs n1 with
       | Some p ->
         let (p0, fseg) = p in
         let (iseg, elt) = p0 in Some (((x :: iseg), elt), fseg)
       | None -> None)
       n0)

type node = __ deq
  (* singleton inductive, whose constructor was MkNode *)

type name = __

(** val name_dec : node -> name deq **)

let name_dec node0 =
  node0

type nat_n = int

type ('a, 'b) bijective =
  'b -> 'a
  (* singleton inductive, whose constructor was Build_bijective *)

(** val bij_inv : ('a1 -> 'a2) -> ('a1, 'a2) bijective -> 'a2 -> 'a1 **)

let bij_inv _ b =
  b

(** val nat_n_deq : int -> nat_n deq **)

let nat_n_deq _ =
  (=)

type quorum_context = { num_nodes : int; node_deq : __ deq;
                        node2nat : (__ -> nat_n);
                        node_bij : (__, nat_n) bijective;
                        node2name : (__ -> name);
                        name2node : (name -> __ option) }

type node_type = __

(** val num_nodes : node -> quorum_context -> int **)

let num_nodes _ x = x.num_nodes

(** val node2nat : node -> quorum_context -> node_type -> nat_n **)

let node2nat _ x = x.node2nat

(** val node_bij : node -> quorum_context -> (node_type, nat_n) bijective **)

let node_bij _ x = x.node_bij

(** val mk_nat_n : int -> int -> nat_n **)

let mk_nat_n x _ =
  x

(** val nodes : node -> quorum_context -> node_type list **)

let nodes _ quorum_context0 =
  mapin (seq 0 quorum_context0.num_nodes) (fun n0 _ ->
    bij_inv quorum_context0.node2nat quorum_context0.node_bij
      (mk_nat_n n0 quorum_context0.num_nodes))

type msg =
| MkMsg

type msg0 = __

type directedMsg = { dmMsg : msg0; dmDst : name list; dmDelay : posDTime }

(** val dmMsg : node -> dTimeContext -> msg -> directedMsg -> msg0 **)

let dmMsg _ _ _ x = x.dmMsg

(** val dmDst : node -> dTimeContext -> msg -> directedMsg -> name list **)

let dmDst _ _ _ x = x.dmDst

(** val dmDelay : node -> dTimeContext -> msg -> directedMsg -> posDTime **)

let dmDelay _ _ _ x = x.dmDelay

type directedMsgs = directedMsg list

type key =
| MkKey

type sending_key = __

type receiving_key = __

type sending_keys = sending_key list

type receiving_keys = receiving_key list

type dSKey = { dsk_dst : name list; dsk_key : sending_key }

(** val dsk_key : node -> key -> dSKey -> sending_key **)

let dsk_key _ _ x = x.dsk_key

type dRKey = { drk_dst : name list; drk_key : receiving_key }

(** val drk_dst : node -> key -> dRKey -> name list **)

let drk_dst _ _ x = x.drk_dst

(** val drk_key : node -> key -> dRKey -> receiving_key **)

let drk_key _ _ x = x.drk_key

type local_key_map = { lkm_sending_keys : dSKey list;
                       lkm_receiving_keys : dRKey list }

(** val lkm_sending_keys : node -> key -> local_key_map -> dSKey list **)

let lkm_sending_keys _ _ x = x.lkm_sending_keys

(** val lkm_receiving_keys : node -> key -> local_key_map -> dRKey list **)

let lkm_receiving_keys _ _ x = x.lkm_receiving_keys

type key_map = name -> local_key_map

(** val lookup_drkeys : node -> key -> local_key_map -> name -> dRKey list **)

let lookup_drkeys n0 _ km h =
  List.filter (fun dk ->
    if in_dec (name_dec n0) h dk.drk_dst then true else false)
    km.lkm_receiving_keys

(** val lookup_receiving_keys :
    node -> key -> local_key_map -> name -> receiving_key list **)

let lookup_receiving_keys n0 pk km h =
  List.map (drk_key n0 pk) (lookup_drkeys n0 pk km h)

type authTok =
  __ deq
  (* singleton inductive, whose constructor was MkAuthTok *)

type token = __

(** val token_dec : authTok -> token deq **)

let token_dec authTok0 =
  authTok0

type tokens = token list

(** val tokens_dec : authTok -> tokens deq **)

let tokens_dec authtok x y =
  list_eq_dec (token_dec authtok) x y

type data =
| MkData

type data0 = __

type authFun = { create : (data0 -> sending_keys -> tokens);
                 verify : (data0 -> name -> receiving_key -> token -> bool) }

(** val create :
    node -> key -> authTok -> data -> authFun -> data0 -> sending_keys ->
    tokens **)

let create _ _ _ _ x = x.create

(** val verify :
    node -> key -> authTok -> data -> authFun -> data0 -> name ->
    receiving_key -> token -> bool **)

let verify _ _ _ _ x = x.verify

(** val authenticate :
    node -> key -> authTok -> data -> authFun -> data0 -> local_key_map ->
    tokens **)

let authenticate n0 pk _ _ authfun d km =
  authfun.create d (List.map (dsk_key n0 pk) km.lkm_sending_keys)

type authenticatedData = { am_data : data0; am_auth : tokens }

(** val am_data : authTok -> data -> authenticatedData -> data0 **)

let am_data _ _ x = x.am_data

(** val am_auth : authTok -> data -> authenticatedData -> tokens **)

let am_auth _ _ x = x.am_auth

type dataAuth =
  name -> data0 -> name option
  (* singleton inductive, whose constructor was MkDataAuth *)

(** val data_auth :
    data -> node -> dataAuth -> name -> data0 -> name option **)

let data_auth _ _ dataAuth0 =
  dataAuth0

(** val verify_authenticated_data_key :
    data -> key -> node -> authTok -> authFun -> name -> authenticatedData ->
    receiving_key -> bool **)

let verify_authenticated_data_key _ _ _ _ paf n0 m k =
  List.exists (fun token0 -> paf.verify m.am_data n0 k token0) m.am_auth

(** val verify_authenticated_data_keys :
    data -> key -> node -> authTok -> authFun -> name -> authenticatedData ->
    receiving_keys -> bool **)

let verify_authenticated_data_keys pd pk pn pat paf n0 m ks =
  List.exists (verify_authenticated_data_key pd pk pn pat paf n0 m) ks

(** val verify_authenticated_data :
    data -> key -> node -> authTok -> authFun -> dataAuth -> name ->
    authenticatedData -> local_key_map -> bool **)

let verify_authenticated_data pd pk pn pat paf pda slf m keys =
  match data_auth pd pn pda slf m.am_data with
  | Some name0 ->
    verify_authenticated_data_keys pd pk pn pat paf name0 m
      (lookup_receiving_keys pn pk keys name0)
  | None -> false

type iOTrusted =
  __
  (* singleton inductive, whose constructor was Build_IOTrusted *)

type iot_output = __

(** val iot_def_output : iOTrusted -> iot_output **)

let iot_def_output iOTrusted0 =
  iOTrusted0

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

(** val minBFT_digestdeq : minBFT_context -> minBFT_digest deq **)

let minBFT_digestdeq x = x.minBFT_digestdeq

(** val f : minBFT_context -> int **)

let f x = x.f

(** val num_replicas : minBFT_context -> int **)

let num_replicas minBFT_context0 =
  add (mul (Pervasives.succ (Pervasives.succ 0)) minBFT_context0.f)
    (Pervasives.succ 0)

type rep = __

(** val rep_deq : minBFT_context -> rep deq **)

let rep_deq x = x.rep_deq

(** val reps2nat : minBFT_context -> rep -> nat_n **)

let reps2nat x = x.reps2nat

(** val reps_bij : minBFT_context -> (rep, nat_n) bijective **)

let reps_bij x = x.reps_bij

(** val num_clients : minBFT_context -> int **)

let num_clients x = x.num_clients

type client = __

(** val client_deq : minBFT_context -> client deq **)

let client_deq x = x.client_deq

(** val clients2nat : minBFT_context -> client -> nat_n **)

let clients2nat x = x.clients2nat

(** val clients_bij : minBFT_context -> (client, nat_n) bijective **)

let clients_bij x = x.clients_bij

type minBFT_data_message = __

(** val minBFT_data_message_deq :
    minBFT_context -> minBFT_data_message deq **)

let minBFT_data_message_deq x = x.minBFT_data_message_deq

type minBFT_result = __

type minBFT_sm_state = __

(** val minBFT_sm_initial_state : minBFT_context -> minBFT_sm_state **)

let minBFT_sm_initial_state x = x.minBFT_sm_initial_state

(** val minBFT_sm_update :
    minBFT_context -> client -> minBFT_sm_state -> minBFT_data_message ->
    minBFT_result * minBFT_sm_state **)

let minBFT_sm_update x = x.minBFT_sm_update

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

(** val name2rep : minBFT_context -> name -> rep option **)

let name2rep _ n0 =
  match Obj.magic n0 with
  | MinBFT_replica n1 -> Some n1
  | MinBFT_client _ -> None

(** val minBFT_I_Quorum : minBFT_context -> quorum_context **)

let minBFT_I_Quorum minBFT_context0 =
  { num_nodes = (num_replicas minBFT_context0); node_deq =
    minBFT_context0.rep_deq; node2nat = minBFT_context0.reps2nat; node_bij =
    minBFT_context0.reps_bij; node2name =
    (Obj.magic (fun x -> MinBFT_replica x)); name2node =
    (name2rep minBFT_context0) }

(** val nat_n_Fp1_0 : minBFT_context -> nat_n **)

let nat_n_Fp1_0 _ =
  0

(** val replica0 : minBFT_context -> rep **)

let replica0 minBFT_context0 =
  bij_inv minBFT_context0.reps2nat minBFT_context0.reps_bij
    (nat_n_Fp1_0 minBFT_context0)

(** val nat2rep : minBFT_context -> int -> rep **)

let nat2rep minBFT_context0 n0 =
  let b = minBFT_context0.reps_bij in
  let s = (<) n0 (num_replicas minBFT_context0) in
  if s
  then b (mk_nat_n n0 (num_replicas minBFT_context0))
  else replica0 minBFT_context0

(** val reps : minBFT_context -> rep list **)

let reps minBFT_context0 =
  nodes (minBFT_I_Node minBFT_context0) (minBFT_I_Quorum minBFT_context0)

(** val clients : minBFT_context -> client list **)

let clients minBFT_context0 =
  mapin (seq 0 minBFT_context0.num_clients) (fun n0 _ ->
    bij_inv minBFT_context0.clients2nat minBFT_context0.clients_bij
      (mk_nat_n n0 minBFT_context0.num_clients))

type view = int
  (* singleton inductive, whose constructor was view *)

(** val view2nat : view -> int **)

let view2nat v =
  v

(** val viewDeq : view deq **)

let viewDeq =
  (=)

(** val initial_view : view **)

let initial_view =
  0

(** val minBFT_I_AuthTok : minBFT_context -> authTok **)

let minBFT_I_AuthTok =
  minBFT_digestdeq

(** val minBFT_I_Key : minBFT_context -> key **)

let minBFT_I_Key _ =
  MkKey

type minBFT_initial_keys =
  key_map
  (* singleton inductive, whose constructor was MkMinBFT_initial_keys *)

(** val initial_keys : minBFT_context -> minBFT_initial_keys -> key_map **)

let initial_keys _ minBFT_initial_keys0 =
  minBFT_initial_keys0

(** val minBFTprimary_nat : minBFT_context -> view -> int **)

let minBFTprimary_nat minBFT_context0 v =
  (mod) (view2nat v) (num_replicas minBFT_context0)

(** val minBFTprimary : minBFT_context -> view -> rep **)

let minBFTprimary minBFT_context0 v =
  nat2rep minBFT_context0 (minBFTprimary_nat minBFT_context0 v)

(** val is_primary : minBFT_context -> view -> rep -> bool **)

let is_primary minBFT_context0 v r =
  if minBFT_context0.rep_deq r (minBFTprimary minBFT_context0 v)
  then true
  else false

(** val not_primary : minBFT_context -> view -> rep -> bool **)

let not_primary minBFT_context0 v r =
  negb (is_primary minBFT_context0 v r)

type compNameKind = char list

type compNameSpace = int

(** val compNameKindDeq : compNameKind deq **)

let compNameKindDeq =
  string_dec

(** val compNameSpaceDeq : compNameSpace deq **)

let compNameSpaceDeq =
  (=)

type compName = { comp_name_kind : compNameKind;
                  comp_name_space : compNameSpace; comp_name_trust : 
                  bool }

(** val comp_name_kind : compName -> compNameKind **)

let comp_name_kind x = x.comp_name_kind

(** val comp_name_trust : compName -> bool **)

let comp_name_trust x = x.comp_name_trust

(** val compNameDeq : compName deq **)

let compNameDeq x y =
  let { comp_name_kind = n1; comp_name_space = s1; comp_name_trust = b1 } = x
  in
  let { comp_name_kind = n2; comp_name_space = s2; comp_name_trust = b2 } = y
  in
  let d = compNameKindDeq n1 n2 in
  if d
  then let d0 = compNameSpaceDeq s1 s2 in if d0 then bool_dec b1 b2 else false
  else false

type 'p p_nproc = { pp_name : compName; pp_proc : 'p }

type 'p p_procs = 'p p_nproc list

type ('p, 'pO) m_p = 'p p_procs -> 'p p_procs * 'pO

type ('p, 'i, 'o, 's) mP_Update = 's -> 'i -> ('p, 's option * 'o) m_p

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

(** val cIOnat : componentIO **)

let cIOnat =
  Obj.magic 0

(** val cIObool : componentIO **)

let cIObool =
  Obj.magic true

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

(** val nat_comp_name_kind : compNameKind **)

let nat_comp_name_kind =
  'N'::('A'::('T'::[]))

(** val bool_comp_name_kind : compNameKind **)

let bool_comp_name_kind =
  'B'::('O'::('O'::('L'::[])))

(** val munit_comp_name : compName **)

let munit_comp_name =
  msg_comp_name (Pervasives.succ 0)

(** val funIOd_msg_nm :
    node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> compName ->
    componentIO **)

let funIOd_msg_nm pn pm dtc iot base_fun_io nm =
  if nm.comp_name_trust
  then cIOtrusted iot
  else if compNameKindDeq nm.comp_name_kind msg_comp_name_kind
       then cIOmsg pn pm dtc
       else if compNameKindDeq nm.comp_name_kind unit_comp_name_kind
            then cIOdef
            else if compNameKindDeq nm.comp_name_kind nat_comp_name_kind
                 then cIOnat
                 else if compNameKindDeq nm.comp_name_kind bool_comp_name_kind
                      then cIObool
                      else bfio base_fun_io nm

(** val funIOd_msg :
    node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> funIO **)

let funIOd_msg =
  funIOd_msg_nm

type 'p mP_StateMachine = { sm_halted : bool;
                            sm_update : ('p, cio_I, cio_O, sf) mP_Update;
                            sm_state : sf }

(** val sm_halted :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> compName -> 'a1 mP_StateMachine -> bool **)

let sm_halted _ _ _ _ _ _ _ _ _ x = x.sm_halted

(** val sm_update :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> compName -> 'a1 mP_StateMachine ->
    ('a1, cio_I, cio_O, sf) mP_Update **)

let sm_update _ _ _ _ _ _ _ _ _ x = x.sm_update

(** val sm_state :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> compName -> 'a1 mP_StateMachine -> sf **)

let sm_state _ _ _ _ _ _ _ _ _ x = x.sm_state

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

(** val ret :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> 'a1 -> 'a1 m_n **)

let ret _ _ _ _ _ _ _ _ _ a s =
  (s, a)

(** val bind :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> 'a1 m_n -> ('a1 -> 'a2 m_n) ->
    'a2 m_n **)

let bind _ _ _ _ _ _ _ _ _ m f1 s =
  let (s1, a) = m s in f1 a s1

(** val bind_pair :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> ('a1 * 'a2) m_n -> ('a1 -> 'a2
    -> 'a3 m_n) -> 'a3 m_n **)

let bind_pair pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 m f1 =
  bind pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 m
    (fun p -> let (a, b) = p in f1 a b)

(** val find_name :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_procs -> n_proc
    option **)

let rec find_name pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 nm = function
| [] -> None
| n1 :: rest ->
  let { pp_name = m; pp_proc = pr } = n1 in
  if compNameDeq m nm
  then Some pr
  else find_name pn pk pm dtc iot base_fun_io base_state_fun
         trusted_state_fun n0 nm rest

(** val replace_name :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> n_procs
    -> n_procs **)

let rec replace_name pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 nm pr = function
| [] -> []
| n1 :: rest ->
  let { pp_name = m; pp_proc = q0 } = n1 in
  if compNameDeq m nm
  then { pp_name = nm; pp_proc = pr } :: rest
  else { pp_name = m; pp_proc =
         q0 } :: (replace_name pn pk pm dtc iot base_fun_io base_state_fun
                   trusted_state_fun n0 nm pr rest)

(** val at2sm :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_proc_at -> (__
    mP_StateMachine, __) sm_or **)

let at2sm _ _ _ _ _ _ _ _ _ _ p =
  Sm_or_at p

(** val mP_haltedSM :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> compName -> int -> sf -> n_proc_at **)

let mP_haltedSM pn _ pm dtc iot base_fun_io _ _ cn _ d =
  { sm_halted = true; sm_update = (fun _ _ p -> (p, (None,
    (cio_default_O (fio (funIOd_msg pn pm dtc iot base_fun_io) cn)))));
    sm_state = d }

(** val incr_n_proc :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> (__
    mP_StateMachine, __) sm_or **)

let incr_n_proc _ _ _ _ _ _ _ _ _ _ p =
  Sm_or_sm p

(** val decr_n_proc :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> n_proc
    option **)

let decr_n_proc _ _ _ _ _ _ _ _ n0 _ =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic (fun _ -> Some __))
    (fun _ p ->
    match Obj.magic p with
    | Sm_or_at _ -> None
    | Sm_or_sm q0 -> Some q0)
    n0

(** val decr_n_nproc :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> n_nproc -> n_nproc option **)

let decr_n_nproc pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 np =
  let { pp_name = m; pp_proc = p } = np in
  (match decr_n_proc pn pk pm dtc iot base_fun_io base_state_fun
           trusted_state_fun n0 m p with
   | Some q0 -> Some { pp_name = m; pp_proc = q0 }
   | None -> None)

(** val decr_n_procs :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> n_procs -> n_procs **)

let decr_n_procs pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 ps =
  mapOption
    (decr_n_nproc pn pk pm dtc iot base_fun_io base_state_fun
      trusted_state_fun n0) ps

(** val incr_pred_n_proc :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> n_proc **)

let incr_pred_n_proc _ _ _ _ _ _ _ _ n0 _ =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic __)
    (fun _ p -> Obj.magic (Sm_or_sm p))
    n0

(** val incr_pred_n_nproc :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> n_nproc -> n_nproc **)

let incr_pred_n_nproc pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 p =
  let { pp_name = m; pp_proc = q0 } = p in
  { pp_name = m; pp_proc =
  (incr_pred_n_proc pn pk pm dtc iot base_fun_io base_state_fun
    trusted_state_fun n0 m q0) }

(** val incr_pred_n_procs :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> n_procs -> n_procs **)

let incr_pred_n_procs pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 ps =
  List.map
    (incr_pred_n_nproc pn pk pm dtc iot base_fun_io base_state_fun
      trusted_state_fun n0) ps

(** val update_state :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_proc_at -> sf ->
    n_proc_at **)

let update_state _ _ _ _ _ _ _ _ _ _ sm s =
  { sm_halted = sm.sm_halted; sm_update = sm.sm_update; sm_state = s }

(** val halt_machine :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_proc_at ->
    n_proc_at **)

let halt_machine _ _ _ _ _ _ _ _ _ _ sm =
  { sm_halted = true; sm_update = sm.sm_update; sm_state = sm.sm_state }

(** val sm_s_to_sm :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_proc_at -> (sf
    option * cio_O) m_n -> (n_proc_at * cio_O) m_n **)

let sm_s_to_sm pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 nm sm x =
  bind_pair pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0
    x (fun ops o ->
    match ops with
    | Some s ->
      ret pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0
        ((update_state pn pk pm dtc iot base_fun_io base_state_fun
           trusted_state_fun n0 nm sm s), o)
    | None ->
      ret pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0
        ((halt_machine pn pk pm dtc iot base_fun_io base_state_fun
           trusted_state_fun n0 nm sm), o))

(** val lift_M_O :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> (n_proc_at * 'a1)
    m_n -> ((__ mP_StateMachine, __) sm_or * 'a1) m_n **)

let lift_M_O pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun m nm x =
  bind_pair pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun m x
    (fun q0 o ->
    ret pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun m
      ((at2sm pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun m
         nm q0), o))

(** val m_on_pred :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> 'a1 m_n -> 'a1 m_n **)

let m_on_pred pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 m ps =
  let (ps', o') =
    m
      (decr_n_procs pn pk pm dtc iot base_fun_io base_state_fun
        trusted_state_fun n0 ps)
  in
  ((incr_pred_n_procs pn pk pm dtc iot base_fun_io base_state_fun
     trusted_state_fun n0 ps'), o')

(** val lift_M_O2 :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> (n_proc * 'a1) m_n
    -> ((__ mP_StateMachine, __) sm_or * 'a1) m_n **)

let lift_M_O2 pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 nm m =
  bind_pair pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0
    (m_on_pred pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun
      n0 m) (fun sm o ->
    ret pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0
      ((incr_n_proc pn pk pm dtc iot base_fun_io base_state_fun
         trusted_state_fun n0 nm sm), o))

(** val app_m_proc :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_proc -> cio_I ->
    (n_proc * cio_O) m_n **)

let rec app_m_proc pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 nm =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    Obj.magic (fun _ _ -> assert true (* absurd case *)))
    (fun m pr i ->
    match Obj.magic pr with
    | Sm_or_at sm ->
      Obj.magic lift_M_O pn pk pm dtc iot base_fun_io base_state_fun
        trusted_state_fun m nm
        (sm_s_to_sm pn pk pm dtc iot base_fun_io base_state_fun
          trusted_state_fun m nm sm (sm.sm_update sm.sm_state i))
    | Sm_or_sm pr' ->
      Obj.magic lift_M_O2 pn pk pm dtc iot base_fun_io base_state_fun
        trusted_state_fun m nm
        (app_m_proc pn pk pm dtc iot base_fun_io base_state_fun
          trusted_state_fun m nm pr' i))
    n0

(** val replace_sub :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> n_procs -> n_proc
    -> n_procs **)

let rec replace_sub pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 nm ps p =
  match ps with
  | [] -> []
  | n1 :: rest ->
    let { pp_name = m; pp_proc = q0 } = n1 in
    if compNameDeq nm m
    then { pp_name = nm; pp_proc =
           (incr_pred_n_proc pn pk pm dtc iot base_fun_io base_state_fun
             trusted_state_fun n0 nm p) } :: rest
    else { pp_name = m; pp_proc =
           q0 } :: (replace_sub pn pk pm dtc iot base_fun_io base_state_fun
                     trusted_state_fun n0 nm rest p)

(** val replace_subs :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> n_procs -> n_procs -> n_procs **)

let rec replace_subs pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 ps = function
| [] -> ps
| p :: rest ->
  let { pp_name = nm; pp_proc = q0 } = p in
  replace_subs pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun
    n0
    (replace_sub pn pk pm dtc iot base_fun_io base_state_fun
      trusted_state_fun n0 nm ps q0) rest

(** val call_proc :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> cio_I -> cio_O m_n **)

let call_proc pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 nm i l =
  match find_name pn pk pm dtc iot base_fun_io base_state_fun
          trusted_state_fun n0 nm l with
  | Some pr ->
    let (l', p) =
      app_m_proc pn pk pm dtc iot base_fun_io base_state_fun
        trusted_state_fun n0 nm pr i
        (decr_n_procs pn pk pm dtc iot base_fun_io base_state_fun
          trusted_state_fun n0 l)
    in
    let (pr', o) = p in
    ((replace_subs pn pk pm dtc iot base_fun_io base_state_fun
       trusted_state_fun n0
       (replace_name pn pk pm dtc iot base_fun_io base_state_fun
         trusted_state_fun n0 nm pr' l) l'), o)
  | None ->
    (l, (cio_default_O (fio (funIOd_msg pn pm dtc iot base_fun_io) nm)))

(** val build_mp_sm :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> sf m_Update -> sf
    -> n_proc_at **)

let build_mp_sm _ _ _ _ _ _ _ _ _ _ upd s =
  { sm_halted = false; sm_update = upd; sm_state = s }

(** val build_m_sm :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> sf m_Update -> sf
    -> (__ mP_StateMachine, __) sm_or **)

let build_m_sm pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 nm upd s =
  at2sm pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 nm
    (build_mp_sm pn pk pm dtc iot base_fun_io base_state_fun
      trusted_state_fun n0 nm upd s)

type localSystem = { ls_main : n_proc_at; ls_subs : n_procs }

(** val ls_main :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> localSystem ->
    n_proc_at **)

let ls_main _ _ _ _ _ _ _ _ _ _ x = x.ls_main

(** val ls_subs :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> localSystem ->
    n_procs **)

let ls_subs _ _ _ _ _ _ _ _ _ _ x = x.ls_subs

type mLocalSystem = localSystem

(** val upd_ls_main_state_and_subs :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compName -> localSystem -> sf
    -> n_procs -> localSystem **)

let upd_ls_main_state_and_subs pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun l s ls s0 ss =
  { ls_main =
    (update_state pn pk pm dtc iot base_fun_io base_state_fun
      trusted_state_fun l s ls.ls_main s0); ls_subs = ss }

type funLevelSpace = { fls_level : (name -> int); fls_space : (name -> int) }

(** val fls_level : node -> funLevelSpace -> name -> int **)

let fls_level _ x = x.fls_level

(** val fls_space : node -> funLevelSpace -> name -> int **)

let fls_space _ x = x.fls_space

type m_USystem = name -> mLocalSystem

(** val m_break :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> 'a1 m_n -> n_procs -> (n_procs
    -> 'a1 -> 'a2) -> 'a2 **)

let m_break _ _ _ _ _ _ _ _ _ sm subs f1 =
  let (subs', out) = sm subs in f1 subs' out

type 'o proc =
| PROC_RET of 'o
| PROC_BIND of __ proc * (__ -> 'o proc)
| PROC_CALL of compName * cio_I

(** val proc_bind_pair :
    node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> ('a1 * 'a2) proc
    -> ('a1 -> 'a2 -> 'a3 proc) -> 'a3 proc **)

let proc_bind_pair _ _ _ _ _ m f1 =
  PROC_BIND ((Obj.magic m), (fun p -> let (a, b) = Obj.magic p in f1 a b))

(** val interp_proc :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> 'a1 proc -> 'a1 m_n **)

let rec interp_proc pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 = function
| PROC_RET f1 ->
  Obj.magic ret pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun
    n0 f1
| PROC_BIND (p0, q0) ->
  Obj.magic bind pn pk pm dtc iot base_fun_io base_state_fun
    trusted_state_fun n0
    (Obj.magic interp_proc pn pk pm dtc iot base_fun_io base_state_fun
      trusted_state_fun n0 p0) (fun a ->
    interp_proc pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun
      n0 (q0 a))
| PROC_CALL (cn, i) ->
  Obj.magic call_proc pn pk pm dtc iot base_fun_io base_state_fun
    trusted_state_fun n0 cn i

(** val to_proc_some_state :
    node -> msg -> dTimeContext -> iOTrusted -> baseFunIO -> ('a1 * 'a2) proc
    -> ('a1 option * 'a2) proc **)

let to_proc_some_state pn pm dtc iot base_fun_io m =
  proc_bind_pair pn pm dtc iot base_fun_io m (fun s o -> PROC_RET ((Some s),
    o))

(** val interp_s_proc :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> ('a1 * 'a2) proc -> ('a1
    option * 'a2) m_n **)

let interp_s_proc pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun n0 p =
  interp_proc pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun
    n0 (to_proc_some_state pn pm dtc iot base_fun_io p)

type 's uProc = 's -> cio_I -> ('s * cio_O) proc

(** val str_concat : char list list -> char list **)

let rec str_concat = function
| [] -> []
| s :: ss -> append s (str_concat ss)

(** val bool2string : bool -> char list **)

let bool2string = function
| true -> 't'::('r'::('u'::('e'::[])))
| false -> 'f'::('a'::('l'::('s'::('e'::[]))))

(** val nat2string : int -> char list **)

let nat2string n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> '0'::[])
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> '1'::[])
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> '2'::[])
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> '3'::[])
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> '4'::[])
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> '5'::[])
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> '6'::[])
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> '7'::[])
                  (fun n8 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> '8'::[])
                    (fun n9 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> '9'::[])
                      (fun n10 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> '1'::('0'::[]))
                        (fun n11 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> '1'::('1'::[]))
                          (fun n12 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> '1'::('2'::[]))
                            (fun _ -> '-'::[])
                            n12)
                          n11)
                        n10)
                      n9)
                    n8)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

(** val op2string : ('a1 -> char list) -> 'a1 option -> char list **)

let op2string f1 = function
| Some t ->
  str_concat
    (('S'::('o'::('m'::('e'::('('::[]))))) :: ((f1 t) :: ((')'::[]) :: [])))
| None -> 'N'::('o'::('n'::('e'::[])))

type uSIG_state = { usig_id : rep; usig_counter : int;
                    usig_local_keys : local_key_map }

(** val usig_id : minBFT_context -> uSIG_state -> rep **)

let usig_id _ x = x.usig_id

(** val usig_counter : minBFT_context -> uSIG_state -> int **)

let usig_counter _ x = x.usig_counter

(** val usig_local_keys : minBFT_context -> uSIG_state -> local_key_map **)

let usig_local_keys _ x = x.usig_local_keys

type preUI = { pre_ui_id : rep; pre_ui_counter : int }

(** val pre_ui_id : minBFT_context -> preUI -> rep **)

let pre_ui_id _ x = x.pre_ui_id

(** val pre_ui_counter : minBFT_context -> preUI -> int **)

let pre_ui_counter _ x = x.pre_ui_counter

type uI = { ui_pre : preUI; ui_digest : minBFT_digest }

(** val ui_pre : minBFT_context -> uI -> preUI **)

let ui_pre _ x = x.ui_pre

(** val ui_digest : minBFT_context -> uI -> minBFT_digest **)

let ui_digest _ x = x.ui_digest

type uIs = uI list

(** val ui2rep : minBFT_context -> uI -> rep **)

let ui2rep _ ui =
  ui.ui_pre.pre_ui_id

(** val ui2counter : minBFT_context -> uI -> int **)

let ui2counter _ ui =
  ui.ui_pre.pre_ui_counter

(** val ui2digest : minBFT_context -> uI -> minBFT_digest **)

let ui2digest _ ui =
  ui.ui_digest

type timestamp =
  int
  (* singleton inductive, whose constructor was time_stamp *)

(** val timestamp2nat : timestamp -> int **)

let timestamp2nat t =
  t

type bare_Request = { bare_request_c : client; bare_request_t : timestamp;
                      bare_request_m : minBFT_data_message }

type request = { request_b : bare_Request; request_a : tokens }

(** val request_b : minBFT_context -> request -> bare_Request **)

let request_b _ x = x.request_b

(** val request_a : minBFT_context -> request -> tokens **)

let request_a _ x = x.request_a

type bare_Reply = { bare_reply_r : request; bare_reply_result : int;
                    bare_reply_rep : rep; bare_reply_view : view }

(** val bare_reply_r : minBFT_context -> bare_Reply -> request **)

let bare_reply_r _ x = x.bare_reply_r

(** val bare_reply_rep : minBFT_context -> bare_Reply -> rep **)

let bare_reply_rep _ x = x.bare_reply_rep

type reply = { reply_b : bare_Reply; reply_a : tokens }

(** val reply_b : minBFT_context -> reply -> bare_Reply **)

let reply_b _ x = x.reply_b

type bare_Prepare = { bare_prepare_v : view; bare_prepare_m : request }

(** val bare_prepare_v : minBFT_context -> bare_Prepare -> view **)

let bare_prepare_v _ x = x.bare_prepare_v

(** val bare_prepare_m : minBFT_context -> bare_Prepare -> request **)

let bare_prepare_m _ x = x.bare_prepare_m

type prepare = { prepare_b : bare_Prepare; prepare_ui : uI }

(** val prepare_b : minBFT_context -> prepare -> bare_Prepare **)

let prepare_b _ x = x.prepare_b

(** val prepare_ui : minBFT_context -> prepare -> uI **)

let prepare_ui _ x = x.prepare_ui

type bare_Commit = { bare_commit_v : view; bare_commit_m : request;
                     bare_commit_ui : uI }

(** val bare_commit_v : minBFT_context -> bare_Commit -> view **)

let bare_commit_v _ x = x.bare_commit_v

(** val bare_commit_m : minBFT_context -> bare_Commit -> request **)

let bare_commit_m _ x = x.bare_commit_m

(** val bare_commit_ui : minBFT_context -> bare_Commit -> uI **)

let bare_commit_ui _ x = x.bare_commit_ui

type commit = { commit_b : bare_Commit; commit_uj : uI }

(** val commit_b : minBFT_context -> commit -> bare_Commit **)

let commit_b _ x = x.commit_b

(** val commit_uj : minBFT_context -> commit -> uI **)

let commit_uj _ x = x.commit_uj

type accept = { accept_r : request; accept_c : int }

(** val accept_r : minBFT_context -> accept -> request **)

let accept_r _ x = x.accept_r

(** val accept_c : minBFT_context -> accept -> int **)

let accept_c _ x = x.accept_c

(** val prepare2view : minBFT_context -> prepare -> view **)

let prepare2view _ p =
  p.prepare_b.bare_prepare_v

(** val commit2view : minBFT_context -> commit -> view **)

let commit2view _ c0 =
  c0.commit_b.bare_commit_v

(** val bare_request2timestamp :
    minBFT_context -> bare_Request -> timestamp **)

let bare_request2timestamp _ r =
  r.bare_request_t

(** val request2timestamp : minBFT_context -> request -> timestamp **)

let request2timestamp minbft_context r =
  let { request_b = br; request_a = _ } = r in
  bare_request2timestamp minbft_context br

(** val bare_request2sender : minBFT_context -> bare_Request -> client **)

let bare_request2sender _ r =
  r.bare_request_c

(** val request2sender : minBFT_context -> request -> client **)

let request2sender minbft_context r =
  let { request_b = b; request_a = _ } = r in
  bare_request2sender minbft_context b

(** val prepare2sender : minBFT_context -> prepare -> rep **)

let prepare2sender _ p =
  p.prepare_ui.ui_pre.pre_ui_id

(** val commit2sender_i : minBFT_context -> commit -> rep **)

let commit2sender_i _ c0 =
  c0.commit_b.bare_commit_ui.ui_pre.pre_ui_id

(** val commit2sender_j : minBFT_context -> commit -> rep **)

let commit2sender_j _ c0 =
  c0.commit_uj.ui_pre.pre_ui_id

(** val bare_reply2sender : minBFT_context -> bare_Reply -> rep **)

let bare_reply2sender _ r =
  r.bare_reply_rep

(** val bare_reply2request : minBFT_context -> bare_Reply -> request **)

let bare_reply2request _ r =
  r.bare_reply_r

(** val bare_reply2client : minBFT_context -> bare_Reply -> client **)

let bare_reply2client minbft_context r =
  request2sender minbft_context (bare_reply2request minbft_context r)

(** val reply2client : minBFT_context -> reply -> client **)

let reply2client minbft_context r =
  bare_reply2client minbft_context r.reply_b

(** val prepare2ui : minBFT_context -> prepare -> uI **)

let prepare2ui _ p =
  p.prepare_ui

(** val commit2ui_i : minBFT_context -> commit -> uI **)

let commit2ui_i _ c0 =
  c0.commit_b.bare_commit_ui

(** val commit2ui_j : minBFT_context -> commit -> uI **)

let commit2ui_j _ c0 =
  c0.commit_uj

(** val commit2counter_i : minBFT_context -> commit -> int **)

let commit2counter_i minbft_context c0 =
  (commit2ui_i minbft_context c0).ui_pre.pre_ui_counter

(** val prepare2request : minBFT_context -> prepare -> request **)

let prepare2request _ p =
  p.prepare_b.bare_prepare_m

(** val commit2request : minBFT_context -> commit -> request **)

let commit2request _ c0 =
  c0.commit_b.bare_commit_m

(** val commit2bare_request : minBFT_context -> commit -> bare_Request **)

let commit2bare_request minbft_context c0 =
  (commit2request minbft_context c0).request_b

(** val commit2msg : minBFT_context -> commit -> minBFT_data_message **)

let commit2msg minbft_context c0 =
  (commit2bare_request minbft_context c0).bare_request_m

(** val commit2client : minBFT_context -> commit -> client **)

let commit2client minbft_context c0 =
  request2sender minbft_context (commit2request minbft_context c0)

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

(** val minBFT_I_Msg : minBFT_context -> msg **)

let minBFT_I_Msg _ =
  MkMsg

type hashData = { hd_view : view; hd_msg : request; hd_pre : preUI }

type uSIG_hash = { create_hash_usig : (hashData -> local_key_map ->
                                      minBFT_digest);
                   verify_hash_usig : (hashData -> minBFT_digest ->
                                      local_key_map -> bool) }

(** val create_hash_usig :
    minBFT_context -> uSIG_hash -> hashData -> local_key_map -> minBFT_digest **)

let create_hash_usig _ x = x.create_hash_usig

(** val verify_hash_usig :
    minBFT_context -> uSIG_hash -> hashData -> minBFT_digest -> local_key_map
    -> bool **)

let verify_hash_usig _ x = x.verify_hash_usig

(** val uSIG_initial :
    minBFT_context -> minBFT_initial_keys -> rep -> uSIG_state **)

let uSIG_initial minbft_context minbft_initial_keys r =
  { usig_id = r; usig_counter = 0; usig_local_keys =
    (initial_keys minbft_context minbft_initial_keys
      (Obj.magic (MinBFT_replica r))) }

(** val increment_USIG : minBFT_context -> uSIG_state -> uSIG_state **)

let increment_USIG _ u =
  { usig_id = u.usig_id; usig_counter = (Pervasives.succ u.usig_counter);
    usig_local_keys = u.usig_local_keys }

(** val create_UI :
    minBFT_context -> uSIG_hash -> view -> request -> uSIG_state ->
    uSIG_state * uI **)

let create_UI minbft_context usig_hash v msg1 u =
  let u' = increment_USIG minbft_context u in
  let pre = { pre_ui_id = u'.usig_id; pre_ui_counter = u'.usig_counter } in
  let hd = { hd_view = v; hd_msg = msg1; hd_pre = pre } in
  let d = usig_hash.create_hash_usig hd u'.usig_local_keys in
  let ui = { ui_pre = pre; ui_digest = d } in (u', ui)

(** val verify_UI :
    minBFT_context -> uSIG_hash -> view -> request -> uI -> uSIG_state -> bool **)

let verify_UI minbft_context usig_hash v msg1 ui u =
  let hd = { hd_view = v; hd_msg = msg1; hd_pre = ui.ui_pre } in
  usig_hash.verify_hash_usig hd (ui2digest minbft_context ui)
    u.usig_local_keys

type uSIG_input_interface =
| Create_ui_in of (view * request)
| Verify_ui_in of ((view * request) * uI)

type uSIG_output_interface =
| Create_ui_out of uI
| Verify_ui_out of bool
| Verify_ui_out_def

(** val cIOusig : minBFT_context -> componentIO **)

let cIOusig _ =
  Obj.magic Verify_ui_out_def

(** val minBFT_I_Data : minBFT_context -> data **)

let minBFT_I_Data _ =
  MkData

type minBFT_auth = { minBFT_create : (data0 -> sending_keys -> minBFT_digest
                                     list);
                     minBFT_verify : (data0 -> name -> receiving_key ->
                                     minBFT_digest -> bool) }

(** val minBFT_create :
    minBFT_context -> minBFT_auth -> data0 -> sending_keys -> minBFT_digest
    list **)

let minBFT_create _ x = x.minBFT_create

(** val minBFT_verify :
    minBFT_context -> minBFT_auth -> data0 -> name -> receiving_key ->
    minBFT_digest -> bool **)

let minBFT_verify _ x = x.minBFT_verify

(** val minBFT_I_AuthFun : minBFT_context -> minBFT_auth -> authFun **)

let minBFT_I_AuthFun _ minbft_auth =
  { create = minbft_auth.minBFT_create; verify = minbft_auth.minBFT_verify }

(** val minBFT_data_auth : minBFT_context -> name -> data0 -> name option **)

let minBFT_data_auth minbft_context _ d =
  match Obj.magic d with
  | MinBFT_msg_bare_request r ->
    Some (Obj.magic (MinBFT_client (bare_request2sender minbft_context r)))
  | MinBFT_msg_bare_reply r ->
    Some (Obj.magic (MinBFT_replica (bare_reply2sender minbft_context r)))
  | MinBFT_msg_bare_prepare (_, pui) ->
    Some (Obj.magic (MinBFT_replica pui.pre_ui_id))
  | MinBFT_msg_bare_commit (_, pui) ->
    Some (Obj.magic (MinBFT_replica pui.pre_ui_id))

(** val minBFT_I_DataAuth : minBFT_context -> dataAuth **)

let minBFT_I_DataAuth =
  minBFT_data_auth

(** val other_replicas : minBFT_context -> rep -> rep list **)

let other_replicas minbft_context r =
  remove_elt minbft_context.rep_deq r (reps minbft_context)

(** val other_names : minBFT_context -> rep -> name list **)

let other_names minbft_context r =
  List.map (Obj.magic (fun x -> MinBFT_replica x))
    (other_replicas minbft_context r)

(** val broadcast2others :
    dTimeContext -> minBFT_context -> rep -> (name list -> directedMsg) ->
    directedMsg **)

let broadcast2others _ minbft_context slf f1 =
  f1 (other_names minbft_context slf)

(** val send_prepare :
    dTimeContext -> minBFT_context -> prepare -> name list -> directedMsg **)

let send_prepare dtc _ p n0 =
  { dmMsg = (Obj.magic (MinBFT_prepare p)); dmDst = n0; dmDelay =
    (cast0 (n2t dtc) 0) }

(** val send_commit :
    dTimeContext -> minBFT_context -> commit -> name list -> directedMsg **)

let send_commit dtc _ c0 n0 =
  { dmMsg = (Obj.magic (MinBFT_commit c0)); dmDst = n0; dmDelay =
    (cast0 (n2t dtc) 0) }

(** val send_reply :
    dTimeContext -> minBFT_context -> reply -> directedMsg **)

let send_reply dtc minbft_context r =
  { dmMsg = (Obj.magic (MinBFT_reply r)); dmDst =
    ((Obj.magic (MinBFT_client (reply2client minbft_context r))) :: []);
    dmDelay = (cast0 (n2t dtc) 0) }

(** val send_accept :
    dTimeContext -> minBFT_context -> accept -> name list -> directedMsg **)

let send_accept dtc _ a n0 =
  { dmMsg = (Obj.magic (MinBFT_accept a)); dmDst = n0; dmDelay =
    (cast0 (n2t dtc) 0) }

(** val send_debug :
    dTimeContext -> minBFT_context -> char list -> name -> directedMsg **)

let send_debug dtc _ s n0 =
  { dmMsg = (Obj.magic (MinBFT_debug s)); dmDst = (n0 :: []); dmDelay =
    (cast0 (n2t dtc) 0) }

(** val mk_auth_prepare :
    minBFT_context -> view -> request -> uI -> prepare **)

let mk_auth_prepare _ v m ui =
  let bpp = { bare_prepare_v = v; bare_prepare_m = m } in
  { prepare_b = bpp; prepare_ui = ui }

(** val mk_auth_commit :
    minBFT_context -> view -> request -> uI -> uI -> commit **)

let mk_auth_commit _ v m ui_i ui_j =
  let bcomm = { bare_commit_v = v; bare_commit_m = m; bare_commit_ui = ui_i }
  in
  { commit_b = bcomm; commit_uj = ui_j }

(** val mk_auth_reply :
    minBFT_context -> minBFT_auth -> request -> int -> rep -> view ->
    local_key_map -> reply **)

let mk_auth_reply minbft_context minbft_auth req res i v keys =
  let brep = { bare_reply_r = req; bare_reply_result = res; bare_reply_rep =
    i; bare_reply_view = v }
  in
  let toks =
    authenticate (minBFT_I_Node minbft_context) (minBFT_I_Key minbft_context)
      (minBFT_I_AuthTok minbft_context) (minBFT_I_Data minbft_context)
      (minBFT_I_AuthFun minbft_context minbft_auth)
      (Obj.magic (MinBFT_msg_bare_reply brep)) keys
  in
  { reply_b = brep; reply_a = toks }

type requestData =
| Request_data of view * request * uI

(** val request_data2ui : minBFT_context -> requestData -> uI **)

let request_data2ui _ = function
| Request_data (_, _, ui) -> ui

(** val request_data2rep : minBFT_context -> requestData -> rep **)

let request_data2rep minbft_context rd =
  ui2rep minbft_context (request_data2ui minbft_context rd)

(** val timestamp_deq : timestamp deq **)

let timestamp_deq =
  (=)

(** val view_deq : view deq **)

let view_deq =
  (=)

(** val bare_Request_Deq : minBFT_context -> bare_Request deq **)

let bare_Request_Deq minbft_context x y =
  let { bare_request_c = c1; bare_request_t = t1; bare_request_m = m1 } = x in
  let { bare_request_c = c2; bare_request_t = t2; bare_request_m = m2 } = y in
  let d = minbft_context.client_deq c1 c2 in
  if d
  then let d0 = minbft_context.minBFT_data_message_deq m1 m2 in
       if d0 then timestamp_deq t1 t2 else false
  else false

(** val request_Deq : minBFT_context -> request deq **)

let request_Deq minbft_context x y =
  let { request_b = r1; request_a = a1 } = x in
  let { request_b = r2; request_a = a2 } = y in
  let d = bare_Request_Deq minbft_context r1 r2 in
  if d then tokens_dec (minBFT_I_AuthTok minbft_context) a1 a2 else false

(** val requestData_Deq : minBFT_context -> requestData deq **)

let requestData_Deq minbft_context x y =
  let Request_data (v1, m1, ui1) = x in
  let Request_data (v2, m2, ui2) = y in
  let d = viewDeq v1 v2 in
  if d
  then let d0 = request_Deq minbft_context m1 m2 in
       if d0
       then let { ui_pre = ui_pre0; ui_digest = ui_digest0 } = ui1 in
            let { ui_pre = ui_pre1; ui_digest = ui_digest1 } = ui2 in
            let { pre_ui_id = ui_id0; pre_ui_counter = ui_counter0 } = ui_pre0
            in
            let { pre_ui_id = ui_id1; pre_ui_counter = ui_counter1 } = ui_pre1
            in
            let d1 = minbft_context.rep_deq ui_id0 ui_id1 in
            if d1
            then let s = (=) ui_counter0 ui_counter1 in
                 if s
                 then minbft_context.minBFT_digestdeq ui_digest0 ui_digest1
                 else false
            else false
       else false
  else false

(** val prepare2request_data : minBFT_context -> prepare -> requestData **)

let prepare2request_data _ p =
  let { prepare_b = prepare_b0; prepare_ui = ui } = p in
  let { bare_prepare_v = v; bare_prepare_m = m } = prepare_b0 in
  Request_data (v, m, ui)

(** val commit2request_data_i : minBFT_context -> commit -> requestData **)

let commit2request_data_i _ c0 =
  let { commit_b = commit_b0; commit_uj = _ } = c0 in
  let { bare_commit_v = v; bare_commit_m = m; bare_commit_ui = ui } =
    commit_b0
  in
  Request_data (v, m, ui)

type lOG_state_entry = { log_entry_request_data : requestData;
                         log_entry_commits : uIs }

(** val log_entry_request_data :
    minBFT_context -> lOG_state_entry -> requestData **)

let log_entry_request_data _ x = x.log_entry_request_data

(** val log_entry_commits : minBFT_context -> lOG_state_entry -> uIs **)

let log_entry_commits _ x = x.log_entry_commits

type lOG_state = lOG_state_entry list

(** val lOG_initial : minBFT_context -> lOG_state **)

let lOG_initial _ =
  []

(** val is_committed_entry : minBFT_context -> lOG_state_entry -> bool **)

let is_committed_entry minbft_context entry =
  (<=) minbft_context.f (List.length entry.log_entry_commits)

(** val find_entry :
    minBFT_context -> requestData -> lOG_state -> lOG_state_entry option **)

let rec find_entry minbft_context rd = function
| [] -> None
| entry :: entries ->
  if requestData_Deq minbft_context rd entry.log_entry_request_data
  then Some entry
  else find_entry minbft_context rd entries

(** val is_committed : minBFT_context -> commit -> lOG_state -> bool **)

let is_committed minbft_context c0 l =
  match find_entry minbft_context (commit2request_data_i minbft_context c0) l with
  | Some e -> is_committed_entry minbft_context e
  | None -> false

(** val mkNewLogEntryFromPrepare :
    minBFT_context -> prepare -> lOG_state_entry **)

let mkNewLogEntryFromPrepare minbft_context p =
  { log_entry_request_data = (prepare2request_data minbft_context p);
    log_entry_commits = [] }

(** val mkNewLogEntryFromCommit :
    minBFT_context -> commit -> lOG_state_entry **)

let mkNewLogEntryFromCommit minbft_context c0 =
  { log_entry_request_data = (commit2request_data_i minbft_context c0);
    log_entry_commits = (c0.commit_uj :: []) }

(** val add_commit2commits : minBFT_context -> uI -> uIs -> uIs **)

let add_commit2commits minbft_context c0 uis =
  if in_dec minbft_context.rep_deq (ui2rep minbft_context c0)
       (List.map (ui2rep minbft_context) uis)
  then uis
  else c0 :: uis

(** val add_commit2entry :
    minBFT_context -> uI -> lOG_state_entry -> lOG_state_entry **)

let add_commit2entry minbft_context ui entry =
  let { log_entry_request_data = rd; log_entry_commits = comms } = entry in
  if minbft_context.rep_deq (ui2rep minbft_context ui)
       (request_data2rep minbft_context rd)
  then entry
  else { log_entry_request_data = rd; log_entry_commits =
         (add_commit2commits minbft_context ui comms) }

(** val prepare_already_in_log :
    minBFT_context -> prepare -> lOG_state -> bool **)

let rec prepare_already_in_log minbft_context p = function
| [] -> false
| entry :: entries ->
  if requestData_Deq minbft_context (prepare2request_data minbft_context p)
       entry.log_entry_request_data
  then true
  else prepare_already_in_log minbft_context p entries

(** val log_new_prepare :
    minBFT_context -> prepare -> lOG_state -> lOG_state **)

let rec log_new_prepare minbft_context p l = match l with
| [] -> (mkNewLogEntryFromPrepare minbft_context p) :: []
| entry :: entries ->
  if requestData_Deq minbft_context entry.log_entry_request_data
       (prepare2request_data minbft_context p)
  then l
  else entry :: (log_new_prepare minbft_context p entries)

(** val log_new_commit :
    minBFT_context -> commit -> lOG_state -> lOG_state **)

let rec log_new_commit minbft_context c0 = function
| [] -> (mkNewLogEntryFromCommit minbft_context c0) :: []
| entry :: entries ->
  if requestData_Deq minbft_context (commit2request_data_i minbft_context c0)
       entry.log_entry_request_data
  then (add_commit2entry minbft_context (commit2ui_j minbft_context c0) entry) :: entries
  else entry :: (log_new_commit minbft_context c0 entries)

type lOG_input_interface =
| Log_new_prepare_log_in of prepare
| Log_new_commit_log_in of commit
| Prepare_already_in_log_in of prepare
| Is_committed_in of commit

type lOG_output_interface =
  bool
  (* singleton inductive, whose constructor was log_out *)

(** val cIOlog : minBFT_context -> componentIO **)

let cIOlog _ =
  Obj.magic true

type latest_executed_request = (client * timestamp) list

(** val initial_latest_executed_request :
    minBFT_context -> latest_executed_request **)

let initial_latest_executed_request _ =
  []

(** val update_latest_executed_request :
    minBFT_context -> request -> latest_executed_request ->
    latest_executed_request **)

let rec update_latest_executed_request minbft_context r = function
| [] ->
  ((request2sender minbft_context r),
    (request2timestamp minbft_context r)) :: []
| p :: l0 ->
  let (c0, t) = p in
  if minbft_context.client_deq c0 (request2sender minbft_context r)
  then if Nat.ltb (timestamp2nat t)
            (timestamp2nat (request2timestamp minbft_context r))
       then (c0, (request2timestamp minbft_context r)) :: l0
       else (c0, t) :: l0
  else (c0, t) :: (update_latest_executed_request minbft_context r l0)

type latest_executed_counter = int

(** val initial_latest_executed_counter : latest_executed_counter **)

let initial_latest_executed_counter =
  0

type highest_received_counter_value = (rep * int) list

(** val initial_highest_received_counter_value :
    minBFT_context -> highest_received_counter_value **)

let initial_highest_received_counter_value _ =
  []

(** val update_highest_received_counter_value :
    minBFT_context -> uI -> highest_received_counter_value ->
    highest_received_counter_value **)

let rec update_highest_received_counter_value minbft_context ui = function
| [] -> ((ui2rep minbft_context ui), (ui2counter minbft_context ui)) :: []
| p :: l0 ->
  let (r, c0) = p in
  if minbft_context.rep_deq r (ui2rep minbft_context ui)
  then if Nat.ltb c0 (ui2counter minbft_context ui)
       then (r, (ui2counter minbft_context ui)) :: l0
       else (r, c0) :: l0
  else (r, c0) :: (update_highest_received_counter_value minbft_context ui l0)

type mAIN_state = { local_keys : local_key_map; current_view : view;
                    sm_state0 : minBFT_sm_state;
                    cexec : latest_executed_counter;
                    vreq : latest_executed_request;
                    vacc : highest_received_counter_value;
                    current_seq : timestamp option }

(** val local_keys : minBFT_context -> mAIN_state -> local_key_map **)

let local_keys _ x = x.local_keys

(** val current_view : minBFT_context -> mAIN_state -> view **)

let current_view _ x = x.current_view

(** val sm_state0 : minBFT_context -> mAIN_state -> minBFT_sm_state **)

let sm_state0 _ x = x.sm_state0

(** val cexec : minBFT_context -> mAIN_state -> latest_executed_counter **)

let cexec _ x = x.cexec

(** val vreq : minBFT_context -> mAIN_state -> latest_executed_request **)

let vreq _ x = x.vreq

(** val vacc :
    minBFT_context -> mAIN_state -> highest_received_counter_value **)

let vacc _ x = x.vacc

(** val current_seq : minBFT_context -> mAIN_state -> timestamp option **)

let current_seq _ x = x.current_seq

(** val initial_state :
    minBFT_context -> minBFT_initial_keys -> rep -> mAIN_state **)

let initial_state minbft_context minbft_initial_keys r =
  { local_keys =
    (initial_keys minbft_context minbft_initial_keys
      (Obj.magic (MinBFT_replica r))); current_view = initial_view;
    sm_state0 = minbft_context.minBFT_sm_initial_state; cexec =
    initial_latest_executed_counter; vreq =
    (initial_latest_executed_request minbft_context); vacc =
    (initial_highest_received_counter_value minbft_context); current_seq =
    None }

(** val replace_sm_state :
    minBFT_context -> mAIN_state -> minBFT_sm_state -> mAIN_state **)

let replace_sm_state _ s x =
  { local_keys = s.local_keys; current_view = s.current_view; sm_state0 = x;
    cexec = s.cexec; vreq = s.vreq; vacc = s.vacc; current_seq =
    s.current_seq }

(** val minBFT_I_baseFunIO : minBFT_context -> baseFunIO **)

let minBFT_I_baseFunIO minbft_context nm =
  if compNameKindDeq nm.comp_name_kind ('U'::('S'::('I'::('G'::[]))))
  then cIOusig minbft_context
  else if compNameKindDeq nm.comp_name_kind ('L'::('O'::('G'::[])))
       then cIOlog minbft_context
       else cIOdef

(** val uSIGname : compName **)

let uSIGname =
  { comp_name_kind = ('U'::('S'::('I'::('G'::[])))); comp_name_space = 0;
    comp_name_trust = true }

(** val minBFT_I_baseStateFun : minBFT_context -> baseStateFun **)

let minBFT_I_baseStateFun _ =
  MkBaseStateFun

(** val minBFT_I_IOTrusted : minBFT_context -> iOTrusted **)

let minBFT_I_IOTrusted _ =
  Obj.magic Verify_ui_out_def

(** val minBFT_I_trustedStateFun : minBFT_context -> trustedStateFun **)

let minBFT_I_trustedStateFun _ =
  MkTrustedStateFun

(** val uSIG_update :
    dTimeContext -> minBFT_context -> uSIG_hash -> uSIG_state -> cio_I ->
    n_proc p_nproc list -> n_proc p_nproc list * (uSIG_state option * cio_O) **)

let uSIG_update dtc minbft_context usig_hash s m =
  Obj.magic interp_s_proc (minBFT_I_Node minbft_context)
    (minBFT_I_Key minbft_context) (minBFT_I_Msg minbft_context) dtc
    (minBFT_I_IOTrusted minbft_context) (minBFT_I_baseFunIO minbft_context)
    (minBFT_I_baseStateFun minbft_context)
    (minBFT_I_trustedStateFun minbft_context) 0
    (match Obj.magic m with
     | Create_ui_in msg1 ->
       let (v, r) = msg1 in
       let (s', ui) = create_UI minbft_context usig_hash v r s in
       PROC_RET (s', (Create_ui_out ui))
     | Verify_ui_in msgui ->
       let (p, ui) = msgui in
       let (v, r) = p in
       let b = verify_UI minbft_context usig_hash v r ui s in
       PROC_RET (s, (Verify_ui_out b)))

(** val uSIG_comp :
    dTimeContext -> minBFT_context -> minBFT_initial_keys -> uSIG_hash -> rep
    -> (n_proc mP_StateMachine, n_proc) sm_or **)

let uSIG_comp dtc minbft_context minbft_initial_keys usig_hash r =
  Obj.magic build_m_sm (minBFT_I_Node minbft_context)
    (minBFT_I_Key minbft_context) (minBFT_I_Msg minbft_context) dtc
    (minBFT_I_IOTrusted minbft_context) (minBFT_I_baseFunIO minbft_context)
    (minBFT_I_baseStateFun minbft_context)
    (minBFT_I_trustedStateFun minbft_context) 0 uSIGname
    (uSIG_update dtc minbft_context usig_hash)
    (uSIG_initial minbft_context minbft_initial_keys r)

(** val lOGname : compName **)

let lOGname =
  { comp_name_kind = ('L'::('O'::('G'::[]))); comp_name_space = 0;
    comp_name_trust = false }

(** val lOG_update :
    dTimeContext -> minBFT_context -> lOG_state -> cio_I -> n_proc p_nproc
    list -> n_proc p_nproc list * (lOG_state option * cio_O) **)

let lOG_update dtc minbft_context l m =
  Obj.magic interp_s_proc (minBFT_I_Node minbft_context)
    (minBFT_I_Key minbft_context) (minBFT_I_Msg minbft_context) dtc
    (minBFT_I_IOTrusted minbft_context) (minBFT_I_baseFunIO minbft_context)
    (minBFT_I_baseStateFun minbft_context)
    (minBFT_I_trustedStateFun minbft_context) 0
    (match Obj.magic m with
     | Log_new_prepare_log_in p ->
       let l' = log_new_prepare minbft_context p l in PROC_RET (l', true)
     | Log_new_commit_log_in c0 ->
       let l' = log_new_commit minbft_context c0 l in PROC_RET (l', true)
     | Prepare_already_in_log_in p ->
       let b = prepare_already_in_log minbft_context p l in PROC_RET (l, b)
     | Is_committed_in c0 ->
       let b = is_committed minbft_context c0 l in PROC_RET (l, b))

(** val lOG_comp :
    dTimeContext -> minBFT_context -> (n_proc mP_StateMachine, n_proc) sm_or **)

let lOG_comp dtc minbft_context =
  Obj.magic build_m_sm (minBFT_I_Node minbft_context)
    (minBFT_I_Key minbft_context) (minBFT_I_Msg minbft_context) dtc
    (minBFT_I_IOTrusted minbft_context) (minBFT_I_baseFunIO minbft_context)
    (minBFT_I_baseStateFun minbft_context)
    (minBFT_I_trustedStateFun minbft_context) 0 lOGname
    (lOG_update dtc minbft_context) (lOG_initial minbft_context)

(** val on_create_ui_out :
    minBFT_context -> (uI -> 'a1) -> 'a1 -> uSIG_output_interface -> 'a1 **)

let on_create_ui_out _ f1 d = function
| Create_ui_out ui -> f1 ui
| _ -> d

(** val call_create_ui :
    dTimeContext -> minBFT_context -> (view * request) -> 'a1 proc -> (uI ->
    'a1 proc) -> 'a1 proc **)

let call_create_ui _ minbft_context m d f1 =
  PROC_BIND ((PROC_CALL (uSIGname, (Obj.magic (Create_ui_in m)))),
    (Obj.magic on_create_ui_out minbft_context f1 d))

(** val if_true_verify_ui_out :
    minBFT_context -> 'a1 -> 'a1 -> uSIG_output_interface -> 'a1 **)

let if_true_verify_ui_out _ f1 d = function
| Verify_ui_out b -> if b then f1 else d
| _ -> d

(** val call_verify_ui :
    dTimeContext -> minBFT_context -> ((view * request) * uI) -> 'a1 proc ->
    'a1 proc -> 'a1 proc **)

let call_verify_ui _ minbft_context mui d f1 =
  PROC_BIND ((PROC_CALL (uSIGname, (Obj.magic (Verify_ui_in mui)))),
    (Obj.magic if_true_verify_ui_out minbft_context f1 d))

(** val on_log_out : 'a1 -> 'a1 -> lOG_output_interface -> 'a1 **)

let on_log_out d f1 = function
| true -> d
| false -> f1

(** val call_prepare_already_in_log :
    dTimeContext -> minBFT_context -> prepare -> 'a1 proc -> 'a1 proc -> 'a1
    proc **)

let call_prepare_already_in_log _ _ p d f1 =
  PROC_BIND ((PROC_CALL (lOGname,
    (Obj.magic (Prepare_already_in_log_in p)))), (Obj.magic on_log_out d f1))

(** val on_log_out_bool : (bool -> 'a1) -> lOG_output_interface -> 'a1 **)

let on_log_out_bool f1 =
  f1

(** val call_prepare_already_in_log_bool :
    dTimeContext -> minBFT_context -> prepare -> (bool -> 'a1 proc) -> 'a1
    proc **)

let call_prepare_already_in_log_bool _ _ p f1 =
  PROC_BIND ((PROC_CALL (lOGname,
    (Obj.magic (Prepare_already_in_log_in p)))),
    (Obj.magic on_log_out_bool f1))

(** val call_is_committed :
    dTimeContext -> minBFT_context -> commit -> 'a1 proc -> 'a1 proc -> 'a1
    proc **)

let call_is_committed _ _ c0 d f1 =
  PROC_BIND ((PROC_CALL (lOGname, (Obj.magic (Is_committed_in c0)))),
    (Obj.magic on_log_out f1 d))

(** val call_log_prepare :
    dTimeContext -> minBFT_context -> prepare -> 'a1 proc -> 'a1 proc **)

let call_log_prepare _ _ p f1 =
  PROC_BIND ((PROC_CALL (lOGname, (Obj.magic (Log_new_prepare_log_in p)))),
    (fun _ -> f1))

(** val call_log_commit :
    dTimeContext -> minBFT_context -> commit -> 'a1 proc -> 'a1 proc **)

let call_log_commit _ _ c0 f1 =
  PROC_BIND ((PROC_CALL (lOGname, (Obj.magic (Log_new_commit_log_in c0)))),
    (fun _ -> f1))

(** val on_data_message :
    dTimeContext -> minBFT_context -> minBFT_msg -> 'a1 proc -> (request ->
    'a1 proc) -> 'a1 proc **)

let on_data_message _ _ m d f1 =
  match m with
  | MinBFT_request m0 -> f1 m0
  | _ -> d

(** val on_prepare :
    dTimeContext -> minBFT_context -> minBFT_msg -> 'a1 proc -> (prepare ->
    'a1 proc) -> 'a1 proc **)

let on_prepare _ _ m d f1 =
  match m with
  | MinBFT_prepare p -> f1 p
  | _ -> d

(** val on_commit :
    dTimeContext -> minBFT_context -> minBFT_msg -> 'a1 proc -> (commit ->
    'a1 proc) -> 'a1 proc **)

let on_commit _ _ m d f1 =
  match m with
  | MinBFT_commit c0 -> f1 c0
  | _ -> d

(** val on_accept :
    dTimeContext -> minBFT_context -> minBFT_msg -> 'a1 proc -> (accept ->
    'a1 proc) -> 'a1 proc **)

let on_accept _ _ m d f1 =
  match m with
  | MinBFT_accept a -> f1 a
  | _ -> d

(** val mAINname : compName **)

let mAINname =
  msg_comp_name 0

(** val processing : minBFT_context -> mAIN_state -> bool **)

let processing _ s =
  match s.current_seq with
  | Some _ -> true
  | None -> false

(** val maybe_processing :
    minBFT_context -> timestamp -> mAIN_state -> bool **)

let maybe_processing _ t s =
  match s.current_seq with
  | Some seq0 -> if timestamp_deq t seq0 then true else false
  | None -> true

(** val new_request :
    minBFT_context -> request -> latest_executed_request -> bool **)

let rec new_request minbft_context r = function
| [] -> true
| p :: l0 ->
  let (c0, t) = p in
  if minbft_context.client_deq c0 (request2sender minbft_context r)
  then Nat.ltb (timestamp2nat t)
         (timestamp2nat (request2timestamp minbft_context r))
  else new_request minbft_context r l0

(** val verify_request :
    minBFT_context -> minBFT_auth -> rep -> local_key_map -> request -> bool **)

let verify_request minbft_context minbft_auth slf km r =
  verify_authenticated_data (minBFT_I_Data minbft_context)
    (minBFT_I_Key minbft_context) (minBFT_I_Node minbft_context)
    (minBFT_I_AuthTok minbft_context)
    (minBFT_I_AuthFun minbft_context minbft_auth)
    (minBFT_I_DataAuth minbft_context) (Obj.magic (MinBFT_replica slf))
    { am_data = (Obj.magic (MinBFT_msg_bare_request r.request_b)); am_auth =
    r.request_a } km

(** val valid_request :
    minBFT_context -> minBFT_auth -> rep -> local_key_map -> request ->
    mAIN_state -> bool **)

let valid_request minbft_context minbft_auth slf km r s =
  (&&)
    ((&&) (negb (processing minbft_context s))
      (new_request minbft_context r s.vreq))
    (verify_request minbft_context minbft_auth slf km r)

(** val invalid_request :
    minBFT_context -> minBFT_auth -> rep -> local_key_map -> request ->
    mAIN_state -> bool **)

let invalid_request minbft_context minbft_auth slf km r s =
  negb (valid_request minbft_context minbft_auth slf km r s)

(** val prepare2timestamp : minBFT_context -> prepare -> timestamp **)

let prepare2timestamp minbft_context p =
  request2timestamp minbft_context (prepare2request minbft_context p)

(** val commit2timestamp : minBFT_context -> commit -> timestamp **)

let commit2timestamp minbft_context c0 =
  request2timestamp minbft_context (commit2request minbft_context c0)

(** val highest_received_counter :
    minBFT_context -> rep -> highest_received_counter_value -> int option **)

let rec highest_received_counter minbft_context r = function
| [] -> None
| p :: l0 ->
  let (r', c') = p in
  if minbft_context.rep_deq r r'
  then Some c'
  else highest_received_counter minbft_context r l0

(** val highest_received_counter_is :
    minBFT_context -> rep -> int -> highest_received_counter_value -> bool **)

let highest_received_counter_is minbft_context r c0 l =
  match highest_received_counter minbft_context r l with
  | Some c' -> if (=) c0 c' then true else false
  | None -> false

(** val received_prior_counter :
    minBFT_context -> uI -> mAIN_state -> bool **)

let received_prior_counter minbft_context ui s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ ->
      highest_received_counter_is minbft_context (ui2rep minbft_context ui)
        n0 s.vacc)
      n0)
    (ui2counter minbft_context ui)

(** val received_equal_counter :
    minBFT_context -> uI -> mAIN_state -> bool **)

let received_equal_counter minbft_context ui s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun n0 ->
    highest_received_counter_is minbft_context (ui2rep minbft_context ui)
      (Pervasives.succ n0) s.vacc)
    (ui2counter minbft_context ui)

(** val received_prior_or_equal_counter :
    minBFT_context -> uI -> bool -> mAIN_state -> bool **)

let received_prior_or_equal_counter minbft_context ui pil s =
  if pil
  then received_equal_counter minbft_context ui s
  else received_prior_counter minbft_context ui s

(** val executed_prior_counter :
    minBFT_context -> uI -> mAIN_state -> bool **)

let executed_prior_counter minbft_context ui s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun n0 ->
    if (=) n0 s.cexec then true else false)
    (ui2counter minbft_context ui)

(** val valid_prepare :
    minBFT_context -> minBFT_auth -> rep -> local_key_map -> view -> prepare
    -> mAIN_state -> bool **)

let valid_prepare minbft_context minbft_auth slf km v p s =
  (&&)
    ((&&)
      ((&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                (maybe_processing minbft_context
                  (prepare2timestamp minbft_context p) s)
                (new_request minbft_context
                  (prepare2request minbft_context p) s.vreq))
              (if view_deq v (prepare2view minbft_context p)
               then true
               else false))
            (is_primary minbft_context v (prepare2sender minbft_context p)))
          (negb (is_primary minbft_context v slf)))
        (verify_request minbft_context minbft_auth slf km
          (prepare2request minbft_context p)))
      (executed_prior_counter minbft_context (prepare2ui minbft_context p) s))
    (received_prior_counter minbft_context (prepare2ui minbft_context p) s)

(** val invalid_prepare :
    minBFT_context -> minBFT_auth -> rep -> local_key_map -> view -> prepare
    -> mAIN_state -> bool **)

let invalid_prepare minbft_context minbft_auth slf km v p s =
  negb (valid_prepare minbft_context minbft_auth slf km v p s)

(** val valid_commit :
    minBFT_context -> minBFT_auth -> rep -> local_key_map -> view -> commit
    -> bool -> mAIN_state -> int **)

let valid_commit minbft_context minbft_auth slf km v c0 pil s =
  if maybe_processing minbft_context (commit2timestamp minbft_context c0) s
  then if new_request minbft_context (commit2request minbft_context c0) s.vreq
       then if view_deq v (commit2view minbft_context c0)
            then if minbft_context.rep_deq slf
                      (commit2sender_j minbft_context c0)
                 then Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ 0)))
                 else if is_primary minbft_context v
                           (commit2sender_i minbft_context c0)
                      then if negb
                                (is_primary minbft_context v
                                  (commit2sender_j minbft_context c0))
                           then if verify_request minbft_context minbft_auth
                                     slf km (commit2request minbft_context c0)
                                then if executed_prior_counter minbft_context
                                          (commit2ui_i minbft_context c0) s
                                     then if received_prior_or_equal_counter
                                               minbft_context
                                               (commit2ui_i minbft_context c0)
                                               pil s
                                          then if received_prior_counter
                                                    minbft_context
                                                    (commit2ui_j
                                                      minbft_context c0) s
                                               then 0
                                               else Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      0)))))))))
                                          else Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0))))))))
                                     else Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            0)))))))
                                else Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ 0))))))
                           else Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ 0)))))
                      else Pervasives.succ (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ 0))))
            else Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
       else Pervasives.succ (Pervasives.succ 0)
  else Pervasives.succ 0

(** val invalid_commit :
    minBFT_context -> minBFT_auth -> rep -> local_key_map -> view -> commit
    -> bool -> mAIN_state -> bool **)

let invalid_commit minbft_context minbft_auth slf km v c0 pil s =
  if (=) (valid_commit minbft_context minbft_auth slf km v c0 pil s) 0
  then false
  else true

(** val start_processing :
    minBFT_context -> request -> mAIN_state -> mAIN_state **)

let start_processing minbft_context r s =
  { local_keys = s.local_keys; current_view = s.current_view; sm_state0 =
    s.sm_state0; cexec = s.cexec; vreq = s.vreq; vacc = s.vacc; current_seq =
    (Some (request2timestamp minbft_context r)) }

(** val stop_processing : minBFT_context -> mAIN_state -> mAIN_state **)

let stop_processing _ s =
  { local_keys = s.local_keys; current_view = s.current_view; sm_state0 =
    s.sm_state0; cexec = s.cexec; vreq = s.vreq; vacc = s.vacc; current_seq =
    None }

(** val update_latest_executed :
    minBFT_context -> request -> mAIN_state -> mAIN_state **)

let update_latest_executed minbft_context r s =
  { local_keys = s.local_keys; current_view = s.current_view; sm_state0 =
    s.sm_state0; cexec = s.cexec; vreq =
    (update_latest_executed_request minbft_context r s.vreq); vacc = s.vacc;
    current_seq = s.current_seq }

(** val update_highest_received_counter :
    minBFT_context -> uI -> mAIN_state -> mAIN_state **)

let update_highest_received_counter minbft_context ui s =
  { local_keys = s.local_keys; current_view = s.current_view; sm_state0 =
    s.sm_state0; cexec = s.cexec; vreq = s.vreq; vacc =
    (update_highest_received_counter_value minbft_context ui s.vacc);
    current_seq = s.current_seq }

(** val increment_latest_executed_counter :
    minBFT_context -> mAIN_state -> mAIN_state **)

let increment_latest_executed_counter _ s =
  { local_keys = s.local_keys; current_view = s.current_view; sm_state0 =
    s.sm_state0; cexec = (Pervasives.succ s.cexec); vreq = s.vreq; vacc =
    s.vacc; current_seq = s.current_seq }

(** val handle_request :
    dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state uProc **)

let handle_request dtc minbft_context minbft_auth slf state m =
  let keys = state.local_keys in
  let cview = state.current_view in
  if not_primary minbft_context cview slf
  then PROC_RET (state,
         (Obj.magic
           ((send_debug dtc minbft_context
              ('n'::('o'::('t'::(' '::('p'::('r'::('i'::('m'::('a'::('r'::('y'::[])))))))))))
              (Obj.magic (MinBFT_replica slf))) :: [])))
  else on_data_message dtc minbft_context (Obj.magic m) (PROC_RET (state,
         (Obj.magic
           ((send_debug dtc minbft_context
              ('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))))
              (Obj.magic (MinBFT_replica slf))) :: [])))) (fun m0 ->
         if invalid_request minbft_context minbft_auth slf keys m0 state
         then PROC_RET (state,
                (Obj.magic
                  ((send_debug dtc minbft_context
                     ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))))))
                     (Obj.magic (MinBFT_replica slf))) :: [])))
         else let state1 = start_processing minbft_context m0 state in
              call_create_ui dtc minbft_context (cview, m0) (PROC_RET
                (state1,
                (Obj.magic
                  ((send_debug dtc minbft_context
                     ('c'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('c'::('r'::('e'::('a'::('t'::('e'::(' '::('U'::('I'::[])))))))))))))))))))
                     (Obj.magic (MinBFT_replica slf))) :: [])))) (fun ui ->
                let p = mk_auth_prepare minbft_context cview m0 ui in
                PROC_BIND ((PROC_CALL (lOGname,
                (Obj.magic (Log_new_prepare_log_in p)))), (fun _ ->
                let state2 =
                  update_highest_received_counter minbft_context ui state1
                in
                PROC_RET (state2,
                (Obj.magic
                  ((broadcast2others dtc minbft_context slf
                     (send_prepare dtc minbft_context p)) :: [])))))))

(** val handle_prepare :
    dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state uProc **)

let handle_prepare dtc minbft_context minbft_auth slf state m =
  let keys = state.local_keys in
  let cview = state.current_view in
  on_prepare dtc minbft_context (Obj.magic m) (PROC_RET (state,
    (Obj.magic
      ((send_debug dtc minbft_context
         ('n'::('o'::('t'::(' '::('a'::(' '::('p'::('r'::('e'::('p'::('a'::('r'::('e'::[])))))))))))))
         (Obj.magic (MinBFT_replica slf))) :: [])))) (fun p ->
    if invalid_prepare minbft_context minbft_auth slf keys cview p state
    then PROC_RET (state,
           (Obj.magic
             ((send_debug dtc minbft_context
                ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('r'::('e'::('p'::('a'::('r'::('e'::[])))))))))))))))
                (Obj.magic (MinBFT_replica slf))) :: [])))
    else let state1 =
           start_processing minbft_context (prepare2request minbft_context p)
             state
         in
         let state2 =
           update_highest_received_counter minbft_context
             (prepare2ui minbft_context p) state1
         in
         let v = prepare2view minbft_context p in
         let r = prepare2request minbft_context p in
         let ui = prepare2ui minbft_context p in
         call_verify_ui dtc minbft_context ((v, r), ui) (PROC_RET (state2,
           (Obj.magic
             ((send_debug dtc minbft_context
                ('c'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('v'::('e'::('r'::('i'::('f'::('y'::(' '::('U'::('I'::[])))))))))))))))))))
                (Obj.magic (MinBFT_replica slf))) :: []))))
           (call_prepare_already_in_log dtc minbft_context p (PROC_RET
             (state2,
             (Obj.magic
               ((send_debug dtc minbft_context
                  ('a'::('l'::('r'::('e'::('a'::('d'::('y'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('t'::('h'::('i'::('s'::(' '::('p'::('r'::('e'::('p'::('a'::('r'::('e'::[])))))))))))))))))))))))))))))
                  (Obj.magic (MinBFT_replica slf))) :: []))))
             (call_log_prepare dtc minbft_context p
               (call_create_ui dtc minbft_context (v, r) (PROC_RET (state2,
                 (Obj.magic
                   ((send_debug dtc minbft_context
                      ('c'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('c'::('r'::('e'::('a'::('t'::('e'::(' '::('U'::('I'::[])))))))))))))))))))
                      (Obj.magic (MinBFT_replica slf))) :: [])))) (fun ui0 ->
                 let comm =
                   mk_auth_commit minbft_context cview
                     (prepare2request minbft_context p)
                     (prepare2ui minbft_context p) ui0
                 in
                 call_log_commit dtc minbft_context comm (PROC_RET (state2,
                   (Obj.magic
                     ((broadcast2others dtc minbft_context slf
                        (send_commit dtc minbft_context comm)) :: [])))))))))

(** val commit2prepare : minBFT_context -> commit -> prepare **)

let commit2prepare minbft_context c0 =
  mk_auth_prepare minbft_context (commit2view minbft_context c0)
    (commit2request minbft_context c0) (commit2ui_i minbft_context c0)

(** val mk_my_commit : minBFT_context -> commit -> uI -> commit **)

let mk_my_commit minbft_context c0 ui =
  mk_auth_commit minbft_context (commit2view minbft_context c0)
    (commit2request minbft_context c0) (commit2ui_i minbft_context c0) ui

(** val send_debug_valid_commit :
    dTimeContext -> minBFT_context -> minBFT_auth -> rep -> local_key_map ->
    view -> commit -> bool -> mAIN_state -> directedMsg **)

let send_debug_valid_commit dtc minbft_context minbft_auth slf keys cview c0 pil state =
  send_debug dtc minbft_context
    (str_concat
      (('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('m'::('m'::('i'::('t'::(':'::(' '::[])))))))))))))))) :: (
      (nat2string
        (valid_commit minbft_context minbft_auth slf keys cview c0 pil state)) :: ((' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('p'::('r'::('i'::('o'::('r'::(' '::('c'::('o'::('u'::('n'::('t'::('e'::('r'::('?'::[])))))))))))))))))))))))) :: (
      (bool2string
        (received_prior_or_equal_counter minbft_context
          (commit2ui_i minbft_context c0) pil state)) :: ((' '::('p'::('i'::('l'::('?'::[]))))) :: (
      (bool2string pil) :: ((' '::('c'::('o'::('u'::('n'::('t'::('e'::('r'::('?'::[]))))))))) :: (
      (nat2string (ui2counter minbft_context (commit2ui_i minbft_context c0))) :: ((' '::('h'::('i'::('g'::('h'::('e'::('s'::('t'::('?'::[]))))))))) :: (
      (op2string nat2string
        (highest_received_counter minbft_context
          (ui2rep minbft_context (commit2ui_i minbft_context c0)) state.vacc)) :: [])))))))))))
    (Obj.magic (MinBFT_replica slf))

(** val handle_commit :
    dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state uProc **)

let handle_commit dtc minbft_context minbft_auth slf state m =
  let keys = state.local_keys in
  let cview = state.current_view in
  on_commit dtc minbft_context (Obj.magic m) (PROC_RET (state,
    (Obj.magic []))) (fun c0 ->
    let p = commit2prepare minbft_context c0 in
    call_prepare_already_in_log_bool dtc minbft_context p (fun pil ->
      if invalid_commit minbft_context minbft_auth slf keys cview c0 pil state
      then PROC_RET (state,
             (Obj.magic
               ((send_debug_valid_commit dtc minbft_context minbft_auth slf
                  keys cview c0 pil state) :: [])))
      else let state1 =
             start_processing minbft_context
               (commit2request minbft_context c0) state
           in
           let state2 =
             update_highest_received_counter minbft_context
               (commit2ui_i minbft_context c0) state1
           in
           let state3 =
             update_highest_received_counter minbft_context
               (commit2ui_j minbft_context c0) state2
           in
           let v = commit2view minbft_context c0 in
           let r = commit2request minbft_context c0 in
           let ui = commit2ui_i minbft_context c0 in
           let uj = commit2ui_j minbft_context c0 in
           call_verify_ui dtc minbft_context ((v, r), ui) (PROC_RET (state3,
             (Obj.magic
               ((send_debug dtc minbft_context
                  ('b'::('a'::('d'::(' '::('p'::('r'::('i'::('m'::('a'::('r'::('y'::(' '::('u'::('i'::[]))))))))))))))
                  (Obj.magic (MinBFT_replica slf))) :: []))))
             (call_verify_ui dtc minbft_context ((v, r), uj) (PROC_RET
               (state3,
               (Obj.magic
                 ((send_debug dtc minbft_context
                    ('b'::('a'::('d'::(' '::('s'::('e'::('l'::('f'::(' '::('u'::('i'::[])))))))))))
                    (Obj.magic (MinBFT_replica slf))) :: []))))
               (proc_bind_pair (minBFT_I_Node minbft_context)
                 (minBFT_I_Msg minbft_context) dtc
                 (minBFT_I_IOTrusted minbft_context)
                 (minBFT_I_baseFunIO minbft_context)
                 (call_prepare_already_in_log dtc minbft_context p (PROC_RET
                   (state3, []))
                   (call_create_ui dtc minbft_context (v, r) (PROC_RET
                     (state3,
                     ((send_debug dtc minbft_context
                        ('c'::('o'::('u'::('l'::('d'::('n'::('\''::('t'::(' '::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('e'::(' '::('c'::('o'::('m'::('m'::('i'::('t'::(' '::('u'::('i'::[])))))))))))))))))))))))))))
                        (Obj.magic (MinBFT_replica slf))) :: [])))
                     (fun ui0 ->
                     let comm = mk_my_commit minbft_context c0 ui0 in
                     call_log_commit dtc minbft_context comm (PROC_RET
                       (state3,
                       ((broadcast2others dtc minbft_context slf
                          (send_commit dtc minbft_context comm)) :: []))))))
                 (fun state4 out ->
                 call_log_commit dtc minbft_context c0
                   (call_is_committed dtc minbft_context c0 (PROC_RET
                     (state4,
                     (Obj.magic
                       ((send_debug dtc minbft_context
                          ('n'::('o'::('t'::(' '::('c'::('o'::('m'::('m'::('i'::('t'::('t'::('e'::('d'::[])))))))))))))
                          (Obj.magic (MinBFT_replica slf))) :: out))))
                     (let acc = { accept_r =
                        (commit2request minbft_context c0); accept_c =
                        (commit2counter_i minbft_context c0) }
                      in
                      let state5 =
                        update_latest_executed minbft_context
                          (commit2request minbft_context c0) state4
                      in
                      let state6 =
                        increment_latest_executed_counter minbft_context
                          state5
                      in
                      let state7 = stop_processing minbft_context state6 in
                      let (_, x) =
                        minbft_context.minBFT_sm_update
                          (commit2client minbft_context c0) state7.sm_state0
                          (commit2msg minbft_context c0)
                      in
                      let state8 = replace_sm_state minbft_context state7 x in
                      PROC_RET (state8,
                      (Obj.magic
                        ((send_accept dtc minbft_context acc
                           ((Obj.magic (MinBFT_replica slf)) :: [])) :: out))))))))))

(** val handle_accept :
    dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state uProc **)

let handle_accept dtc minbft_context minbft_auth slf state m =
  let keys = state.local_keys in
  let cview = state.current_view in
  on_accept dtc minbft_context (Obj.magic m) (PROC_RET (state,
    (Obj.magic []))) (fun a ->
    let rep0 =
      mk_auth_reply minbft_context minbft_auth a.accept_r a.accept_c slf
        cview keys
    in
    PROC_RET (state, (Obj.magic ((send_reply dtc minbft_context rep0) :: []))))

(** val handle_reply :
    dTimeContext -> minBFT_context -> rep -> mAIN_state uProc **)

let handle_reply _ _ _ state _ =
  PROC_RET (state, (Obj.magic []))

(** val handle_debug :
    dTimeContext -> minBFT_context -> rep -> mAIN_state uProc **)

let handle_debug _ _ _ state _ =
  PROC_RET (state, (Obj.magic []))

(** val mAIN_update :
    dTimeContext -> minBFT_context -> minBFT_auth -> rep -> mAIN_state ->
    cio_I -> (n_proc mP_StateMachine, n_proc) sm_or p_nproc list -> (n_proc
    mP_StateMachine, n_proc) sm_or p_nproc list * (mAIN_state option * cio_O) **)

let mAIN_update dtc minbft_context minbft_auth slf s m =
  Obj.magic interp_s_proc (minBFT_I_Node minbft_context)
    (minBFT_I_Key minbft_context) (minBFT_I_Msg minbft_context) dtc
    (minBFT_I_IOTrusted minbft_context) (minBFT_I_baseFunIO minbft_context)
    (minBFT_I_baseStateFun minbft_context)
    (minBFT_I_trustedStateFun minbft_context) (Pervasives.succ 0)
    (match Obj.magic m with
     | MinBFT_request _ ->
       handle_request dtc minbft_context minbft_auth slf s m
     | MinBFT_reply _ -> handle_reply dtc minbft_context slf s m
     | MinBFT_prepare _ ->
       handle_prepare dtc minbft_context minbft_auth slf s m
     | MinBFT_commit _ -> handle_commit dtc minbft_context minbft_auth slf s m
     | MinBFT_accept _ -> handle_accept dtc minbft_context minbft_auth slf s m
     | MinBFT_debug _ -> handle_debug dtc minbft_context slf s m)

(** val mAIN_comp :
    dTimeContext -> minBFT_context -> minBFT_initial_keys -> minBFT_auth ->
    rep -> (n_proc mP_StateMachine, n_proc) sm_or mP_StateMachine **)

let mAIN_comp dtc minbft_context minbft_initial_keys minbft_auth r =
  Obj.magic build_mp_sm (minBFT_I_Node minbft_context)
    (minBFT_I_Key minbft_context) (minBFT_I_Msg minbft_context) dtc
    (minBFT_I_IOTrusted minbft_context) (minBFT_I_baseFunIO minbft_context)
    (minBFT_I_baseStateFun minbft_context)
    (minBFT_I_trustedStateFun minbft_context) (Pervasives.succ 0) mAINname
    (mAIN_update dtc minbft_context minbft_auth r)
    (initial_state minbft_context minbft_initial_keys r)

(** val minBFTsubs :
    dTimeContext -> minBFT_context -> minBFT_initial_keys -> uSIG_hash -> rep
    -> (n_proc mP_StateMachine, n_proc) sm_or p_nproc list **)

let minBFTsubs dtc minbft_context minbft_initial_keys usig_hash n0 =
  { pp_name = uSIGname; pp_proc =
    (uSIG_comp dtc minbft_context minbft_initial_keys usig_hash n0) } :: ({ pp_name =
    lOGname; pp_proc = (lOG_comp dtc minbft_context) } :: [])

type minBFTls = mLocalSystem

(** val minBFTlocalSys :
    dTimeContext -> minBFT_context -> minBFT_initial_keys -> uSIG_hash ->
    minBFT_auth -> rep -> minBFTls **)

let minBFTlocalSys dtc minbft_context minbft_initial_keys usig_hash minbft_auth n0 =
  { ls_main =
    (Obj.magic mAIN_comp dtc minbft_context minbft_initial_keys minbft_auth
      n0); ls_subs =
    (Obj.magic minBFTsubs dtc minbft_context minbft_initial_keys usig_hash n0) }

(** val minBFTfunLevelSpace : minBFT_context -> funLevelSpace **)

let minBFTfunLevelSpace _ =
  { fls_level = (fun n0 ->
    match Obj.magic n0 with
    | MinBFT_replica _ -> Pervasives.succ 0
    | MinBFT_client _ -> 0); fls_space = (fun n0 ->
    match Obj.magic n0 with
    | MinBFT_replica _ -> 0
    | MinBFT_client _ -> Pervasives.succ 0) }

type time = { time_get_time : (unit -> __); time_sub : (__ -> __ -> __);
              time_2string : (__ -> char list) }

type time_type = __

(** val time_get_time : time -> unit -> time_type **)

let time_get_time x = x.time_get_time

type timedDirectedMsg = { tdm_dmsg : directedMsg; tdm_time : time_type }

type timedDirectedMsgs = timedDirectedMsg list

type simState = { ss_fls : funLevelSpace; ss_sys : m_USystem; ss_step : 
                  int; ss_out_inflight : directedMsgs;
                  ss_in_inflight : directedMsgs;
                  ss_delivered : timedDirectedMsgs }

(** val ss_fls :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> funLevelSpace **)

let ss_fls _ _ _ _ _ _ _ _ _ x = x.ss_fls

(** val ss_sys :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> m_USystem **)

let ss_sys _ _ _ _ _ _ _ _ _ x = x.ss_sys

(** val ss_step :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> int **)

let ss_step _ _ _ _ _ _ _ _ _ x = x.ss_step

(** val ss_out_inflight :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> directedMsgs **)

let ss_out_inflight _ _ _ _ _ _ _ _ _ x = x.ss_out_inflight

(** val ss_in_inflight :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> directedMsgs **)

let ss_in_inflight _ _ _ _ _ _ _ _ _ x = x.ss_in_inflight

(** val ss_delivered :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> timedDirectedMsgs **)

let ss_delivered _ _ _ _ _ _ _ _ _ x = x.ss_delivered

(** val replace_out_inflight :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> directedMsgs ->
    simState **)

let replace_out_inflight _ _ _ _ _ _ _ _ _ s l =
  { ss_fls = s.ss_fls; ss_sys = s.ss_sys; ss_step = s.ss_step;
    ss_out_inflight = l; ss_in_inflight = s.ss_in_inflight; ss_delivered =
    s.ss_delivered }

(** val replace_in_inflight :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> directedMsgs ->
    simState **)

let replace_in_inflight _ _ _ _ _ _ _ _ _ s l =
  { ss_fls = s.ss_fls; ss_sys = s.ss_sys; ss_step = s.ss_step;
    ss_out_inflight = s.ss_out_inflight; ss_in_inflight = l; ss_delivered =
    s.ss_delivered }

(** val mkInitSimState :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> funLevelSpace -> m_USystem ->
    directedMsgs -> simState **)

let mkInitSimState _ _ _ _ _ _ _ _ _ f1 sys msgs =
  { ss_fls = f1; ss_sys = sys; ss_step = 0; ss_out_inflight = msgs;
    ss_in_inflight = []; ss_delivered = [] }

(** val m_run_ls_on_this_one_msg :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> int -> compNameSpace -> mLocalSystem
    -> msg0 -> mLocalSystem option * directedMsgs **)

let m_run_ls_on_this_one_msg pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun l s ls m =
  m_break pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun l
    (Obj.magic sm_update (assert true (* Proj Args *)) (assert true
      (* Proj Args *)) (assert true (* Proj Args *)) (assert true
      (* Proj Args *)) (assert true (* Proj Args *)) (assert true
      (* Proj Args *)) (assert true (* Proj Args *)) (assert true
      (* Proj Args *)) (assert true (* Proj Args *)) ls.ls_main
      ls.ls_main.sm_state m) ls.ls_subs (fun subs' out ->
    let (sop, msgs) = out in
    ((option_map (fun s0 ->
       upd_ls_main_state_and_subs pn pk pm dtc iot base_fun_io base_state_fun
         trusted_state_fun l (msg_comp_name s) ls s0 subs') sop), msgs))

(** val run_ls_with_time :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> int -> compNameSpace ->
    mLocalSystem -> msg0 -> posDTime ->
    (mLocalSystem * directedMsgs) * time_type **)

let run_ls_with_time pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun time0 l s ls m _ =
  let (o, msgs) =
    m_run_ls_on_this_one_msg pn pk pm dtc iot base_fun_io base_state_fun
      trusted_state_fun l s ls m
  in
  (match o with
   | Some ls' -> let t2 = time0.time_get_time () in ((ls', msgs), t2)
   | None -> let t2 = time0.time_get_time () in ((ls, msgs), t2))

(** val dmsg2one_dst :
    node -> msg -> dTimeContext -> directedMsg -> name -> directedMsg **)

let dmsg2one_dst _ _ _ dm d =
  { dmMsg = dm.dmMsg; dmDst = (d :: []); dmDelay = dm.dmDelay }

(** val run_sim_on_nth_out :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> int -> simState **)

let run_sim_on_nth_out pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun time0 s n0 =
  match decomp_nth s.ss_out_inflight n0 with
  | Some p ->
    let (p0, fseg) = p in
    let (iseg, dmsg) = p0 in
    (match dmsg.dmDst with
     | [] ->
       replace_out_inflight pn pk pm dtc iot base_fun_io base_state_fun
         trusted_state_fun time0 s (List.append iseg fseg)
     | dst :: dsts ->
       let (p1, time1) =
         run_ls_with_time pn pk pm dtc iot base_fun_io base_state_fun
           trusted_state_fun time0 (s.ss_fls.fls_level dst)
           (s.ss_fls.fls_space dst) (s.ss_sys dst) dmsg.dmMsg
           (cast0 (n2t dtc) 0)
       in
       let (ls', outs) = p1 in
       { ss_fls = s.ss_fls; ss_sys = (fun name0 ->
       if name_dec pn dst name0 then ls' else s.ss_sys name0); ss_step =
       (Pervasives.succ s.ss_step); ss_out_inflight =
       (if nullb dsts
        then List.append iseg fseg
        else List.append iseg ({ dmMsg = dmsg.dmMsg; dmDst = dsts; dmDelay =
               (cast0 (n2t dtc) 0) } :: fseg)); ss_in_inflight =
       (List.append outs s.ss_in_inflight); ss_delivered = ({ tdm_dmsg =
       (dmsg2one_dst pn pm dtc dmsg dst); tdm_time =
       time1 } :: s.ss_delivered) })
  | None -> s

(** val run_sim_on_nth_in :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> simState -> int -> bool ->
    simState **)

let run_sim_on_nth_in pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun time0 s n0 b =
  match decomp_nth s.ss_in_inflight n0 with
  | Some p ->
    let (p0, fseg) = p in
    let (iseg, dmsg) = p0 in
    (match dmsg.dmDst with
     | [] ->
       replace_in_inflight pn pk pm dtc iot base_fun_io base_state_fun
         trusted_state_fun time0 s (List.append iseg fseg)
     | dst :: dsts ->
       let (p1, time1) =
         run_ls_with_time pn pk pm dtc iot base_fun_io base_state_fun
           trusted_state_fun time0 (s.ss_fls.fls_level dst)
           (s.ss_fls.fls_space dst) (s.ss_sys dst) dmsg.dmMsg
           (cast0 (n2t dtc) 0)
       in
       let (ls', outs) = p1 in
       { ss_fls = s.ss_fls; ss_sys = (fun name0 ->
       if name_dec pn dst name0 then ls' else s.ss_sys name0); ss_step =
       (Pervasives.succ s.ss_step); ss_out_inflight = s.ss_out_inflight;
       ss_in_inflight =
       (if b
        then if nullb dsts
             then List.append iseg (List.append outs fseg)
             else List.append iseg
                    (List.append outs ({ dmMsg = dmsg.dmMsg; dmDst = dsts;
                      dmDelay = (cast0 (n2t dtc) 0) } :: fseg))
        else if nullb dsts
             then List.append iseg (List.append fseg outs)
             else List.append iseg ({ dmMsg = dmsg.dmMsg; dmDst = dsts;
                    dmDelay =
                    (cast0 (n2t dtc) 0) } :: (List.append fseg outs)));
       ss_delivered = ({ tdm_dmsg = (dmsg2one_dst pn pm dtc dmsg dst);
       tdm_time = time1 } :: s.ss_delivered) })
  | None ->
    run_sim_on_nth_out pn pk pm dtc iot base_fun_io base_state_fun
      trusted_state_fun time0 s n0

type round = { round_pos : int; round_num : int }

type rounds = round list

type switch = { switch_step : int; switch_pos : int }

type switches = switch list

(** val find_switch : int -> switches -> int option **)

let rec find_switch step = function
| [] -> None
| s0 :: l0 ->
  let { switch_step = s; switch_pos = p } = s0 in
  if (=) step s then Some p else find_switch step l0

(** val iterate_n_steps :
    node -> key -> msg -> dTimeContext -> iOTrusted -> baseFunIO ->
    baseStateFun -> trustedStateFun -> time -> rounds -> switches -> simState
    -> simState **)

let rec iterate_n_steps pn pk pm dtc iot base_fun_io base_state_fun trusted_state_fun time0 rounds0 switch0 s =
  match rounds0 with
  | [] -> s
  | r :: rounds1 ->
    let { round_pos = pos; round_num = round_num0 } = r in
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ ->
       iterate_n_steps pn pk pm dtc iot base_fun_io base_state_fun
         trusted_state_fun time0 rounds1 switch0 s)
       (fun m ->
       match find_switch s.ss_step switch0 with
       | Some p ->
         let s1 =
           run_sim_on_nth_out pn pk pm dtc iot base_fun_io base_state_fun
             trusted_state_fun time0 s p
         in
         iterate_n_steps pn pk pm dtc iot base_fun_io base_state_fun
           trusted_state_fun time0 ({ round_pos = pos; round_num =
           m } :: rounds1) switch0 s1
       | None ->
         let s1 =
           run_sim_on_nth_in pn pk pm dtc iot base_fun_io base_state_fun
             trusted_state_fun time0 s pos false
         in
         iterate_n_steps pn pk pm dtc iot base_fun_io base_state_fun
           trusted_state_fun time0 ({ round_pos = pos; round_num =
           m } :: rounds1) switch0 s1)
       round_num0)

type minbft_digest = int list

(** val minbft_digest_def : minbft_digest **)

let minbft_digest_def =
  []

(** val minbft_digest_deq : minbft_digest deq **)

let minbft_digest_deq x y =
  list_eq_dec (=) x y

type sending_key_stub =
| Minbft_sending_key_stub

type receiving_key_stub =
| Minbft_receiving_key_stub

type minbft_sending_key = sending_key_stub

type minbft_receiving_key = receiving_key_stub

(** val nreps : int -> int **)

let nreps f1 =
  add (mul (Pervasives.succ (Pervasives.succ 0)) f1) (Pervasives.succ 0)

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

(** val client1 : int -> client0 **)

let client1 _ =
  0

(** val client_deq0 : int -> client0 deq **)

let client_deq0 c0 =
  nat_n_deq (nclients c0)

(** val clients2nat0 : int -> client0 -> nat_n **)

let clients2nat0 _ n0 =
  n0

(** val bijective_clients2nat : int -> (client0, nat_n) bijective **)

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
  { minBFT_digestdeq = (Obj.magic minbft_digest_deq); f = f0; rep_deq =
    (Obj.magic replica_deq f0); reps2nat = (Obj.magic reps2nat0 f0);
    reps_bij = (Obj.magic bijective_reps2nat f0); num_clients = (nclients c);
    client_deq = (Obj.magic client_deq0 c); clients2nat =
    (Obj.magic clients2nat0 c); clients_bij =
    (Obj.magic bijective_clients2nat c); minBFT_data_message_deq =
    (Obj.magic minbft_data_message_deq); minBFT_resdeq =
    (Obj.magic minbft_result_deq); minBFT_sm_initial_state =
    (Obj.magic minbft_sm_initial_state); minBFT_sm_update =
    (Obj.magic minbft_sm_update c) }

(** val minbft_create_signature :
    minBFT_Bare_Msg -> sending_keys -> minBFT_digest list **)

let minbft_create_signature _ _ =
  (Obj.magic minbft_digest_def) :: []

(** val minbft_verify_signature :
    minBFT_Bare_Msg -> name -> receiving_key -> minBFT_digest -> bool **)

let minbft_verify_signature _ _ _ _ =
  true

(** val minBFT_I_auth : minBFT_auth **)

let minBFT_I_auth =
  { minBFT_create = (Obj.magic minbft_create_signature); minBFT_verify =
    (Obj.magic minbft_verify_signature) }

(** val minbft_lookup_client_sending_key : client -> minbft_sending_key **)

let minbft_lookup_client_sending_key _ =
  Minbft_sending_key_stub

(** val minbft_lookup_client_receiving_key :
    client -> minbft_receiving_key **)

let minbft_lookup_client_receiving_key _ =
  Minbft_receiving_key_stub

(** val initial_minbft_local_key_map_replicas : name -> local_key_map **)

let initial_minbft_local_key_map_replicas src =
  match Obj.magic src with
  | MinBFT_replica _ ->
    { lkm_sending_keys =
      (List.map (fun c0 -> { dsk_dst =
        ((Obj.magic (MinBFT_client c0)) :: []); dsk_key =
        (Obj.magic minbft_lookup_client_sending_key c0) })
        (clients minBFT_I_context)); lkm_receiving_keys =
      (List.map (fun c0 -> { drk_dst =
        ((Obj.magic (MinBFT_client c0)) :: []); drk_key =
        (Obj.magic minbft_lookup_client_receiving_key c0) })
        (clients minBFT_I_context)) }
  | MinBFT_client _ -> { lkm_sending_keys = []; lkm_receiving_keys = [] }

(** val minBFT_I_keys : minBFT_initial_keys **)

let minBFT_I_keys =
  initial_minbft_local_key_map_replicas

(** val minbft_create_hash_usig :
    hashData -> local_key_map -> minBFT_digest **)

let minbft_create_hash_usig _ _ =
  Obj.magic []

(** val minbft_verify_hash_usig :
    hashData -> minBFT_digest -> local_key_map -> bool **)

let minbft_verify_hash_usig _ _ _ =
  true

(** val minBFT_I_usig_hash : uSIG_hash **)

let minBFT_I_usig_hash =
  { create_hash_usig = minbft_create_hash_usig; verify_hash_usig =
    minbft_verify_hash_usig }

(** val tIME_I : time **)

let tIME_I =
  { time_get_time = (Obj.magic Prelude.Time.get_time); time_sub =
    (Obj.magic Prelude.Time.sub_time); time_2string =
    (Obj.magic Prelude.Time.time2string) }

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

(** val str_concat0 : char list list -> char list **)

let rec str_concat0 = function
| [] -> []
| s :: ss -> append s (str_concat0 ss)

(** val minbft_data_message2string : minbft_data_message -> char list **)

let minbft_data_message2string = function
| Minbft_data_message_plus n0 ->
  str_concat0 (('+'::[]) :: ((Prelude.char_list_of_int n0) :: []))
| Minbft_data_message_minus n0 ->
  str_concat0 (('-'::[]) :: ((Prelude.char_list_of_int n0) :: []))

(** val nat_n2string : int -> nat_n -> char list **)

let nat_n2string _ =
  Prelude.char_list_of_int

(** val replica2string : replica -> char list **)

let replica2string r =
  nat_n2string (nreps f0) r

(** val bare_request2string : bare_Request -> char list **)

let bare_request2string br =
  let { bare_request_c = c0; bare_request_t = ts; bare_request_m = m } = br in
  str_concat0
    ((client2string (Obj.magic c0)) :: ((','::[]) :: ((timestamp2string ts) :: ((','::[]) :: (
    (minbft_data_message2string (Obj.magic m)) :: [])))))

(** val request2string : request -> char list **)

let request2string r =
  let { request_b = br; request_a = a } = r in
  str_concat0
    (('R'::('E'::('Q'::('U'::('E'::('S'::('T'::('('::[])))))))) :: ((bare_request2string
                                                                    br) :: ((','::[]) :: (
    (tokens2string a) :: ((')'::[]) :: [])))))

(** val bare_prepare2string : bare_Prepare -> char list **)

let bare_prepare2string bp =
  let { bare_prepare_v = v; bare_prepare_m = m } = bp in
  str_concat0 ((view2string v) :: ((','::[]) :: ((request2string m) :: [])))

(** val pre_ui2string : preUI -> char list **)

let pre_ui2string pui =
  let { pre_ui_id = id; pre_ui_counter = counter } = pui in
  str_concat0
    ((replica2string (Obj.magic id)) :: ((','::[]) :: ((Prelude.char_list_of_int
                                                         counter) :: [])))

(** val ui2string : uI -> char list **)

let ui2string ui =
  let { ui_pre = pui; ui_digest = d } = ui in
  str_concat0
    ((pre_ui2string pui) :: ((','::[]) :: ((minbft_digest2string
                                             (Obj.magic d)) :: [])))

(** val bare_commit2string : bare_Commit -> char list **)

let bare_commit2string bc =
  let { bare_commit_v = v; bare_commit_m = m; bare_commit_ui = ui } = bc in
  str_concat0
    ((view2string v) :: ((','::[]) :: ((request2string m) :: ((','::[]) :: (
    (ui2string ui) :: [])))))

(** val prepare2string : prepare -> char list **)

let prepare2string p =
  let { prepare_b = bp; prepare_ui = a } = p in
  str_concat0
    (('P'::('R'::('E'::('P'::('A'::('R'::('E'::('('::[])))))))) :: ((bare_prepare2string
                                                                    bp) :: ((','::[]) :: (
    (ui2string a) :: ((')'::[]) :: [])))))

(** val commit2string : commit -> char list **)

let commit2string c0 =
  let { commit_b = bc; commit_uj = a } = c0 in
  str_concat0
    (('C'::('O'::('M'::('M'::('I'::('T'::('('::[]))))))) :: ((bare_commit2string
                                                               bc) :: ((','::[]) :: (
    (ui2string a) :: ((')'::[]) :: [])))))

(** val accept2string : accept -> char list **)

let accept2string r =
  let { accept_r = r0; accept_c = c0 } = r in
  str_concat0
    (('A'::('C'::('C'::('E'::('P'::('T'::('('::[]))))))) :: ((request2string
                                                               r0) :: ((','::[]) :: (
    (Prelude.char_list_of_int c0) :: ((')'::[]) :: [])))))

(** val bare_reply2string : bare_Reply -> char list **)

let bare_reply2string br =
  let { bare_reply_r = req; bare_reply_result = res; bare_reply_rep = i;
    bare_reply_view = _ } = br
  in
  str_concat0
    ((request2string req) :: ((','::[]) :: ((Prelude.char_list_of_int res) :: ((','::[]) :: (
    (replica2string (Obj.magic i)) :: [])))))

(** val reply2string : reply -> char list **)

let reply2string r =
  let { reply_b = br; reply_a = a } = r in
  str_concat0
    (('R'::('E'::('P'::('L'::('Y'::('('::[])))))) :: ((bare_reply2string br) :: ((','::[]) :: (
    (tokens2string a) :: ((')'::[]) :: [])))))

(** val msg2string : minBFT_msg -> char list **)

let msg2string = function
| MinBFT_request r -> request2string r
| MinBFT_reply r -> reply2string r
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
     str_concat0
       ((name2string n0) :: ((','::[]) :: ((names2string ns) :: []))))

(** val z2string : z -> char list **)

let z2string _ =
  []

(** val pos2string : positive -> char list **)

let pos2string _ =
  []

(** val q2string : q -> char list **)

let q2string q0 =
  str_concat0
    (('('::[]) :: ((z2string q0.qnum) :: (('/'::[]) :: ((pos2string q0.qden) :: ((')'::[]) :: [])))))

(** val posdtime2string : posDTime -> char list **)

let posdtime2string p =
  q2string (Obj.magic pos_dt_t dTimeContextQ p)

(** val directedMsg2string : directedMsg -> char list **)

let directedMsg2string dm =
  let { dmMsg = msg1; dmDst = dst; dmDelay = delay } = dm in
  str_concat0
    ((msg2string (Obj.magic msg1)) :: ((':'::[]) :: (('['::[]) :: ((names2string
                                                                    dst) :: ((']'::[]) :: ((':'::[]) :: (
    (posdtime2string delay) :: [])))))))

(** val directedMsgs2string : directedMsgs -> char list **)

let rec directedMsgs2string = function
| [] -> []
| dm :: dmsgs ->
  (match dmsgs with
   | [] -> directedMsg2string dm
   | _ :: _ ->
     str_concat0
       ((directedMsg2string dm) :: (['\n'] :: ((directedMsgs2string dmsgs) :: []))))

(** val timedDirectedMsg2string : timedDirectedMsg -> char list **)

let timedDirectedMsg2string m =
  let { tdm_dmsg = dm; tdm_time = time0 } = m in
  str_concat0
    ((directedMsg2string dm) :: ((':'::[]) :: ((Prelude.Time.time2string
                                                 (Obj.magic time0)) :: [])))

(** val timedDirectedMsgs2string : timedDirectedMsgs -> char list **)

let rec timedDirectedMsgs2string = function
| [] -> []
| dm :: dmsgs ->
  (match dmsgs with
   | [] -> timedDirectedMsg2string dm
   | _ :: _ ->
     str_concat0
       ((timedDirectedMsg2string dm) :: (['\n'] :: ((timedDirectedMsgs2string
                                                      dmsgs) :: []))))

(** val simState2string : simState -> char list **)

let simState2string s =
  let { ss_fls = _; ss_sys = _; ss_step = step; ss_out_inflight =
    out_inflight; ss_in_inflight = in_inflight; ss_delivered = delivered } = s
  in
  str_concat0
    (['\n'] :: (('='::('='::('='::('='::('='::('='::(' '::('S'::('T'::('E'::('P'::(' '::('='::('='::('='::('='::('='::('='::[])))))))))))))))))) :: (['\n'] :: (
    (Prelude.char_list_of_int step) :: (['\n'] :: (('='::('='::('='::('='::('='::('='::(' '::('I'::('N'::(' '::('F'::('L'::('I'::('G'::('H'::('T'::(' '::('('::('f'::('r'::('o'::('m'::(' '::('o'::('u'::('t'::('s'::('i'::('d'::('e'::(' '::('t'::('h'::('e'::(' '::('s'::('y'::('s'::('t'::('e'::('m'::(')'::(' '::('='::('='::('='::('='::('='::('='::[]))))))))))))))))))))))))))))))))))))))))))))))))) :: (['\n'] :: (
    (directedMsgs2string out_inflight) :: (['\n'] :: (('='::('='::('='::('='::('='::('='::(' '::('I'::('N'::(' '::('F'::('L'::('I'::('G'::('H'::('T'::(' '::('('::('f'::('r'::('o'::('m'::(' '::('i'::('n'::('s'::('i'::('d'::('e'::(' '::('t'::('h'::('e'::(' '::('s'::('y'::('s'::('t'::('e'::('m'::(')'::(' '::('='::('='::('='::('='::('='::('='::[])))))))))))))))))))))))))))))))))))))))))))))))) :: (['\n'] :: (
    (directedMsgs2string in_inflight) :: (['\n'] :: (('='::('='::('='::('='::('='::('='::(' '::('D'::('E'::('L'::('I'::('V'::('E'::('R'::('E'::('D'::(' '::('='::('='::('='::('='::('='::('='::[]))))))))))))))))))))))) :: (['\n'] :: (
    (timedDirectedMsgs2string delivered) :: (['\n'] :: [])))))))))))))))))

(** val minBFT_instance_sys : m_USystem **)

let minBFT_instance_sys name0 =
  match Obj.magic name0 with
  | MinBFT_replica n0 ->
    minBFTlocalSys dTimeContextQ minBFT_I_context minBFT_I_keys
      minBFT_I_usig_hash minBFT_I_auth n0
  | MinBFT_client _ ->
    { ls_main =
      (mP_haltedSM (minBFT_I_Node minBFT_I_context)
        (minBFT_I_Key minBFT_I_context) (minBFT_I_Msg minBFT_I_context)
        dTimeContextQ (minBFT_I_IOTrusted minBFT_I_context)
        (minBFT_I_baseFunIO minBFT_I_context)
        (minBFT_I_baseStateFun minBFT_I_context)
        (minBFT_I_trustedStateFun minBFT_I_context) munit_comp_name 0
        (Obj.magic ())); ls_subs = [] }

(** val mk_request_to : rep -> int -> minBFT_data_message -> directedMsg **)

let mk_request_to rep0 ts m =
  let breq = { bare_request_c = (Obj.magic client1 c); bare_request_t = ts;
    bare_request_m = m }
  in
  let dst = MinBFT_replica rep0 in
  let toks = minbft_digest_def :: [] in
  let req = { request_b = breq; request_a = (Obj.magic toks) } in
  let msg1 = MinBFT_request req in
  { dmMsg = (Obj.magic msg1); dmDst = ((Obj.magic dst) :: []); dmDelay =
  (nat2pdt dTimeContextQ 0) }

(** val mk_request : int -> minBFT_data_message -> directedMsg **)

let mk_request ts opr =
  mk_request_to (minBFTprimary minBFT_I_context initial_view) ts opr

(** val mk_requests_start :
    int -> int -> minBFT_data_message -> directedMsgs **)

let rec mk_requests_start n0 start opr =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m ->
    List.append (mk_requests_start m start opr)
      ((mk_request (add n0 start) opr) :: []))
    n0

type initRequests = { num_requests : int; starting_seq_num : int;
                      req_operation : minBFT_data_message }

(** val num_requests : initRequests -> int **)

let num_requests x = x.num_requests

(** val starting_seq_num : initRequests -> int **)

let starting_seq_num x = x.starting_seq_num

(** val req_operation : initRequests -> minBFT_data_message **)

let req_operation x = x.req_operation

(** val minBFT_init_msgs : directedMsgs -> simState **)

let minBFT_init_msgs msgs =
  mkInitSimState (minBFT_I_Node minBFT_I_context)
    (minBFT_I_Key minBFT_I_context) (minBFT_I_Msg minBFT_I_context)
    dTimeContextQ (minBFT_I_IOTrusted minBFT_I_context)
    (minBFT_I_baseFunIO minBFT_I_context)
    (minBFT_I_baseStateFun minBFT_I_context)
    (minBFT_I_trustedStateFun minBFT_I_context) tIME_I
    (minBFTfunLevelSpace minBFT_I_context) minBFT_instance_sys msgs

(** val minBFT_init : initRequests -> simState **)

let minBFT_init init =
  minBFT_init_msgs
    (mk_requests_start init.num_requests init.starting_seq_num
      init.req_operation)

(** val minBFT_simul_n : initRequests -> rounds -> switches -> simState **)

let minBFT_simul_n init rounds0 switches0 =
  iterate_n_steps (minBFT_I_Node minBFT_I_context)
    (minBFT_I_Key minBFT_I_context) (minBFT_I_Msg minBFT_I_context)
    dTimeContextQ (minBFT_I_IOTrusted minBFT_I_context)
    (minBFT_I_baseFunIO minBFT_I_context)
    (minBFT_I_baseStateFun minBFT_I_context)
    (minBFT_I_trustedStateFun minBFT_I_context) tIME_I rounds0 switches0
    (minBFT_init init)

(** val minBFT_simul : simState **)

let minBFT_simul =
  let num_requests0 = Pervasives.succ (Pervasives.succ 0) in
  let starting_seq_num0 = 0 in
  let req_operation0 = Minbft_data_message_plus (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))
  in
  let rounds0 = { round_pos = 0; round_num = (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))) } :: []
  in
  let switches0 = [] in
  minBFT_simul_n { num_requests = num_requests0; starting_seq_num =
    starting_seq_num0; req_operation = (Obj.magic req_operation0) } rounds0
    switches0

(** val minBFT_simul_pp : unit **)

let minBFT_simul_pp =
  Prelude.print_coq_endline (simState2string minBFT_simul)
