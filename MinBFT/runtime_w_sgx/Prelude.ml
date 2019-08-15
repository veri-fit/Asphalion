(* set SGX to true to run trusted components within Graphene-SGX *)
let debug : bool = false
let sgx   : bool = true

let of_list = Batteries.String.of_list
let to_list = Batteries.String.to_list

let print_coq_endline (s : char list) : unit = print_string (of_list s)

let char_list_of_int (i : int) : char list = to_list (string_of_int i)

module type TIME =
  sig
    type t
    val mk_time     : float -> t
    val get_time    : unit -> t
    val sub_time    : t -> t -> t
    val add_time    : t -> t -> t
    val mul_time    : t -> int -> t
    val div_time    : t -> int -> t
    val lt_time     : t -> t -> bool
    val time2string : t -> char list
  end

module Time0 : TIME =
  struct
    type t = float
    let mk_time t = t
    let get_time () = float 0
    let sub_time time1 time2 = time1 -. time2
    let add_time time1 time2 = time1 +. time2
    let mul_time time n = time *. float n
    let div_time time n = time /. float n
    let lt_time  time1 time2 = time1 < time2
    let time2string time = to_list (string_of_float ((float 1000) *. time))
  end

module Time1 : TIME =
  struct
    type t = float
    let mk_time t = t
    let get_time () = Unix.time ()
    let sub_time time1 time2 = time1 -. time2
    let add_time time1 time2 = time1 +. time2
    let mul_time time n = time *. float n
    let div_time time n = time /. float n
    let lt_time  time1 time2 = time1 < time2
    let time2string time = to_list (string_of_float ((float 1000) *. time))
  end

module Time2 : TIME =
  struct
    type t = float
    let mk_time t = t
    let get_time () = Unix.gettimeofday ()
    let sub_time time1 time2 = time1 -. time2
    let add_time time1 time2 = time1 +. time2
    let mul_time time n = time *. float n
    let div_time time n = time /. float n
    let lt_time  time1 time2 = time1 < time2
    let time2string time = to_list (string_of_float ((float 1000) *. time))
  end

module Time = Time2

external call_c_tcp_client : 'a -> 'b = "caml_tcp_client"

module SM =
  struct
    type 'a id = 'a

    let ret (a : 'a) : 'a = a

    let bind (p : 'a * ('a -> 'b)) : 'b = let (m,f) = p in f m

    (* the first parameter of type 'a is the name of the component *)
    let call_proc (lkup : (('a * (bool * ('i -> (unit * 'o)))) list) ref) (p : 'a * 'i) : 'o =
      let _ = if debug then print_endline "[CALL_PROC]" else () in
      let (cn,i) = p in
      let rec search l =
        match l with
        | [] -> failwith "key not found"
        | (a,(b,c)) :: l -> if a = cn
                            then ((*print_endline "found key";*)
                              if sgx && b then
                                (* The component is trusted, in which case we use the tcp interface *)
                                (if debug then print_endline "SGX-CALL-PROC" else ();
                                 Obj.magic (call_c_tcp_client (Obj.magic i)))
                              else
                                snd((Obj.magic c)(i)))
                            else search l in
      search (!lkup)
  end
