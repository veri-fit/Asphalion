open Batteries;;


let print_coq_endline (s : char list) : unit = print_string (String.of_list s)

let char_list_of_int (i : int) : char list = String.to_list (string_of_int i)

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
    let time2string time = String.to_list (string_of_float ((float 1000) *. time))
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
    let time2string time = String.to_list (string_of_float ((float 1000) *. time))
  end

module Time = Time2

module SM =
  struct
    exception CALL_FAILED of string

    type 'a id = 'a

    let ret (a : 'a) : 'a = a

    let bind (p : 'a * ('a -> 'b)) : 'b = let (m,f) = p in f m

    let call_proc (lkup : (('a * ('b * ('i -> (unit * 'o)))) list) ref) (p : 'a * 'i) =
      let (cn,i) = p in
      let rec search l =
        match l with
        | [] -> raise (CALL_FAILED "key not found")
        | (a,(b,c)) :: l -> if a = cn
                            then ((*print_endline "found key";*)
                              snd((Obj.magic c)(i)))
                            else search l in
      search (!lkup)
  end
