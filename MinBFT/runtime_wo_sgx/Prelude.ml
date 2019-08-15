open Batteries;;

(* set SGX to true to run trusted components within Graphene-SGX *)
let sgx : bool = false


let nodeid : int ref = ref 0
let getId () : int = !nodeid
let setId (i : int) : unit = nodeid := i
let printId () : unit = print_endline ("id is " ^ string_of_int (getId()))


let trustedSocket : int ref = ref 0
let getTrustedSocket () : int = !trustedSocket
let setTrustedSocket (s : int) : unit = trustedSocket := s


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
    type 'a id = 'a

    let ret (a : 'a) : 'a = a

    let bind (p : 'a * ('a -> 'b)) : 'b = let (m,f) = p in let x = m in f x

    (* the first parameter of type 'a is the name of the component *)
    let call_proc (lkup : (('a * (bool * ('i -> (unit * 'o)))) list) ref) (p : 'a * 'i) : 'o =
      let (cn,i) = p in
      let rec search l =
        match l with
        | [] -> failwith "key not found"
        | (a,(b,c)) :: l -> if a = cn
                            then ((*print_endline "found key";*)
                              if sgx && b then
                                (* The component is trusted, in which case we use the tcp interface *)
                                failwith "TODO"
                              else 
                                (snd((Obj.magic c)(i))))
                            else search l in
      (*let _ = print_endline ("lookup table has size " ^ string_of_int (List.length (!lkup))) in*)
      search (!lkup)
  end
