(* set SGX to true to run trusted components within Graphene-SGX *)
let sgx : bool = true

(* These are available in Batteries, but we don't want to depend on Batteries *)
let to_list (s : string) : char list =
  let l = String.length s in
  let rec accum n = if n = l then [] else String.get s n :: accum (n + 1) in
  accum 0

let of_list (l : char list) : string = String.concat "" (List.map (String.make 1) l)

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

module Time = Time0

module SM =
  struct
    type 'a id = 'a

    let ret (a : 'a) : 'a = a

    let bind (p : 'a * ('a -> 'b)) : 'b = let (m,f) = p in f m

    (* the first parameter of type 'a is the name of the component *)
    let call_proc (lkup : (('a * (bool * ('i -> (unit * 'o)))) list) ref) (p : 'a * 'i) : 'o =
      let (cn,i) = p in
      let rec search l =
        match l with
        | [] -> failwith "key not found"
        | (a,(b,c)) :: l -> if a = cn
                            then ((*print_endline "found key";*)
                              if sgx && b then
                                (* this Prelude is used by the trusted component, in which case it's not supposed to depend on other trusted components *)
                                failwith "CALL-PROC"
                              else
                                snd((Obj.magic c)(i)))
                            else search l in
      search (!lkup)
  end
