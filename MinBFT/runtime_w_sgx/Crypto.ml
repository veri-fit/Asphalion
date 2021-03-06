module type CRYPTO =
  sig
    type sign
    type key

    val cstruct2sign : Cstruct.t -> sign
    val sign2string  : sign -> string

    val cstruct2key : Cstruct.t -> key
    val key2cstruct : key -> Cstruct.t

    val key2string  : key -> string
    val string2key  : string -> key
  end

module Crypto0 : CRYPTO =
  struct
    type sign = Cstruct.t
    type key  = Cstruct.t

    let cstruct2sign (s : Cstruct.t) : sign = s
    let sign2string  (s : sign)   : string = Cstruct.to_string s

    let cstruct2key (k : Cstruct.t) : key = k
    let key2cstruct (k : key) : Cstruct.t = k

    let key2string  (k : key) : string = Cstruct.to_string k
    let string2key  (k : string) : key = Cstruct.of_string k
  end

module Crypto1 : CRYPTO with type sign = string and type key  = string =
  struct
    type sign = string
    type key  = string

    let sanatize (s : string) : string =
      String.map (fun x -> if x = ' ' then '0' else x) s

    let cstruct2sign (s : Cstruct.t) : sign = sanatize (Cstruct.to_string s)
    let sign2string  (s : sign)   : string = s

    let cstruct2key (k : Cstruct.t) : key = Cstruct.to_string k
    let key2cstruct (k : key) : Cstruct.t = Cstruct.of_string k

    let key2string  (k : key) : string = k
    let string2key  (k : string) : key = k
  end

module Crypto = Crypto1
