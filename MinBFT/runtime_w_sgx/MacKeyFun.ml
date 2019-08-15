open Colors
open Crypto


let debug = false



let read_symmetric_key (symkeyfile : string) : Crypto.key =
  print_endline ("[reading symmetric key from " ^ symkeyfile ^ "]");
  (*Cstruct.of_string symkeyfile*)
  let ch = Pervasives.open_in symkeyfile in
  let s  = Pervasives.input_line ch in
  let _  = Pervasives.close_in ch in
  Crypto.string2key s


let lookup_replica_key (slf : Obj.t(*rep*)) (i : Obj.t(*rep*)) : Crypto.key =
  try
    read_symmetric_key ("symmetric_key" ^ string_of_int (Obj.magic slf) ^ "-" ^ string_of_int (Obj.magic i))
  with
  | _ -> read_symmetric_key ("somekeys/symmetric_key" ^ string_of_int (Obj.magic slf) ^ "-" ^ string_of_int (Obj.magic i))

let lookup_client_key (slf : Obj.t(*rep*)) (c : Obj.t(*client*)) : Crypto.key =
  try
    read_symmetric_key ("symmetric_key_client" ^ string_of_int (Obj.magic slf) ^ "-" ^ string_of_int (Obj.magic c))
  with
  | _ -> read_symmetric_key ("somekeys/symmetric_key_client" ^ string_of_int (Obj.magic slf) ^ "-" ^ string_of_int (Obj.magic c))


let rec compare_strings (s1 : string) (s2 : string) : string =
  if (0 < String.length s1) && (0 < String.length s2) then
    let a = String.sub s1 0 1 in
    let b = String.sub s2 0 1 in
    "(" ^ a ^ "|" ^ b ^ ")"
    ^ (if a = b then "+" else "-")
    ^ compare_strings (String.sub s1 1 (String.length s1 - 1)) (String.sub s2 1 (String.length s2 - 1))
  else "{" ^ s1 ^ "|" ^ s2 ^ "}"


let rec remove_left_padding (s : string) : string =
  if 0 < String.length s then
    if String.sub s 0 1 = "\x00"
    then remove_left_padding (String.sub s 1 (String.length s - 1))
    else s
  else s


(*let sign (symkeyfile : string) (i : string) : unit =
  let () = Nocrypto_entropy_unix.initialize () in

  let sym  = read_symmetric_key symkeyfile in
  let msg  = Cstruct.of_string i in
  let hmac = Nocrypto.Hash.SHA256.hmac sym msg in

  let hash = Nocrypto.Hash.SHA256.digest msg in

  print_endline ("[verified-with-padding? " ^ string_of_bool (hash = enc) ^ "]");
  print_endline ("[verified-without-padding? " ^ string_of_bool (remove_left_padding (Cstruct.to_string hash) = remove_left_padding (Cstruct.to_string enc)) ^ "]");
  print_endline (kBLU ^ "[msg-:" ^ Cstruct.to_string msg  ^ "]" ^ kNRM);
  print_endline (kRED ^ "[hash:" ^ Cstruct.to_string hash ^ "]" ^ kNRM);
  print_endline (kGRN ^ "[dec-:" ^ Cstruct.to_string dec  ^ "]" ^ kNRM);
  print_endline (kRED ^ "[enc-:" ^ Cstruct.to_string enc  ^ "]" ^ kNRM);
  ()*)


let verify_one_debug (o : Obj.t) (n : Obj.t) (sym : Crypto.key) (msg : Cstruct.t) (mac : Crypto.sign) (hmac : Crypto.sign) : unit =
  let i  = Msg.hashData2rep (Obj.magic o) in
  let ch = Pervasives.open_out ("SIGNATURES_DONT_MATCH-" ^ string_of_int i ^ "-" ^ string_of_int (Obj.magic n) ^ "-" ^ string_of_float (Unix.time ())) in
  let _  = Pervasives.output_string ch (Crypto.sign2string mac)  in
  let _  = Pervasives.output_string ch "\n===================\n" in
  let _  = Pervasives.output_string ch (Crypto.key2string sym) in
  let _  = Pervasives.output_string ch "\n-------------------\n" in
  let _  = Pervasives.output_string ch (Msg.hashData2string (Obj.magic o)) in
  let _  = Pervasives.output_string ch "\n-------------------\n" in
  let _  = Pervasives.output_string ch (Cstruct.to_string msg) in
  let _  = Pervasives.output_string ch "\n-------------------\n" in
  let _  = Pervasives.output_string ch (Crypto.sign2string hmac) in
  let _  = Pervasives.close_out ch in
  ()


let verify_one (o : Obj.t) (n : Obj.t) (sym : Crypto.key) (mac : Crypto.sign) : bool =
  (*print_endline (kCYN ^ "[verifying signature]" ^ kNRM);*)
  (*let pub_key = Sexplib.Sexp.to_string (Nocrypto.Rsa.sexp_of_pub pub) in
  print_endline ("[using public key:" ^ pub_key ^ "]");*)

  let smsg : string      = Marshal.to_string o [] in
  (*print_endline ("[message: " ^ smsg ^ "]");*)
  let msg  : Cstruct.t   = Cstruct.of_string smsg in
  let hmac : Crypto.sign = Crypto.cstruct2sign (Nocrypto.Hash.SHA256.hmac (Crypto.key2cstruct sym) msg) in

  (*print_endline (kCYN ^ "[comparing 2 macs]" ^ kNRM);*)
  let b : bool = remove_left_padding (Crypto.sign2string hmac) = remove_left_padding (Crypto.sign2string mac) in
  (
    if b then () (*print_endline "++++ signatures match ++++"*)
    else
      (
        if debug then verify_one_debug o n sym msg mac hmac else ();
        print_endline "***** signatures don't match";
        print_endline (Crypto.key2string sym);
        print_endline "-----";
        print_endline (Crypto.sign2string mac);
        print_endline "-----";
        print_endline (Crypto.sign2string hmac);
        print_endline "*****";
        ()
      (*print_endline (kBRED ^ "could not verify signature" ^ kNRM)*)

      (*;

        print_endline ("[redoing the computation]");
        print_endline ("[getting private key of sender]");
        let priv = lookup_replica_sending_key (Obj.magic 1) in
        print_endline ("[signing as if it were the sender]");
        let new_dec = Nocrypto.Rsa.decrypt priv hash in
        print_endline ("[verifying new signature]");
        let new_enc = Nocrypto.Rsa.encrypt pub new_dec in
        let b : bool = remove_left_padding (Cstruct.to_string hash) = remove_left_padding (Cstruct.to_string new_enc) in
        if b then print_endline ("[managed to redo the computation]")
        else print_endline ("[could not redo the computation]")*)
      )
  );

  (*  print_endline (kMAG ^ "[verified signature: " ^ string_of_bool b ^ "]" ^ kNRM);
  print_endline (kBLU ^ "[1: " ^ Cstruct.to_string enc  ^ "]" ^ kNRM);
  print_endline (kYEL ^ "[2: " ^ Cstruct.to_string hash ^ "]" ^ kNRM);*)
  b


let sign_one_debug (o : Obj.t) (sym : Crypto.key) (msg : Cstruct.t) (hmac : Crypto.sign) : unit =
  let i  = Msg.hashData2rep (Obj.magic o) in
  let ch = Pervasives.open_out ("SIGNING-" ^ string_of_int i ^ "-" ^ string_of_float (Unix.time ())) in
  let _  = Pervasives.output_string ch (Crypto.key2string sym) in
  let _  = Pervasives.output_string ch "\n-------------------\n" in
  let _  = Pervasives.output_string ch (Msg.hashData2string (Obj.magic o)) in
  let _  = Pervasives.output_string ch "\n-------------------\n" in
  let _  = Pervasives.output_string ch (Cstruct.to_string msg) in
  let _  = Pervasives.output_string ch "\n-------------------\n" in
  let _  = Pervasives.output_string ch (Crypto.sign2string hmac) in
  let _  = Pervasives.close_out ch in
  ()

let sign_one (o : Obj.t) (sym : Crypto.key) : Crypto.sign =
  let smsg = Marshal.to_string o [] in
  let msg  = Cstruct.of_string smsg in
  let hmac = Crypto.cstruct2sign (Nocrypto.Hash.SHA256.hmac (Crypto.key2cstruct sym) msg) in
  let _    = if debug then sign_one_debug o sym msg hmac else () in
  (*let _  = print_endline (kBRED ^ Cstruct.to_string hmac ^ kNRM) in*)
  (*let _ = print_endline (kBRED ^ "[DIGEST:" ^ Sexplib.Sexp.to_string (Cstruct_sexp.sexp_of_t hmac) ^ "]" ^ kNRM) in*)
  hmac

let sign_list (o : Obj.t) (syms : Crypto.key list) : Crypto.sign list =
  Nocrypto_entropy_unix.initialize ();
  List.map (sign_one o) syms
