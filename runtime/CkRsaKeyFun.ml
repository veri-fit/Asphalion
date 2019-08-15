(* Uses cryptokit *)

open Colors
open Core
open Async


let () = Nocrypto_entropy_unix.initialize ()


type key =
  | PrivK of Cryptokit.RSA.key
  | PubK  of Cryptokit.RSA.key

let to_code (s : string) : string =
  let x : string ref = ref "" in
  String.iter
    s
    (fun c ->
      if !x = "" then x := string_of_int (Char.to_int c)
      else x := !x ^ "." ^ string_of_int (Char.to_int c)); !x

let from_code (s : string) : string =
  String.concat
    (List.map
       (String.split s ~on:'.')
       (fun (x : string) -> match Char.of_int (int_of_string x) with
                            | Some x -> String.of_char x
                            | None -> ""))


let key2pub (key : Cryptokit.RSA.key) : string =
  "("
  ^ "(size " ^ string_of_int key.size ^ ")"
  ^ "(n "    ^ to_code key.n ^ ")"
  ^ "(e "    ^ to_code key.e ^ ")"
  ^ ")"

let key2priv (key : Cryptokit.RSA.key) : string =
  "("
  ^ "(size " ^ string_of_int key.size ^ ")"
  ^ "(n "    ^ to_code key.n ^ ")"
  ^ "(e "    ^ to_code key.e ^ ")"
  ^ "(d "    ^ to_code key.d ^ ")"
  ^ "(p "    ^ to_code key.p ^ ")"
  ^ "(q "    ^ to_code key.q ^ ")"
  ^ "(dp "   ^ to_code key.dp ^ ")"
  ^ "(dq "   ^ to_code key.dq ^ ")"
  ^ "(qinv " ^ to_code key.qinv ^ ")"
  ^ ")"

let pub2key (s : string) : Cryptokit.RSA.key =
  let r = Str.regexp "((size \\([0-9.]+\\))(n \\([0-9.]+\\))(e \\([0-9.]+\\)))" in
  {size = int_of_string (Str.replace_first r "\\1" s);
   n    = from_code (Str.replace_first r "\\2" s);
   e    = from_code (Str.replace_first r "\\3" s);
   d    = "";
   p    = "";
   q    = "";
   dp   = "";
   dq   = "";
   qinv = ""}

let priv2key (s : string) : Cryptokit.RSA.key =
  let r = Str.regexp "((size \\([0-9.]+\\))(n \\([0-9.]+\\))(e \\([0-9.]+\\))(d \\([0-9.]+\\))(p \\([0-9.]+\\))(q \\([0-9.]+\\))(dp \\([0-9.]+\\))(dq \\([0-9.]+\\))(qinv \\([0-9.]+\\)))" in
  {size = int_of_string (Str.replace_first r "\\1" s);
   n    = from_code (Str.replace_first r "\\2" s);
   e    = from_code (Str.replace_first r "\\3" s);
   d    = from_code (Str.replace_first r "\\4" s);
   p    = from_code (Str.replace_first r "\\5" s);
   q    = from_code (Str.replace_first r "\\6" s);
   dp   = from_code (Str.replace_first r "\\7" s);
   dq   = from_code (Str.replace_first r "\\8" s);
   qinv = from_code (Str.replace_first r "\\9" s)}

let export_key printb privatekeyfile publickeyfile : unit Deferred.t =
  print_endline ("[export keys---private:" ^ privatekeyfile ^ ";public:" ^ publickeyfile ^ "]");

  let prng = Cryptokit.Random.pseudo_rng (Cryptokit.Random.string Cryptokit.Random.secure_rng 160) in
  let key : Cryptokit.RSA.key = Cryptokit.RSA.new_key ~rng:prng ~e:65537 2048 in
  (*let key : Cryptokit.RSA.key = Cryptokit.RSA.new_key 2048 in*)
  let priv_key : string = key2priv key in
  let pub_key  : string = key2pub key in

  Writer.open_file ~append:(false) privatekeyfile
  >>= fun privw ->
  let _ = Writer.write privw (priv_key ^ "\n") in
  let _ =
    if printb
    then print_endline ("[private key exported to " ^ privatekeyfile ^ ": " ^ priv_key ^ "]")
    else print_endline ("[private key exported to " ^ privatekeyfile ^ "]") in

  Writer.open_file ~append:(false) publickeyfile
  >>= fun pubw ->
  let _ = Writer.write pubw (pub_key ^ "\n") in
  let _ =
    if printb
    then print_endline ("[public key exported to " ^ publickeyfile ^ ": " ^ pub_key ^ "]")
    else print_endline ("[public key exported to " ^ publickeyfile ^ "]") in

  Deferred.return ()


let read_private_key (privatekey : string) : Cryptokit.RSA.key =
  print_endline ("[reading private key from " ^ privatekey ^ "]");
  let ic   = Pervasives.open_in privatekey in
  let line = Pervasives.input_line ic in
  let key  = priv2key line in
  let _    = Pervasives.close_in ic in
  key

let read_public_key  (publickey  : string) : Cryptokit.RSA.key  =
  print_endline ("[reading public key from " ^ publickey ^ "]");
  let ic   = Pervasives.open_in publickey in
  let line = Pervasives.input_line ic in
  let key  = pub2key line in
  let _    = Pervasives.close_in ic in
  key


let read_key privatekey publickey : unit Deferred.t =
  let priv : Cryptokit.RSA.key = read_private_key privatekey in
  let pub  : Cryptokit.RSA.key = read_public_key publickey in
  let priv_key : string = key2priv priv in
  let pub_key  : string = key2pub pub in
  print_endline ("[private key read from " ^ privatekey ^ ": " ^ priv_key ^ "]");
  print_endline ("[public key read from " ^ publickey ^ ": " ^ pub_key ^ "]");
  Deferred.return ()


let lookup_replica_sending_key (i : Obj.t(*rep*)) : Cryptokit.RSA.key =
  try
    read_private_key ("ck_private_key" ^ string_of_int (Obj.magic i))
  with
  | _ -> read_private_key ("somekeys/ck_private_key" ^ string_of_int (Obj.magic i))

let lookup_client_sending_key (c : Obj.t(*client*)) : Cryptokit.RSA.key =
  try
    read_private_key ("ck_private_key_client" ^ string_of_int (Obj.magic c))
  with
  | _ -> read_private_key ("somekeys/ck_private_key_client" ^ string_of_int (Obj.magic c))

let lookup_replica_receiving_key (i : Obj.t(*rep*)) : Cryptokit.RSA.key =
  try
    read_public_key ("public_key" ^ string_of_int (Obj.magic i))
  with
  | _ -> read_public_key ("somekeys/ck_public_key" ^ string_of_int (Obj.magic i))

let lookup_client_receiving_key (c : Obj.t(*client*)) : Cryptokit.RSA.key =
  try
    read_public_key ("ck_public_key_client" ^ string_of_int (Obj.magic c))
  with
  | _ -> read_public_key ("somekeys/ck_public_key_client" ^ string_of_int (Obj.magic c))


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


let sign (privatekey : string) (publickey : string) (msg : string) : unit =
  (*let () = Nocrypto_entropy_unix.initialize () in*)

  let priv = read_private_key privatekey in
  let pub  = read_public_key publickey in

  let hash = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) msg in
  let dec  = Cryptokit.RSA.decrypt priv hash in
  let enc  = Cryptokit.RSA.encrypt pub dec in

  print_endline ("[verified-with-padding? " ^ string_of_bool (hash = enc) ^ "]");
  print_endline ("[verified-without-padding? " ^ string_of_bool (remove_left_padding hash = remove_left_padding enc) ^ "]");
  print_endline (kBLU ^ "[msg-:" ^ msg  ^ "]" ^ kNRM);
  print_endline (kRED ^ "[hash:" ^ hash ^ "]" ^ kNRM);
  print_endline (kGRN ^ "[dec-:" ^ dec  ^ "]" ^ kNRM);
  print_endline (kRED ^ "[enc-:" ^ enc  ^ "]" ^ kNRM);
  ()



let verify_one (o : Obj.t) (n : Obj.t) (pub : Cryptokit.RSA.key) (dec : string) : bool =
(*  print_endline (kCYN ^ "[verifying signature]" ^ kNRM);
  let pub_key = Sexplib.Sexp.to_string (Nocrypto.Rsa.sexp_of_pub pub) in
  print_endline ("[using public key:" ^ pub_key ^ "]");*)

  let msg  = Marshal.to_string o [] in
  let hash = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) msg in
  let enc  = Cryptokit.RSA.encrypt pub dec in
  let b : bool = remove_left_padding hash = remove_left_padding enc in
  (
    if b then ()
    else
      (
        print_endline (kBRED ^ "could not verify signature" ^ kNRM)(*;

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


let sign_one (o : Obj.t) (priv : Cryptokit.RSA.key) : string =
  (*print_endline (kCYN ^ "[signing message]" ^ kNRM);*)
  let msg  = Marshal.to_string o [] in
  (*print_endline ("[message: " ^ smsg ^ "]");*)
  let hash = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) msg in
  (*print_endline ("[hash:" ^ Cstruct.to_string hash ^ "]");*)
  let dec  = Cryptokit.RSA.decrypt priv hash in
  (*print_endline (kMAG ^ "[signed message]" ^ kNRM);*)
  dec

let sign_list (o : Obj.t) (privs : Cryptokit.RSA.key list) : string list =
  List.map privs (sign_one o)

let test () =
  let o : Obj.t = Obj.magic "foo" in
  let priv : Cryptokit.RSA.key = read_private_key "ck_private_key1" in
  let pub : Cryptokit.RSA.key = read_public_key "ck_public_key1" in


  (* SIGNATURE *)
(*  let time1 = Prelude.Time.get_time () in
  (*Nocrypto_entropy_unix.initialize ();*)
  print_endline (kYEL ^ "[sign init: " ^ Batteries.String.of_list (Prelude.Time.time2string (Prelude.Time.sub_time (Prelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);*)

  let time1 = Prelude.Time.get_time () in
  let msg = Marshal.to_string o [] in
  print_endline (kYEL ^ "[sign marsh: " ^ Batteries.String.of_list (Prelude.Time.time2string (Prelude.Time.sub_time (Prelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);

  let time1 = Prelude.Time.get_time () in
  let hash = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) msg in
  print_endline (kYEL ^ "[sign hash: " ^ Batteries.String.of_list (Prelude.Time.time2string (Prelude.Time.sub_time (Prelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);

  let time1 = Prelude.Time.get_time () in
  let dec  = Cryptokit.RSA.decrypt priv hash in
  print_endline (kYEL ^ "[sign decrypt: " ^ Batteries.String.of_list (Prelude.Time.time2string (Prelude.Time.sub_time (Prelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);


  (* VERIFICATION *)
  let time1 = Prelude.Time.get_time () in
  let msg : string = Marshal.to_string o [] in
  print_endline (kYEL ^ "[verif mash: " ^ Batteries.String.of_list (Prelude.Time.time2string (Prelude.Time.sub_time (Prelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);

  let time1 = Prelude.Time.get_time () in
  let hash = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) msg in
  print_endline (kYEL ^ "[verif hash: " ^ Batteries.String.of_list (Prelude.Time.time2string (Prelude.Time.sub_time (Prelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);

  let time1 = Prelude.Time.get_time () in
  let enc  = Cryptokit.RSA.encrypt pub dec in
  print_endline (kYEL ^ "[verif encrypt: " ^ Batteries.String.of_list (Prelude.Time.time2string (Prelude.Time.sub_time (Prelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);

  let time1 = Prelude.Time.get_time () in
  let _ : bool = remove_left_padding hash = remove_left_padding enc in
  print_endline (kYEL ^ "[verif comp: " ^ Batteries.String.of_list (Prelude.Time.time2string (Prelude.Time.sub_time (Prelude.Time.get_time ()) time1)) ^ "]" ^ kNRM);
  ()
