open Ocamlbuild_plugin
open Command

let _ =
  dispatch (function
      | After_rules ->
         pdep ["link"] "linkdep" (fun param -> [param])
      | _ -> ())

(*
(** This function implements the action for building the native C library *)
let library_build env (_build : builder) =
  let lib_main = env "%.cmxa" in
  let stub_obj = env "%_api.obj" in
  let final_link_cmd = Cmd (S [ S[A "ocamlfind"; A "ocamlopt"; 
                  S[A "-package"; A "ocamlgraph"];
                  S[A "-package"; A "batteries"];
                                  S[A "-cclib"; A "-implib"];
                  S[A "-cclib"; A "-maindll"];
                  A "-output-obj"; A "-linkpkg"; A "-linkall"]; S [A "-o"; A "ourlibrary.dll"]; P stub_obj; P lib_main]) in
  let pn_lib_main = Pathname.mk lib_main in
  let pn_stub_main = Pathname.mk stub_obj in
  let _ = _build [[pn_lib_main]; [pn_stub_main]] in 
  final_link_cmd

let () =
  dispatch (function
    | After_rules ->
       rule "Building C-DLL from OCaml with a C-API"
        ~prod:"%.clibrary"
        ~deps:["%.ml"; "%_api.c"; "%.h"]
            library_build;
       flag ["clibrary"] (A "-linkpkg");
       tag_file "<*/*.so>" ["clibrary"]
    | _ -> ())
 *)
