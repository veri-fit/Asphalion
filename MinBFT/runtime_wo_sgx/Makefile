EXTRACTED=MinbftReplica
REPLICA=Replica

default: ${EXTRACTED}.native ${REPLICA}.native Client.native RsaKey.native MacKey.native

ext: ${EXTRACTED}.ml

${EXTRACTED}.ml: MinBFTinstance.v Prelude.ml
	(cd ../..; make model/ASPHALIONall.vo)
	(cd ../..; make MinBFT/MinBFT.vo)
	coqc -R ../../coq-tools util -R ../../model model -R ../../MinBFT MinBFT MinBFTinstance.v
	# This is because we don't seem to be able to get rid of the last argument during extraction
	sed -i -- "s/lookup_table __/lookup_table/g" ${EXTRACTED}.ml
	sed -i -- "s/lookup_table _/lookup_table/g" ${EXTRACTED}.ml
	sed -i -- "s/val lookup_table : __ ->/val lookup_table :/g" ${EXTRACTED}.mli

${EXTRACTED}.native: ${EXTRACTED}.ml Prelude.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cstruct-sexp ${EXTRACTED}.native

${REPLICA}.native: ${REPLICA}.ml ${EXTRACTED}.ml Prelude.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cstruct-sexp ${REPLICA}.native

Client.native: Client.ml ${EXTRACTED}.ml Prelude.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cstruct-sexp Client.native

RsaKey.native: RsaKey.ml Prelude.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cstruct-sexp RsaKey.native

MacKey.native: MacKey.ml Prelude.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cstruct-sexp MacKey.native


## Clean
clean:
	rm -f *.a
	rm -f *.cmo
	rm -f *.cmi
	rm -f *.cma
	rm -f *.native
	rm -f *.byte
	rm -f a.out
	rm -Rf _build
	rm -f ${EXTRACTED}*
	rm -f *.glob
	rm -f *.vo
	rm -f .*.aux
	rm -f *.dat
	rm -f private_key*
	rm -f public_key*
	rm -f symmetric_key*
