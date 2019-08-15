EXTRACTED=MinbftReplica
USIG=USIG_extracted
REPLICA=Replica
PRELUDE=Prelude
SPPRELUDE=SpPrelude
MACKEYFUN=MacKeyFun
MACKEY=MacKey
CRYPTO=Crypto
EXPORT=Export
MSG=Msg
COLORS=Colors
SERVER=server
BUILD=_build


default: ${EXTRACTED}.native ${REPLICA}.native Client.native RsaKey.native MacKey.native server

ext: ${EXTRACTED}.ml ${USIG}.ml


## Client to the USIG
${EXTRACTED}.ml: MinBFTinstance.v MinBFTinstance_main.v
	(cd ../..; make model/ASPHALIONall.vo)
	(cd ../..; make MinBFT/MinBFT.vo)
	coqc -R ../../coq-tools util -R ../../model model -R ../../MinBFT MinBFT MinBFTinstance.v
	coqc -R ../../coq-tools util -R ../../model model -R ../../MinBFT MinBFT MinBFTinstance_main.v
	# This is because we don't seem to be able to get rid of the last argument during extraction
	sed -i -- "s/lookup_table __/lookup_table/g" ${EXTRACTED}.ml
	sed -i -- "s/lookup_table _/lookup_table/g" ${EXTRACTED}.ml
	sed -i -- "s/val lookup_table : __ ->/val lookup_table :/g" ${EXTRACTED}.mli

${EXTRACTED}.native: ${EXTRACTED}.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix ${EXTRACTED}.native

tcp_client.o: tcp_client.c
	ocamlbuild tcp_client.o


client: tcp_client.o ${EXTRACTED}.o
	cc tcp_client.o ${EXTRACTED}.o -o client -L`ocamlc -where` -lcamlrun -ldl -lm -lncurses -Wall

${REPLICA}.native: ${REPLICA}.ml tcp_client.o ${EXTRACTED}.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix ${REPLICA}.native

Client.native: Client.ml tcp_client.o ${EXTRACTED}.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Client.native

RsaKey.native: RsaKeyFun.ml RsaKey.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix RsaKey.native

${MACKEY}.native: ${MSG}.ml ${CRYPTO}.ml ${MACKEYFUN}.ml ${EXPORT}.ml ${MACKEY}.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix ${MACKEY}.native


## Server running the USIG
tcp_server.o: tcp_server.c
	ocamlc -c tcp_server.c

# ${BUILD}/tcp_server.o: tcp_server.o
# 	mv tcp_server.o ${BUILD}/

${USIG}.ml: MinBFTinstance.v MinBFTinstance_usig.v
	(cd ../..; make model/ASPHALIONall.vo)
	(cd ../..; make MinBFT/MinBFT.vo)
	coqc -R ../../coq-tools util -R ../../model model -R ../../MinBFT MinBFT MinBFTinstance.v
	coqc -R ../../coq-tools util -R ../../model model -R ../../MinBFT MinBFT MinBFTinstance_usig.v
	# This is because we don't seem to be able to get rid of the last argument during extraction
	sed -i -- "s/Prelude/SpPrelude/g" ${USIG}.ml
	sed -i -- "s/lookup_table __/lookup_table/g" ${USIG}.ml
	sed -i -- "s/lookup_table _/lookup_table/g" ${USIG}.ml
	sed -i -- "s/val lookup_table : __ ->/val lookup_table :/g" ${USIG}.mli
	rm ${USIG}.mli

${USIG}.native: ${USIG}.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix ${USIG}.native

${USIG}.o: ${USIG}.native
	#ocamlc -output-obj -o ${USIG}.o ${SPPRELUDE}.ml ${USIG}.ml
	#ocamlfind ocamlc -o ${USIG}.o -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cstruct -output-obj -thread zarith.cma unix.cma spawn.cma sexplib0.cma threads/threads.cma caml.cma shadow_stdlib.cma bigarray.cma base.cma typerep_lib.cma stdio.cma ppx_bench_lib.cma ppx_compare_lib.cma ppx_inline_test_lib.cma ppx_sexp_conv_lib.cma parsexp.cma sexplib.cma sexplib_unix.cma ppx_assert_lib.cma md5_lib.cma bin_shape_lib.cma bin_prot.cma inline_test_config.cma base_for_tests.cma expect_test_common.cma expect_test_config.cma expect_test_collector.cma splittable_random.cma core_kernel.cma core.cma async_kernel.cma async_unix.cma async_extra.cma async.cma cstruct.cma nocrypto.cma nocrypto_unix.cma nums.cma batteries.cma ${COLORS}.ml ${MSG}.ml ${CRYPTO}.ml ${MACKEYFUN}.ml ${SPPRELUDE}.ml ${USIG}.ml
	ocamlfind ocamlc -o ${USIG}.o -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cstruct,bigarray-compat -output-obj -thread zarith.cma unix.cma sexplib0.cma bigarray.cma bigarray_compat.cma ppx_sexp_conv_lib.cma parsexp.cma sexplib.cma cstruct.cma nocrypto.cma nocrypto_unix.cma nums.cma batteries.cma ${COLORS}.ml ${MSG}.ml ${CRYPTO}.ml ${MACKEYFUN}.ml ${SPPRELUDE}.ml ${USIG}.ml

# ${BUILD}/${USIG}.o: ${USIG}.o
# 	#mv ${SPPRELUDE}.o   ${BUILD}/
# 	mv ${SPPRELUDE}.cmi ${BUILD}/
# 	mv ${SPPRELUDE}.cmo ${BUILD}/
# 	mv ${USIG}.o   ${BUILD}/
# 	mv ${USIG}.cmi ${BUILD}/
# 	mv ${USIG}.cmo ${BUILD}/

${SERVER}: ${USIG}.o tcp_server.o
	#cc tcp_server.o ${USIG}.o -o ${SERVER} -L`ocamlc -where` -lcamlrun -ldl -lm -lncurses -lunix -lbigarray -lnums -Wall
	#cc tcp_server.o ${USIG}.o -o ${SERVER} -L`ocamlc -where` -L`opam var zarith:lib` -L`opam var core:lib` -L`opam var nocrypto:lib` -lcamlrun -ldl -lm -lncurses -lbigarray -lnums -lzarith -lgmp `opam var core:lib`/*.a `opam var nocrypto:lib`/*.a `opam var spawn:lib`/*.a `opam var core_kernel:lib`/*.a `opam var base:lib`/*.a `opam var bin_prot:lib`/*.a `opam var cstruct:lib`/*.a `opam var async_unix:lib`/*.a `opam var ppx_expect:lib`/collector/*.a -lthreads -lpthread -lunix -Wall
	cc tcp_server.o ${USIG}.o -o ${SERVER} -L`ocamlc -where` -L`opam var zarith:lib` -L`opam var nocrypto:lib` `opam var nocrypto:lib`/*.a `opam var cstruct:lib`/*.a -lcamlrun -ldl -lm -lncurses -lbigarray -lnums -lzarith -lgmp -lunix -Wall


## Clean
clean:
	rm -f *.a
	rm -f *.o
	rm -f *.cmo
	rm -f *.cmi
	rm -f *.cma
	rm -f *.native
	rm -f *.byte
	rm -f a.out
	rm -Rf _build
	rm -f ${EXTRACTED}*
	rm -f ${USIG}*
	rm -f ${SERVER}*
	rm -f *.glob
	rm -f *.vo
	rm -f .*.aux
	rm -f *.dat
	rm -f private_key*
	rm -f public_key*
	rm -f symmetric_key*
	rm -f native/symmetric_key*
	mv native original_native
	rm -rf native*
	mv original_native native
