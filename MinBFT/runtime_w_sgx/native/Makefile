EXTRACTED=USIG_extracted
SERVER=tcp_server
PRELUDE=SpPrelude
MSG=Msg
COLORS=Colors
MACKEYFUN=MacKeyFun
CRYPTO=Crypto
#MACKEY=MacKey



special_executables = ${SERVER}
c_executables = $(filter-out $(special_executables),$(patsubst %.c,%,$(wildcard *.c)))
cxx_executables = $(patsubst %.cpp,%,$(wildcard *.cpp))
manifests = $(patsubst %.template,%,$(wildcard *.manifest.template)) manifest

exec_target = $(special_executables) $(c_executables) $(cxx_executables) ls.manifest
target = $(exec_target) $(manifests)

OCAMLC=ocamlc

CC=cc

App_C_Files := ${SERVER}.c
ML_Files := ${EXTRACTED}.ml
ML_Objects := $(ML_Files:.ml=_camlcode.o)

App_Link_Flags := -L`ocamlc -where` -lcamlrun -ldl -lm -lncurses
App_C_Objects := $(App_C_Files:.c=.o)
App_Name := foo


level = ../
include ../Makefile

CFLAGS-libos = -I$(SHIMDIR)/../include -L$(SHIMDIR)/../../glibc-build/libos

ifeq ($(SYS),x86_64-linux-gnu)

$(c_executables): %: %.c
	echo ["native cx:" $@ ]
	$(CC) $(CFLAGS) $(if $(findstring .libos,$@),$(CFLAGS-libos),) -o $@ $<
##\
##	$(shell echo $@ | sed 's/^[^\.]*//g' | sed 's/\./ -l/g')

##$(cxx_executables): %: %.cpp
##	echo [ "native cppx:" $@ ]
##	$(CC) $(CFLAGS) $(if $(findstring .libos,$@),$(CFLAGS-libos),) -o $@ $< \
##	$(shell echo $@ | sed 's/^[^\.]*//g' | sed 's/\./ -l/g')

${SERVER}: %: %.c  ${EXTRACTED}.ml
	echo ["xxx ${SERVER} xxx" $@ ]
	ocamlc -c ${SERVER}.c
##	ocamlc -output-obj -o ${EXTRACTED}.o ${PRELUDE}.ml ${EXTRACTED}.ml
##	ocamlfind ocamlc -o ${EXTRACTED}.o -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cstruct -output-obj -thread zarith.cma unix.cma spawn.cma sexplib0.cma threads/threads.cma caml.cma shadow_stdlib.cma bigarray.cma base.cma typerep_lib.cma stdio.cma ppx_bench_lib.cma ppx_compare_lib.cma ppx_inline_test_lib.cma ppx_sexp_conv_lib.cma parsexp.cma sexplib.cma sexplib_unix.cma ppx_assert_lib.cma md5_lib.cma bin_shape_lib.cma bin_prot.cma inline_test_config.cma base_for_tests.cma expect_test_common.cma expect_test_config.cma expect_test_collector.cma splittable_random.cma core_kernel.cma core.cma async_kernel.cma async_unix.cma async_extra.cma async.cma cstruct.cma nocrypto.cma nocrypto_unix.cma nums.cma batteries.cma ${COLORS}.ml ${MSG}.ml ${MACKEYFUN}.ml ${PRELUDE}.ml ${EXTRACTED}.ml
	ocamlfind ocamlc -o ${EXTRACTED}.o -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cstruct -output-obj -thread zarith.cma unix.cma sexplib0.cma bigarray.cma ppx_sexp_conv_lib.cma parsexp.cma sexplib.cma cstruct.cma nocrypto.cma nocrypto_unix.cma nums.cma batteries.cma ${COLORS}.ml ${MSG}.ml ${CRYPTO}.ml ${MACKEYFUN}.ml ${PRELUDE}.ml ${EXTRACTED}.ml
##	cc ${SERVER}.o ${EXTRACTED}.o -o ${SERVER} -L`ocamlc -where` -lcamlrun -ldl -lm -lncurses -Wall	
##	cc tcp_server.o ${EXTRACTED}.o -o ${SERVER} -L`ocamlc -where` -L`opam var zarith:lib` -L`opam var core:lib` -L`opam var nocrypto:lib` -lcamlrun -ldl -lm -lncurses -lbigarray -lnums -lzarith -lgmp `opam var core:lib`/*.a `opam var nocrypto:lib`/*.a `opam var spawn:lib`/*.a `opam var core_kernel:lib`/*.a `opam var base:lib`/*.a `opam var bin_prot:lib`/*.a `opam var cstruct:lib`/*.a `opam var async_unix:lib`/*.a `opam var ppx_expect:lib`/collector/*.a  -lthreads -lpthread -lunix -Wall
	cc tcp_server.o ${EXTRACTED}.o -o ${SERVER} -L`ocamlc -where` -L`opam var zarith:lib` -L`opam var nocrypto:lib` `opam var nocrypto:lib`/*.a `opam var cstruct:lib`/*.a -lcamlrun -ldl -lm -lncurses -lbigarray -lnums -lzarith -lgmp -lunix -Wall
##\
##	$(shell echo $@ | sed 's/^[^\.]*//g' | sed 's/\./ -l/g')

##pie: %: %.c
##	echo [ "native piex:" $@ ]
##	$(CC) $(CFLAGS) -fPIC --pie -o $@ $< \
##	$(shell echo $@ | sed 's/^[^\.]*//g' | sed 's/\./ -l/g')

else
.IGNORE: $(special_executables) $(c_executables) $(cxx_executables)
$(special_executables) $(c_executables) $(cxx_executables):
endif

mlclean:
	rm -f *.o
	rm -f *.cmo
	rm -f *.cmi
