CC = gcc
CFLAGS = `pkg-config --cflags glib-2.0 gio-2.0 openssl libcrypto`
LDLIBS = `pkg-config --libs   glib-2.0 gio-2.0 openssl libcrypto`

COMP_C_Files := $(wildcard *.c)
COMP_C_Files := $(filter-out sign1.c sign2.c sign_3.c, $(COMP_C_Files))

COMP_C_Objects := $(COMP_C_Files:.c=.o)


default: Replica.native Client.native Client_mac.native RsaKey.native MacKey.native Simul.native

%.o: %.c
	@$(CC) $(CFLAGS) $(LDLIBS) -c $< -o $@
	@echo "CC  <=  $<"

prog1: sign1.c sign1.ml SpPrelude.ml Colors.ml
	ocamlc -c sign1.c
	ocamlc -custom -o prog1 unix.cma Colors.ml SpPrelude.ml sign1.ml sign1.o

sign2: sign2.c $(COMP_C_Objects)
	@$(CC) $< -o $@ $(CFLAGS) $(LDLIBS) $(COMP_C_Objects)
	@echo "LINK <= $@"

prog2: sign2.o sign2.ml SpPrelude.ml Colors.ml
	ocamlc -custom -o prog2 unix.cma Colors.ml SpPrelude.ml sign2.ml sign2.o -cclib -lgio-2.0 -cclib -lgobject-2.0 -cclib -lglib-2.0 -cclib -lssl -cclib -lcrypto

# 2nd solution (prefered solution)
sign3_obj.o: sign3.ml
	ocamlfind ocamlc -o sign3_obj.o -package batteries -output-obj unix.cma bigarray.cma nums.cma batteries.cma sign3.ml

prog3: sign_3.o sign3_obj.o
	cc sign3_obj.o sign_3.o -o prog3  -L`ocamlc -where` -lcamlrun -ldl -lm -lncurses -lunix -lbigarray -lnums -Wall

Replica.native: Replica.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Replica.native

Client.native: Client.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Client.native

Client_mac.native: Client_mac.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Client_mac.native

RsaKey.native: RsaKey.ml RsaKeyFun.ml Prelude.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix RsaKey.native

CkRsaKey.native: CkRsaKey.ml CkRsaKeyFun.ml Prelude.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,cryptokit CkRsaKey.native

MacKey.native: MacKey.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix MacKey.native

Simul.native: Simul.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Simul.native

Test.native: Test.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Test.native

TestServer.native: TestServer.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix TestServer.native

TestClient.native: TestClient.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix TestClient.native

ext:
	(cd ..; make PBFT/PBFT.vo)
	(cd ..; make PBFT/PBFTcollision_resistant.vo)
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds Simulator.v
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds PBFTsim.v

sext:
	(cd ..; make PBFT/PBFT.vo)
	(cd ..; make PBFT/PBFTcollision_resistant.vo)
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds Simulator.v
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds PBFTsim_mac.v

oldext:
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds PBFTsim.v

clean:
	rm -f *.cmo
	rm -f *.cmi
	rm -f *.cma
	rm -f *.cmx
	rm -f *.native
	rm -f *.byte
	rm -f a.out
	rm -Rf _build
	rm -f PbftReplica*
	rm -f *.glob
	rm -f *.vo
	rm -f .*.aux
	rm -f *.dat
	rm -f private_key*
	rm -f public_key*
	rm -f *.o
