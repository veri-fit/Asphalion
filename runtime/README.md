=====================================================================
=--

We use Async to implement sender/receiver threads, and
[Nocrypto](http://mirleft.github.io/ocaml-nocrypto/doc/index.html) for
crypto stuff.  To install all that, run:

- opam repo add janestreet https://ocaml.janestreet.com/opam-repository
- opam install async ppx_jane core_extended rpc_parallel batteries cppo_ocamlbuild nocrypto


@Ivana: "opam install async" failed for me. I had to use
"npm install --save async". It turned out that this version does not work either

=====================================================================
=--

To use the simulator:

- run "make"
- run "./Simul.native -max XXX", where XXX is the number of requests
  to send


=====================================================================
=--

To use the runtime environment:

- run: ./run.sh

- Clients will produce data files (pbftX.dat) that can be plotted using:
    cp pbft_ts_X_R_C.dat pbft.dat; gnuplot script.p
    cp pbft_avg_X_R_C.dat pbft.dat; gnuplot script.p
  where X is the client id
        R is the number of replicas
	C is the number of clients
