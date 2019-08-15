Authors
=======

- Vincent Rahli
- Ivana Vukotic


Description
===========

Asphalion is a Coq-based framework for verifying the correctness of
implementations of fault-tolerant systems. It especially provides
features to verify the correctness of hybrid fault-tolerant systems
(such as the MinBFT protocol
http://www.di.fc.ul.pt/~bessani/publications/tc11-minimal.pdf), where
normal components (that can for example fail arbitrarily) trust some
special components (that can for example only crash on failure) to
provide properties in a trustworthy manner.  Asphalion allows running
such trusted-trustworthy components inside Intel SGX enclaves.
More details are provided here:
https://vrahli.github.io/articles/asphalion-long.pdf


Getting Started
===============

What you will find here are instructions on how to compile our proofs
and run the extracted code. If you just want to test our MinBFT
implementation, go straight to the `Running MinBFT` section. Getting
MinBFT to run without SGX should take you less than 10 minutes, and
getting MinBFT to run with SGX should take you less than 30 minutes.

SGX is not strictly necessary to use/test our framework, as we provide
runtime environments that also work without SGX. Note that to run our
MinBFT implementation on top of SGX, you will need an SGX-enabled
Intel processor. Check out the specs of your Intel processor on the
Intel website, to see if it supports SGX.

We provide a VM, where the dependencies are installed and the code is
compiled. However, you won't be able to test our SGX-based runtime
with this VM, as we have not yet found a convenient solution that
allows us to run our code on top SGX within a VM. Contact us to get
access to that VM.

Dependencies
------------

Before, you get a chance to use/test our framework, you'll have to
install everything it depends on:

* Everything here has been tested on an Ubuntu 18.04. In addition the
  non-SGX part has been on an Ubuntu 19.04. The SGX-part of our
  framework has been tested on an Ubuntu 18.04 with gcc 7.4.0.

* You will need opam version 2.0.3 to install the dependencies. Here
  are the instructions on how to install opam:
  https://opam.ocaml.org/doc/Install.html.

  Essentially, what you'll have to do is type:
    `sudo apt-get install opam mccs libgmp-dev`
    `opam init --solver=mccs`
    `eval $(opam env)`

  When running `opam init`, just answer yes to all questions.

* You will need OCaml version 4.05.0, which you will get through opam.
  Here are the instructions how to install OCaml:
  https://ocaml.org/docs/install.html.

  Essentially, you'll have to type (if you're not already using that
  one):
    `opam switch create ocaml-system.4.05.0`
    `eval $(opam env)`

* In order to install all other packages that our framework depends on
  you need to type the following command:

    `opam install coq.8.9.1 ppx_jane.v0.11.0 async.v0.11.0 core_extended.v0.11.0 batteries.2.9.0 rpc_parallel.v0.11.0 nocrypto.0.5.4-1 cstruct-sexp.5.0.0 bigarray-compat.1.0.0`

  Those are the version numbers we use. It might be that other
  versions work, but we haven't tested them. In case you get an error,
  when runing this command, just re-run it until you no longer get an
  error.

* In addition to the above, as mentioned in our
  MinBFT/runtime_w_sgx/README.md file, you will also need to install
  Intel-SGX (driver, SDK and PSW) and Graphene-SGX. The version
  numbers we indicate in MinBFT/runtime_w_sgx/README.md are the ones
  we use.

Roadmap
-------

So...let's now look at how to use/test our framework without the VM:

* Go to the `compilation` section to see how to compile our code
  (including proofs).
* Go to the `Asphalion` section to see what is Asphalion composed of,
  and where to find its different components.
* Go to the `MinBFT roadmap` section to see what our MinBFT
  formalization contains.
* Go to the `Running MinBFT` section to see how to run our MinBFT
  implementation.


DISCLAIMER
==========

As explained below, Asphalion reuses part of the code base of
Velisarios (see https://github.com/vrahli/Velisarios). Therefore, for
simplicity, this directory includes the entire code base of
Velisarios. We explain below in the `Asphalion` section, which files
are strictly part of Asphalion.



Compilation
===========

The code compiles with Coq version 8.9.0. To compile the code, first
generate a Makefile by running `./create-makefile.sh` in the root
directory of this repository.


Skip the rest of this section if you just want to execute he code. If
you want to execute our implementations (in which case you don't need
to compile all the proofs), jump to the `running PBFT` and `running
MinBFT` sections. Otherwise, keep reading.

To actually compile the whole project (Velisarios + Asphalion),
including all the proofs, then type `make -j X`, where X is the number
of jobs you want to use.  This is going to take a while (a few hours).

Note that create-makefile.sh requires a version of base >= 4.



Velisarios's roadmap
====================

- The model is in `model`.
- Our runtime environment is in `runtime`
- the `PBFT` directory provides a formalization of PBFT
- the `SM` directory provides a formalization of SM



Running PBFT
============

To run PBFT, check out `runtime/README.md`.



Asphalion
=========

Asphalion is related to Velisarios to the extent that its logic
extends the logic of events provided by Velisarios. Asphalion can be
used to implement and reason about hybrid fault-tolerant protocols as
opposed to just Byzantine fault-tolerant protocols for Velisarios. In
addition to this new extended logic (called HyLoE), Asphalion provides
a language (called MoC) to program hybrid systems as collection of
interacting components; and a knowledge calculus (called LoCK) to
reason about hybrid systems at a high level of abstraction. Its files
are:

* HyLoE: a hybrid logic of event model of distributed computation
    - `model/EventOrdering.v` contains HyLoE, our variant of
      Velisarios's logic of event, which also supports hybrid faults
      (this file is also used in Velisarios, as opposed to the other
      files mentioned here).
* MoC: a monadic component-based programming language
    - `model/ComponentSM.v` contains MoC, our monadic model of hybrid
      executable interacting components, which are shallowly embedded
      in Coq.
    - `model/ComponentSM2.v` contains a deep embedding of a simple
      language of interacting components, that contains only return,
      bind, and call.
    - `model/ComponentSM3.v` contains results regarding this simple
      language, most notably about lifting properties of (trusted)
      sub-components.
    - `model/ComponentSM5.v` contains a deep embedding of a slightly
      more complex language of interacting components, that contains
      in addition to return, bind, and call constructor, a spawn
      constructor to spawn new components.
    - `model/ComponentSM6.v` provides means to prove properties about
      collections of components compositionally.
    - `model/ComponentSMExample1.v` and `model/ComponentSMExample2.v`
      contain simple examples of systems.
    - `model/RunSM.v` contains a simulator for our component language.
    - `model/ComponentAxiom.v` contains our main axiom regarding
      hybrid systems.
* LoCK: a logic-of-event based knowledge calculus
    - `model/CalculusSM.v` contains our calculus of hybrid knowledge.
    - `model/CalculusSM_derived.v` contains further rules.
    - `model/CalculusSM_tacs.v` contains tactics that can be used
      within LoCK proofs.
* MinBFT use case
    - the `MinBFT` directory provides a formalization of two versions
      of MinBFT: a USIG-based (as in the original paper); and a
      TrInc-based. The files for the USIG-based version are called
      MinBFTxxx; while the files for the TrInc-based version are
      called TrIncxxx (with some exceptions for the shared files).
      See our `MinBFT roadmap` for more information.
      In addition this directory contains a formalization of
      simplified version of MinBFT, which we call Micro.
    - See the section `running MinBFT` for instructions on how to
      execute our implementation of MinBFT (either using or without
      using SGX).



MinBFT roadmap
==============

Some files are shared by our USIG-based and TrInc-based versions of
MinBFT, while some are USIG-specific, and some are TrInc-specific.
Note that more files could be shared by both implementations.  This is
left for future work.

* Shared files:
    - `MinBFT/MinBFTheader.v` contains basic concepts necessary to
      implement MinBFT such as node names and messages.
    - `MinBFT/USIG.v` contains an implementation of the USIG trusted
      component (this is currently loaded by `MinBFT/MinBFTg.v`
      because it also contains generic definitions such as the
      IO-interface of the trusted component, which is the same in both
      the USIG version and the TrInc version).
    - `MinBFT/TrIncUSIG.v` contains an implementation of the TrInc
      trusted component (this is currently loaded by
      `MinBFT/MinBFTg.v` because it contains generic definition).
    - `MinBFT/MinBFTg.v` contains a generic definition of MinBFT (the
      MinBFT system, including its components---the USIG component is
      left abstract here), that can be instantiated for both the USIG
      version and the TrInc version.
    - `MinBFT/MinBFTtacts.v` contains generic tactics that can be used
      to prove properties of our generic MinBFT implementation.
    - `MinBFT/MinBFTkn0.v` contains a partial instantiation of our
      knowledge theory that can be used to prove properties of our
      generic MinBFT implementation.
    - `MinBFT/MinBFTrep.v`, `MinBFT/MinBFTprops0.v`,
      `MinBFT/MinBFTbreak.v`, `MinBFT/MinBFTgen.v` contain simple
      generic definitions and properties about our generic MinBFT
      implementation.
    - `MinBFT/MinBFTcount_gen1.v` to `MinBFT/MinBFTcount_gen5.v`
      contain complex (inductive) generic properties about our generic
      MinBFT implementation.
* USIG-based version:
    - `MinBFT/MinBFT.v` contains our USIG-based instantiation of our
      generic MinBFT implementation.
    - `MinBFT/MinBFTcount.v` contains generic definitions and proofs
      of our USIG-based version of MinBFT that rely on the generic
      `MinBFT/MinBFTcount_gen` files.
    - `MinBFT/MinBFTsubs.v`, `MinBFT/MinBFTstate.v`,
      `MinBFT/MinBFTbreak0.v`, `MinBFT/MinBFTtacts2,v`,
      `MinBFT/MinBFTprops1.v`, `MinBFT/MinBFTprops2.v`,
      `MinBFT/MinBFTview.v` are definitions and proofs concerning our
      USIG-based version of MinBFT.
    - The `MinBFT/MinBFTass_` files contain proofs that the
      assumptions we made in the generic LoCK lemma we used to derive
      MinBFT's agreement property, are indeed correct.
    - Finally, `MinBFT/MinBFTagreement.v` (and the more general
      `MinBFT/MinBFTagreement_iff.v`) contains a proofs of the
      agreement property of our USIG-based version of MinBFT.
* TrInc-based version:
    - `MinBFT/TrInc.v` contains our TrInc-based instantiation of our
      generic MinBFT implementation.
    - `MinBFT/TrInccount.v` contains generic definitions and proofs
      of our USIG-based version of MinBFT that rely on the generic
      `MinBFT/MinBFTcount_gen` files.
    - `MinBFT/TrIncsubs.v`, `MinBFT/TrIncstate.v`,
      `MinBFT/TrIncbreak.v`, `MinBFT/TrInctacts,v`,
      `MinBFT/TrIncprops1.v`, `MinBFT/TrIncprops2.v`,
      `MinBFT/TrIncview.v` are definitions and proofs concerning our
      TrInc-based version of MinBFT.
    - The `MinBFT/TrIncass_` files contain proofs that the
      assumptions we made in the generic LoCK lemma we used to derive
      MinBFT's agreement property, are indeed correct.
    - Finally, `MinBFT/TrIncagreement.v` (and the more general
      `MinBFT/TrIncagreement_iff.v`) contains a proofs of the
      agreement property of our TrInc-based version of MinBFT.



Running MinBFT
==============

To test our implementation of MinBFT without SGX (the USIG-based one,
but the same can be done for the TrInc-based one), first type
`./create_makefile` in this directory, to create a Makefile (*don't*
necessarily run `make` here, otherwise it will compile everything,
even the proofs, which is going to take quite a while and might not be
what you want if you just want to execute the code). Then go to
`MinBFT/runtime_wo_sgx` and type `./run.sh`. This should start 3
replicas and 1 client, which is going to send 10 requests by default.
You can change all these parameters by editing
`MinBFT/runtime_wo_sgx/run.sh`.

The above step won't compile everything.  To compile everything (all
of Asphalion & Velisarios actually), including our MinBFT proofs, then
type `make` in this directory.  This will take a while (a few hours).

To test our implementation of MinBFT with SGX (the USIG-based one, but
the same can be done for the TrInc-based one), read
`MinBFT/runtime_w_sgx/README.md`.

Our runtime environments are implemented in OCaml (plus SGX and
Graphene-SGX for the SGX-based one). We tested them on the version
4.05.0 of OCaml (which you can obtain through opam---we're using opam
version 2.0.3). In addition they rely on the following packages, which
you can also obtain through opam: coq version 8.9.1, ppx\_jane version
v0.11.0, async version v0.11.0, core\_extended version v0.11.0,
batteries version 2.9.0, rpc\_parallel version v0.11.0, nocrypto
version 0.5.4-1, cstruct-sexp version 5.0.0, and bigarray-compat
version 1.0.0 (those are the versions we use).

To play a bit with our code, feel free to change some of the
parameters in the run.sh scripts, either in MinBFT/runtime_wo_sgx or
in MinBFT/runtime_w_sgx. Most notably, you can send more requests by
changing the value of `NUM_REQUESTS`. You can run run a larger system
that can tolerate more faults by changing the value of `NUM_FAULTS`.
Note that our configuration file currently only support
`NUM_FAULTS<6`. You can also try to kill replicas (not the first
one---number 0---though, as we haven't implemented view-change yet).
Note that there might still be some liveness issues left, as we have
only proved safety (agreement) so far.
