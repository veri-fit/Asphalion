# Use an official ocaml runtime as a parent image
FROM ocaml/opam2:4.05

# Set the working directory to /app
WORKDIR /app

RUN sudo chown opam /app
USER opam

# Copy the current directory contents into the container at /app
COPY test.ml /app
## COPY ../coq-tools          /app
## COPY ../model              /app
## COPY ../MinBFT             /app
## COPY ../create_makefile.sh /app

# Install any needed packages
RUN sudo apt-get install -y m4 libgmp-dev
## RUN opam install coq.8.9.0 ppx_jane.v0.11.0 async.v0.11.0 core_extended.v0.11.0 batteries.2.9.0 rpc_parallel.v0.11.0 nocrypto.0.5.4-1 cstruct-sexp.4.0.0 bigarray-compat.1.0.0
RUN opam install batteries \
    && eval $(opam env) \
    && ocamlbuild -use-ocamlfind -package batteries test.native

# Run test.ml when the container launches
CMD ["./test.native"]
