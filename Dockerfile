# Use an official ocaml runtime as a parent image
FROM ocaml/opam2:ubuntu

# Set the working directory to /app
WORKDIR /app

# Copy the current directory contents into the container at /app
COPY coq-tools          /app/coq-tools
COPY model              /app/model
COPY MinBFT             /app/MinBFT
COPY create_makefile.sh /app
COPY all.v              /app

USER opam
RUN sudo chown -R opam /app

# Install needed packages
RUN sudo apt-get install -y m4 libgmp-dev libncurses-dev

RUN opam switch 4.05 \
    && eval $(opam env) \
    && opam install coq.8.9.1 ppx_jane.v0.11.0 async.v0.11.0 core_extended.v0.11.0 batteries.2.9.0 rpc_parallel.v0.11.0 nocrypto.0.5.4-1 cstruct-sexp.5.0.0 bigarray-compat.1.0.0 \
    && eval $(opam env) \
    && ./create_makefile.sh \
    && make clean \
    && (cd MinBFT/runtime_w_sgx; ./run.sh setup)

RUN echo "#!/bin/bash" >> test.sh \
    && echo "(cd MinBFT/runtime_w_sgx; ./run.sh one)" >> test.sh \
    && chmod +x test.sh

# Run test.ml when the container launches
CMD ["./test.sh"]



## sudo docker build --tag=test .
## sudo docker run test
