This is what you have to do to run USIG's MinBFT components within SGX:

(1) Run the `installsgx.sh` script at root directory of your machine
    in order to install SGX (driver, SDK and PSW) and Graphene-SGX.
    First time the script stops enter the following:

    `no`
    `/opt/intel`

    Next time the script stops enter the following:

    `/opt/intel/linux-sgx-driver/`
    `2.6`

    This script installs SGX in the `/opt/intel` directory and
    Graphene-SGX in `Desktop/graphene`. Moreover, to check that
    everything is installed properly, this script runs SGX and
    Graphine-SGX builtin examples.

    We ran our tests on an Intel® Core™ i7-6700 CPU @ 3.40GHz × 8
    machine that runs Ubuntu 18.04.1 LTS.

    NOTE: Before you're installing SGX, please make sure that
    Intel SGX is actually enabled in your BIOS, as well as that the secure
    boot is turned off.

(2) Run the `prepare.sh` script inside Asphalion's
    `MinBFT/runtime_w_sgx` directory. This is going to prepare `2*F+1`
    directories (`native0`, `native1`, ...) that eventually
    will be running inside Graphene-SGX (see below).

(3) Copy the 3 directories `native0`, `native1`,... that
    got created by step 2, to `graphene/LibOS/shim/test/`.

(4) Copy the file called `libtinfo.so.5` (which you can most probably
    find in `/lib/x86_64-linux-gnu`, otherwise search for it in your
    file system, it should be there somewhere) to the
    `graphene/Runtime` directory.

    Copy the file called `libgmp.so.10` (which you can most probably
    find in `/urs/lib/x86_64-linux-gnu`, otherwise search for it in
    your file system, it should be there somewhere) to the
    `graphene/Runtime` directory.

(5) Run USIG instances within graphene by running:
      `run_sgx.sh 0` within `native0`
      `run_sgx.sh 1` within `native1`
      `run_sgx.sh 2` within `native2`
      etc.

(6) Now, run `./run.sh SGX` in Asphalion's `MinBFT/runtime_w_sgx` and
    check that the client indeed receives replies. Note that you can
    change the parameters such as how many requests are sent, by
    editing the `run.sh` file in `MinBFT/runtime_w_sgx`.
