#!/bin/bash

SGX=1 make
SGX_RUN=1 make
SGX=1 ./pal_loader tcp_server $1 config symmetric_key0-0 symmetric_key0-1 symmetric_key0-2
