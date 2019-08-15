#!/bin/bash


set -e


TERMINAL=gnome-terminal
CONF_FILE=config
NUM_REQUESTS=10
NUM_FAULTS=1
NUM_CLIENTS=1
PRINTING_PERIOD=1
PLOTTING_PERIOD=100

INS_FILE=MinBFTinstance.v
# Same as in Makefile:
EXTRACTED=MinbftReplica
REPLICA=Replica

NUM_REPLICAS=$(( (2*${NUM_FAULTS})+1 ))
NUM_REPLICASM1=$(( ${NUM_REPLICAS}-1 ))
NUM_CLIENTSM1=$(( ${NUM_CLIENTS}-1 ))


# Create a Makefile in case that hasn't been done yet
(cd ../..; ./create_makefile.sh)


# Sets number of faults and clients
sed -i -- "s/Definition F := [0-9]*/Definition F := ${NUM_FAULTS}/g"    ${INS_FILE}
sed -i -- "s/Definition C := [0-9]*/Definition C := ${NUM_CLIENTSM1}/g" ${INS_FILE}


# Extract the code
make ext


# Compile OCaml files
make
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    cp ${EXTRACTED}.ml ${EXTRACTED}${i}.ml
    sed -i -- "s/let self = Obj.magic 0/let self = Obj.magic ${i}/g" ${EXTRACTED}${i}.ml

    cp ${REPLICA}.ml ${REPLICA}${i}.ml
    sed -i -- "s/${EXTRACTED}/${EXTRACTED}${i}/g" ${REPLICA}${i}.ml

    make ${REPLICA}${i}.native REPLICA=${REPLICA}${i} EXTRACTED=${EXTRACTED}${i}
done


# Replica keys
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    ./RsaKey.native -priv private_key${i} -pub public_key${i} -print false
    for j in `seq 0 ${NUM_REPLICASM1}`;
    do
	./MacKey.native -sym symmetric_key${i}-${j} -symsrc ${i} -symdst ${j} -print false
    done
done


# Client keys
for i in `seq 0 ${NUM_CLIENTSM1}`;
do
    ./RsaKey.native -priv private_key_client${i} -pub public_key_client${i} -print false
done


# Replicas
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    ${TERMINAL} --title=replica${i} --geometry 60x20+$(( 100*(${i}+1) ))+$(( 100*(${i}+1) )) -x ./${REPLICA}${i}.native -id ${i} -num-faults ${NUM_FAULTS} -num-clients ${NUM_CLIENTS} -conf ${CONF_FILE}
done


sleep 2


# Clients
for i in `seq 0 ${NUM_CLIENTSM1}`;
do
    ${TERMINAL} --title=client${i} --geometry 150x40+$(( 500+(100*(${i}+1)) ))+$(( 100*(${i}+1) )) -x ./Client.native -id ${i} -max ${NUM_REQUESTS} -num-faults ${NUM_FAULTS} -printing-period ${PRINTING_PERIOD} -plotting-period ${PLOTTING_PERIOD} -conf ${CONF_FILE}
done
