#!/bin/bash


set -e


NATIVE=native
NUM_FAULTS=1


INS_MAN1=exec_victim.manifest.template
INS_MAN2=ls.manifest.template
INS_MAN3=manifest.template

NUM_REPLICAS=$(( (2*${NUM_FAULTS})+1 ))
NUM_REPLICASM1=$(( ${NUM_REPLICAS}-1 ))


# Generating the required files
./run.sh setup


# copy symmetric keys in native
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    for j in `seq 0 ${NUM_REPLICASM1}`;
    do
	cp symmetric_key${i}-${j} ${NATIVE}/
    done
done

# create native directory for each replica
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    cp -R ${NATIVE} ${NATIVE}${i}
done

# copy necessary files in native
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    cp SpPrelude.ml ${NATIVE}${i}/
    cp tcp_server.c ${NATIVE}${i}/
    cp config ${NATIVE}${i}/
    cp Msg.ml ${NATIVE}${i}/
    cp Colors.ml ${NATIVE}${i}/
    cp Crypto.ml ${NATIVE}${i}/
    cp MacKeyFun.ml ${NATIVE}${i}/
    cp USIG_extracted${i}.ml ${NATIVE}${i}/USIG_extracted.ml
done


# # change manifest in native directories so that Graphee-SGX allows use of the current keys
for k in `seq 0 ${NUM_REPLICASM1}`;
do
    for i in `seq 0 ${NUM_REPLICASM1}`;
    do
	for j in `seq 0 ${NUM_REPLICASM1}`;
	do
	    echo -e "sgx.trusted_files.key${i}${j} = file:symmetric_key${i}-${j}" >> ${NATIVE}${k}/${INS_MAN1}
	    echo -e "sgx.trusted_files.key${i}${j} = file:symmetric_key${i}-${j}" >> ${NATIVE}${k}/${INS_MAN2}
	    echo -e "sgx.trusted_files.key${i}${j} = file:symmetric_key${i}-${j}" >> ${NATIVE}${k}/${INS_MAN3}
	done
    done
done
