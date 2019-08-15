#!/bin/bash


set -e


# 1st argument is either
#   - 'setup' to just compile the files
#   - 'run'   to run the code without compiling it and without SGX (within multiple terminals)
#   - 'one'   to run the code without compiling it and without SGX (within 1 terminal)
#   - 'SGX'   to compile the code and run USIGs within SGX
#   - no argument means to compile the code and run it without SGX

echo `pwd`

if [ "$1" = "" ]
then
    echo "you're not using any option, which means that you want to compile and run without SGX"
elif [ "$1" = "setup" ]
then
    echo "you're using the 'setup' option to compile the files"
elif [ "$1" = "run" ]
then
    echo "you're using the 'run' option to run the code (in multiple terminals) without compiling it and without SGX"
elif [ "$1" = "one" ]
then
    echo "you're using the 'one' option to run the code (in one terminal) without compiling it and without SGX"
elif [ "$1" = "SGX" ]
then
    echo "you're using the 'SGX' option to compile the code and execute USIGs inside SGX"
else
    echo "this option doesn't exist"
    exit 1
fi



TERMINAL=gnome-terminal
CONF_FILE=config
NUM_REQUESTS=10
NUM_FAULTS=1
NUM_CLIENTS=1
PRINTING_PERIOD=1
PLOTTING_PERIOD=1


INS_FILE=MinBFTinstance.v
# Same as in Makefile:
EXTRACTED=MinbftReplica
USIG=USIG_extracted
REPLICA=Replica
SERVER=server


INS_SCRIPT=prepare.sh


NUM_REPLICAS=$(( (2*${NUM_FAULTS})+1 ))
NUM_REPLICASM1=$(( ${NUM_REPLICAS}-1 ))
NUM_CLIENTSM1=$(( ${NUM_CLIENTS}-1 ))



if [ "$1" = "run" ] || [ "$1" = "one" ]
then
    echo "---skipping setup stuff---"
else
    # Create a Makefile in case that hasn't been done yet
    (cd ../..; ./create_makefile.sh)


    # Sets number of faults and clients
    sed -i -- "s/Definition F := [0-9]*/Definition F := ${NUM_FAULTS}/g"    ${INS_FILE}
    sed -i -- "s/Definition C := [0-9]*/Definition C := ${NUM_CLIENTSM1}/g" ${INS_FILE}


    # Sets number of faults in script prepare.sh
    sed -i -- "s/NUM_FAULTS=[0-9]*/NUM_FAULTS=${NUM_FAULTS}/g"    ${INS_SCRIPT}


    # Extraction
    make ext


    # Compile OCaml files
    rm -f *.native *.o *.cmo *.cmi
    make RsaKey.native
    make MacKey.native
    make Client.native
    for i in `seq 0 ${NUM_REPLICASM1}`;
    do
        cp ${EXTRACTED}.ml ${EXTRACTED}${i}.ml
        sed -i -- "s/let self = Obj.magic 0/let self = Obj.magic ${i}/g" ${EXTRACTED}${i}.ml

        cp ${USIG}.ml ${USIG}${i}.ml
        sed -i -- "s/let self = Obj.magic 0/let self = Obj.magic ${i}/g" ${USIG}${i}.ml

        cp ${REPLICA}.ml ${REPLICA}${i}.ml
        sed -i -- "s/${EXTRACTED}/${EXTRACTED}${i}/g" ${REPLICA}${i}.ml

        rm -f *.o *.cmo *.cmi
        make ${REPLICA}${i}.native REPLICA=${REPLICA}${i} EXTRACTED=${EXTRACTED}${i} USIG=${USIG}${i} SERVER=${SERVER}${i}
        make ${SERVER}${i}         REPLICA=${REPLICA}${i} EXTRACTED=${EXTRACTED}${i} USIG=${USIG}${i} SERVER=${SERVER}${i}
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
fi



if [ "$1" = "setup" ]
then
    echo "---all done generating the files---"
else
    # USIG servers
    if [ "$1" = "" ] || [ "$1" = "run" ] || [ "$1" = "one" ]
    then
        for i in `seq 0 ${NUM_REPLICASM1}`;
        do
            if [ "$1" = "one" ]
            then ./${SERVER}${i} ${i} ${CONF_FILE} &
            else ${TERMINAL} --title=server${i} --geometry 50x10+$(( 100*(${i}+1) ))+$(( 100*(${i}+1) )) -x ./${SERVER}${i} ${i} ${CONF_FILE}
            fi
        done
    fi


    sleep 2


    # Replicas
    for i in `seq 0 ${NUM_REPLICASM1}`;
    do
        if [ "$1" = "one" ]
        then ./${REPLICA}${i}.native -id ${i} -num-faults ${NUM_FAULTS} -num-clients ${NUM_CLIENTS} -conf ${CONF_FILE} &
        else ${TERMINAL} --title=replica${i} --geometry 60x20+$(( 100*(${i}+1) ))+$(( 100*(${i}+1) )) -x ./${REPLICA}${i}.native -id ${i} -num-faults ${NUM_FAULTS} -num-clients ${NUM_CLIENTS} -conf ${CONF_FILE}
        fi
    done


    sleep 2


    # Clients
    for i in `seq 0 ${NUM_CLIENTSM1}`;
    do
        if [ "$1" = "one" ]
        then
            ./Client.native -id ${i} -max ${NUM_REQUESTS} -num-faults ${NUM_FAULTS} -printing-period ${PRINTING_PERIOD} -plotting-period ${PLOTTING_PERIOD} -conf ${CONF_FILE} &
            pid=$!
            wait $pid
        else ${TERMINAL} --title=client${i} --geometry 150x40+$(( 500+(100*(${i}+1)) ))+$(( 100*(${i}+1) )) -x ./Client.native -id ${i} -max ${NUM_REQUESTS} -num-faults ${NUM_FAULTS} -printing-period ${PRINTING_PERIOD} -plotting-period ${PLOTTING_PERIOD} -conf ${CONF_FILE}
        fi
    done
fi
