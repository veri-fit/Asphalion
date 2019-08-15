# script that copies the files from runtime_w_sgx to graphene

NUM_FAULTS=1

NUM_REPLICAS=$(( (2*${NUM_FAULTS})+1 ))
NUM_REPLICASM1=$(( ${NUM_REPLICAS}-1 ))

for i in `seq 0 ${NUM_REPLICASM1}`;
do
    rm -rf native${i}
done

for i in `seq 0 ${NUM_REPLICASM1}`;
do
    cp -r ~/Desktop/verifC/Velisarios/MinBFT/runtime_w_sgx/native${i} native${i}
done
