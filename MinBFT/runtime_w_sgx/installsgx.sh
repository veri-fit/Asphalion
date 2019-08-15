## WARNING: Please make sure that Intel-SGX is enabled in BIOS, as well as that secure boot is off


## in case the script fails, it will stop
set -e


## ---- Install dependencies
sudo apt update
sudo apt install git
sudo apt install gcc
sudo apt install build-essential
sudo apt-get install -y libelf-dev


## ---- Making Intel SGX directory
cd /opt
sudo mkdir intel
cd intel


## ---- Install SGX driver
# https://github.com/intel/linux-sgx-driver
# We're using linux-sgx-driver's commit 5d6abcc3fed7bb7e6aff09814d9f692999abd4dc
# from Wed May 22 13:19:54 2019 +0300
sudo git clone https://github.com/intel/linux-sgx-driver.git
cd linux-sgx-driver
sudo git checkout 5d6abcc3fed7bb7e6aff09814d9f692999abd4dc


## ---- Setting up SGX driver
dpkg-query -s linux-headers-$(uname -r)
sudo apt-get install linux-headers-$(uname -r)
sudo make -j4
sudo mkdir -p "/lib/modules/"`uname -r`"/kernel/drivers/intel/sgx"
sudo cp isgx.ko "/lib/modules/"`uname -r`"/kernel/drivers/intel/sgx"
sudo sh -c "cat /etc/modules | grep -Fxq isgx || echo isgx >> /etc/modules"
sudo /sbin/depmod
sudo /sbin/modprobe isgx


## ---- Install SGX SDK and PSW
# https://github.com/intel/linux-sgx
# We're using linux-sgx's commit da495bd6bf47e82303657708b63ed7ae64498315
# from Wed May 29 09:52:37 2019 +0800
cd ..
sudo git clone https://github.com/intel/linux-sgx.git
cd linux-sgx
sudo git checkout da495bd6bf47e82303657708b63ed7ae64498315


## ---- Setting up SGX SDK and PSW
sudo apt-get install build-essential ocaml ocamlbuild automake autoconf libtool wget python libssl-dev
sudo apt-get install libssl-dev libcurl4-openssl-dev protobuf-compiler libprotobuf-dev debhelper cmake
sudo ./download_prebuilt.sh
sudo make -j4
sudo make sdk_install_pkg -j4
sudo make deb_pkg -j4
sudo apt-get install build-essential python
cd linux/installer/bin
sudo ./sgx_linux_x64_sdk_2.5.101.50123.bin
# following two lines have to be entered manually
# no
# /opt/intel
source /opt/intel/sgxsdk/environment
# Taken from https://github.com/hyperledger-labs/minbft
echo -e ". /opt/intel/sgxsdk/environment\n" >> ~/.profile
sudo bash -c "echo /opt/intel/sgxsdk/sdk_libs > /etc/ld.so.conf.d/sgx-sdk.conf"
sudo ldconfig


## ---- Test SGX SDK
cd ../../../
# test if sgx is working properly in simulation mode
cd SampleCode/LocalAttestation
sudo make SGX_MODE=SIM
sudo ./app
cd ../../


## ---- Install PSW
sudo apt-get install libssl-dev libcurl4-openssl-dev libprotobuf-dev
cd linux/installer/deb
sudo dpkg -i ./libsgx-urts_2.5.101.50123-bionic1_amd64.deb ./libsgx-enclave-common_2.5.101.50123-bionic1_amd64.deb
sudo service aesmd start


## ---- Test if sgx is working properly in hardware mode
cd /opt/intel/linux-sgx/SampleCode/LocalAttestation
sudo make clean
sudo make SGX_MODE=HW
sudo ./app
cd ../../


## ---- Intsall Graphene-SGX
# https://github.com/oscarlab/graphene
# We're using Graphene's commit 7ac25ca5560523a48226abfb3b70f252387e8df7
# from Fri Jun 21 15:12:23 2019 -0700
cd ~/Desktop
git clone https://github.com/oscarlab/graphene.git
cd graphene
git checkout 7ac25ca5560523a48226abfb3b70f252387e8df7


## ---- Setting up Graphene-SGX
sudo apt-get install -y build-essential autoconf gawk
sudo apt-get install -y python-protobuf
git submodule update --init -- Pal/src/host/Linux-SGX/sgx-driver/
sudo make -j4
openssl genrsa -3 -out enclave-key.pem 3072
cp enclave-key.pem Pal/src/host/Linux-SGX/signer/enclave-key.pem
cd Pal/src/host/Linux-SGX/sgx-driver
sudo make -j4
# following two lines have to be entered manually
# /opt/intel/linux-sgx-driver/
# 2.6
sudo ./load.sh
cd ~/Desktop/graphene
sudo make SGX=1


## ---- test if Graphene is working properly
cd  LibOS/shim/test/native
sudo make SGX=1
sudo make SGX_RUN=1
sudo SGX=1 ./pal_loader helloworld
