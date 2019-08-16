set -x
sudo add-apt-repository -y ppa:$PPA
sudo apt-get update -qq
sudo apt-get install -qq ocaml opam ocaml-native-compilers camlp4-extra
echo "Ocaml version" && ocaml -version
echo "OPAM version" && opam --version 
opam init -y
opam switch 4.04.1
git clone git@github.com:facebook/planout.git
wget https://github.com/Z3Prover/z3/releases/download/z3-4.6.0/z3-4.6.0-x64-ubuntu-14.04.zip
unzip z3-4.6.0-x64-ubuntu-14.04.zip