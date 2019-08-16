FROM "ocaml/opam2:ubuntu-lts"

RUN opam switch 4.04 && eval $(opam env)
RUN sudo apt-get update && sudo apt-get install -y m4 pkg-config nodejs wget
RUN opam install "ocamlbuild=0.12.0" "ocamlfind=1.7.3" "oasis=0.4.10" "ounit=2.0.7" "yojson=1.4.0" "dolog=3.0" "core=v0.10.0" "async_unix=v0.10.0" "yaml=0.1.0" "ppx_deriving=4.2.1" "ppx_sexp_conv=v0.10.0" "ppx_fields_conv=v0.10.0"

COPY --chown=opam:opam bootstrap.sh /home/opam/
WORKDIR /home/opam
RUN ./bootstrap.sh
COPY --chown=opam:opam ocaml /home/opam/ocaml
WORKDIR /home/opam/ocaml
