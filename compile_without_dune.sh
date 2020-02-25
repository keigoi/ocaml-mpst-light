#!/bin/bash
set -e
OPTS="-short-paths"
LIBS="-I +unix -I +threads -I examples unix.cma threads.cma"
ocamlc $LIBS -c -impl concur-shims/concur_shims.threads.ml -o concur_shims.cmo
ocamlc $LIBS -c base.ml
ocamlc $LIBS -c mpst_no_lin_check.ml
ocamlc $LIBS -c mpst_light.ml
ocamlc $LIBS -c examples/example.ml

which -s rlwrap
if [ $? == 0 ]; then
  rlwrap ocaml $OPTS $LIBS concur_shims.cmo base.cmo mpst_no_lin_check.cmo mpst_light.cmo examples/example.cmo
else
  ocaml $OPTS $LIBS concur_shims.cmo base.cmo mpst_no_lin_check.cmo mpst_light.cmo examples/example.cmo
fi
