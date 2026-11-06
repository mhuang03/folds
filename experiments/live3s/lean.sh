#!/bin/sh
# lean.sh FILE: compile a Lean file against the prebuilt oleans of the main checkout
# (no lake build of the Folds library needed), with a 3 GB memory cap and peak RSS report.
P=/home/user/folds/.lake/packages
LP=/home/user/folds/.lake/build/lib/lean
for d in $P/*; do LP=$LP:$d/.lake/build/lib/lean; done
export LEAN_PATH=$LP
export PATH=$HOME/.elan/bin:$PATH
exec lean -M 3000 "$@"
