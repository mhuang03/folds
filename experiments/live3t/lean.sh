#!/bin/sh
# lean.sh [lean args] FILE: compile a Lean file against the prebuilt oleans of the main checkout
# (Folds.Live3s and below), with a 3 GB cap.
P=/home/user/folds/.lake/packages
LP=/home/user/folds/.lake/build/lib/lean
for d in $P/*; do LP=$LP:$d/.lake/build/lib/lean; done
export LEAN_PATH=$LP
export PATH=$HOME/.elan/bin:$PATH
exec lean -M 3000 "$@"
