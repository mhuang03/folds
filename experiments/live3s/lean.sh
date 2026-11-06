#!/bin/sh
# lean.sh [lean args] FILE: compile a Lean file against the prebuilt oleans of the main checkout
# (no lake build of the Folds library needed) and the scratch olean directory OLEAN (where
# `lean.sh -o $OLEAN/Folds/Live3s.olean Folds/Live3s.lean` puts Live3s), with a 3 GB cap.
OLEAN=/tmp/claude-0/-home-user-folds/bd994c7a-a824-526f-8ce9-3cfdb91d329e/scratchpad/l3s/olean
P=/home/user/folds/.lake/packages
LP=$OLEAN:/home/user/folds/.lake/build/lib/lean
for d in $P/*; do LP=$LP:$d/.lake/build/lib/lean; done
export LEAN_PATH=$LP
export PATH=$HOME/.elan/bin:$PATH
exec lean -M 3000 "$@"
