#!/bin/sh
# lean.sh FILE: compile a Lean file against the prebuilt oleans of the main checkout
# (no lake build of the Folds library needed); peak memory via /usr/bin/time if present.
P=/home/user/folds/.lake/packages
LP=/tmp/claude-0/-home-user-folds/bd994c7a-a824-526f-8ce9-3cfdb91d329e/scratchpad/olean
for d in $P/*; do LP=$LP:$d/.lake/build/lib/lean; done
export LEAN_PATH=$LP
export PATH=$HOME/.elan/bin:$PATH
exec lean -M 3000 "$@"
