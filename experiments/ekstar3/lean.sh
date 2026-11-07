#!/bin/sh
# lean.sh [lean args] FILE: compile a Lean file against the oleans of this worktree's .lake
# (the build directory copied from the main checkout), with a 3 GB cap.
W=$(cd "$(dirname "$0")/../.." && pwd)
P=$W/.lake/packages
LP=$W/.lake/build/lib/lean
for d in $P/*; do LP=$LP:$d/.lake/build/lib/lean; done
export LEAN_PATH=$LP
export PATH=$HOME/.elan/bin:$PATH
exec lean -M 3000 "$@"
