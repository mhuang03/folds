#!/bin/bash
# chk.sh NAME... : elaborate Folds/ThinCover<NAME>.lean (lean -M 3000), print errors and the time.
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")/../.."
for n in "$@"; do
  s=$(date +%s)
  out=$(lake env lean -M 3000 "Folds/ThinCover$n.lean" 2>&1)
  e=$(date +%s)
  echo "== $n: $((e - s)) s, $(echo "$out" | grep -c 'error') errors"
  echo "$out" | grep -A8 'error' | head -40
done
