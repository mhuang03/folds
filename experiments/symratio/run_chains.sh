#!/bin/sh
# r(x 2^j) along doubling chains beyond the "all" range (one target per run, one core,
# memory < 2 GB).  Output appended to data/chains.txt (same columns as window.bin).
for n in 640 768 896 1024 1152 1280 1408 1536 1664 1792 1920; do
  ./window.bin chain $n | tail -1 >> data/chains.txt
done
