#!/bin/sh
# Larger N for the liveness data (one core, low priority).
cd "$(dirname "$0")"
for n in 29 30 31; do nice -n 19 ./live $n; done > dead_29_31.txt
