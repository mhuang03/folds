#!/bin/sh
# NF density of the stored layer with block-preserving (NF_SUB=0) and sub-block-preserving
# (NF_SUB=4) shifts, counted over stored mirror blocks only (NF_HALF=1), N = $1..$2.
# Output: out/nfcount_sub.txt (appended).
n=$1
while [ "$n" -le "$2" ]; do
  h=$((n / 2))
  if [ $((n % 2)) -eq 0 ]; then j=$((h - 1)); else j=$h; fi
  NF_HALF=1 NF_SUB=0 ./nf.bin count2 "$n" "$j" 3 >> out/nfcount_sub.txt
  NF_HALF=1 NF_SUB=4 ./nf.bin count2 "$n" "$j" 3 >> out/nfcount_sub.txt
  n=$((n + 1))
done
