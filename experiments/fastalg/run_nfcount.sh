#!/bin/sh
# Normal-form compression at the layers that the MITM stores (h-1, h) for N = $1..$2.
# Output: out/nfcount.txt (appended).  Uses 3 threads.
lo=$1
hi=$2
n=$lo
while [ "$n" -le "$hi" ]; do
  h=$((n / 2))
  ./nf.bin count2 "$n" $((h - 1)) 3 >> out/nfcount.txt
  ./nf.bin count2 "$n" "$h" 3 >> out/nfcount.txt
  if [ $((n % 2)) -eq 1 ]; then ./nf.bin count2 "$n" $((h + 1)) 3 >> out/nfcount.txt; fi
  n=$((n + 1))
done
