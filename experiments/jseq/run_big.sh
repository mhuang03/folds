#!/bin/bash
# run_big.sh N THREADS P1 P2 ...: one jdp run per modulus (skips moduli already done).
#   N = 32: u32 primes 4294967291 4294967279 4294967231 4294967197  (4.8 GB each)
#   N = 33: u16 primes 65521 65519 65497 65479 65449 65447           (4.7 GB each)
cd "$(dirname "$0")"
mkdir -p out
n=$1; th=$2; shift 2
for p in "$@"; do
  if grep -q '^a ' "out/jdp_${n}_${p}.txt" 2>/dev/null; then continue; fi
  ./jdp "$n" "$p" "$th" > "out/jdp_${n}_${p}.txt" 2> "out/jdp_${n}_${p}.err"
done
