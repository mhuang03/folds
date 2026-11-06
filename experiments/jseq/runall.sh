#!/bin/bash
# runall.sh LO HI MOD [threads]: run jdp for N = LO..HI with modulus MOD, outputs to out/jdp_N_MOD.txt
cd "$(dirname "$0")"
mkdir -p out
for n in $(seq "$1" "$2"); do
  ./jdp "$n" "$3" "${4:-3}" > "out/jdp_${n}_$3.txt" 2> "out/jdp_${n}_$3.err"
done
