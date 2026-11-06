#!/bin/bash
# N = 34: u8 words (2 x 2.33 GB), 12 primes < 256 (a(34) ~ 2^80.5; 11 primes give ~87 bits,
# the 12th is the redundancy check).  Waits for the N = 33 runs to finish first.
cd "$(dirname "$0")"
until grep -q '^a ' out/jdp_33_65447.txt 2>/dev/null; do sleep 20; done
bash run_big.sh 34 3 251 241 239 233 229 227 223 211 199 197 193 191
