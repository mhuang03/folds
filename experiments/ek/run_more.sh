#!/bin/sh
# Second batch (1 core): Conjecture E*_k for k = 7, 8 (sets inside [4, N-3]) and k = 4 beyond 40.
cd "$(dirname "$0")"
gcc -O2 -march=native -o ek ek.c
for N in $(seq 9 28); do ./ek $N 7 4 300000; done > k7lo4.txt
for N in $(seq 10 24); do ./ek $N 8 4 300000; done > k8lo4.txt
for N in $(seq 41 48); do ./ek $N 4 2 300000; done > k4b.txt
for N in $(seq 33 36); do ./ek $N 6 3 300000; done > k6lo3b.txt
