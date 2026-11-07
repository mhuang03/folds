#!/bin/sh
# E*_k extension checks (1 core).  Usage: sh run.sh
cd "$(dirname "$0")"
gcc -O2 -march=native -o ek ek.c
for N in $(seq 49 64); do ./ek $N 4 2 300000; done > k4c.txt
for N in $(seq 41 48); do ./ek $N 5 3 300000; done > k5lo3c.txt
for N in $(seq 37 48); do ./ek $N 6 3 300000; done > k6lo3c.txt
