#!/bin/sh
# E*_k extension checks (1 core).  Usage: sh run.sh
cd "$(dirname "$0")"
gcc -O2 -march=native -o ek ek.c
for N in $(seq 49 64); do ./ek $N 4 2 300000; done > k4c.txt
for N in $(seq 41 48); do ./ek $N 5 3 300000; done > k5lo3c.txt
for N in $(seq 37 48); do ./ek $N 6 3 300000; done > k6lo3c.txt
gcc -O2 -o ek2 ek2.c
(./ek2 60 set 2 30 31 59; ./ek2 64 set 2 32 33 63) > k4c_resolve.txt
