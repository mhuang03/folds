#!/bin/sh
# Regenerates the data files of experiments/ek (1 core).  Usage: sh run_all.sh
cd "$(dirname "$0")"
gcc -O2 -march=native -o ek ek.c
for N in $(seq 4 40); do ./ek $N 4 2 2000000; done > k4.txt
for N in $(seq 5 40); do ./ek $N 5 2 500000; done > k5.txt
for N in $(seq 6 40); do ./ek $N 5 3 500000; done > k5lo3.txt
for N in $(seq 6 32); do ./ek $N 6 2 300000; done > k6.txt
for N in $(seq 6 32); do ./ek $N 6 3 300000; done > k6lo3.txt
for N in $(seq 7 24); do ./ek $N 7 3 300000; done > k7lo3.txt
for N in $(seq 5 100); do ./ek $N 3 2 200000; done > k3.txt
for N in $(seq 4 100); do ./ek $N 2 2 200000; done > k2.txt
