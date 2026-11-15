#!/bin/sh
# Rank statistics for N = 1..NMAX (default 24); output in out/levels.txt
cd "$(dirname "$0")"
mkdir -p bin out
gcc -O2 -o bin/levels levels.c
NMAX=${1:-24}
: > out/levels.txt
for N in $(seq 1 "$NMAX"); do ./bin/levels "$N" >> out/levels.txt; done
