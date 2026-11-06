#!/bin/bash
# nearhalf.sh: copies of size (N+1)/2 - j for odd N (j = 0..J), and N/2 + 1 - j for N = 2 mod 4
cd "$(dirname "$0")"
for n in 59 61 67 71 73 79 83; do
  line="$n:"
  for j in $(seq 0 16); do
    s=$(( (n + 1) / 2 - j ))
    line="$line $(./copies $n c $s | cut -d' ' -f3)"
  done
  echo "$line"
done
for n in 58 62 74 82 86; do
  line="$n:"
  for j in $(seq 0 14); do
    s=$(( n / 2 + 1 - j ))
    line="$line $(./copies $n c $s | cut -d' ' -f3)"
  done
  echo "$line"
done
