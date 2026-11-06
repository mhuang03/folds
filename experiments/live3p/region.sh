#!/bin/sh
# For each N: among valid non-dead 3-sets {a<b<c} not inward after <= 3 extra steps,
# the largest a and the largest N+1-c (both about the "wideness" of the hard sets).
for n in "$@"; do
  ./live3k $n v | awk -v N=$n '/noGk/ {a=$3; c=$5; if (a>ma) ma=a; if (N+1-c>mc) mc=N+1-c; k++}
     /hist/ {h=$0} END {print "N=" N, "hard=" k+0, "max a=" ma+0, "max N+1-c=" mc+0, h}'
done
