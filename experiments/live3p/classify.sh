#!/bin/sh
# Run the 3-prefix classification check for N = $1 .. $2 (output: classify.txt lines).
for n in $(seq $1 $2); do ./live3 $n; done
