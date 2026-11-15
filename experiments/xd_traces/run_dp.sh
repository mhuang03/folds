#!/bin/sh
# Tables of K(N) (swap classes), signed count, AO(N) (all traces), F(N), Z(N).
# usage: sh run_dp.sh  > dp_out.txt
for n in $(seq 1 28); do ./kdp $n k; done
for n in $(seq 1 28); do ./kdp $n s; done
for n in $(seq 1 24); do ./kdp $n t; done
for n in $(seq 1 24); do ./kdp $n f; done
for n in $(seq 2 22); do ./zdp $n; done
