#!/bin/bash
# polynomial DPs -> polydp_out.txt
cd "$(dirname "$0")"
for N in $(seq 1 18); do ./polydp "$N" des >> polydp_out.txt; done
for N in $(seq 1 22); do ./polydp "$N" free >> polydp_out.txt; ./polydp "$N" lrmax >> polydp_out.txt; done
