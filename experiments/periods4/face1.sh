#!/bin/sh
# one free point (f = 1): all mixed orders new at m = 6, 7, 8 in c_1(T(N, m+1))
for sa in "2 3" "3 2" "4 1" "2 4" "3 3" "4 2" "5 1" "2 5" "3 4" "4 3" "5 2" "6 1"; do
  python3 mixedface.py $sa 1 all | tail -1
done
