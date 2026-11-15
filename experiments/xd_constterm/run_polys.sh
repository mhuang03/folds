#!/bin/sh
# one-variable specialisations for N = 1..18 (mode 2 only to N = 17: memory)
for N in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18; do
  for mode in 0 1 3; do ./bin/polydp $N $mode; done
  if [ $N -le 17 ]; then ./bin/polydp $N 2; fi
done
