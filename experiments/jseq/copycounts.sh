#!/bin/bash
# copycounts.sh LO HI  -> copycounts.txt lines "N k #copies" for N = LO..HI
cd "$(dirname "$0")"
for n in $(seq "$1" "$2"); do ./copies "$n"; done
