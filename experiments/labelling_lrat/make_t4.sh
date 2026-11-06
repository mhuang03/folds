#!/bin/bash
# Regenerate the t = 4 certificate files Folds/LabellingSAT4Certs{A..H}.lean (and the noLab
# theorems in $OUT/nolab4*.txt, pasted into Folds/LabellingSAT4.lean).
# Needs CADICAL and LRAT_TRIM (see env.sh).  About 2 minutes.
cd "$(dirname "$0")/../.."
OUT=${OUT:-/tmp}
gen() {  # letter specs...
  l=$1; shift
  python3 experiments/labelling_lrat/mkfile.py Folds/LabellingSAT4Certs$l.lean \
    "Certificates for four labels ($l)" 4 "$@" --nolab=$OUT/nolab4$l.txt
}
gen A L61 31 32 33
gen B 34 35 36 37
gen C 38 39 40 41
gen D 42 43 44 45
gen E 46 47 48 49
gen F 50 51 52 53
gen G 54 55 56 57
gen H 58 59 60
