#!/bin/bash
# Regenerate the t = 3 certificate file Folds/LabellingSAT3Certs.lean (and the noLab theorems
# in $OUT/nolab3.txt, pasted into Folds/LabellingSAT3.lean).  Needs CADICAL and LRAT_TRIM
# (see env.sh).  A few seconds.
cd "$(dirname "$0")/../.."
OUT=${OUT:-/tmp}
python3 experiments/labelling_lrat/mkfile.py Folds/LabellingSAT3Certs.lean \
  "Certificates for three labels" 3 L21 15 16 17 18 19 20 --nolab=$OUT/nolab3.txt
