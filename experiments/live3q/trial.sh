#!/bin/bash
# trial.sh N1 N2 OUT: assemble Folds/Live3q.lean core (everything before the certificates,
# i.e. up to the marker line) + certificates for N1..N2 into Folds/OUT.lean, and compile it.
set -e
cd "$(dirname "$0")"
N1=$1; N2=$2; OUT=$3
python3 mkq.py $N1 $N2 3 ${CH:-60} > /tmp/claude-0/-home-user-folds/bd994c7a-a824-526f-8ce9-3cfdb91d329e/scratchpad/cert.lean
cd ../..
head -n -2 Folds/Live3q.lean > Folds/$OUT.lean
echo 'set_option Elab.async false' >> Folds/$OUT.lean
cat /tmp/claude-0/-home-user-folds/bd994c7a-a824-526f-8ce9-3cfdb91d329e/scratchpad/cert.lean >> Folds/$OUT.lean
printf 'end Live3q\nend Folds\n' >> Folds/$OUT.lean
wc -c Folds/$OUT.lean
export PATH=$HOME/.elan/bin:$PATH
cd experiments/live3q && python3 memtime.py Folds/$OUT.lean
