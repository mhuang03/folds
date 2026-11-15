#!/bin/sh
# All Python analyses (needs run_enum.sh, run_statdp.sh, run_extra.sh first).
cd "$(dirname "$0")"
python3 qsym.py 12 > data/qsym_out.txt
python3 rsk.py 10 > data/rsk_out.txt
python3 stats.py 12 > data/stats_out.txt
python3 polys.py > data/polys_out.txt
python3 oprec.py > data/oprec_out.txt
python3 permuton.py > data/permuton_out.txt
echo done
