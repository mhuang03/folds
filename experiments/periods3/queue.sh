#!/bin/bash
# sequential job queue (1 core): Normaliz k = 7 checks, then chain F = 2 data.
S=/tmp/claude-0/-home-user-folds/bd994c7a-a824-526f-8ce9-3cfdb91d329e/scratchpad/nz
cd /home/user/folds/.claude/worktrees/agent-a68230e067fe8e5de/experiments/periods3
while pgrep -f "ehrhart.py 7" > /dev/null; do sleep 10; done
J=$S/classes_7.json
{
for qm in "7 4" "8 4" "15 5" "16 5" "31 6" "32 6" "63 7" "64 7" "3 3" "4 3"; do
  set -- $qm
  EXACT=1 DPS=120 python3 ../periods2/fourier2.py $J 7 $1 $2
done
} > normaliz7.log 2>&1
timeout 4000 python3 probe5.py 2 11 15 > probe5_F2b.log 2>&1
for M in 5 6 7; do timeout 3000 python3 chainface.py $M $((M+2)) | tail -1; done > chain_full_F2.log 2>&1
echo done > queue.done
