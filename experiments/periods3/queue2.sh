#!/bin/bash
# runs after queue.sh: the full chain sum at (m, k) = (8, 10), where dominance is not enough.
cd /home/user/folds/.claude/worktrees/agent-a68230e067fe8e5de/experiments/periods3
while [ ! -f queue.done ]; do sleep 20; done
timeout 6000 python3 chainface.py 8 10 | tail -1 >> chain_full_F2.log 2>&1
echo done > queue2.done
