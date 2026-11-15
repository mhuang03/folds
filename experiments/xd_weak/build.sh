#!/bin/sh
# Build Folds/XdWeak.lean through the shared semaphore and print only errors / own warnings.
cd "$(dirname "$0")/../.." || exit 1
export PATH=$HOME/.elan/bin:$PATH
flock /home/user/folds/.lake/lean-slot-$(( $$ % 3 )).lock lake build Folds.XdWeak 2>&1 \
  | grep -v '^⚠\|^✔\|Replayed\|^warning: Folds/[A-WY-Z]\|deprecated\|^Hint\|^  \[apply\]\|^Note: This linter\|^$\|^trace\|consider adding' \
  | head -${1:-120}
