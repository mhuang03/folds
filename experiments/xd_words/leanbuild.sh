#!/bin/sh
# Build Folds.XdWords through the shared semaphore; print only this module's messages.
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")/../.."
flock /home/user/folds/.lake/lean-slot-$(( $$ % 3 )).lock lake build Folds.XdWords 2>&1 \
  | awk '/XdWords/{f=1} f' | grep -v "designed for use with the module system" | head -${1:-80}
