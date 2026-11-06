#!/bin/bash
# kbuild.sh K... : build Folds.ThinCoverKernelK sequentially (one lean process at a time).
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")/../.."
for k in "$@"; do
  s=$(date +%s)
  lake build "Folds.ThinCoverKernel$k" > /dev/null 2>&1
  echo "Kernel$k exit $? $(( $(date +%s) - s )) s"
done
