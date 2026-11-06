#!/bin/bash
# chk.sh FILE: elaborate a Lean file of the project with a 3 GB address-space limit, report time.
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")/../.." || exit 1
# memory: lean -M (MB)
lake env lean -M 3000 "$1" 2>&1 | grep -v "^warning: .*linter\|^Note:" | head -${2:-60}
