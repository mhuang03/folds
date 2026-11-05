#!/bin/bash
# usage: run_selfdual2.sh FROM TO -> appends to selfdual2_out.txt (layered DP)
cd "$(dirname "$0")"
for N in $(seq "$1" "$2"); do
  s=$(date +%s)
  ./selfdual2 "$N" >> selfdual2_out.txt
  echo "# N=$N took $(( $(date +%s) - s ))s" >> selfdual_log.txt
done
