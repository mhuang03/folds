#!/bin/bash
# usage: run_selfdual.sh FROM TO  -> appends "N c(N)" lines and timings to selfdual_out.txt
cd "$(dirname "$0")"
for N in $(seq "$1" "$2"); do
  s=$(date +%s)
  ./selfdual "$N" >> selfdual_out.txt
  echo "# N=$N took $(( $(date +%s) - s ))s" >> selfdual_log.txt
done
