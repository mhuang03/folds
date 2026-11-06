#!/bin/sh
# trylean.sh OUT.lean MEM N1 N2 ...: write a test file with the certificates for N1, N2, ...
# (importing Folds.Live3p) and check it with lean -M MEM; prints errors and the peak RSS (MB)
# sampled every 0.5 s.
out=$1; mem=$2; shift 2
cd "$(dirname "$0")"
:
cd ../..
export PATH=$HOME/.elan/bin:$PATH
start=$(date +%s)
lake env lean -M "$mem" "$out" > "$out.log" 2>&1 &
pid=$!
peak=0
while kill -0 $pid 2>/dev/null; do
  for p in $(pgrep -f "lean -M $mem $out"); do
    r=$(awk '/VmRSS/ {print int($2/1024)}' /proc/$p/status 2>/dev/null)
    [ -n "$r" ] && [ "$r" -gt "$peak" ] && peak=$r
  done
  sleep 0.5
done
echo "time $(( $(date +%s) - start ))s peakRSS ${peak}MB"
head -5 "$out.log"
