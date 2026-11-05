#!/bin/bash
# Chain u8 residue runs of the sub-block path, one process per residue.
#   run_sub.sh N LOG IDX...      (env: FOLDS_SPILL, FOLDS_ANON, SUB_T (default 4), THREADS (default 4))
# stdout of each run goes to LOG, per-job progress to LOG.err; every run gets
# "# start" and "# exit" lines with time, load and available memory.
n=$1; log=$2; shift 2
bin="$(dirname "$0")/../target/release/folds"
for idx in "$@"; do
  echo "# start idx $idx $(date -u +%FT%TZ) load $(cut -d' ' -f1-3 /proc/loadavg) avail $(grep MemAvailable /proc/meminfo | awk '{print $2, $3}') disk_avail $(df --output=avail -B1M /home/user | tail -1) MB anon_cap ${FOLDS_ANON:-7} spill ${FOLDS_SPILL:-none}" >> "$log"
  echo "# start idx $idx $(date -u +%FT%TZ)" >> "$log.err"
  "$bin" residue semi "$n" 8 "$idx" --sub "${SUB_T:-4}" --threads "${THREADS:-4}" -v >> "$log" 2>> "$log.err"
  code=$?
  echo "# exit idx $idx code $code $(date -u +%FT%TZ) load $(cut -d' ' -f1-3 /proc/loadavg)" >> "$log"
  if [ -n "$FOLDS_SPILL" ]; then rm -f "$FOLDS_SPILL"/folds-*.bin; fi
done
