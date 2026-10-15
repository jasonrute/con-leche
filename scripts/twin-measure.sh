#!/usr/bin/env bash
# scripts/twin-measure.sh — elaboration cost of the cached-to-pure
# simulation modules (task #356), one row per module:
#
#   <module path> <instructions:u> <task-clock ms>
#
# Each module is elaborated alone by `lake env lean <file>` under
# `perf stat -e instructions:u` (imports loaded from the built tree, so
# run `lake build` first).  One run per module: instructions:u is
# deterministic to ~0.01 G on this machine; wall time is not a
# measurement here (CLAUDE.md), task-clock is printed for orientation.
#
# Usage: scripts/twin-measure.sh [file …]   (default: ConLeche/Verify/Cached/*.lean)
set -u
cd "$(dirname "$0")/.."
if [ $# -eq 0 ]; then set -- ConLeche/Verify/Cached/*.lean; fi
total=0
for f in "$@"; do
  out=$(timeout 3600 perf stat -x, -e instructions:u,task-clock \
          lake env lean "$f" 2>&1 >/dev/null)
  rc=$?
  ins=$(printf '%s\n' "$out" | awk -F, '$3 ~ /^instructions/ {print $1}')
  clk=$(printf '%s\n' "$out" | awk -F, '$3 ~ /^task-clock/ {printf "%d", $1}')
  if [ $rc -ne 0 ] || [ -z "$ins" ]; then
    echo "$f FAILED(rc=$rc)"
    printf '%s\n' "$out" | grep -v '^[0-9.]*,' | head -20 >&2
    continue
  fi
  printf '%s %s %s\n' "$f" "$ins" "$clk"
  total=$((total + ins))
done
printf 'TOTAL %s\n' "$total"
