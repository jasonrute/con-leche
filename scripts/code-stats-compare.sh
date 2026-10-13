#!/usr/bin/env bash
# scripts/code-stats-compare.sh — executed-code statistics of two revisions.
#
#     scripts/code-stats-compare.sh OLD NEW
#
# For each revision: a throwaway worktree under _tmp/code-stats/, THIS
# checkout's `scripts/code-stats.py` and `scripts/executed-decls.lean`
# copied in (so older revisions are measured by the same instrument), a
# build of `con-leche`, and `code-stats.py --executed --json`.  Then one
# table per area and one per checker component, OLD vs NEW with the
# change.  The worktrees are removed afterwards; the JSON stays in
# _tmp/code-stats/.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
[ $# -eq 2 ] || { echo "usage: scripts/code-stats-compare.sh OLD NEW" >&2; exit 2; }
OUT=$ROOT/_tmp/code-stats
mkdir -p "$OUT"
for rev in "$1" "$2"; do
  tag=$(git rev-parse --short "$rev")
  wt=$OUT/wt-$tag
  [ -d "$wt" ] && git worktree remove --force "$wt"
  git worktree add -q --detach "$wt" "$rev"
  cp scripts/code-stats.py scripts/executed-decls.lean "$wt/scripts/"
  echo "[code-stats-compare] measuring $rev ($tag)" >&2
  (cd "$wt" && python3 scripts/code-stats.py --executed --json "$OUT/$tag.json" > "$OUT/$tag.txt")
  git worktree remove --force "$wt"
done
python3 - "$1" "$(git rev-parse --short "$1")" "$2" "$(git rev-parse --short "$2")" "$OUT" <<'EOF'
import json, sys
la, ta, lb, tb, out = sys.argv[1:6]
a = json.load(open(f"{out}/{ta}.json")); b = json.load(open(f"{out}/{tb}.json"))
def row(name, x, y, cols):
    cells = []
    for c in cols:
        d = y[c] - x[c]
        pct = f" ({d / x[c]:+.1%})" if x[c] else ""
        cells.append(f"{x[c]:,} → {y[c]:,}{pct}")
    print(f"| {name} | " + " | ".join(cells) + " |")
print(f"## the checker by component, {la} → {lb}")
print("| component | code | executed |")
print("|---|---:|---:|")
for name in a["components"]:
    row(name, a["components"][name], b["components"][name], ("code", "executed"))
print()
print(f"## areas, {la} → {lb}")
print("| area | code | executed | proof |")
print("|---|---:|---:|---:|")
for name in a["areas"]:
    row(name, a["areas"][name], b["areas"][name], ("code", "executed", "proof"))
EOF
