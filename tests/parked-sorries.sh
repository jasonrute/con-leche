#!/usr/bin/env bash
# tests/parked-sorries.sh — THE PARKED SORRY GATE.
#
# `ConLeche/Complete/ArithSound.lean` is in-progress work in the parked
# lane (`ConLeche/Complete/*`): its two remaining `sorry`s
# (`arith_env_facts`'s two goals) are allowlisted in
# `tests/trust-surface.sh` WITH the justification there, and the module
# is a TCB dead end — nothing outside `ConLeche/Complete/` may import
# it (`tests/layering.sh`'s parked clause), so the `sorryAx` reaches no
# proved or shipped declaration.
#
# The repo rule is that `lake build` is WARNING-FREE and a `sorry` is a
# warning, so this module must NOT be a default target: the same shape
# as the Palomar challenge (`ConLeche/Challenge.lean`, own lib
# `ConLecheChallenge`, not in `defaultTargets`, built by
# `tests/challenge.sh`).  Here `ConLecheComplete` stays a default
# target for the finished parked results, and the sorry-carrying module
# is built by THIS gate instead: it must build with the expected
# `declaration uses \`sorry\`` warnings and NO other diagnostic — the
# same check `tests/challenge.sh` runs, so a real error (not a parked
# sorry) fails loudly here exactly as it would in `lake build`.
#
# Usage: tests/parked-sorries.sh   (needs `lake build` to have run)
set -uo pipefail
cd "$(dirname "$0")/.."

MODULE=ConLeche.Complete.ArithSound
tmp="_tmp/parked-sorries-gate"; mkdir -p "$tmp"
log="$tmp/build.log"

if ! timeout 1800 lake build "$MODULE" > "$log" 2>&1; then
  echo "PARKED-SORRY GATE FAIL — $MODULE did not build:"
  tail -30 "$log" | sed 's/^/    /'
  exit 1
fi

bad="$(grep -E '^(warning|error):' "$log" | grep -v 'declaration uses `sorry`' || true)"
if [ -n "$bad" ]; then
  echo "PARKED-SORRY GATE FAIL — $MODULE built with diagnostics other than the expected sorry warnings:"
  printf '%s\n' "$bad" | sed 's/^/    /'
  exit 1
fi

nsorry=$(grep -c 'declaration uses `sorry`' "$log" || true)
echo "parked sorries: $MODULE builds with exactly $nsorry sorry warning(s), nothing else"
