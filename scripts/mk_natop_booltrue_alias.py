#!/usr/bin/env python3
"""Store `Bool.true` at a type that is `Bool` only up to unfolding.

    scripts/mk_natop_booltrue_alias.py <in.ndjson> <out.ndjson>

The stream's `Bool` block keeps its shape, but its `true` constructor
is renamed `Bool.tt`; at the front of the stream come two new
definitions,

    def BoolAlias : Type := Bool
    def Bool.true : BoolAlias := Bool.tt

and `Nat.shiftLeft` and its theorem `shlEx` are dropped (its
install guard, `divModEnvGuard`, already pinned the constructors'
type).  So every use of the constructor (by name index) is now `Bool.tt`, and
the name `Bool.true` that the structural `Nat` recurrences spell
(`ble 0 y = Bool.true`, ...) is a definition whose stored type is not
syntactically `Bool`.  The official kernel should accept the stream
(not run: `Bool.true` unfolds to the constructor); the
checker's `natOpGuard` pins the `Bool` constructors at the type `Bool`
itself (task #342 L8) and declines the comparison operation's install.
`tests/e2e/natop_booltrue_alias.ndjson` is
`tests/e2e/natop_order.ndjson` through this script.
"""
import json
import sys


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    src, out = sys.argv[1], sys.argv[2]
    names = {0: ""}
    recs = []
    max_in = max_ie = max_il = 0
    with open(src) as f:
        for raw in f:
            line = raw.rstrip("\n")
            if not line.strip():
                continue
            r = json.loads(line)
            recs.append(r)
            if "in" in r:
                i = r["in"]
                max_in = max(max_in, i)
                if "str" in r:
                    p = names[r["str"]["pre"]]
                    names[i] = (p + "." if p else "") + r["str"]["str"]
                else:
                    p = names[r["num"]["pre"]]
                    names[i] = (p + "." if p else "") + str(r["num"]["i"])
            elif "il" in r:
                max_il = max(max_il, r["il"])
            elif "ie" in r:
                max_ie = max(max_ie, r["ie"])
    inv = {v: k for k, v in names.items()}
    true_n = inv["Bool.true"]
    # the new records go FIRST (after the meta line): the stream's own
    # `Bool` is installed ahead of everything (the prelude), and the
    # ground hoist moves `Nat.ble` ahead of the operations it grounds, so
    # only the front is ahead of it.  They spell their own name, level
    # and expression entries.
    b, tt, a, t = (max_in + k for k in (1, 2, 3, 4))
    l1 = max_il + 1
    e_ty, e_bool, e_alias, e_tt = (max_ie + k for k in (1, 2, 3, 4))
    front = [
        {"in": b, "str": {"pre": 0, "str": "Bool"}},
        {"in": tt, "str": {"pre": b, "str": "tt"}},
        {"in": a, "str": {"pre": 0, "str": "BoolAlias"}},
        {"in": t, "str": {"pre": b, "str": "true"}},
        {"il": l1, "succ": 0},
        {"ie": e_ty, "sort": l1},
        {"const": {"name": b, "us": []}, "ie": e_bool},
        {"const": {"name": a, "us": []}, "ie": e_alias},
        {"const": {"name": tt, "us": []}, "ie": e_tt},
        {"def": {"all": [a], "hints": "abbrev", "levelParams": [],
                 "name": a, "safety": "safe", "type": e_ty,
                 "value": e_bool}},
        {"def": {"all": [t], "hints": "abbrev", "levelParams": [],
                 "name": t, "safety": "safe", "type": e_alias,
                 "value": e_tt}},
    ]
    out_recs = [recs[0]] + front
    for r in recs[1:]:
        decl = next((r[k] for k in ("def", "thm") if k in r), None)
        if decl is not None and (names[decl["name"]].startswith("Nat.shiftLeft")
                                 or names[decl["name"]] == "shlEx"):
            continue
        if r.get("in") == true_n:
            r = {"in": true_n, "str": {"pre": r["str"]["pre"], "str": "tt"}}
        out_recs.append(r)
    with open(out, "w") as f:
        for r in out_recs:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
