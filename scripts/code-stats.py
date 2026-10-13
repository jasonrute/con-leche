#!/usr/bin/env python3
"""Line statistics of the Lean sources, by area and by kind.

    scripts/code-stats.py [REV ...]        # default: the working tree
    scripts/code-stats.py master port-342  # a table per revision, plus the change

Every line of every `.lean` file under `ConLeche/` (and `Main.lean`) is
classified as

  * blank,
  * comment  — inside `--`, `/- … -/` or a docstring `/-- … -/`,
  * proof    — any other line of a `theorem` / `lemma` / `example`
               declaration (statement and proof),
  * code     — any other line (definitions, structures, inductives,
               instances, and the `namespace`/`open`/`variable`/`import`
               lines between declarations).

The classification is lexical: a declaration runs from its header line
(after optional attributes and modifiers) to the next line that starts a
new top-level command at column 0.  It is an approximation, but a
stable one, so comparisons between revisions are meaningful.

Areas:
  kernel, cached, frontend, driver — the executed checker
             (ConLeche/{Kernel,Cached,Frontend,Driver}, Main.lean);
             the row "checker" sums them
  proofs   — everything else under ConLeche/ (the statement, the theory, the proofs)
  fragment — whitepaper/Fragment (the paper's own Lean development)
"""
import re
import subprocess
import sys

AREAS = [
    ("kernel", ("ConLeche/Kernel/",)),
    ("cached", ("ConLeche/Cached/",)),
    ("frontend", ("ConLeche/Frontend/",)),
    ("driver", ("ConLeche/Driver/", "Main.lean")),
    ("proofs", ("ConLeche/",)),
    ("fragment", ("whitepaper/Fragment/",)),
]

MODS = r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec|meta|scoped|local)\s+)*"
PROOF_START = re.compile(r"^" + MODS + r"(?:theorem|lemma|example)\b")
CMD_START = re.compile(r"^(?:@\[|[a-z#])")  # any top-level command at column 0


def area_of(path):
    for name, prefixes in AREAS:
        if any(path == p or path.startswith(p) for p in prefixes):
            return name
    return None


def classify(text):
    """Return counts {blank, comment, proof, code} for one file."""
    counts = dict(blank=0, comment=0, proof=0, code=0)
    depth = 0          # block-comment nesting
    in_proof = False
    for line in text.splitlines():
        stripped = line.strip()
        # block comments (nested), line by line
        if depth > 0 or stripped.startswith("/-"):
            i = 0
            had_code = False
            s = line
            while i < len(s):
                if s.startswith("/-", i):
                    depth += 1; i += 2; continue
                if s.startswith("-/", i) and depth > 0:
                    depth -= 1; i += 2; continue
                if depth == 0 and not s[i].isspace():
                    had_code = True
                    break
                i += 1
            if not had_code:
                counts["comment"] += 1
                continue
        if not stripped:
            counts["blank"] += 1
            continue
        if stripped.startswith("--"):
            counts["comment"] += 1
            continue
        if line[:1] and not line[0].isspace() and CMD_START.match(line):
            in_proof = bool(PROOF_START.match(line))
        counts["proof" if in_proof else "code"] += 1
    return counts


def files_at(rev):
    if rev is None:
        out = subprocess.run(["git", "ls-files"], capture_output=True, text=True, check=True).stdout
    else:
        out = subprocess.run(["git", "ls-tree", "-r", "--name-only", rev],
                             capture_output=True, text=True, check=True).stdout
    return [f for f in out.splitlines() if f.endswith(".lean") and area_of(f)]


def read(rev, path):
    if rev is None:
        with open(path, encoding="utf-8") as fh:
            return fh.read()
    return subprocess.run(["git", "show", f"{rev}:{path}"], capture_output=True,
                          text=True, check=True).stdout


def stats(rev):
    table = {name: dict(files=0, blank=0, comment=0, proof=0, code=0) for name, _ in AREAS}
    for f in files_at(rev):
        a = area_of(f)
        c = classify(read(rev, f))
        table[a]["files"] += 1
        for k, v in c.items():
            table[a][k] += v
    table["checker"] = {k: sum(table[n][k] for n in CHECKER) for k in table["kernel"]}
    return table


CHECKER = ("kernel", "cached", "frontend", "driver")
ROWS = CHECKER + ("checker", "proofs", "fragment")
COLS = ("files", "code", "proof", "comment", "blank")


def show(label, table):
    print(f"## {label}")
    print(f"| area | {' | '.join(COLS)} |")
    print("|---|" + "---:|" * len(COLS))
    for name in ROWS:
        row = table[name]
        print(f"| {name} | " + " | ".join(f"{row[c]:,}" for c in COLS) + " |")
    print()


def main(argv):
    revs = argv or [None]
    tables = [(r or "working tree", stats(r)) for r in revs]
    for label, t in tables:
        show(label, t)
    if len(tables) >= 2:
        (la, a), (lb, b) = tables[0], tables[-1]
        print(f"## change {la} → {lb}")
        print(f"| area | {' | '.join(COLS)} |")
        print("|---|" + "---:|" * len(COLS))
        for name in ROWS:
            cells = []
            for c in COLS:
                x, y = a[name][c], b[name][c]
                pct = f" ({(y - x) / x:+.1%})" if x else ""
                cells.append(f"{y - x:+,}{pct}")
            print(f"| {name} | " + " | ".join(cells) + " |")


if __name__ == "__main__":
    main(sys.argv[1:])
