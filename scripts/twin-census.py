#!/usr/bin/env python3
"""scripts/twin-census.py — the line census of the cached-to-pure
simulation (task #356's retrospective).

Every non-blank, non-comment line of the given Lean files (default:
`ConLeche/Verify/Cached/*.lean`) falls into one of four classes:

  meta        `macro`/`elab`/`syntax`/`macro_rules`/`register_*` blocks
              (custom tactics and attributes);
  vocabulary  declarations registered for `grind` (an attribute mentioning
              `grind`, e.g. `@[conleche_grind]`, `@[grind =]`), whole
              (statement and proof), and `grind_pattern` commands;
  proof       the proof part of every other `theorem`/`lemma`/`instance`
              block: from the line holding its top-level `:=` (or its first
              `|` equation arm) to the end of the block;
  statement   everything else: theorem statements, definitions,
              structures, `open`/`variable`/`section` lines, imports.

A block starts at a column-0 line beginning with a command keyword (doc
comments and attributes attach to the block that follows).  The split is
textual and approximate (a `:=` inside a statement's default argument is
read as the proof's start); it is applied identically before and after,
which is what the comparison needs.

Usage: scripts/twin-census.py [--per-file] [file …]
"""
import glob
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")

CMD_RE = re.compile(
    r"^(@\[|private |protected |noncomputable |theorem |lemma |def |abbrev |"
    r"instance|structure |inductive |class |example|opaque |axiom |"
    r"macro|elab|syntax|macro_rules|register_|grind_pattern|attribute |"
    r"open |variable|section|namespace|end\b|mutual|set_option|"
    r"import |public |module\b|meta |local |scoped |#)")
META_RE = re.compile(r"^(?:(?:local|scoped|private|public) )*"
                     r"(macro|elab|syntax|macro_rules|register_\w+)\b")
THM_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|"
                    r"public|nonrec) )*(theorem|lemma|instance)\b")
ATTR_GRIND_RE = re.compile(r"@\[[^\]]*\bgrind\b[^\]]*\]|@\[[^\]]*_grind\b[^\]]*\]")


def code_lines(text):
    """(line, is_code) with comments stripped; doc comments are comments."""
    out = []
    depth = 0
    for raw in text.split("\n"):
        line = raw
        code = ""
        i = 0
        while i < len(line):
            if depth > 0:
                if line.startswith("-/", i):
                    depth -= 1
                    i += 2
                elif line.startswith("/-", i):
                    depth += 1
                    i += 2
                else:
                    i += 1
            else:
                if line.startswith("/-", i):
                    depth += 1
                    i += 2
                elif line.startswith("--", i):
                    break
                else:
                    code += line[i]
                    i += 1
        out.append(code.rstrip())
    return out


def census(path):
    with open(path, encoding="utf-8") as f:
        lines = code_lines(f.read())
    counts = {"meta": 0, "vocabulary": 0, "proof": 0, "statement": 0}
    # split into blocks at column-0 command lines
    blocks = []
    cur = []
    for ln in lines:
        if ln and not ln[0].isspace() and CMD_RE.match(ln) and cur and \
                not (cur[-1].strip().startswith("@[") and cur[-1].strip().endswith("]")):
            blocks.append(cur)
            cur = []
        cur.append(ln)
    if cur:
        blocks.append(cur)
    for b in blocks:
        nonblank = [l for l in b if l.strip()]
        if not nonblank:
            continue
        head = " ".join(l.strip() for l in nonblank[:3])
        if META_RE.match(nonblank[0].strip()):
            counts["meta"] += len(nonblank)
            continue
        if nonblank[0].startswith("grind_pattern") or ATTR_GRIND_RE.search(head) \
                or re.match(r"^attribute \[[^\]]*grind", nonblank[0]):
            counts["vocabulary"] += len(nonblank)
            continue
        if THM_RE.match(head):
            start = None
            for i, l in enumerate(nonblank):
                if ":=" in l or (i > 0 and l.lstrip().startswith("|")):
                    start = i
                    break
            if start is None:
                counts["statement"] += len(nonblank)
            else:
                # the line holding `:=` counts as statement unless it is
                # only the proof's opening
                counts["statement"] += start
                counts["proof"] += len(nonblank) - start
            continue
        counts["statement"] += len(nonblank)
    return counts


def main(argv):
    per_file = "--per-file" in argv
    files = [a for a in argv if not a.startswith("--")]
    if not files:
        files = sorted(glob.glob(os.path.join(ROOT, "ConLeche/Verify/Cached/*.lean")))
    tot = {"meta": 0, "vocabulary": 0, "proof": 0, "statement": 0}
    for f in files:
        c = census(f)
        for k in tot:
            tot[k] += c[k]
        if per_file:
            print(f"{os.path.relpath(f, ROOT)} " +
                  " ".join(f"{k}={c[k]}" for k in tot))
    print("TOTAL " + " ".join(f"{k}={tot[k]}" for k in tot) +
          f" all={sum(tot.values())}")


if __name__ == "__main__":
    main(sys.argv[1:])
