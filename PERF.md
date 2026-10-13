# PERF.md — the con-leche performance battery

| | |
|---|---|
| commit measured | `a0f1865afe2bbdf948a0cf90a224004080c14336` |
| tree | con-leche at `a0f1865a`, built with **Lean v4.35.0-rc3** (the repository's `lean-toolchain`), measured end to end in one session: one pair of binaries, one set of streams, no cell carried forward.  The `official v4.33.0` binary is the arena's own `checkers/official-v4.33.0` (`leanprover/lean-kernel-arena` at `aa259bf^`, the last revision that carried that directory; `echo leanprover/lean4:v4.33.0 > lean-toolchain && lake build`; md5 `6125c70e83490973a07be2ea69523a2c`).  The streams are Lean **v4.33.0** exports, read unchanged by both checkers: `mathlib-full` is `lean4export` at `15f6055` over the `Mathlib` module of mathlib4 `6f1ef4e5` (the last mathlib4 commit on v4.33.0), **6 069 002 157 bytes, 107 820 903 lines, 691 203 declaration records**; `init-full` is `lean4export` of `Init` at v4.33.0, 57 977 declaration records, 347 714 179 bytes. |
| date | 2026-10-13T02:19:56+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.111 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `timeout 3000`, `nice -n 5` (the `mathlib-full` row: 8 h, `--progress=5000`) |
| check phase | one worker: every con-leche cell passes `--jobs=1` (the worker-count table below is the parallel lane) |
| streams | `lean4export` NDJSON, read unchanged by both checkers |
| Mathlib stream | `<checkout>/_tmp/ref/mathlib-full.ndjson` (6069002157 bytes, 107820903 lines, raw) |
| concurrent load | shared machine throughout — the per-cell load average is recorded in `perf-data/table.tsv` |
| official kernel | `<checkout>/_tmp/ref/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| con-leche binary | md5 `4f88173b2bc04a85c902516f498c8109` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.12 G | 2.76 G | 2.76 G | 0.45× | 0.45× |
| `beta-ladder` | 10.13 G | 5.22 G | 5.22 G | 0.52× | 0.52× |
| `init-prelude` | 2.21 G | 2.00 G | 2.05 G | 0.91× | 0.93× |
| `grind-ring-5` | 13.40 G | 15.90 G | 16.28 G | 1.19× | 1.21× |
| `app-lam` | 29.42 G | 23.44 G | 23.45 G | 0.80× | 0.80× |
| `init-full` | 439.61 G | 402.66 G | 408.36 G | 0.92× | 0.93× |
| `mathlib-full` | 10.26 T | 6.40 T | 7.05 T | 0.62× | 0.69× |

## exit code / accepted declaration records

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 22 | 0 / 13 | 0 / 13 |
| `beta-ladder` | 0 / 20 | 0 / 11 | 0 / 11 |
| `init-prelude` | 0 / 2056 | 0 / 1777 | 0 / 1777 |
| `grind-ring-5` | 0 / 2429 | 0 / 2185 | 0 / 2185 |
| `app-lam` | 0 / 34 | 0 / 21 | 0 / 21 |
| `init-full` | 0 / 59430 | 0 / 57977 | 0 / 57977 |
| `mathlib-full` | 0 / 707578 | 0 / 691203 | 0 / 691203 |

Exit codes: 0 accept, 1 reject, 2 decline, 3 error.

## the input: what each stream contains

Properties of the FILE, computed by
`scripts/stream-census.py` — nobody's environment representation
enters here.  `records` is the number of declaration records in the
file; `con-leche` and `official` are what each checker's verdict line
reports on it, both derived from the file alone (see the count note
below).  `pinned` counts the basis blocks the parse matches;
`native` is every other inductive block, which con-leche installs
itself (the uniform fixpoint route),
split by shape.

**The `con-leche` column IS the verdict line's count**: the file's
own declaration records, so the census predicts the verdict.

| stream | records | con-leche | official | pinned | native | structures | sums | indexed |
|---|---|---|---|---|---|---|---|---|
| `let-ladder` | 13 | 13 | 19 | 2 | 2 | 2 | 0 | 0 |
| `beta-ladder` | 11 | 11 | 17 | 3 | 1 | 1 | 0 | 0 |
| `init-prelude` | 1777 | 1777 | 2056 | 5 | 121 | 104 | 14 | 3 |
| `grind-ring-5` | 2185 | 2185 | 2429 | 4 | 101 | 78 | 16 | 7 |
| `app-lam` | 21 | 21 | 31 | 2 | 4 | 4 | 0 | 0 |
| `init-full` | 57977 | 57977 | 59430 | 5 | 610 | 493 | 63 | 54 |
| `mathlib-full` | 691203 | 691203 | 707578 | 5 | 6714 | 5764 | 604 | 346 |

## the Mathlib row, as data (not a measurement)

Wall time and resident memory on a shared 96-core machine are
**data**, not comparisons — `instructions:u` above is the
measurement.  These are here because they are the two numbers a
reader wants before pointing the checker at all of Mathlib.

| | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| wall | 28.9 min | 9.8 min | 10.7 min |
| peak RSS (`time -v`) | 11.44 GiB | 4.27 GiB | 4.27 GiB |

## more than one thread

A run has three phases, parse, install and check; at `--jobs=<n>`
above one, all three run on `<n>` threads (`con-leche --help`).
Wall time on a shared machine is **indicative only**:
`instructions:u` above is the measurement, and it is taken at one
worker.  Every cell is `--verified`, one run.

| stream | `--jobs=1` | `--jobs=4` | `--jobs=8` |
|---|---|---|---|
| `init-full` | 39 s | 11 s | 7 s |
| `mathlib-full` | 14.7 min | 3.1 min | 100 s |

The run's own `stats: phases:` line splits each cell.  On `mathlib-full`: parse 18.4 s, install 28.4 s, check 834.0 s at one worker; 8.1 s, 9.6 s, 169.2 s at four; 5.4 s, 5.3 s, 88.5 s at eight.  On `init-full`: 1.4 s, 1.4 s, 35.7 s; 0.6 s, 0.7 s, 10.0 s; 0.3 s, 0.6 s, 5.6 s.  The parse and the install shorten with the worker count as the check does: on `mathlib-full` they take 47 s ahead of the check at one worker (5 % of the run) and 11 s at eight (11 %).  The pool costs instructions: `mathlib-full` takes 7.05 T at one worker and 7.29 T at four and at eight (+3.5 %), `init-full` 408.38 G, 419.08 G and 419.83 G (+2.6 %, +2.8 %).  The one-worker wall time is noisy: the battery's verified `mathlib-full` cell above is the same run at the same instruction count (7.05 T) and took 10.7 min, its check phase 594 s.  Each worker thread reserves about 1 GiB of address space (`con-leche --help`), so a run under an `ulimit -v` can afford only so many of them; none of the cells here runs under one.  Peak resident set on `mathlib-full` is 4.27, 4.67 and 4.74 GiB at one, four and eight workers.

## Notes

* **All of Mathlib, all three checkers, one stream.**  The `mathlib-full` row is the whole export described in the header.  **Every cell accepts**: official 707 578 declarations, con-leche 691 203 declaration records in both modes, at **0.69× verified and 0.62× trusted**, where `init-full` sits at 0.93× / 0.92×.  The count difference is the official binary's counting (see below), not a verdict difference.  **Parsing.**  The official checker's `--parse-only` mode costs a flat ~306 instructions per input byte: 106.83 G on `init-full`'s 347.7 MB and 1 852.40 G on this row's 6 069.0 MB (307.2 / 305.2 instr/B), so reading the file is 24.3 % of its `init-full` run and 18.1 % of its full-Mathlib run.  Charge con-leche its whole run, its own parse included, against official's run without its parse, and the verified ratio is 1.23× on `init-full` and 0.84× on `mathlib-full` (trusted 1.21× / 0.76×).  **Per declaration.**  Official's run without its parse costs 5.60 M instructions per declaration on `init-full` and 11.89 M on all of Mathlib, ×2.12; con-leche's whole verified run costs 7.04 M per record on `init-full` and 10.19 M on all of Mathlib, ×1.45.  Mathlib's declarations are heavier than Init's for both checkers; official's cost per declaration grows the faster of the two.
* **The Lean runtime's allocator and reference counting are a large share of con-leche's instructions.**  The binary is built with Lean v4.35.0-rc3, whose small-object path is `lean_alloc_small_object_core`/`lean_free_object` over mimalloc.  A `perf record -e instructions:u` of the verified mode at `--jobs=1` puts the allocation and reference-counting symbols (`mi_*`, `lean_alloc*`, `lean_free*`, `lean_dec_ref*`, `lean_del*`) at **48 % of `grind-ring-5`, 45 % of `init-prelude` and 45 % of `init-full`**, `lean_dec_ref_cold` alone at 16–20 %; the same symbols are 25 % of a profile of official's `init-full` run.  Peak resident set on `mathlib-full` is 4.27 GiB in both modes, against official's 11.44 GiB.
* **The verdict line counts declaration RECORDS**, the FILE's own count
  `decls.size - genRecords` (the file's own records: the built-in
  prelude adds none, since the stream's own record is what is used
  wherever it has one),
  not the number of environment CONSTANTS, which would count an
  inductive block's type former, its constructors, its recursor and
  its projection table separately — a property of con-leche's
  representation.  `scripts/stream-census.py` derives both numbers
  from the stream.
* **The official number is not a record count either.**  Its
  `Main.lean` prints `constMap.size`: one entry per exported
  constant, so an inductive record contributes its type formers, its
  constructors AND its recursors, less the three `Quot.mk`/`.lift`/
  `.ind` entries it erases before replay.  Both numbers are
  functions of the input file alone, and the census table above
  reproduces each of them exactly from the bytes.
* **Same bytes, same job — but not the same work.**  Both sides read
  the same file and install every inductive block themselves.
  con-leche installs every block, mutual and nested ones included,
  through its uniform fixpoint route; official has native
  inductive/recursor support.
* **`--trusted` is `--verified` without the certification-only
  steps**: checks the official kernel does not make, which exist so
  that the soundness proof can rely on their outcome
  (`con-leche --help`).  The gap between the two columns is what
  those steps cost.
* **The cells are the single-worker lane.**  Every con-leche cell passes
  `--jobs=1` — one worker thread, no shared claim counter and no
  result table — which is the apples-to-apples comparison against a
  single-threaded official kernel; without the flag the parse, the
  install and the check phase run on one thread per hardware thread.
  The worker-count table above
  is where the parallel lane is reported, in wall time.
* One run per cell on a shared machine: `instructions:u` is
  contention-independent, so a cell may overlap other work.  The only
  wall times here are the Mathlib row's and the worker-count table's,
  both labelled as data.
* Regenerate with `lake build con-leche && scripts/perf-tables.sh`;
  `PERF_STREAMS=… PERF_APPEND=1` re-runs a single stream, and
  `scripts/perf-tables-render.py perf-data/table.tsv PERF.md
  perf-data/meta.txt perf-data/census.tsv` — which is what
  `scripts/perf-tables.sh --render` runs — re-renders this file from
  the tracked record without measuring.  The `mathlib-full` row needs
  its stream exported by hand first.  Per-cell data (with wall time
  and load) are tracked in `perf-data/table.tsv`, the input census in
  `perf-data/census.tsv`, provenance in `perf-data/meta.txt`.  The
  worker-count table is a sweep of its own, which the battery does not
  run; its cells are tracked in `perf-data/parallel.tsv`.

