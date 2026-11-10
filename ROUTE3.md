# ROUTE3: `Con(ZFC + {inacc n | n ∈ ω}) → Con(con-leche)`, axiom-free, via internal formalization

Status: **plan only — not started.** Branch: `vibe/first-order-main-e3dbd3` (PR #3).
Do NOT start from `master`: `ConLeche/SetTheory/Form.lean` (the `Form` DSL,
`Form.lean:35`) and `bridge/lean4lean-model/ConLecheBridge/` exist only on the
PR #3 line. PR #2's branch (`vibe/arith-sound-71ddff`) is a different track and
also lacks the Track B work.

## 1. Goal

Prove, with no axioms beyond `[propext, Classical.choice, Quot.sound]`:

- **T1 (internal Con, arbitrary M).** For every `M : Type` with
  `[LSet.Structure M]` (`FirstOrderZFC.lean:88`), if `M ⊨ ZFC` (`ZFC`,
  `FirstOrderZFC.lean:260`) and `∀ n, M ⊨ inacc n` (`inacc`, `:340`;
  `ZFCInacc`, `:344`), then `M ⊨ φCon`, where `φCon` is a fixed `LSet.Sentence`
  expressing "no internal proof of `False` in con-leche" (Phase 0).
- **T2 (the payoff).** `Con(ZFCInacc) → P`, where `P` is the meta-level
  statement that con-leche's checker rejects every `False` declaration — the
  conclusion of `ConLeche.no_False_declaration` (`ConLeche/MainTheorem.lean:110`).

Assembly: T1 + Gödel completeness (Mathlib) gives a model from `Con(ZFCInacc)`;
then extract `M ⊨ φCon → P` by Δ₀-absoluteness (Section 3). Equivalently,
T1 + any one model `M ⊨ ZFCInacc` gives `P` directly.

## 2. Why Route 3 (and how it differs from Routes 1 and 2)

- **Route 1 (Track A, nearly done):** `OmegaInaccessibles → P`
  (`carneiro_implies_conleche`, `Carneiro.lean:245`, pinned
  `[propext, Classical.choice, Quot.sound]`, + `no_False_declaration`). Works on
  the single concrete structure `ZFSet`, where meta-level `repl` holds via
  `Classical.allZFSetDefinable` (`Carneiro.lean:126,199,216`). Hypothesis is
  strictly stronger than `Con(ZFCInacc)`.
- **Route 2 (current headline):** `∀ M ⊨ ZFCInacc, P` via a meta-level
  `SetTheory M` instance — `no_False_declaration_first_order`
  (`FirstOrderZFC.lean:755`), pinned with the two bridge axioms
  `replScheme_of_ZFC_model` (`:710`) and `exists_univChain_of_inacc` (`:720`).
  The instance's `repl` (`ConLeche/SetTheory/Core.lean`) quantifies over all
  meta `p : M → M → Prop`, which is **false for every countable M**; hence the
  axioms cannot be discharged for arbitrary M.
- **Route 3:** never build a meta-level `SetTheory` instance on `M`. Carry out
  the whole Carneiro construction *inside* M (first-order, using only M's own
  separation/replacement schemes), conclude `M ⊨ φCon`, and extract to meta `P`.
  The ∀M statement is then true and axiom-free. Cost: the entire semantic
  development must be replayed inside first-order ZFC (Section 5).

## 3. Logical skeleton (the extraction lemma — prove this first)

Con is Π₁. For a standard meta proof/derivation `p`, its code `⌜p⌝` is a
standard natural, standard naturals embed into `ω^M` as an initial segment
closed under the primitive-recursive `Proof` predicate, so for Δ₁ `Proof`:
`M ⊨ Proof(⌜p⌝, ⌜False⌝) ↔ Proof(p, ⌜False⌝)` in the meta-theory. Hence
`M ⊨ ¬Proof(⌜p⌝, ⌜False⌝)` implies meta `¬Proof(p, ⌜False⌝)` — contrapositive:
a real proof of `False` would be seen by M. No ω-model is needed in this
direction (Π₁ downward absoluteness to ℕ; the ω-model issue goes the other
way, meta `Con → M ⊨ Con`, and is irrelevant here). Caveat: the internal
`Proof` must be the standard encoding of the same checker, so `⌜p⌝^M = ⌜p⌝`
for standard `p`.

## 4. Where the code lives

The bridge package `bridge/lean4lean-model/` (separate Lake package because it
needs Mathlib; the main `ConLeche` libraries must never depend on Mathlib —
see `bridge/lean4lean-model/README.md`). New files under
`bridge/lean4lean-model/ConLecheBridge/`:

- `InternalSyntax.lean` — Phase 0
- `InternalTower.lean` — Phase 1
- `InternalInterp.lean` — Phase 2 (M-side replay of the semantics)
- `Route3.lean` — Phase 3 (assembly, extraction, final theorem + axiom pin)

New `Form` readers that the replay needs go in the main package as usual:
append-only in `ConLeche/Semantics/Interp.lean` before
`end ConLeche.Semantics`, one `example` per stage in
`tests/ConLecheTests/DefinableAppTests.lean`.

## 5. Phase / stage plan

### Phase 0 — internal syntax + `Proof` predicate (est. 2–5k lines)

Encode the **kernel** syntax only — `Term`, `BConst`, `Env`, `HasType`
derivations (`ConLeche/Kernel/`, 17.7k lines) — not the frontend (`ByteArray`
parsing). Kernel-only suffices because the meta-level chain already proves
checker-acceptance ⇒ kernel-derivability (the `MainTheorem.lean` proof of
`no_False_declaration`), so internal kernel-Con implies `P`.

- Use Mathlib `Encodable` to code syntax into `ℕ`; define in the `LSet`
  language the Δ₀/Σ₁ formulas `isTermCode`, `isDeclCode`, `isDerivCode`, and
  the proof predicate `Proof(x, y)`; define `φCon := ¬∃ x, Proof(x, ⌜False⌝)`.
- Prove the absoluteness glue (Section 3): for standard `d`,
  `M ⊨ Proof(⌜d⌝, ⌜False⌝) ↔` meta-derivability of `False` from `d`, for any
  `M ⊨ ZFC`. This is the lemma everything else consumes.
- Stages 123+: one encoding block per stage (term codes, const codes, env
  codes, derivation rules as Σ₁ formulas, then the glue lemmas).

### Phase 1 — internal universe tower (est. 1–3k lines)

Internal analogue of `setTheoryOfChain` (`Carneiro.lean:181`,
`univChain n := V_(κ n).ord` at `:232`):

- From `M ⊨ ZFC` and `∀ n, M ⊨ inacc n`, define inside M the n-th inaccessible
  `κₙ`, the internal cumulative hierarchy `V^M_α`, and `univChain^M n := V^M_{κₙ}`
  (a set of M, since M ⊨ ZFC proves `V_α` is a set for every `α ∈ M`).
- Prove in the meta that M satisfies the first-order sentences asserting the
  internal `SetTheory`/`IsUniverse` axioms of the tower.
- **Open problem (axiom-2 residue):** extracting a coherent meta-level chain
  `univChain : ℕ → M` from `M ⊨ inacc n` for standard n is where
  `exists_univChain_of_inacc` (`:720`) is needed today (coherent ω-chain,
  `IsUniverse` clause 5; König/inverse-limit caution for countable M). Route 3
  sidesteps it by staying internal: only *standard* facts are ever extracted,
  via Phase 0's absoluteness glue. If a meta chain is ever needed, that is the
  single place axiom 2 could resurface.

### Phase 2 — internal ⟦…⟧ and internal soundness (est. 20–30k lines; the bulk)

**Primary strategy (2B): meta-level induction on meta derivations, with the
internal interpretation as M-definable classes.** For each meta derivation
`Γ ⊢ a : A`, prove `M ⊨ "∀ γ ∈ ⟦⌜Γ⌝⌝(γ), ⟦⌜a⌝⌝(γ) ∈ ⟦⌜A⌝⌝(γ)"`. This needs no
meta `repl` on M — only that each interpretation clause is first-order
definiable in M, which is exactly what Track B built:

- the `Form` DSL (`ConLeche/SetTheory/Form.lean:35`) and the definable twins
  `sepF`/`imageF`/`replF`;
- the reader chain, stages 108–122 (`ConLeche/Semantics/Interp.lean`):
  `sortStepF`, `univAppEqF`, `interpStepF3`, `vnatListGetF`, `tgVnatF`,
  `sepTyFEqF`, `tyUVnatF`, `univVnatF_apply`, `univChainAppEqF_apply`,
  `sortStepG`, `interpStepG`, `memTgVnatF`, `isTyF`, `memUnivVnatF`,
  `memUnivChainVnatF`, `realize_interpStepG_tmCode_const`;
- `replF_of_ZFC_model` (`FirstOrderZFC.lean:676`) — replacement for
  **Form-definable** relations is already proved **axiom-free** from `M ⊨ ZFC`.

Remaining Track B work that Phase 2 consumes or extends: the ~20 meta
`sep`/`image` call sites (`Access.lean:128/138/146/545/786/898`,
`GraphRec.lean:94/98/281/298`, `TeleAcc.lean:94`, `ContAccFrame.lean:816/1003`,
`TargetNodePres.lean:201`, `BlockRecGraph.lean:86`, `LfpAcc.lean:295`,
`Graphs.lean:35/346`, `Ops.lean`, `LfpTuple.lean:85/171`) and the hard `bval`
const cases of `interpStepG` (bottoming out at the `univChain` reader).

**Fallback strategy (2A): fully internal** — define ⟦…⟧ by recursion on internal
syntax inside M and run the soundness induction internally, concluding
`M ⊨ φCon` wholesale. More faithful to "theorem of ZFC", but requires the
internal induction on internal derivations; use only if 2B stalls.

### Phase 3 — assembly (est. ~0.5k lines)

In `ConLecheBridge/Route3.lean`:

1. T1: `∀ M [LSet.Structure M], M ⊨ ZFC → (∀ n, M ⊨ inacc n) → M ⊨ φCon`
   (Phases 0–2; ⟦⌜False⌝⌝ = ∅ is `bval … .empty … = empty`,
   `ConLeche/SetModel/Value.lean:634`).
2. Extraction: `M ⊨ φCon → P` via the Phase 0 absoluteness glue.
3. Completeness (Mathlib): `Con(ZFCInacc) → ∃ M, M ⊨ ZFCInacc`.
4. Final theorem, pinned:
   `#guard_msgs in #print axioms <final>` = `[propext, Classical.choice, Quot.sound]`.

## 6. Stage conventions (as executed for stages 108–122)

- Branch `vibe/first-order-main-e3dbd3`; stage by explicit path
  (`git add <file>`, never `git add -A`); check the branch before committing.
- Each stage: append-only edit (main package: before the namespace `end` in
  `ConLeche/Semantics/Interp.lean`; one `example` before the `end` in
  `tests/ConLecheTests/DefinableAppTests.lean`; bridge: new declarations in the
  phase file), then warning-free build, then commit, then push:
  `git push origin vibe/first-order-main-e3dbd3`.
- Commit message: `Stage NNN (route-3 track): <desc>` + blank line +
  `Generated by Mistral Vibe.` +
  `Co-authored-by: jasonrute <jasonrute@users.noreply.github.com>`.
- Build: `export PATH="$HOME/.elan/bin:$PATH"`; `lake build ConLecheTests`
  (~10–13 min) in the main package; `lake build` in `bridge/lean4lean-model` for
  bridge files. Never run two lake builds on the same build dir concurrently;
  background with `nohup … > /tmp/sNNN.log 2>&1 &` and poll the log; gate on
  `EXIT=` and zero `warning:` lines.
- Namespace trap: in `Interp.lean` the tail opens `SetTheory`, so `pt` is
  `SetTheory.pt` — never bind a local `pt` (it shadows and breaks
  `realize_univZeroEqF` matching and `Strict` unfolding).
- Reader pattern (stages 108–122): per relabeled subform a `Fin m → Fin n` map;
  prove `hM : ∀ bound…, (ctx ∘ map) = (target ctx)` by
  `funext ⟨k, hk⟩; …; rcases … with rfl | … <;> rfl`; then
  `simp only [readerF, Form.realize_*, hM…, realize_<subform>]`, which closes
  the iff when both sides become syntactically equal.

## 7. Verification gates

- Main package (`ci.yml`): `lake build` and `lake test` green AND
  `grep -n 'warning:'` empty; axiom pins in `tests/ConLecheTests/Axioms.lean`
  (`[propext, Classical.choice, Quot.sound]`, `Axioms.lean:95–113`).
- Bridge (`bridge.yml`, runs on `bridge/**` changes): warning-free
  `lake build` in `bridge/lean4lean-model` + the `#guard_msgs in
  #print axioms` pins (`FirstOrderZFC.lean:766–774`, `Carneiro.lean:250–253`,
  and the new Route 3 pin).
- Full battery: `tests/arena.sh` (layering, quote-gate, overview-links, etc.).
  Note: `quote-gate.sh`/`overview-links.sh` only cover `OVERVIEW.md`/`README.md`,
  so this document is not link-gated — keep its file:line references accurate
  anyway.

## 8. Estimates and risks

Measured on head `82a9953a`: main package ~246k lines / ~7.2k theorems, but the
soundness-relevant core is `Semantics/` 17.6k lines (659 theorems) +
`SetTheory/` 8.2k + `SetModel/` 4.3k; the checker itself (`Model/` 104k,
`Verify/` 66k) is not replayed internally. Bridge `ConLecheBridge/` is 1,031
lines / 64 decls. Route 3 total estimate: **30–40k new lines, several hundred
stages** (at ~15 stages per session of a few hundred lines each). Dominant
cost: the definability side-condition on every internal construction. Risks:
internal encoding of kernel syntax in `ω^M`; the univChain standard-prefix
extraction (Section 5, Phase 1 open problem); replaying each `interpStep`
clause as an M-satisfied sentence.

## 9. Existing artifacts to reuse (file:line on `82a9953a`)

- `bridge/lean4lean-model/ConLecheBridge/FirstOrderZFC.lean`: `LSet`:88,
  `ZFC`:260, `inacc`:340, `ZFCInacc`:344, `replF_of_ZFC_model`:676 (axiom-free),
  axioms `:710`/`:720`, `setTheory_of_ZFC_model`:733,
  `no_False_declaration_first_order`:755, pin `:766–774`.
- `bridge/lean4lean-model/ConLecheBridge/Carneiro.lean`:
  `OmegaInaccessibles`:64, `setTheoryOfChain`:181 (`univChain n := V_(κ n).ord`
  :232), `setTheoryOfCarneiro`:238, `carneiro_implies_conleche`:245, pin
  `:250–253`.
- `ConLeche/MainTheorem.lean:110` (`no_False_declaration`),
  `ConLeche/SetTheory/Form.lean:35` (`Form`),
  `ConLeche/SetTheory/Core.lean` (`repl` field),
  `ConLeche/Semantics/Interp.lean:134` (`interp`; readers = stages 108–122),
  `ConLeche/SetModel/Value.lean:625` (`bval`), `:634` (`.empty => empty`).
