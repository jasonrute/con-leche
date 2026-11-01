# The lean4lean-model bridge: Carneiro's hypothesis implies ConLeche's

A separate Lake package (task #204) proving, in Lean, that the
large-cardinal hypothesis of Mario Carneiro's
[lean4lean-model](https://github.com/digama0/lean4lean-model) implies
ConLeche's `SetTheory` interface (`ConLeche/SetTheory/Core.lean`) —
which is now stated in **first-order** form: ZF⁻ (extensionality,
pairing, union, power set, regularity, the replacement *scheme* as a
meta-level scheme over relations) plus an ω-chain of Grothendieck
universes (`ConLeche.IsUniverse`, five first-order closure clauses).

It is a **separate package on purpose**: the ConLeche libraries never
acquire a Mathlib dependency (build time, trust surface, layering).  The
main repository's `lake build` and gates do not see this directory.

## Building

```sh
cd bridge/lean4lean-model
lake build          # `lake update` was already run; the manifest is committed.
```

The first build fetches Mathlib's oleans automatically (Mathlib's
post-update hook runs `cache get`; if it did not, run `lake exe cache
get` first).  `lean-toolchain` is a copy of the repository's; Mathlib is
pinned to the matching tag (`v4.35.0`).  `ConLeche.SetTheory.Core` is built
from `../..` by the path `require`.  Everything lands in this
directory's `.lake` (gitignored).

## Contents

`ConLecheBridge/Carneiro.lean`:

* `ConLecheBridge.OmegaInaccessibles` — **Carneiro's hypothesis, verbatim**
  from `Lean4LeanModel/Consistency.lean`:

  ```lean
  def OmegaInaccessibles : Prop :=
    ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible
  ```

  His file is internal to his repository (which also depends on
  lean4lean), so the definition is transcribed, not imported; the text
  and the Mathlib notions (`Cardinal.IsInaccessible`, `StrictMono`) are
  identical.  His theorem is
  `consistency (_ : OmegaInaccessibles.{u}) {env : VEnv} (_ : env.WF) (U : Nat) :
  ¬ ∃ e, env.HasType U [] e Term.false` (sorried there, pending his
  model construction).

* `isUniverse_vonNeumann : κ.IsInaccessible → ConLeche.IsUniverse (· ∈ ·) (V_ κ.ord)`
  — Mathlib's von Neumann stage at an inaccessible satisfies the five
  first-order closure clauses.  Transitivity, subset closure, power-set
  closure (`rank_powerset` + `IsSuccLimit.succ_lt`) and union closure
  (`rank_sUnion_le`) are direct Mathlib computations.  The fibre-wise
  replacement clause is where inaccessibility enters: the image of a
  member `a ∈ V_ κ.ord` under a functional relation with values in
  `V_ κ.ord` is a subset of `V_ κ.ord` (the values are members), and its
  cardinality is `< κ`: `card a ≤ card (V_ (rank a)) = preBeth (rank a)
  < κ` by **strong limitness** (`card_lt_of_mem_vonNeumann`), hence
  `card (image f a) ≤ card a < κ` (`card_image_le`), so by
  **regularity** (`rank_lt_ord_of_card_lt`: fewer than `κ` ordinals
  below `κ.ord` are bounded below `κ.ord`) the image is a member
  (`mem_vonNeumann`).

* `setTheoryOfChain κ hmono hinacc : ConLeche.SetTheory ZFSet.{u}` — the
  explicit instance: ZF⁻ fields from Mathlib (`ZFSet.ext`, `{a, b}`,
  `⋃₀`, `powerset`, `mem_wf`, and the replacement scheme via `image`
  under `Classical.allZFSetDefinable`), `univChain n := V_ (κ n).ord`.

* `carneiro_implies_conleche : OmegaInaccessibles.{u} → Nonempty (Σ V : Type (u + 1), ConLeche.SetTheory V)`.

* Axiom pin (`#guard_msgs in #print axioms`): `propext`,
  `Classical.choice`, `Quot.sound` — nothing else.

Nothing beyond Carneiro's hypothesis was needed: `ℵ₀ < κ` is used only
to make `κ.ord` a limit ordinal (for `powerset y ∈ V_ κ`), regularity
and strong limitness exactly as described above.

## The converse

The briefing for this task expected the converse to fail, with `H(κ)`
for a *singular* strong-limit `κ` (hereditarily `< κ`-sized sets) as a
universe that is not a `V_λ` for `λ` inaccessible.  **That
countermodel is wrong.**  Take `κ = ℶ_ω` and `y = {V_{ω+n} | n < ω}`:
every member is in `H(κ)` (`|TC(V_{ω+n})| = ℶ_n < κ`), so `y ⊆ H(κ)`;
but `|TC(y)| = ℶ_ω = κ`, so `y ∉ H(κ)`; and `|y| = ℵ₀ ≠ κ = |H(κ)|`, so
`y` is not equinumerous with `H(κ)`.  The old Tarski-form clause fails
for it.

The same argument shows the five first-order clauses are the right
strength: a fibre-wise replacement image of a member is *small*
(cardinality `< κ`), which regularity turns into membership, so
singular strong limits are excluded just as before.  In fact, over any
model with the ambient cardinal arithmetic, a transitive universe
satisfying the five clauses is `∅`, `V_ω`, or `V_κ` with `κ` strongly
inaccessible; applied to ConLeche's chain, `univChain (n + 2)` is
`V_{κ_n}` for a strictly increasing sequence of inaccessibles (the
bottom two may be `∅` and `V_ω`), so the two hypotheses are
**equivalent up to that shift**.  The converse is not mechanized here
(the counting argument needs a lower bound on the number of small
subsets that Mathlib does not provide off the shelf); it is recorded
in `DESIGN.md` as a follow-up.

## CI

Not part of the default gates.  `.github/workflows/bridge.yml` builds
it on demand (`workflow_dispatch`) and on pushes touching `bridge/**` or
`ConLeche/SetTheory/Core.lean`.
