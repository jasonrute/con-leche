import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.SetTheory.ZFC.Cardinal
import ConLeche.SetTheory.Core

/-!
# Carneiro's hypothesis implies ConLeche's `SetTheory` (task #204)

Mario Carneiro's lean4lean-model (`Lean4LeanModel/Consistency.lean`,
<https://github.com/digama0/lean4lean-model>) states the consistency of
Lean's type theory relative to one hypothesis, `OmegaInaccessibles`:
*there are `ω` inaccessible cardinals — a strictly increasing
`ℕ`-indexed sequence of them, one to interpret each Lean universe*.
ConLeche's consistency proof is parametric in the `ConLeche.SetTheory`
class (`ConLeche/SetTheory/Core.lean`): first-order ZF⁻ (extensionality,
pairing, union, power set, regularity, the first-order replacement
scheme as a meta-level scheme over relations) plus an ω-chain of
Grothendieck universes (`ConLeche.IsUniverse`, five first-order closure
clauses).  This module proves, in Lean, that his hypothesis implies
ours:

* `OmegaInaccessibles` is transcribed **verbatim** from his file (same
  Mathlib notions — `Cardinal.IsInaccessible`, `StrictMono`; his file is
  internal to his repository, which additionally depends on lean4lean,
  so it is copied rather than imported; the text is identical).
* `setTheoryOfChain κ` is an explicit `ConLeche.SetTheory` instance on
  Mathlib's `ZFSet.{u}` for any strictly increasing sequence of
  inaccessibles `κ`, with `univChain n := V_ (κ n).ord` (Mathlib's
  von Neumann hierarchy).  The ZF⁻ fields are Mathlib's; the work is
  `isUniverse_vonNeumann`: `V_ κ` for `κ` inaccessible satisfies the
  five closure clauses.  Clause 5 (fibre-wise replacement) is where
  inaccessibility enters: the image of a member of `V_ κ.ord` under a
  functional relation with values in `V_ κ.ord` is a subset of
  `V_ κ.ord` of cardinality `< κ` (it is an image of a member, and
  `card (V_ (rank a)) = preBeth (rank a) < κ` by strong limitness), so
  by **regularity** (`rank_lt_ord_of_card_lt`) it is a member.
* `carneiro_implies_conleche : OmegaInaccessibles.{u} →
  Nonempty (Σ V : Type (u + 1), ConLeche.SetTheory V)`.

Nothing here is imported by the ConLeche libraries: this is a separate Lake
package so that ConLeche never acquires a Mathlib dependency.  The closing
`#print axioms` guard pins the bridge theorem to Lean's three standard
axioms.
-/

universe u

open Cardinal Order ZFSet

namespace ConLecheBridge

/-- **Carneiro's hypothesis**, transcribed verbatim from
`Lean4LeanModel/Consistency.lean` (lean4lean-model, pinned in
`_tmp/lean4lean-model`; Mathlib `v4.30.0` there, `v4.35.0` here — the
definition of `Cardinal.IsInaccessible` is the same structure in both):

> There are `ω` inaccessible cardinals: a strictly increasing
> `ℕ`-indexed sequence of them, one to interpret each Lean universe
> `Sort 0, Sort 1, ...`.

His consistency theorem is
`theorem consistency (_ : OmegaInaccessibles.{u}) {env : VEnv} (_ : env.WF) (U : Nat) :
  ¬ ∃ e, env.HasType U [] e Term.false`. -/
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

/-! ### `V_ κ` is a Grothendieck universe (the five first-order closure
clauses) for `κ` inaccessible -/

variable {κ : Cardinal.{u}}

/-- A subset of `V_ κ.ord` of cardinality `< κ` has rank `< κ.ord`:
regularity of `κ` bounds the least strict upper bound of `< κ` many
ordinals below `κ.ord`. -/
theorem rank_lt_ord_of_card_lt (hκ : κ.IsRegular) {y : ZFSet.{u}}
    (hy : y ⊆ V_ κ.ord) (hc : y.card < κ) : y.rank < κ.ord := by
  let e : y ≃ Shrink.{u} y := equivShrink _
  let f : Shrink.{u} y → Ordinal.{u} := fun z => rank (e.symm z).1
  have hlt : ⨆ z, f z + 1 < κ.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hκ.cof_ord]) fun z =>
      mem_vonNeumann.mp (hy (e.symm z).2)
  refine lt_of_le_of_lt ?_ hlt
  rw [rank_le_iff]
  intro z hz
  have := Ordinal.lt_iSup_add_one f (e ⟨z, hz⟩)
  simpa [f, e] using this

/-- Below an inaccessible, the beth function stays below it. -/
theorem preBeth_lt_of_lt_ord (hκ : κ.IsInaccessible) :
    ∀ {a : Ordinal.{u}}, a < κ.ord → preBeth a < κ := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => intro _; rw [preBeth_zero]; exact hκ.pos
  | add_one a ih =>
    intro h
    rw [preBeth_add_one]
    exact hκ.isStrongPrelimit (ih ((lt_add_one a).trans h))
  | limit a ha ih =>
    intro h
    rw [preBeth_limit ha.isSuccPrelimit]
    refine Cardinal.lift_iSup_lt_of_lt_cof_ord ?_ fun b => ih b b.2 (b.2.trans h)
    rw [hκ.isRegular.lift.cof_ord, mk_Iio_ordinal, lift_lift, lift_lt]
    exact lt_ord.mp h

/-- The cardinality of a member of `V_ κ.ord` is below an inaccessible `κ`. -/
theorem card_lt_of_mem_vonNeumann (hκ : κ.IsInaccessible) {a : ZFSet.{u}}
    (ha : a ∈ V_ κ.ord) : a.card < κ := by
  have h1 : a.card ≤ (V_ (rank a)).card := card_mono (subset_vonNeumann_self a)
  rw [card_vonNeumann] at h1
  exact h1.trans_lt (preBeth_lt_of_lt_ord hκ (mem_vonNeumann.mp ha))

/-- **`V_ κ` is a Grothendieck universe** (ConLeche's five-clause
`IsUniverse`) **for every inaccessible `κ`**. -/
theorem isUniverse_vonNeumann (hκ : κ.IsInaccessible) :
    ConLeche.IsUniverse (· ∈ ·) (V_ κ.ord) := by
  have hlim : IsSuccLimit κ.ord := isSuccLimit_ord hκ.aleph0_lt.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- transitivity
    intro y z (hy : y ∈ V_ κ.ord) (hz : z ∈ y)
    exact isTransitive_vonNeumann _ y hy hz
  · -- subsets of members are members
    intro y z (hy : y ∈ V_ κ.ord) hzy
    exact mem_vonNeumann_of_subset (fun w hw => hzy w hw) hy
  · -- power sets stay inside
    intro y (hy : y ∈ V_ κ.ord)
    refine ⟨powerset y, ?_, fun z hz => mem_powerset.mpr fun w hw => hz w hw⟩
    show powerset y ∈ V_ κ.ord
    rw [mem_vonNeumann, rank_powerset]
    exact hlim.succ_lt (mem_vonNeumann.mp hy)
  · -- unions stay inside
    intro s (hs : s ∈ V_ κ.ord)
    refine ⟨⋃₀ s, ?_, fun z => mem_sUnion⟩
    show ⋃₀ s ∈ V_ κ.ord
    rw [mem_vonNeumann]
    exact (rank_sUnion_le s).trans_lt (mem_vonNeumann.mp hs)
  · -- fibre-wise replacement
    intro a ha p hfun
    classical
    let f : ZFSet.{u} → ZFSet.{u} := fun z => if hz : z ∈ a then Classical.choose (hfun z hz) else ∅
    have hf : ∀ z (hz : z ∈ a), f z = Classical.choose (hfun z hz) := fun z hz => dite_eq_left hz
    have instDefinable : ZFSet.Definable 1 (fun s => f (s 0)) := Classical.allZFSetDefinable _
    have : ZFSet.Definable 1 (fun s => f (s 0)) := instDefinable
    clear instDefinable
    refine ⟨ZFSet.image (fun z => f z) a, ?_, fun y => ?_⟩
    · show ZFSet.image (fun z => f z) a ∈ V_ κ.ord
      rw [mem_vonNeumann]
      refine rank_lt_ord_of_card_lt hκ.isRegular ?_ ?_
      · intro z hz
        rw [ZFSet.mem_image] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        rw [hf w hw]
        exact (Classical.choose_spec (hfun w hw)).1
      · refine (card_image_le (f := fun z => f z) (x := a)).trans_lt
          (card_lt_of_mem_vonNeumann hκ ha)
    · show y ∈ ZFSet.image (fun z => f z) a ↔ ∃ x, x ∈ a ∧ p x y
      rw [ZFSet.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, (hf z hz ▸ (Classical.choose_spec (hfun z hz)).2.1)⟩
      · rintro ⟨x, hx, hxy⟩
        refine ⟨x, hx, ?_⟩
        rw [hf x hx]
        exact ((Classical.choose_spec (hfun x hx)).2.2 y hxy).symm

/-! ### The `ConLeche.SetTheory` instance on `ZFSet` -/

set_option warn.classDefReducibility false in
/-- ConLeche's set theory on Mathlib's `ZFSet.{u}`, from any strictly
increasing sequence of inaccessibles: the ZF⁻ fields are Mathlib's
(`ZFSet.ext`, pairs, `⋃₀`, `powerset`, `mem_wf`, `image` under
`Classical.allZFSetDefinable` — the first-order replacement scheme),
and `univChain n := V_ (κ n).ord`. -/
noncomputable def setTheoryOfChain (
    κ : ℕ → Cardinal.{u}) (hmono : StrictMono κ)
    (hinacc : ∀ n, (κ n).IsInaccessible) : ConLeche.SetTheory ZFSet.{u} where
  Mem := (· ∈ ·)
  ext h := ZFSet.ext h
  upair a b := {a, b}
  mem_upair := mem_pair
  sUnion := ZFSet.sUnion
  mem_sUnion := mem_sUnion
  power := powerset
  mem_power := mem_powerset
  regularity x h := by
    obtain ⟨y, hy, hmin⟩ := mem_wf.has_min {y | y ∈ x} h
    exact ⟨y, hy, fun ⟨z, hzy, hzx⟩ => hmin z hzx hzy⟩
  repl a p hfun := by
    classical
    let f : ZFSet.{u} → ZFSet.{u} := fun z => if hz : z ∈ a then Classical.choose (hfun z hz) else ∅
    have hf : ∀ z (hz : z ∈ a), f z = Classical.choose (hfun z hz) := fun z hz => dite_eq_left hz
    have instDefinable : ZFSet.Definable 1 (fun s => f (s 0)) := Classical.allZFSetDefinable _
    have : ZFSet.Definable 1 (fun s => f (s 0)) := instDefinable
    clear instDefinable
    refine ⟨ZFSet.image (fun z => f z) a, fun y => ?_⟩
    show y ∈ ZFSet.image (fun z => f z) a ↔ ∃ x, x ∈ a ∧ p x y
    rw [ZFSet.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, (hf z hz ▸ (Classical.choose_spec (hfun z hz)).1)⟩
    · rintro ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      rw [hf x hx]
      exact ((Classical.choose_spec (hfun x hx)).2 y hxy).symm
  univChain n := V_ (κ n).ord
  univChain_mem n := vonNeumann_mem_of_lt (ord_lt_ord.mpr (hmono (Nat.lt_succ_self n)))
  univChain_univ n := isUniverse_vonNeumann (hinacc n)

set_option warn.classDefReducibility false in
/-- ConLeche's set theory on `ZFSet.{u}` under Carneiro's hypothesis. -/
noncomputable def setTheoryOfCarneiro (h : OmegaInaccessibles.{u}) : ConLeche.SetTheory ZFSet.{u} :=
  setTheoryOfChain (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2

/-- **Carneiro's hypothesis implies ConLeche's.**  `ω` strongly inaccessible
cardinals (lean4lean-model's `OmegaInaccessibles`) give a model of
ConLeche's `SetTheory` interface — on Mathlib's `ZFSet.{u}`, with the
universe chain `V_ (κ n).ord`. -/
theorem carneiro_implies_conleche :
    OmegaInaccessibles.{u} → Nonempty (Σ V : Type (u + 1), ConLeche.SetTheory V) :=
  fun h => ⟨⟨ZFSet.{u}, setTheoryOfCarneiro h⟩⟩

/--
info: 'ConLecheBridge.carneiro_implies_conleche' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms carneiro_implies_conleche

end ConLecheBridge
