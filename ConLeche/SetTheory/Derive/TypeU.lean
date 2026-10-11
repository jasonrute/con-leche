module

public import ConLeche.SetTheory.Derive.Lfp

@[expose] public section

/-!
# Strict sets and the restricted universes (task #342)

A **strict** set is not the proof point and does not contain it.  What
`Sort n` will denote (stage 1b of task #342) is `typeU n`: the truth
values at `0`, the strict members of `univ n` above.  Until then
`typeU` is used where a construction must already land in the
restricted universe — the least pre-fixed families and tuples
(`Derive/LfpFam.lean`, `Derive/LfpTuple.lean`), whose family spaces
range over type-valued families.

The closure facts the lfp constructions need: `∅` is strict, a union of
strict sets is strict (a union equal to `pt = {ptTag}` would have all
its members inside `pt`, hence each `∅` or `pt`), and a subset of a
strict set is strict unless it is the point itself — which `unPt`
replaces by `∅`.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- A **strict** set: not the point, and the point is not a member. -/
def Strict (X : V) : Prop := X ≠ pt ∧ ¬ pt ∈ˢ X

/-- **The restricted universe**: the truth values at `0`, the strict
members of `univ n` above. -/
noncomputable def typeU (n : Nat) : V := if n = 0 then univ 0 else sep (univ n) Strict

theorem mem_typeU_zero {T : V} : T ∈ˢ typeU 0 ↔ T ∈ˢ (univ 0 : V) := by
  simp [typeU]

theorem mem_typeU_pos {n : Nat} (hn : n ≠ 0) {T : V} :
    T ∈ˢ typeU n ↔ T ∈ˢ (univ n : V) ∧ Strict T := by
  simp only [typeU, hn, ↓reduceIte]
  exact mem_sep

theorem mem_univ_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ typeU n) : T ∈ˢ (univ n : V) := by
  by_cases hn : n = 0
  · subst hn; exact mem_typeU_zero.mp h
  · exact ((mem_typeU_pos hn).mp h).1

theorem strict_of_mem_typeU {n : Nat} (hn : n ≠ 0) {T : V} (h : T ∈ˢ typeU n) : Strict T :=
  ((mem_typeU_pos hn).mp h).2

/-- A member of `univ n` that is strict when `n ≠ 0` is in `typeU n`. -/
theorem mem_typeU_of {n : Nat} {T : V} (hT : T ∈ˢ (univ n : V)) (hs : n ≠ 0 → Strict T) :
    T ∈ˢ typeU n := by
  by_cases hn : n = 0
  · subst hn; exact mem_typeU_zero.mpr hT
  · exact (mem_typeU_pos hn).mpr ⟨hT, hs hn⟩

/-- The point is not a truth value (`ptTag ∉ unitSet`). -/
theorem ne_pt_of_mem_univ_zero {T : V} (h : T ∈ˢ (univ 0 : V)) : T ≠ pt := by
  rintro rfl
  rw [univ_zero] at h
  have h1 : (ptTag : V) ∈ˢ unitSet := mem_univZero.mp h ptTag ptTag_mem_pt
  have h3 : (pt : V) ∈ˢ pt := mem_pt.mpr (mem_unitSet_iff.mp h1).symm
  exact not_mem_self (pt : V) h3

/-- A member of `typeU n` is not the point. -/
theorem ne_pt_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ typeU n) : T ≠ pt := by
  by_cases hn : n = 0
  · subst hn; exact ne_pt_of_mem_univ_zero (mem_typeU_zero.mp h)
  · exact (strict_of_mem_typeU hn h).1

/-! ## Closure facts -/

theorem strict_empty : Strict (empty : V) :=
  ⟨pt_ne_empty.symm, not_mem_empty _⟩

theorem empty_mem_typeU (n : Nat) : (empty : V) ∈ˢ typeU n :=
  mem_typeU_of (empty_mem_univ n) fun _ => strict_empty

/-- A set inside the point with no point member is empty. -/
theorem eq_empty_of_subset_pt {X : V} (hX : X ⊆ˢ pt) (hne : X ≠ pt) : X = empty := by
  refine Subset.antisymm (fun z hz => ?_) (empty_subset _)
  exfalso
  apply hne
  have hz' : z = ptTag := mem_pt.mp (hX z hz)
  refine Subset.antisymm hX fun y hy => ?_
  rw [mem_pt.mp hy, ← hz']
  exact hz

/-- **A union of strict sets is strict.** -/
theorem strict_sUnion {S : V} (h : ∀ y, y ∈ˢ S → Strict y) : Strict (sUnion S) := by
  refine ⟨fun he => ?_, fun hp => ?_⟩
  · have : (ptTag : V) ∈ˢ sUnion S := he ▸ ptTag_mem_pt
    obtain ⟨y, hy, hty⟩ := mem_sUnion.mp this
    have hsub : y ⊆ˢ pt := fun z hz => he ▸ mem_sUnion.mpr ⟨y, hy, hz⟩
    have := eq_empty_of_subset_pt hsub (h y hy).1
    rw [this] at hty
    exact not_mem_empty _ hty
  · obtain ⟨y, hy, hpy⟩ := mem_sUnion.mp hp
    exact (h y hy).2 hpy

theorem strict_binUnion {X Y : V} (hX : Strict X) (hY : Strict Y) : Strict (binUnion X Y) := by
  refine strict_sUnion fun y hy => ?_
  rcases mem_upair.mp hy with rfl | rfl
  · exact hX
  · exact hY

/-- A subset of a strict set is strict unless it is the point. -/
theorem strict_of_subset {X Y : V} (hY : Strict Y) (hXY : X ⊆ˢ Y) (hX : X ≠ pt) : Strict X :=
  ⟨hX, fun h => hY.2 (hXY _ h)⟩

/-! ## Dropping the point -/

open Classical in
/-- The point replaced by `∅`; every other set unchanged. -/
noncomputable def unPt (X : V) : V := if X = pt then empty else X

theorem unPt_of_ne {X : V} (h : X ≠ pt) : unPt X = X := by
  unfold unPt; exact ite_eq_right h

theorem unPt_ne_pt (X : V) : unPt X ≠ pt := by
  unfold unPt
  split
  · exact pt_ne_empty.symm
  · assumption

theorem unPt_subset (X : V) : unPt X ⊆ˢ X := by
  unfold unPt
  split
  · exact empty_subset _
  · exact Subset.refl _

theorem mem_of_mem_unPt {X x : V} (h : x ∈ˢ unPt X) : x ∈ˢ X := unPt_subset X x h

theorem mem_unPt {X x : V} (hX : X ≠ pt) : x ∈ˢ unPt X ↔ x ∈ˢ X := by
  rw [unPt_of_ne hX]

/-- A set inside the point is dropped to `∅` or is `∅` already. -/
theorem unPt_eq_empty_of_subset_pt {X : V} (h : X ⊆ˢ pt) : unPt X = empty := by
  unfold unPt
  split
  · rfl
  · exact eq_empty_of_subset_pt h ‹_›

/-- **A subset of a type, the point dropped, is a type of the level.** -/
theorem unPt_mem_typeU {n : Nat} {X Y : V} (hY : Y ∈ˢ typeU n) (hXY : X ⊆ˢ Y) :
    unPt X ∈ˢ typeU n := by
  refine mem_typeU_of (univ_mem_of_subset_mem (mem_univ_of_mem_typeU hY)
    ((unPt_subset X).trans hXY)) fun hn => ?_
  exact strict_of_subset (strict_of_mem_typeU hn hY) ((unPt_subset X).trans hXY) (unPt_ne_pt X)

/-- A separation from a type, the point dropped, is a type. -/
theorem unPt_sep_mem_typeU {n : Nat} {Y : V} {p : V → Prop} (hY : Y ∈ˢ typeU n) :
    unPt (sep Y p) ∈ˢ typeU n :=
  unPt_mem_typeU hY sep_subset

/-- A subset of a type that is not the point is a type. -/
theorem mem_typeU_of_subset {n : Nat} {X Y : V} (hY : Y ∈ˢ typeU n) (hXY : X ⊆ˢ Y)
    (hX : X ≠ pt) : X ∈ˢ typeU n := by
  have := unPt_mem_typeU hY hXY
  rwa [unPt_of_ne hX] at this

/-- A type inside a set lies inside the set with the point dropped. -/
theorem subset_unPt_of_mem_typeU {n : Nat} {X Y : V} (hY : Y ∈ˢ typeU n) (hYX : Y ⊆ˢ X) :
    Y ⊆ˢ unPt X := by
  by_cases hX : X = pt
  · subst hX
    rw [eq_empty_of_subset_pt hYX (ne_pt_of_mem_typeU hY)]
    exact empty_subset _
  · rw [unPt_of_ne hX]; exact hYX

/-- **A union of a member-indexed family of types is a type** (above
`Prop`). -/
theorem famUnion_mem_typeU {n : Nat} (hn : n ≠ 0) {A : V} {F : V → V} (hA : A ∈ˢ (univ n : V))
    (hF : ∀ a, a ∈ˢ A → F a ∈ˢ typeU n) : sUnion (image F A) ∈ˢ typeU n := by
  refine (mem_typeU_pos hn).mpr ⟨(univ_isTGUniverse hn).famUnion_mem hA fun a ha =>
    mem_univ_of_mem_typeU (hF a ha), strict_sUnion fun y hy => ?_⟩
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
  exact strict_of_mem_typeU hn (hF a ha)

end ConLeche.SetTheory
