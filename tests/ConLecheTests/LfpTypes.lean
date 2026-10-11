module

public import ConLeche.SetModel.Access

public section

/-!
# The least-fixed-point constructions over the restricted universe (task #342)

The family and tuple constructions (`Derive/LfpFam.lean`,
`Derive/LfpTuple.lean`) and the accessibility construction
(`SetModel/Access.lean`) read of a level `univ w` only `∅ ∈ univ w`,
`univ_dropClosed`, `univ_famUnion_mem` and
`univ_binUnion_sing_empty_mem`.  Stage 1b makes `univ` the restricted
universe: the truth values at `0`, above the members of `tg w` that are
not the proof point and do not contain it.  This file checks that the
four facts hold there (`restr`, built here from `tg`), so the
constructions' laws carry over to stage 1b unchanged; and it pins the
countermodel that makes the drop necessary: two strict fibres whose
intersection is the point.
-/

namespace ConLeche.SetTheory.LfpTypesTest

universe u

variable {V : Type u} [SetTheory V]

/-- Strict: not the point, and the point is not a member. -/
def StrictR (X : V) : Prop := X ≠ pt ∧ ¬ pt ∈ˢ X

open Classical in
/-- The restricted universe, built from the axiomatic chain. -/
noncomputable def restr (w : Nat) : V := if w = 0 then tg 0 else sep (tg w) StrictR

theorem mem_restr_pos {w : Nat} (hw : w ≠ 0) {X : V} :
    X ∈ˢ restr w ↔ X ∈ˢ (tg w : V) ∧ StrictR X := by
  unfold restr; rw [ite_eq_right hw]; exact mem_sep

theorem restr_zero : (restr 0 : V) = tg 0 := by unfold restr; rw [ite_eq_left rfl]

/-- A nonempty set inside the point is the point. -/
theorem eq_pt_of_subset_pt {Y y : V} (hY : Y ⊆ˢ pt) (hy : y ∈ˢ Y) : Y = pt := by
  refine Subset.antisymm hY fun z hz => ?_
  rw [mem_pt.mp hz, ← mem_pt.mp (hY y hy)]
  exact hy

theorem empty_mem_restr (w : Nat) : (empty : V) ∈ˢ restr w := by
  by_cases hw : w = 0
  · subst hw; rw [restr_zero]; exact empty_mem_tg 0
  · exact (mem_restr_pos hw).mpr ⟨empty_mem_tg w, pt_ne_empty.symm, not_mem_empty _⟩

/-- `univ_dropClosed`, at the restricted universe. -/
theorem restr_dropClosed (w : Nat) : DropClosed (restr w : V) := by
  intro Z S Y hZ hSZ hS hY hYS
  by_cases hw : w = 0
  · subst hw
    rw [restr_zero] at hZ hS
    exact absurd (subsetClosed_tg 0 _ _ hZ hSZ) hS
  · obtain ⟨hZt, -, hZp⟩ := (mem_restr_pos hw).mp hZ
    obtain ⟨-, hYne, -⟩ := (mem_restr_pos hw).mp hY
    -- `S` is a subset of a strict member, not a member: it is the point
    have hSpt : S = pt := by
      refine Classical.byContradiction fun hne => hS ((mem_restr_pos hw).mpr
        ⟨subsetClosed_tg w _ _ hZt hSZ, hne, fun h => hZp (hSZ _ h)⟩)
    subst hSpt
    refine Subset.antisymm (fun y hy => absurd (eq_pt_of_subset_pt hYS hy) hYne) (empty_subset _)

/-- `univ_famUnion_mem`, at the restricted universe: a union of strict
sets is strict. -/
theorem restr_famUnion_mem {w : Nat} (hw : w ≠ 0) {A : V} {F : V → V} (hA : A ∈ˢ (tg w : V))
    (hF : ∀ a, a ∈ˢ A → F a ∈ˢ restr w) : sUnion (image F A) ∈ˢ restr w := by
  refine (mem_restr_pos hw).mpr ⟨(tg_isTGUniverse hw).famUnion_mem hA fun a ha =>
    ((mem_restr_pos hw).mp (hF a ha)).1, fun he => ?_, fun hp => ?_⟩
  · have : (ptTag : V) ∈ˢ sUnion (image F A) := he ▸ ptTag_mem_pt
    obtain ⟨y, hy, hty⟩ := mem_sUnion.mp this
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact ((mem_restr_pos hw).mp (hF a ha)).2.1
      (eq_pt_of_subset_pt (fun z hz => he ▸ mem_sUnion.mpr ⟨_, hy, hz⟩) hty)
  · obtain ⟨y, hy, hpy⟩ := mem_sUnion.mp hp
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact ((mem_restr_pos hw).mp (hF a ha)).2.2 hpy

/-- `univ_binUnion_sing_empty_mem`, at the restricted universe. -/
theorem restr_binUnion_sing_empty_mem {w : Nat} (hw : w ≠ 0) {X : V} (hX : X ∈ˢ restr w) :
    binUnion X (sing empty) ∈ˢ restr w := by
  obtain ⟨hXt, hXne, hXp⟩ := (mem_restr_pos hw).mp hX
  have hU := tg_isTGUniverse (V := V) hw
  refine (mem_restr_pos hw).mpr ⟨hU.binUnion_mem (empty_mem_tg w) hXt
    (hU.sing_mem (empty_mem_tg w) (empty_mem_tg w)), fun he => ?_, fun hp => ?_⟩
  · -- `∅` is a member, and `∅ ≠ ptTag`
    have h0 : (empty : V) ∈ˢ binUnion X (sing empty) :=
      mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl))
    rw [he] at h0
    have h1 : (empty : V) ∈ˢ ptTag := empty_mem_ptTag
    rw [← mem_pt.mp h0] at h1
    exact not_mem_empty _ h1
  · rcases mem_binUnion.mp hp with h | h
    · exact hXp h
    · exact pt_ne_empty (mem_sing.mp h)

/-! ## The countermodel: an intersection of strict sets can be the point -/

theorem ptTag_ne_empty : (ptTag : V) ≠ empty := fun h =>
  not_mem_empty _ (h ▸ empty_mem_ptTag)

theorem ptTag_ne_pt : (ptTag : V) ≠ pt := fun h =>
  ptTag_ne_empty (mem_pt.mp (h ▸ empty_mem_ptTag)).symm

theorem strict_pair {a : V} (ha : a ≠ ptTag) (hpa : a ≠ pt) : StrictR (upair ptTag a : V) := by
  refine ⟨fun h => ha (mem_pt.mp (h ▸ mem_upair.mpr (Or.inr rfl))), fun hp => ?_⟩
  rcases mem_upair.mp hp with h | h
  · exact ptTag_ne_pt h.symm
  · exact hpa h.symm

/-- `{ptTag, ∅}` and `{ptTag, {∅}}` are strict, and their intersection is
the point: the closed fibres of `F X i = if ∅ ∈ X i then {ptTag, ∅} else
{ptTag, {∅}}`, whose raw least fibre is therefore not a type. -/
theorem countermodel :
    StrictR (upair ptTag empty : V) ∧ StrictR (upair ptTag (sing empty) : V) ∧
      sep (upair ptTag empty : V) (fun x => x ∈ˢ upair ptTag (sing empty)) = pt := by
  have hs0 : (sing empty : V) ≠ ptTag := fun h => ptTag_ne_sing empty h.symm
  have hspt : (sing empty : V) ≠ pt := fun h =>
    ptTag_ne_empty (mem_sing.mp (h ▸ ptTag_mem_pt : (ptTag : V) ∈ˢ sing empty))
  refine ⟨strict_pair ptTag_ne_empty.symm pt_ne_empty.symm, strict_pair hs0 hspt, ?_⟩
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := mem_sep.mp hx
    rcases mem_upair.mp h1 with rfl | rfl
    · exact ptTag_mem_pt
    · rcases mem_upair.mp h2 with h | h
      · exact absurd h.symm ptTag_ne_empty
      · have h0 : (empty : V) ∈ˢ sing empty := mem_sing.mpr rfl
        rw [← h] at h0
        exact absurd h0 (not_mem_empty _)
  · rw [mem_pt.mp hx]
    exact mem_sep.mpr ⟨mem_upair.mpr (Or.inl rfl), mem_upair.mpr (Or.inl rfl)⟩

/-- At a positive level the drop sends that intersection to `∅`. -/
example {w : Nat} (hw : w ≠ 0) :
    dropTo (restr w) (sep (upair ptTag empty : V) (fun x => x ∈ˢ upair ptTag (sing empty)))
      = empty := by
  rw [countermodel.2.2]
  unfold dropTo
  rw [ite_eq_right fun h => ((mem_restr_pos hw).mp h).2.1 rfl]

end ConLeche.SetTheory.LfpTypesTest
