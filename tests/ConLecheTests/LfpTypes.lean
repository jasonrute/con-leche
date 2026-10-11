module

public import ConLeche.SetModel.Access

public section

/-!
# Why the least-fixed-point constructions drop a fibre (task #342)

An intersection of types need not be a type: `{ptTag, ∅}` and
`{ptTag, {∅}}` are strict and their intersection is the point — the two
closed fibres of `F X i = if ∅ ∈ X i then {ptTag, ∅} else {ptTag, {∅}}`.
Over the restricted universe (`typeU`, what `univ` becomes at stage 1b)
`lfpFamIn`/`lfpTuple` drop such a fibre to `∅` (`dropTo`).
-/

namespace ConLeche.SetTheory.LfpTypesTest

universe u

variable {V : Type u} [SetTheory V]

/-! ## The countermodel: an intersection of strict sets can be the point -/

theorem ptTag_ne_empty : (ptTag : V) ≠ empty := fun h =>
  not_mem_empty _ (h ▸ empty_mem_ptTag)

theorem ptTag_ne_pt : (ptTag : V) ≠ pt := fun h =>
  ptTag_ne_empty (mem_pt.mp (h ▸ empty_mem_ptTag)).symm

theorem strict_pair {a : V} (ha : a ≠ ptTag) (hpa : a ≠ pt) : Strict (upair ptTag a : V) := by
  refine ⟨fun h => ha (mem_pt.mp (h ▸ mem_upair.mpr (Or.inr rfl))), fun hp => ?_⟩
  rcases mem_upair.mp hp with h | h
  · exact ptTag_ne_pt h.symm
  · exact hpa h.symm

/-- `{ptTag, ∅}` and `{ptTag, {∅}}` are strict, and their intersection is
the point: the closed fibres of `F X i = if ∅ ∈ X i then {ptTag, ∅} else
{ptTag, {∅}}`, whose raw least fibre is therefore not a type. -/
theorem countermodel :
    Strict (upair ptTag empty : V) ∧ Strict (upair ptTag (sing empty) : V) ∧
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
    dropTo (typeU w) (sep (upair ptTag empty : V) (fun x => x ∈ˢ upair ptTag (sing empty)))
      = empty := by
  rw [countermodel.2.2]
  unfold dropTo
  rw [ite_eq_right fun h => ((mem_typeU_pos hw).mp h).2.1 rfl]

end ConLeche.SetTheory.LfpTypesTest
