module

public import ConLeche.SetTheory.Derive.TypeU
import ConLeche.SetTheory.Derive.Graphs
@[expose] public section

/-!
# Least pre-fixed points of family functors (task #188, indexed)

The carrier of a directly installed recursive **family** `T : I → Sort w`
is the least pre-fixed point of its constructor-tower functor acting on
FAMILIES — graphs over the index-tuple set `I` with values in the
restricted universe `typeU w` (`famSpace`: type-valued families, task
#342), ordered pointwise (`FamLe`).  This is `Lfp.lean` fibrewise:

    lfpFamSet w I F = i ↦ {x ∈ L₀ i | ∀ closed X, x ∈ X i}

over a classically chosen closed family `L₀` (the empty family when
there is none), a fibre equal to the point dropped to `∅` — TOTAL, so
the basis constant `lfpFam` needs no certificate (`lfpFamSet_mem`).
An intersection of types need not be a type
(`F X i = if ∅ ∈ X i then {ptTag, ∅} else {ptTag, {∅}}` has the two
closed fibres `{ptTag, ∅}`, `{ptTag, {∅}}`, whose intersection is
`{ptTag} = pt`); for a monotone `F` mapping the family space into
itself the drop never fires (`mem_app_lfpFamSet`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The pointwise order on families over `I`. -/
def FamLe (I X Y : V) : Prop := ∀ i, i ∈ˢ I → app X i ⊆ˢ app Y i

theorem FamLe.refl (I X : V) : FamLe I X X := fun _ _ => Subset.refl _

theorem FamLe.trans {I X Y Z : V} (h₁ : FamLe I X Y) (h₂ : FamLe I Y Z) : FamLe I X Z :=
  fun i hi => Subset.trans (h₁ i hi) (h₂ i hi)

/-! ## Families of arbitrary members of a set (relation graphs)

The least pre-fixed family of a functor on families over `I` with
fibres in a set `C` closed under subsets — the raw fibrewise
intersection.  This is the recursor family's GRAPH
(`SetModel/GraphRec.lean`, `C = tg ℓ`): a relation, whose fibres are
sets of values, not types. -/

section In

/-- The families over `I` with fibres in `C`. -/
noncomputable def famSpaceIn (C I : V) : V := piSet I fun _ => C

/-- An `F`-closed family in `famSpaceIn C I`. -/
def IsClosedFamIn (C I F X : V) : Prop :=
  X ∈ˢ famSpaceIn C I ∧ FamLe I (app F X) X

/-- Monotonicity of a family functor on `famSpaceIn C I`. -/
def MonoFamIn (C I F : V) : Prop :=
  ∀ X Y, X ∈ˢ famSpaceIn C I → Y ∈ˢ famSpaceIn C I → FamLe I X Y → FamLe I (app F X) (app F Y)

/-- The functor maps `famSpaceIn C I` into itself. -/
def MapsFamIn (C I F : V) : Prop :=
  ∀ X, X ∈ˢ famSpaceIn C I → app F X ∈ˢ famSpaceIn C I

/-- `C` is closed under subsets. -/
def SubsetClosed (C : V) : Prop := ∀ y z, y ∈ˢ C → z ⊆ˢ y → z ∈ˢ C

theorem famSpaceIn_app {C I X i : V} (hX : X ∈ˢ famSpaceIn C I) (hi : i ∈ˢ I) : app X i ∈ˢ C :=
  app_mem_of_mem_piSet hX hi

theorem graph_mem_famSpaceIn {C I : V} {G : V → V} (h : ∀ i, i ∈ˢ I → G i ∈ˢ C) :
    graph G I ∈ˢ famSpaceIn C I :=
  graph_mem_piSet h

open Classical in
/-- **The least pre-fixed family of `F` in `famSpaceIn C I`** — fibrewise
the intersection of the closed families when there is one (separated
from a chosen closed family), the empty family otherwise. -/
noncomputable def lfpFamIn (C I F : V) : V :=
  if h : ∃ L, IsClosedFamIn C I F L then
    graph (fun i => sep (app (Classical.choose h) i)
      (fun x => ∀ X, IsClosedFamIn C I F X → x ∈ˢ app X i)) I
  else graph (fun _ => empty) I

theorem mem_app_lfpFamIn {C I F i x : V} (h : ∃ L, IsClosedFamIn C I F L) (hi : i ∈ˢ I) :
    x ∈ˢ app (lfpFamIn C I F) i ↔ ∀ X, IsClosedFamIn C I F X → x ∈ˢ app X i := by
  unfold lfpFamIn
  rw [dite_eq_left h, app_graph hi, mem_sep]
  exact ⟨fun hx => hx.2, fun hx => ⟨hx _ (Classical.choose_spec h), hx⟩⟩

theorem lfpFamIn_le {C I F X : V} (hX : IsClosedFamIn C I F X) : FamLe I (lfpFamIn C I F) X :=
  fun _ hi _x hx => (mem_app_lfpFamIn ⟨X, hX⟩ hi).mp hx X hX

/-- **Formation**: in a subset-closed `C` containing `∅`. -/
theorem lfpFamIn_mem {C : V} (hC : SubsetClosed C) (hE : (empty : V) ∈ˢ C) (I F : V) :
    lfpFamIn C I F ∈ˢ famSpaceIn C I := by
  unfold lfpFamIn
  split
  · rename_i h
    exact graph_mem_famSpaceIn fun _ hi =>
      hC _ _ (famSpaceIn_app (Classical.choose_spec h).1 hi) sep_subset
  · exact graph_mem_famSpaceIn fun _ _ => hE

theorem lfpFamIn_closed {C I F : V} (hC : SubsetClosed C) (hE : (empty : V) ∈ˢ C)
    (h : ∃ L, IsClosedFamIn C I F L) (hmono : MonoFamIn C I F) :
    FamLe I (app F (lfpFamIn C I F)) (lfpFamIn C I F) := by
  intro i hi x hx
  rw [mem_app_lfpFamIn h hi]
  intro X hX
  exact hX.2 i hi x (hmono _ _ (lfpFamIn_mem hC hE I F) hX.1 (lfpFamIn_le hX) i hi x hx)

/-- The fixed-point equation, fibrewise. -/
theorem app_lfpFamIn_eq {C I F : V} (hC : SubsetClosed C) (hE : (empty : V) ∈ˢ C)
    (h : ∃ L, IsClosedFamIn C I F L) (hmono : MonoFamIn C I F) (hmaps : MapsFamIn C I F)
    {i : V} (hi : i ∈ˢ I) :
    app (app F (lfpFamIn C I F)) i = app (lfpFamIn C I F) i := by
  have hmem := lfpFamIn_mem hC hE I F
  have hcl := lfpFamIn_closed hC hE h hmono
  refine Subset.antisymm (hcl i hi) ?_
  exact lfpFamIn_le ⟨hmaps _ hmem, hmono _ _ (hmaps _ hmem) hmem hcl⟩ i hi

end In

/-- Every level of the axiomatic chain `tg` is closed under subsets
(the restricted universe is not: a subset of a strict set can be the
point). -/
theorem subsetClosed_tg (w : Nat) : SubsetClosed (tg w : V) := by
  intro y z hy hz
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [tg_zero, mem_univZero] at hy ⊢
    exact hz.trans hy
  · exact (tg_isTGUniverse (Nat.pos_iff_ne_zero.mp hw)).mem_of_subset_mem hy hz

/-! ## Type-valued families -/

/-- The family space over `I`: graphs into the restricted universe
`typeU w` — type-valued families (task #342). -/
noncomputable def famSpace (w : Nat) (I : V) : V := famSpaceIn (typeU w) I

/-- An `F`-closed family: a pre-fixed point of `app F` in the family
space. -/
def IsClosedFam (w : Nat) (I F X : V) : Prop :=
  X ∈ˢ famSpace w I ∧ FamLe I (app F X) X

/-- A family's fibre is a type of the level. -/
theorem famSpace_app_typeU {w : Nat} {I X i : V} (hX : X ∈ˢ famSpace w I) (hi : i ∈ˢ I) :
    app X i ∈ˢ (typeU w : V) :=
  app_mem_of_mem_piSet hX hi

theorem famSpace_app {w : Nat} {I X i : V} (hX : X ∈ˢ famSpace w I) (hi : i ∈ˢ I) :
    app X i ∈ˢ (univ w : V) :=
  mem_univ_of_mem_typeU (famSpace_app_typeU hX hi)

/-- Above `Prop`, a family's fibre is strict. -/
theorem famSpace_app_strict {w : Nat} (hw : w ≠ 0) {I X i : V} (hX : X ∈ˢ famSpace w I)
    (hi : i ∈ˢ I) : Strict (app X i) :=
  strict_of_mem_typeU hw (famSpace_app_typeU hX hi)

/-- Members of the family space agreeing pointwise are equal. -/
theorem famSpace_ext {w : Nat} {I X Y : V} (hX : X ∈ˢ famSpace w I) (hY : Y ∈ˢ famSpace w I)
    (h : ∀ i, i ∈ˢ I → app X i = app Y i) : X = Y :=
  eq_of_mem_piSet_app_eq hX hY h

/-- A graph with type fibres is in the family space. -/
theorem graph_mem_famSpace {w : Nat} {I : V} {G : V → V}
    (h : ∀ i, i ∈ˢ I → G i ∈ˢ (typeU w : V)) : graph G I ∈ˢ famSpace w I :=
  graph_mem_piSet h

/-- A graph with fibres in `univ w`, strict above `Prop`, is in the
family space. -/
theorem graph_mem_famSpace_of {w : Nat} {I : V} {G : V → V}
    (h : ∀ i, i ∈ˢ I → G i ∈ˢ (univ w : V)) (hs : w ≠ 0 → ∀ i, i ∈ˢ I → Strict (G i)) :
    graph G I ∈ˢ famSpace w I :=
  graph_mem_famSpace fun i hi => mem_typeU_of (h i hi) fun hw => hs hw i hi

/-- The family space lies inside the unrestricted one (`univ w`
fibres) — the carrier `I → Sort w` denotes until stage 1b. -/
theorem mem_piSet_univ_of_famSpace {w : Nat} {I X : V} (hX : X ∈ˢ famSpace w I) :
    X ∈ˢ piSet I fun _ => (univ w : V) := by
  rw [← eq_graph_app_of_mem_piSet hX]
  exact graph_mem_piSet fun _ hi => famSpace_app hX hi

open Classical in
/-- **The least pre-fixed family of `F` over `I`** — fibrewise the
intersection of the closed families when there is one (separated from
a chosen closed family), the empty family otherwise.  An intersection
of types can be the point (`{ptTag, ∅} ∩ {ptTag, {∅}}`); such a fibre is
dropped to `∅` (`unPt`), so the value is a type-valued family for EVERY
`F`.  Under monotonicity and `MapsFam` nothing is dropped
(`mem_app_lfpFamSet`). -/
noncomputable def lfpFamSet (w : Nat) (I F : V) : V :=
  if h : ∃ L, IsClosedFam w I F L then
    graph (fun i => unPt (sep (app (Classical.choose h) i)
      (fun x => ∀ X, IsClosedFam w I F X → x ∈ˢ app X i))) I
  else graph (fun _ => empty) I

theorem lfpFamSet_of_not {w : Nat} {I F : V} (h : ¬ ∃ L, IsClosedFam w I F L) :
    lfpFamSet w I F = graph (fun _ => empty) I := by
  unfold lfpFamSet; exact dite_eq_right h

theorem forall_of_mem_app_lfpFamSet {w : Nat} {I F i x : V} (h : ∃ L, IsClosedFam w I F L)
    (hi : i ∈ˢ I) (hx : x ∈ˢ app (lfpFamSet w I F) i) :
    ∀ X, IsClosedFam w I F X → x ∈ˢ app X i := by
  unfold lfpFamSet at hx
  rw [dite_eq_left h, app_graph hi] at hx
  exact (mem_sep.mp (mem_of_mem_unPt hx)).2

/-- A type below every closed family's fibre is below the least
family's. -/
theorem subset_app_lfpFamSet {w : Nat} {I F i Y : V} (h : ∃ L, IsClosedFam w I F L)
    (hi : i ∈ˢ I) (hY : Y ∈ˢ (typeU w : V))
    (hYX : ∀ X, IsClosedFam w I F X → Y ⊆ˢ app X i) : Y ⊆ˢ app (lfpFamSet w I F) i := by
  unfold lfpFamSet
  rw [dite_eq_left h, app_graph hi]
  refine subset_unPt_of_mem_typeU hY fun x hx => mem_sep.mpr ⟨?_, fun X hX => hYX X hX x hx⟩
  exact hYX _ (Classical.choose_spec h) x hx

/-- **Leastness**: the least pre-fixed family lies in every closed
family. -/
theorem lfpFamSet_le {w : Nat} {I F X : V} (hX : IsClosedFam w I F X) :
    FamLe I (lfpFamSet w I F) X :=
  fun _ hi _x hx => forall_of_mem_app_lfpFamSet ⟨X, hX⟩ hi hx X hX

/-- **Formation, unconditional**: the least pre-fixed family is in the
family space. -/
theorem lfpFamSet_mem (w : Nat) (I F : V) : lfpFamSet w I F ∈ˢ famSpace w I := by
  by_cases h : ∃ L, IsClosedFam w I F L
  · unfold lfpFamSet
    rw [dite_eq_left h]
    exact graph_mem_famSpace fun _ hi =>
      unPt_sep_mem_typeU (famSpace_app_typeU (Classical.choose_spec h).1 hi)
  · rw [lfpFamSet_of_not h]
    exact graph_mem_famSpace fun _ _ => empty_mem_typeU w

/-- Monotonicity of a family functor on the family space. -/
def MonoFam (w : Nat) (I F : V) : Prop :=
  ∀ X Y, X ∈ˢ famSpace w I → Y ∈ˢ famSpace w I → FamLe I X Y → FamLe I (app F X) (app F Y)

/-- The functor maps the family space into itself. -/
def MapsFam (w : Nat) (I F : V) : Prop :=
  ∀ X, X ∈ˢ famSpace w I → app F X ∈ˢ famSpace w I

/-- **Closure**: the least pre-fixed family is a pre-fixed point.  The
functor must map the family space into itself: a fibre dropped from the
point to `∅` stays closed only because the functor's fibre there, a
type below the point, is `∅` too. -/
theorem lfpFamSet_closed {w : Nat} {I F : V} (h : ∃ L, IsClosedFam w I F L)
    (hmono : MonoFam w I F) (hmaps : MapsFam w I F) :
    FamLe I (app F (lfpFamSet w I F)) (lfpFamSet w I F) := by
  intro i hi
  refine subset_app_lfpFamSet h hi (famSpace_app_typeU (hmaps _ (lfpFamSet_mem w I F)) hi)
    fun X hX => ?_
  exact Subset.trans (hmono _ _ (lfpFamSet_mem w I F) hX.1 (lfpFamSet_le hX) i hi) (hX.2 i hi)

/-- **Nothing is dropped** under monotonicity and `MapsFam`: the least
family's fibre is exactly the intersection of the closed families'. -/
theorem mem_app_lfpFamSet {w : Nat} {I F i x : V} (h : ∃ L, IsClosedFam w I F L)
    (hmono : MonoFam w I F) (hmaps : MapsFam w I F) (hi : i ∈ˢ I) :
    x ∈ˢ app (lfpFamSet w I F) i ↔ ∀ X, IsClosedFam w I F X → x ∈ˢ app X i :=
  ⟨forall_of_mem_app_lfpFamSet h hi,
    fun hx => hx _ ⟨lfpFamSet_mem w I F, lfpFamSet_closed h hmono hmaps⟩⟩

/-- The least pre-fixed family is a post-fixed point. -/
theorem lfpFamSet_fixed {w : Nat} {I F : V} (h : ∃ L, IsClosedFam w I F L)
    (hmono : MonoFam w I F) (hmaps : MapsFam w I F) :
    FamLe I (lfpFamSet w I F) (app F (lfpFamSet w I F)) := by
  refine lfpFamSet_le ⟨hmaps _ (lfpFamSet_mem w I F), ?_⟩
  exact hmono _ _ (hmaps _ (lfpFamSet_mem w I F)) (lfpFamSet_mem w I F)
    (lfpFamSet_closed h hmono hmaps)

/-- The fixed-point equation, fibrewise. -/
theorem app_lfpFamSet_eq {w : Nat} {I F : V} (h : ∃ L, IsClosedFam w I F L)
    (hmono : MonoFam w I F) (hmaps : MapsFam w I F) {i : V} (hi : i ∈ˢ I) :
    app (app F (lfpFamSet w I F)) i = app (lfpFamSet w I F) i :=
  Subset.antisymm (lfpFamSet_closed h hmono hmaps i hi) (lfpFamSet_fixed h hmono hmaps i hi)

end ConLeche.SetTheory
