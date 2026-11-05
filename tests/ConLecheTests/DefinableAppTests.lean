module

public import ConLeche.SetTheory.Derive.Rec
public import ConLeche.SetTheory.Derive.Tg

public section

/-!
# Definable application: `appImageF` / `piSetApp` at a concrete graph

The Stage 15 toolkit exercised at `testS = {<pt, {pt}>, pt}`: a
single-valued graph with `app (testS V) pt = unitSet`.  The definable
image `appImageF (testS V) unitSet` and the definable function space
`piSetApp (testS V) unitSet` are shown equal to their meta twins
`image (app (testS V)) unitSet` / `piSet unitSet (fun j => app (testS V) j)`,
and closed under `tg w` via the clause-6 lemmas `appImageF_mem` /
`piSetApp_mem` (and `app_mem` for the point application) — no meta
`sep`/`image`/clause 5 anywhere.
-/

namespace ConLeche.SetTheory.DefinableAppEx

universe u

variable {V : Type u} [SetTheory V]

/-- A concrete single-valued graph: the only pair at `pt` is
`<pt, unitSet>`, so `app (testS V) pt = unitSet`. -/
noncomputable def testS (V : Type u) [SetTheory V] : V := upair (kpair pt unitSet) pt

theorem kpair_pt_unitSet_mem_testS : kpair pt (unitSet : V) ∈ˢ testS V :=
  mem_upair_left _ _

theorem testS_ne_pt : testS V ≠ (pt : V) := by
  intro h
  have hm := h ▸ kpair_pt_unitSet_mem_testS
  exact ptTag_ne_kpair pt unitSet (mem_pt.mp hm).symm

theorem testS_single : ∀ y, kpair pt y ∈ˢ testS V → y = unitSet := by
  intro y hy
  have hyu : (kpair pt y : V) ∈ˢ upair (kpair pt (unitSet : V)) (pt : V) := hy
  rcases mem_upair.mp hyu with h | h
  · exact (kpair_inj h).2
  · exact absurd h.symm (pt_ne_kpair pt y)

theorem app_testS_pt : app (testS V) pt = (unitSet : V) :=
  app_eq_of_unique testS_ne_pt kpair_pt_unitSet_mem_testS testS_single

/-- Single-valuedness of `testS` on the domain `unitSet`, in the shape
the `hfun` arguments of `piSetApp` take. -/
theorem testS_hfun : ∀ x, x ∈ˢ (unitSet : V) → ∃ y, y ∈ˢ app (testS V) x ∧
    ∀ y', y' ∈ˢ app (testS V) x → y' = y := by
  intro x hx
  rw [mem_unitSet_iff] at hx
  subst hx
  refine ⟨pt, ?_, fun y' hy' => ?_⟩
  · show pt ∈ˢ app (testS V) pt
    rw [app_testS_pt]
    exact pt_mem_unitSet
  · rw [app_testS_pt, mem_unitSet_iff] at hy'
    exact hy'

/-! ## Membership and equality with the meta twins -/

example (z : V) : z ∈ˢ appImageF (testS V) unitSet ↔ z = unitSet := by
  rw [mem_appImageF]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_unitSet_iff] at hx
    rw [hx, app_testS_pt]
  · intro rfl
    exact ⟨pt, pt_mem_unitSet, app_testS_pt.symm⟩

example : image (app (testS V)) (unitSet : V) = appImageF (testS V) (unitSet : V) :=
  image_app_eq

example : piSetApp (testS V) unitSet testS_hfun = piSet (unitSet : V) (fun j => app (testS V) j) :=
  piSetApp_eq_piSet testS_hfun

example : (sing (kpair pt pt) : V) ∈ˢ piSetApp (testS V) unitSet testS_hfun := by
  rw [mem_piSetApp testS_hfun]
  constructor
  · intro p hp
    rw [mem_sing] at hp
    subst hp
    rw [mem_sigmaPairs]
    exact ⟨pt, pt_mem_unitSet, pt,
      by show pt ∈ˢ app (testS V) pt; rw [app_testS_pt]; exact pt_mem_unitSet, rfl⟩
  · intro x hx
    rw [mem_unitSet_iff] at hx
    subst hx
    exact ⟨pt, mem_sing.mpr rfl, fun y' hy' => (kpair_inj (mem_sing.mp hy')).2⟩

/-! ## Closure in `tg w` (clause 6, no meta clause 5) -/

variable {w : Nat}

theorem testS_mem_tg (hw : w ≠ 0) : testS V ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).upair_mem (empty_mem_tg w)
    ((tg_isUniverse hw).kpair_mem (empty_mem_tg w)
      ((tg_isUniverse hw).pt_mem (empty_mem_tg w)) (unitSet_mem_tg w))
    ((tg_isUniverse hw).pt_mem (empty_mem_tg w))

example (hw : w ≠ 0) : app (testS V) pt ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).app_mem (empty_mem_tg w) (testS_mem_tg hw)

example (hw : w ≠ 0) : appImageF (testS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).appImageF_mem (empty_mem_tg w) (testS_mem_tg hw) (unitSet_mem_tg w)

example (hw : w ≠ 0) : piSetApp (testS V) unitSet testS_hfun ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).piSetApp_mem (empty_mem_tg w) (testS_mem_tg hw) (unitSet_mem_tg w)
    testS_hfun

/-! ## The definable graph of `app g` (`graphAppF`) -/

example : (kpair pt unitSet : V) ∈ˢ graphAppF (testS V) unitSet :=
  mem_graphAppF.mpr ⟨pt, pt_mem_unitSet, by rw [app_testS_pt]⟩

example : graphAppF (testS V) unitSet = graph (fun x => app (testS V) x) unitSet :=
  graphAppF_eq

example : app (graphAppF (testS V) unitSet) pt = unitSet := by
  rw [app_graphAppF pt_mem_unitSet, app_testS_pt]

example : graphAppF (testS V) unitSet ∈ˢ piSet unitSet (fun _ => upair (empty : V) unitSet) :=
  graphAppF_mem_piSet fun x hx => by
    rw [mem_unitSet_iff] at hx
    subst hx
    rw [app_testS_pt]
    exact mem_upair_right _ _

example (hw : w ≠ 0) : graphAppF (testS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).graphAppF_mem (empty_mem_tg w) (testS_mem_tg hw) (unitSet_mem_tg w)

end ConLeche.SetTheory.DefinableAppEx
