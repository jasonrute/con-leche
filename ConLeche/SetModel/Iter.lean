module

public import ConLeche.SetModel.TaggedSum
public import ConLeche.SetTheory.Derive.Rec

@[expose] public section

/-!
# Countable unions (task #188)

The definable countable union `natUnionF G = ⋃ {app G c | c ∈ᵉ ω}`, a
member of `tg w` at `w ≥ 1` when `G` is (`ω ∈ tg w`, `omega_mem_tg_succ`).
The meta `natUnion f` (the ω-indexed union through the tag fibre
`natFibre f`) was retired in stage 26: its only call site (`accPaths`)
now reads the definable twin.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

/-! ## The definable countable union (`natUnionF`)

`natUnionF G` is the definable countable union of the family read off a
graph `G` over `ω` (the first-order twin of the retired meta `natUnion f`
at `app G (vnat i) = f i`). -/

/-- The definable union of a countable family read off a graph over `ω`:
`⋃ {app G c | c ∈ᵉ ω}`. -/
noncomputable def natUnionF (G : V) : V :=
  sUnion (appImageF G omega)

theorem mem_natUnionF {G x : V} : x ∈ˢ natUnionF G ↔ ∃ c, c ∈ˢ omega ∧ x ∈ˢ app G c := by
  unfold natUnionF
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨c, hc, rfl⟩ := mem_appImageF.mp hy
    exact ⟨c, hc, hxy⟩
  · rintro ⟨c, hc, hxy⟩
    exact ⟨app G c, mem_appImageF.mpr ⟨c, hc, rfl⟩, hxy⟩

/-- A definable countable union of a member graph over `ω` is a member of
a positive axiomatic level (the value closure comes from `appImageF_mem`,
so only `G ∈ᵉ tg w` is needed). -/
theorem natUnionF_mem_tg_pos {w : Nat} (hw : w ≠ 0) {G : V} (hG : G ∈ˢ (tg w : V)) :
    natUnionF G ∈ˢ (tg w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact (tg_isUniverse (Nat.succ_ne_zero w')).sUnion_mem
    ((tg_isUniverse (Nat.succ_ne_zero w')).appImageF_mem (empty_mem_tg _) hG
      (omega_mem_tg_succ w'))

/-! ## The definable iteration graph over `ω`

`iterGraphF A B` internalizes a meta iteration with constant step
`x ↦ sigmaConstF A x` from `unitSet` (the `accPathsN` shape): it is the
definable recursion graph `recGraph unitSet (iterStepGraphF A B)`,
whose step graph is the constant graph of `sigmaConstGraphF A B` over
`ω`.  At the standard numerals it reads off any meta family with the
same equations (`iterGraphF_vnat_eq`); at nonstandard members of `ω`
the values are junk, so union bridges are one-sided. -/

/-- The constant step graph over `ω`:
`app (app (iterStepGraphF A B) n) x = sigmaConstF A x` for
`n ∈ˢ ω` and `x ∈ˢ B`. -/
noncomputable def iterStepGraphF (A B : V) : V := constGraphF (sigmaConstGraphF A B) omega

theorem app_iterStepGraphF {A B n x : V} (hn : n ∈ˢ omega) (hx : x ∈ˢ B) :
    app (app (iterStepGraphF A B) n) x = sigmaConstF A x := by
  have h1 : app (iterStepGraphF A B) n = sigmaConstGraphF A B := app_constGraphF hn
  rw [h1]
  exact app_sigmaConstGraphF hx

/-- The definable iteration graph of the step `x ↦ sigmaConstF A x`
from `unitSet` over `ω`. -/
noncomputable def iterGraphF (A B : V) : V := recGraph unitSet (iterStepGraphF A B)

theorem iterGraphF_app_empty (A B : V) : app (iterGraphF A B) (empty : V) = unitSet :=
  recGraph_app_empty unitSet (iterStepGraphF A B)

theorem iterGraphF_app_vsucc {A B n : V} (hn : n ∈ˢ omega) (hx : app (iterGraphF A B) n ∈ˢ B) :
    app (iterGraphF A B) (vsucc n) = sigmaConstF A (app (iterGraphF A B) n) := by
  have h : app (iterGraphF A B) (vsucc n) =
      app (app (iterStepGraphF A B) n) (app (iterGraphF A B) n) :=
    recGraph_app_vsucc unitSet (iterStepGraphF A B) hn
  rw [h, app_iterStepGraphF hn hx]

/-- Standard-numeral bridge: a meta family `f` with base `unitSet`,
step `f (n + 1) = sigmaConstF A (f n)`, and values in `B` is read off
by the iteration graph at every standard numeral. -/
theorem iterGraphF_vnat_eq (A B : V) (f : Nat → V) (h0 : f 0 = unitSet)
    (hstep : ∀ n, f (n + 1) = sigmaConstF A (f n)) (hB : ∀ n, f n ∈ˢ B) :
    ∀ n, app (iterGraphF A B) (vnat n) = f n := by
  intro n
  have h := natrecF_vnat_eq unitSet (iterStepGraphF A B) f h0
    (fun n => (hstep n).trans (app_iterStepGraphF (vnat_mem_omega n) (hB n)).symm) n
  rw [natrecF_eq] at h
  exact h

/-- The definable path set `⋃ {app (iterGraphF A B) c | c ∈ˢ ω}` — the
first-order twin of `natUnion (accPathsN A)` at the standard numerals. -/
noncomputable def accPathsF (A B : V) : V := natUnionF (iterGraphF A B)

theorem mem_accPathsF {A B x : V} :
    x ∈ˢ accPathsF A B ↔ ∃ c, c ∈ˢ omega ∧ x ∈ˢ app (iterGraphF A B) c :=
  mem_natUnionF

theorem pt_mem_accPathsF (A B : V) : (pt : V) ∈ˢ accPathsF A B := by
  refine mem_accPathsF.mpr ⟨vnat 0, vnat_mem_omega 0, ?_⟩
  have h : app (iterGraphF A B) (vnat 0) = unitSet := iterGraphF_app_empty A B
  rw [h]
  exact pt_mem_unitSet

/-- Pair closure of the definable path set, when the iteration graph
stays in the bound `B` on all of `ω` (e.g. `B` a universe containing
`A` — see `iterGraphF_app_mem`). -/
theorem kpair_mem_accPathsF {A B a p : V} (ha : a ∈ˢ A) (hp : p ∈ˢ accPathsF A B)
    (hB : ∀ c, c ∈ˢ omega → app (iterGraphF A B) c ∈ˢ B) :
    kpair a p ∈ˢ accPathsF A B := by
  obtain ⟨c, hc, hp⟩ := mem_accPathsF.mp hp
  refine mem_accPathsF.mpr ⟨vsucc c, vsucc_mem_omega hc, ?_⟩
  rw [iterGraphF_app_vsucc hc (hB c hc)]
  exact mem_sigmaConstF.mpr ⟨a, ha, p, hp, rfl⟩

/-! ## Bound preservation along the iteration graph

`appBoundF` expresses `app G c ∈ˢ U` (parameter `U` a universe) as a
first-order formula in `c`, so `omega_induction` closes the iteration
graph under `U`. -/

/-- The parameters `(G, U, pt)` of `appBoundF`. -/
noncomputable def appBoundParam (G U : V) : Fin 3 → V := fun i =>
  match i.val with
  | 0 => G
  | 1 => U
  | _ => (pt : V)

/-- Variable map `Fin 4 → Fin 5` reading `appEqF`'s `(pt, v, g, u)` out of
`(G, U, pt, c, v)` as `(pt, v, G, c)`. -/
def appBoundMap : Fin 4 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨4, by omega⟩
  | 2 => ⟨0, by omega⟩
  | _ => ⟨3, by omega⟩

/-- `app G c ∈ˢ U` (parameters `G, U, pt`; variable `3 ↦ c`). -/
def appBoundF : Form 4 :=
  .ex (.and (Form.relabel appBoundMap appEqF) (.mem ⟨4, by omega⟩ ⟨1, by omega⟩))

theorem realize_appBoundF {G U c : V} :
    Form.Realize Mem (Form.snoc (appBoundParam G U) c) appBoundF ↔ app G c ∈ˢ U := by
  have hComp : ∀ v : V,
      (Form.snoc (Form.snoc (appBoundParam G U) c) v) ∘ appBoundMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ => (pt : V)) v) G) c := by
    intro v
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [appBoundF, Form.realize_ex, Form.realize_and, Form.realize_relabel, hComp,
    realize_appEqF, Form.realize_mem, Form.snoc_mk]
  simp [appBoundParam]

/-- The iteration graph over `ω` stays in a universe `U` containing `A`
(definable induction on `ω` via `appBoundF`). -/
theorem iterGraphF_app_mem {U A : V} (hU : IsUniverse (Mem (V := V)) U)
    (he : (empty : V) ∈ˢ U) (hA : A ∈ˢ U) {c : V} (hc : c ∈ˢ omega) :
    app (iterGraphF A U) c ∈ˢ U := by
  have h0 : Form.Realize Mem (Form.snoc (appBoundParam (iterGraphF A U) U) (empty : V))
      appBoundF := by
    rw [realize_appBoundF, iterGraphF_app_empty]
    exact hU.unitSet_mem he
  have hstep : ∀ x : V, x ∈ˢ omega →
      Form.Realize Mem (Form.snoc (appBoundParam (iterGraphF A U) U) x) appBoundF →
      Form.Realize Mem (Form.snoc (appBoundParam (iterGraphF A U) U) (vsucc x)) appBoundF := by
    intro x hx hIH
    rw [realize_appBoundF] at hIH ⊢
    rw [iterGraphF_app_vsucc hx hIH]
    exact hU.sigmaConstF_mem he hA hIH
  exact realize_appBoundF.mp (omega_induction h0 hstep hc)

end ConLeche.SetTheory.Tower
