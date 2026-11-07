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


/-! ## Function-cons paths (stage 26, the `w = 0` branch)

At level `0` no universe contains the bound `A` (`tg 0 = univZero`), so
the iteration-graph path set `accPathsF A (tg w)` cannot be made
pair-closed there.  The escape is to encode a path as a TOTAL FUNCTION
`f : ω → A ∪ {pt}` (`pathSetF A`): the whole function space lives in the
single power set `power (sigmaPairsAppF (pathCodomF A) ω)` — no universe
needed — and `consF`/`tailF` give the head/tail shift. -/

/-- `vsucc` is injective (regularity at the pair). -/
theorem vsucc_inj {a b : V} (h : vsucc a = vsucc b) : a = b :=
  Classical.byContradiction fun hne => by
  have ha : a ∈ˢ b := by
    have h1 : a ∈ˢ vsucc a := self_mem_vsucc a
    rw [h] at h1
    rcases mem_vsucc.mp h1 with h' | h'
    · exact h'
    · exact absurd h' hne
  have hb : b ∈ˢ a := by
    have h1 : b ∈ˢ vsucc b := self_mem_vsucc b
    rw [← h] at h1
    rcases mem_vsucc.mp h1 with h' | h'
    · exact h'
    · exact absurd h'.symm hne
  obtain ⟨y, hy, hmin⟩ := regularity (upair a b) ⟨a, mem_upair_left a b⟩
  have hba : b ∈ˢ upair a b := mem_upair_right a b
  have hab : a ∈ˢ upair a b := mem_upair_left a b
  have hab : a ∈ˢ upair a b := mem_upair_left a b
  rcases mem_upair.mp hy with rfl | rfl
  · exact hmin ⟨b, hb, hba⟩
  · exact hmin ⟨a, ha, hab⟩

/-- Parameters `(empty, omega)` of `omegaCasesF` (`0 ↦ empty`, `1 ↦ omega`). -/
noncomputable def omegaCasesParam : Fin 2 → V := fun i => if i.val = 0 then (empty : V) else omega

/-- Variable map `Fin 2 → Fin 3`, `0 ↦ 2`, `1 ↦ 0` (reads `equalF`'s
`(a, b)` as `(n, empty)` out of `(empty, omega, n)`). -/
def ocEqMap : Fin 2 → Fin 3 := fun i => if i.val = 0 then ⟨2, by omega⟩ else ⟨0, by omega⟩

/-- Variable map `Fin 2 → Fin 4`, `0 ↦ 2`, `1 ↦ 3` (reads `vsuccEqF`'s
`(e, m)` as `(n, x)` out of `(empty, omega, n, x)`). -/
def ocVsMap : Fin 2 → Fin 4 := fun i => if i.val = 0 then ⟨2, by omega⟩ else ⟨3, by omega⟩

/-- `n = empty ∨ ∃ x ∈ˢ ω, n = vsucc x` (bound `2 ↦ n`; parameters
`0 ↦ empty`, `1 ↦ omega`). -/
def omegaCasesF : Form 3 :=
  .or (Form.relabel ocEqMap equalF)
    (.ex (.and (.mem ⟨3, by omega⟩ ⟨1, by omega⟩) (Form.relabel ocVsMap vsuccEqF)))

theorem realize_omegaCasesF {n : V} :
    Form.Realize Mem (Form.snoc omegaCasesParam n) omegaCasesF ↔
      n = (empty : V) ∨ ∃ x, x ∈ˢ (omega : V) ∧ n = vsucc x := by
  have hEq : (Form.snoc omegaCasesParam n) ∘ ocEqMap = Form.snoc (fun _ => n) (empty : V) := by
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hVs : ∀ x : V, (Form.snoc (Form.snoc omegaCasesParam n) x) ∘ ocVsMap =
      Form.snoc (fun _ => n) x := by
    intro x
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [omegaCasesF, Form.realize_or, Form.realize_relabel, hEq, Form.realize_ex,
    Form.realize_and, Form.realize_mem, hVs, realize_equalF, realize_vsuccEqF, Form.snoc_mk]
  simp [omegaCasesParam]

/-- Every member of `ω` is `empty` or a `vsucc`. -/
theorem omega_cases {n : V} (hn : n ∈ˢ (omega : V)) :
    n = (empty : V) ∨ ∃ x, x ∈ˢ (omega : V) ∧ n = vsucc x := by
  have h := omega_induction (p := omegaCasesParam) (φ := omegaCasesF)
    (by rw [realize_omegaCasesF]; exact Or.inl rfl)
    (fun x hx hIH => by
      rw [realize_omegaCasesF] at hIH ⊢
      exact Or.inr ⟨x, hx, rfl⟩)
    hn
  rw [realize_omegaCasesF] at h
  exact h

/-- The codomain graph of a function-cons path: the constant graph of
`A ∪ {pt}` over `ω`. -/
noncomputable def pathCodomF (A : V) : V := constGraphF (binUnion A unitSet) omega

theorem app_pathCodomF {A x : V} (hx : x ∈ˢ (omega : V)) :
    app (pathCodomF A) x = binUnion A unitSet :=
  app_constGraphF hx

/-- The function-cons path set over `A`: total functions
`ω → A ∪ {pt}`, in the single power set
`power (sigmaPairsAppF (pathCodomF A) ω)` — no universe needed. -/
noncomputable def pathSetF (A : V) : V := piSetAppNF (pathCodomF A) omega

theorem mem_pathSetF {A f : V} :
    f ∈ˢ pathSetF A ↔ f ⊆ˢ sigmaPairsAppF (pathCodomF A) omega ∧
      ∀ x, x ∈ˢ (omega : V) → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y := by
  unfold pathSetF
  exact mem_piSetAppNF

theorem pathSetF_ne_pt {A f : V} (hf : f ∈ˢ pathSetF A) : f ≠ (pt : V) := by
  obtain ⟨y, hy, -⟩ := (mem_pathSetF.mp hf).2 (empty : V) empty_mem_omega
  intro h
  exact ptTag_ne_kpair (empty : V) y (mem_pt.mp (h ▸ hy)).symm

/-- The empty path: the constant-`pt` function on `ω`. -/
noncomputable def emptyPathF (_A : V) : V := constGraphF (pt : V) omega

theorem emptyPathF_mem_pathSetF (A : V) : emptyPathF A ∈ˢ pathSetF A := by
  rw [mem_pathSetF]
  constructor
  · intro z hz
    have hz' : z ∈ˢ constGraphF (pt : V) omega := hz
    obtain ⟨x, hx, rfl⟩ := mem_constGraphF.mp hz'
    exact mem_sigmaPairsAppF.mpr ⟨x, hx, (pt : V), by
      rw [app_pathCodomF hx]; exact mem_binUnion.mpr (Or.inr pt_mem_unitSet), rfl⟩
  · intro k hk
    refine ⟨(pt : V), mem_constGraphF.mpr ⟨k, hk, rfl⟩, fun y hy => ?_⟩
    have hy' : kpair k y ∈ˢ constGraphF (pt : V) omega := hy
    obtain ⟨x, -, h⟩ := mem_constGraphF.mp hy'
    exact (kpair_inj h).2

theorem app_emptyPathF {A x : V} (hx : x ∈ˢ (omega : V)) :
    app (emptyPathF A) x = (pt : V) := by
  refine app_eq_of_unique ?_ (mem_constGraphF.mpr ⟨x, hx, rfl⟩) (fun y hy => ?_)
  · intro h
    have hg : constGraphF (pt : V) omega ≠ (pt : V) := by
      rw [constGraphF_eq_graph]; exact graph_ne_pt
    exact hg h
  · have hy' : kpair x y ∈ˢ constGraphF (pt : V) omega := hy
    obtain ⟨x', -, h'⟩ := mem_constGraphF.mp hy'
    exact (kpair_inj h').2

/-! ### The shift: `shiftF p = {⟨vsucc x, y⟩ | x ∈ˢ ω, ⟨x, y⟩ ∈ˢ p}` -/

/-- Variable map `Fin 2 → Fin 5`, `0 ↦ 3`, `1 ↦ 0` (reads `vsuccEqF`'s
`(e, m)` as `(w, x)` out of `(x, z, p, w, y)`). -/
def shiftVMap : Fin 2 → Fin 5 := fun i => if i.val = 0 then ⟨3, by omega⟩ else ⟨0, by omega⟩

/-- Variable map `Fin 3 → Fin 5`, `0 ↦ 1`, `1 ↦ 3`, `2 ↦ 4` (reads
`kpairEqF`'s `(z, x, y)` as `(z, w, y)` out of `(x, z, p, w, y)`). -/
def shiftKMap : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨1, by omega⟩
  | 1 => ⟨3, by omega⟩
  | _ => ⟨4, by omega⟩

/-- Variable map `Fin 3 → Fin 5`, `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 4` (reads
`kpairMemF`'s `(a, f, y)` as `(x, p, y)` out of `(x, z, p, w, y)`). -/
def shiftMMap : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨2, by omega⟩
  | _ => ⟨4, by omega⟩

/-- The shift relation `z = ⟨vsucc x, y⟩` with `⟨x, y⟩ ∈ˢ p`
(replacement convention: `0 ↦ x`, `1 ↦ z`, parameter `2 ↦ p`). -/
def shiftRelF : Form 3 :=
  .ex (.ex (.and (Form.relabel shiftVMap vsuccEqF)
    (.and (Form.relabel shiftKMap kpairEqF) (Form.relabel shiftMMap kpairMemF))))

theorem realize_shiftRelF {x z p : V} :
    Form.Realize Mem (Form.cons2 x z (fun _ => p)) shiftRelF ↔
      ∃ w y, w = vsucc x ∧ z = kpair w y ∧ kpair x y ∈ˢ p := by
  have hcons : Form.cons2 x z (fun _ => p) = (Form.snoc (Form.snoc (fun _ => x) z) p : Fin 3 → V) := by
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  rw [hcons]
  have hV : ∀ w y : V, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => x) z) p) w) y)
      ∘ shiftVMap = Form.snoc (fun _ => w) x := by
    intro w y
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hK : ∀ w y : V, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => x) z) p) w) y)
      ∘ shiftKMap = Form.snoc (Form.snoc (fun _ => z) w) y := by
    intro w y
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hM : ∀ w y : V, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => x) z) p) w) y)
      ∘ shiftMMap = Form.snoc (Form.snoc (fun _ => x) p) y := by
    intro w y
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [shiftRelF, Form.realize_ex, Form.realize_and, Form.realize_relabel, hV, hK, hM,
    realize_vsuccEqF, realize_kpairEqF, realize_kpairMemF]

theorem shiftF_fun {A p : V} (hp : p ∈ˢ pathSetF A) :
    ∀ x, x ∈ˢ (omega : V) → ∃ z, Form.Realize Mem (Form.cons2 x z (fun _ => p)) shiftRelF ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' (fun _ => p)) shiftRelF → z' = z := by
  intro x hx
  obtain ⟨y, hy, huniq⟩ := (mem_pathSetF.mp hp).2 x hx
  refine ⟨kpair (vsucc x) y, realize_shiftRelF.mpr ⟨vsucc x, y, rfl, rfl, hy⟩, fun z' hz => ?_⟩
  obtain ⟨w, y', hw, hz', hmem⟩ := realize_shiftRelF.mp hz
  rw [hz', hw, huniq y' hmem]

/-- The shift of a path: `shiftF p = {⟨vsucc x, y⟩ | x ∈ˢ ω, ⟨x, y⟩ ∈ˢ p}`. -/
noncomputable def shiftF {A : V} (p : V) (hp : p ∈ˢ pathSetF A) : V :=
  imageF shiftRelF (fun _ => p) (omega : V) (shiftF_fun hp)

theorem mem_shiftF {A p z : V} (hp : p ∈ˢ pathSetF A) :
    z ∈ˢ shiftF p hp ↔
      ∃ x, x ∈ˢ (omega : V) ∧ ∃ w y, w = vsucc x ∧ z = kpair w y ∧ kpair x y ∈ˢ p := by
  simp only [shiftF, mem_imageF (shiftF_fun hp), realize_shiftRelF]

/-! ### Cons and tail -/

/-- Cons: `consF a p = {⟨empty, a⟩} ∪ shiftF p` — the path with head `a`
and tail `p`. -/
noncomputable def consF {A : V} (a p : V) (hp : p ∈ˢ pathSetF A) : V :=
  binUnion (sing (kpair (empty : V) a)) (shiftF p hp)

theorem mem_consF {A a p z : V} (hp : p ∈ˢ pathSetF A) :
    z ∈ˢ consF a p hp ↔ z = kpair (empty : V) a ∨ z ∈ˢ shiftF p hp := by
  simp only [consF, mem_binUnion, mem_sing]

theorem consF_ne_pt {A a p : V} (hp : p ∈ˢ pathSetF A) : consF a p hp ≠ (pt : V) := by
  intro h
  have h1 : kpair (empty : V) a ∈ˢ consF a p hp := (mem_consF hp).mpr (Or.inl rfl)
  exact ptTag_ne_kpair (empty : V) a (mem_pt.mp (h ▸ h1)).symm

theorem consF_mem_pathSetF {A a p : V} (ha : a ∈ˢ A) (hp : p ∈ˢ pathSetF A) :
    consF a p hp ∈ˢ pathSetF A := by
  rw [mem_pathSetF]
  constructor
  · intro z hz
    rcases (mem_consF hp).mp hz with rfl | hz
    · exact mem_sigmaPairsAppF.mpr ⟨(empty : V), empty_mem_omega, a, by
        rw [app_pathCodomF empty_mem_omega]; exact mem_binUnion.mpr (Or.inl ha), rfl⟩
    · obtain ⟨x, hx, w, y, hw, rfl, hxy⟩ := (mem_shiftF hp).mp hz
      obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ :=
        mem_sigmaPairsAppF.mp ((mem_pathSetF.mp hp).1 (kpair x y) hxy)
      obtain ⟨-, rfl⟩ := kpair_inj hxy₀
      have hw' : w ∈ˢ (omega : V) := hw ▸ vsucc_mem_omega hx
      exact mem_sigmaPairsAppF.mpr ⟨w, hw', y, by
        rw [app_pathCodomF hw', ← app_pathCodomF hx₀]; exact hy₀, rfl⟩
  · intro k hk
    rcases omega_cases hk with rfl | ⟨x, hx, rfl⟩
    · refine ⟨a, (mem_consF hp).mpr (Or.inl rfl), fun y hy => ?_⟩
      rcases (mem_consF hp).mp hy with h | h
      · exact (kpair_inj h).2
      · obtain ⟨x', -, w, y', hw, h', -⟩ := (mem_shiftF hp).mp h
        exact (vsucc_ne_empty x' ((kpair_inj h').1.trans hw).symm).elim
    · obtain ⟨y₀, hy₀, huniq⟩ := (mem_pathSetF.mp hp).2 x hx
      refine ⟨y₀, (mem_consF hp).mpr (Or.inr ((mem_shiftF hp).mpr
        ⟨x, hx, vsucc x, y₀, rfl, rfl, hy₀⟩)), fun y hy => ?_⟩
      rcases (mem_consF hp).mp hy with h | h
      · exact (vsucc_ne_empty x (kpair_inj h).1).elim
      · obtain ⟨x', hx', w, y', hw, h', hxy'⟩ := (mem_shiftF hp).mp h
        obtain ⟨h1, h2⟩ := kpair_inj h'
        have hx' : x = x' := vsucc_inj (h1.trans hw)
        rw [← hx'] at hxy'
        rw [h2, huniq y' hxy']

theorem app_consF_empty {A a p : V} (hp : p ∈ˢ pathSetF A) :
    app (consF a p hp) (empty : V) = a := by
  refine app_eq_of_unique (consF_ne_pt hp) ((mem_consF hp).mpr (Or.inl rfl)) (fun y hy => ?_)
  rcases (mem_consF hp).mp hy with h | h
  · exact (kpair_inj h).2
  · obtain ⟨x', -, w, y', hw, h', -⟩ := (mem_shiftF hp).mp h
    exact (vsucc_ne_empty x' ((kpair_inj h').1.trans hw).symm).elim

theorem app_consF_vsucc {A a p : V} (hp : p ∈ˢ pathSetF A) {x : V} (hx : x ∈ˢ (omega : V)) :
    app (consF a p hp) (vsucc x) = app p x := by
  obtain ⟨y₀, hy₀, huniq⟩ := (mem_pathSetF.mp hp).2 x hx
  have happ : app p x = y₀ := app_eq_of_unique (pathSetF_ne_pt hp) hy₀ huniq
  rw [happ]
  refine app_eq_of_unique (consF_ne_pt hp)
    ((mem_consF hp).mpr (Or.inr ((mem_shiftF hp).mpr ⟨x, hx, vsucc x, y₀, rfl, rfl, hy₀⟩)))
    (fun y hy => ?_)
  rcases (mem_consF hp).mp hy with h | h
  · exact (vsucc_ne_empty x (kpair_inj h).1).elim
  · obtain ⟨x', hx', w, y', hw, h', hxy'⟩ := (mem_shiftF hp).mp h
    obtain ⟨h1, h2⟩ := kpair_inj h'
    have hx' : x = x' := vsucc_inj (h1.trans hw)
    rw [← hx'] at hxy'
    rw [h2, huniq y' hxy']

/-- Variable map `Fin 3 → Fin 5`, `0 ↦ 1`, `1 ↦ 0`, `2 ↦ 4` (reads
`kpairEqF`'s `(z, x, y)` as `(z, x, y)` out of `(x, z, p, w, y)`). -/
def tailKMap : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨1, by omega⟩
  | 1 => ⟨0, by omega⟩
  | _ => ⟨4, by omega⟩

/-- Variable map `Fin 3 → Fin 5`, `0 ↦ 3`, `1 ↦ 2`, `2 ↦ 4` (reads
`kpairMemF`'s `(a, f, y)` as `(w, p, y)` out of `(x, z, p, w, y)`). -/
def tailMMap : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨2, by omega⟩
  | _ => ⟨4, by omega⟩

/-- The tail relation `z = ⟨x, y⟩` with `⟨vsucc x, y⟩ ∈ˢ p`
(replacement convention: `0 ↦ x`, `1 ↦ z`, parameter `2 ↦ p`). -/
def tailRelF : Form 3 :=
  .ex (.ex (.and (Form.relabel shiftVMap vsuccEqF)
    (.and (Form.relabel tailKMap kpairEqF) (Form.relabel tailMMap kpairMemF))))

theorem realize_tailRelF {x z p : V} :
    Form.Realize Mem (Form.cons2 x z (fun _ => p)) tailRelF ↔
      ∃ w y, w = vsucc x ∧ z = kpair x y ∧ kpair w y ∈ˢ p := by
  have hcons : Form.cons2 x z (fun _ => p) = (Form.snoc (Form.snoc (fun _ => x) z) p : Fin 3 → V) := by
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  rw [hcons]
  have hV : ∀ w y : V, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => x) z) p) w) y)
      ∘ shiftVMap = Form.snoc (fun _ => w) x := by
    intro w y
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hK : ∀ w y : V, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => x) z) p) w) y)
      ∘ tailKMap = Form.snoc (Form.snoc (fun _ => z) x) y := by
    intro w y
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hM : ∀ w y : V, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => x) z) p) w) y)
      ∘ tailMMap = Form.snoc (Form.snoc (fun _ => w) p) y := by
    intro w y
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [tailRelF, Form.realize_ex, Form.realize_and, Form.realize_relabel, hV, hK, hM,
    realize_vsuccEqF, realize_kpairEqF, realize_kpairMemF]

theorem tailF_fun {A p : V} (hp : p ∈ˢ pathSetF A) :
    ∀ x, x ∈ˢ (omega : V) → ∃ z, Form.Realize Mem (Form.cons2 x z (fun _ => p)) tailRelF ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' (fun _ => p)) tailRelF → z' = z := by
  intro x hx
  obtain ⟨y, hy, huniq⟩ := (mem_pathSetF.mp hp).2 (vsucc x) (vsucc_mem_omega hx)
  refine ⟨kpair x y, realize_tailRelF.mpr ⟨vsucc x, y, rfl, rfl, hy⟩, fun z' hz => ?_⟩
  obtain ⟨w, y', hw, hz', hmem⟩ := realize_tailRelF.mp hz
  rw [hz', huniq y' (hw ▸ hmem)]

/-- The tail of a path: `tailF p = {⟨x, y⟩ | x ∈ˢ ω, ⟨vsucc x, y⟩ ∈ˢ p}`. -/
noncomputable def tailF {A : V} (p : V) (hp : p ∈ˢ pathSetF A) : V :=
  imageF tailRelF (fun _ => p) (omega : V) (tailF_fun hp)

theorem mem_tailF {A p z : V} (hp : p ∈ˢ pathSetF A) :
    z ∈ˢ tailF p hp ↔
      ∃ x, x ∈ˢ (omega : V) ∧ ∃ w y, w = vsucc x ∧ z = kpair x y ∧ kpair w y ∈ˢ p := by
  simp only [tailF, mem_imageF (tailF_fun hp), realize_tailRelF]

theorem mem_tailF_iff {A p : V} (hp : p ∈ˢ pathSetF A) {x y : V} (hx : x ∈ˢ (omega : V)) :
    kpair x y ∈ˢ tailF p hp ↔ kpair (vsucc x) y ∈ˢ p := by
  constructor
  · intro h
    obtain ⟨x', hx', w, y', hw, h', hwy'⟩ := (mem_tailF hp).mp h
    obtain ⟨h1, rfl⟩ := kpair_inj h'
    rw [h1, ← hw]
    exact hwy'
  · intro h
    exact (mem_tailF hp).mpr ⟨x, hx, vsucc x, y, rfl, rfl, h⟩

theorem tailF_mem_pathSetF {A p : V} (hp : p ∈ˢ pathSetF A) : tailF p hp ∈ˢ pathSetF A := by
  rw [mem_pathSetF]
  constructor
  · intro z hz
    obtain ⟨x, hx, w, y, hw, rfl, hwy⟩ := (mem_tailF hp).mp hz
    obtain ⟨x₀, hx₀, y₀, hy₀, hwy₀⟩ :=
      mem_sigmaPairsAppF.mp ((mem_pathSetF.mp hp).1 (kpair w y) hwy)
    obtain ⟨-, rfl⟩ := kpair_inj hwy₀
    exact mem_sigmaPairsAppF.mpr ⟨x, hx, y, by
      rw [app_pathCodomF hx, ← app_pathCodomF hx₀]; exact hy₀, rfl⟩
  · intro k hk
    obtain ⟨y₀, hy₀, huniq⟩ := (mem_pathSetF.mp hp).2 (vsucc k) (vsucc_mem_omega hk)
    refine ⟨y₀, (mem_tailF hp).mpr ⟨k, hk, vsucc k, y₀, rfl, rfl, hy₀⟩, fun y hy => ?_⟩
    obtain ⟨x, hx, w, y', hw, h', hwy'⟩ := (mem_tailF hp).mp hy
    obtain ⟨h1, h2⟩ := kpair_inj h'
    rw [h2]
    exact huniq y' (by rw [h1, ← hw]; exact hwy')

theorem app_tailF {A p : V} (hp : p ∈ˢ pathSetF A) {x : V} (hx : x ∈ˢ (omega : V)) :
    app (tailF p hp) x = app p (vsucc x) := by
  obtain ⟨y₀, hy₀, huniq⟩ := (mem_pathSetF.mp hp).2 (vsucc x) (vsucc_mem_omega hx)
  have happ : app p (vsucc x) = y₀ := app_eq_of_unique (pathSetF_ne_pt hp) hy₀ huniq
  rw [happ]
  refine app_eq_of_unique (pathSetF_ne_pt (tailF_mem_pathSetF hp))
    ((mem_tailF_iff hp hx).mpr hy₀) (fun y hy => huniq y ((mem_tailF_iff hp hx).mp hy))

/-- Inversion: the tail of a cons is the original path. -/
theorem tailF_consF {A a p : V} (ha : a ∈ˢ A) (hp : p ∈ˢ pathSetF A) :
    tailF (consF a p hp) (consF_mem_pathSetF ha hp) = p := by
  have hcm := consF_mem_pathSetF ha hp
  refine eq_of_mem_piSetAppNF_app_eq (tailF_mem_pathSetF hcm) hp (fun x hx => ?_)
  rw [app_tailF hcm hx, app_consF_vsucc hp hx]

end ConLeche.SetTheory.Tower
