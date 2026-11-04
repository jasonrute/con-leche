module

public import ConLeche.SetTheory.Derive.Graphs

@[expose] public section

/-!
# Definable recursion on `ω`

The set-theoretic recursion theorem, rebuilt from `replF` (definable
replacement) alone: an *attempt* at `n` is a single-valued relation `f`
all of whose members are pairs, with domain `vsucc n`, base value at
`empty` and step values along `app (app s m) (app f m)`.  Attempts are
encoded as first-order formulas (`funcF`, `domF`, ...), so the
existence and uniqueness inductions run through `omega_induction`.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- `v` is a Kuratowski pair (bound variable `0 → v`). -/
def pairF : Form 1 := .ex (.ex kpairEqF)

theorem realize_pairF {v : V} :
    Form.Realize Mem (fun _ => v) pairF ↔ ∃a b, v = kpair a b := by
  simp only [pairF, Form.realize_ex, realize_kpairEqF]

/-! ## Single-valued pair relations -/

/-- Variable map `Fin 1 → Fin 2`, `0 → 1` (reads `p` out of
`(f, p)`). -/
def funcMapP : Fin 1 → Fin 2 := fun _ => ⟨1, by omega⟩

/-- Variable map `Fin 3 → Fin 5`, `0 → 2`, `1 → 0`, `2 → 3`
(reads `(a, f, b)` as `kpairMemF`'s `(a, f, y)` out of `(f, p, a, b, b')`). -/
def funcMapB : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨0, by omega⟩
  | _ => ⟨3, by omega⟩

/-- Variable map `Fin 3 → Fin 5`, `0 → 2`, `1 → 0`, `2 → 4`
(as `funcMapB`, with `b'`). -/
def funcMapB' : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨0, by omega⟩
  | _ => ⟨4, by omega⟩

/-- `f` is a single-valued relation whose members are all pairs
(bound variable `0 → f`). -/
def funcF : Form 1 :=
  .all (.imp (.mem ⟨1, by omega⟩ ⟨0, by omega⟩)
    (.and (Form.relabel funcMapP pairF)
      (.all (.all (.all
        (.imp (.and (Form.relabel funcMapB kpairMemF)
              (Form.relabel funcMapB' kpairMemF))
          (.equal ⟨3, by omega⟩ ⟨4, by omega⟩)))))))

theorem realize_funcF {f : V} :
    Form.Realize Mem (fun _ => f) funcF ↔
      ∀ p, p ∈ˢ f → (∃a b, p = kpair a b) ∧
        ∀ a b b', kpair a b ∈ˢ f → kpair a b' ∈ˢ f → b = b' := by
  have hP : ∀ p : V,
      (Form.snoc (fun _ => f) p) ∘ funcMapP = (fun _ => p : Fin 1 → V) := by
    intro p
    funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  have hB : ∀ p a b b' : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => f) p) a) b) b') ∘ funcMapB =
        Form.snoc (Form.snoc (fun _ => a) f) b := by
    intro p a b b'
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hB' : ∀ p a b b' : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => f) p) a) b) b') ∘ funcMapB' =
        Form.snoc (Form.snoc (fun _ => a) f) b' := by
    intro p a b b'
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [funcF, Form.realize_all, Form.realize_imp, Form.realize_mem,
    Form.realize_and, Form.realize_relabel, hP, hB, hB', realize_pairF,
    realize_kpairMemF, Form.realize_equal, Form.snoc_mk]
  simp

/-! ## Domains -/

/-- Variable map `Fin 3 → Fin 5`, `0 → 4`, `1 → 2`, `2 → 3`
(reads `(c, x, y)` as `kpairEqF`'s `(z, x, y)` out of `(a, f, x, y, c)`). -/
def domMap : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨4, by omega⟩
  | 1 => ⟨2, by omega⟩
  | _ => ⟨3, by omega⟩

/-- `dom f = a` (variables `0 → a`, `1 → f`, bound variable `2 → x`). -/
def domF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
    (.ex (.ex (.and (Form.relabel domMap kpairEqF)
        (.mem ⟨4, by omega⟩ ⟨1, by omega⟩)))))

theorem realize_domF {a f : V} :
    Form.Realize Mem (Form.snoc (fun _ => a) f) domF ↔
      ∀ x, x ∈ˢ a ↔ ∃y, kpair x y ∈ˢ f := by
  have hC : ∀ x y c : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => a) f) x) y) c) ∘ domMap =
        Form.snoc (Form.snoc (fun _ => c) x) y := by
    intro x y c
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [domF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, Form.realize_relabel, hC,
    realize_kpairEqF, Form.snoc_mk]
  simp


/-! ## `vsucc`-equality and `app`-equality as formulas -/

/-- `e = vsucc m` (variables `0 → e`, `1 → m`), by extensionality
and `mem_vsucc`. -/
def vsuccEqF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
    (.or (.mem ⟨2, by omega⟩ ⟨1, by omega⟩)
      (.equal ⟨2, by omega⟩ ⟨1, by omega⟩)))

theorem realize_vsuccEqF {e m : V} :
    Form.Realize Mem (Form.snoc (fun _ => e) m) vsuccEqF ↔ e = vsucc m := by
  simp only [vsuccEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_or, Form.realize_equal, Form.snoc_mk]
  constructor
  · intro h
    apply SetTheory.ext
    intro w
    exact (h w).trans (mem_vsucc (n := m)).symm
  · intro h w
    rw [h]
    exact mem_vsucc (n := m)

/-- Variable map `Fin 3 → Fin 6`, `0 → 3`, `1 → 2`, `2 → 5`
(reads `(u, g, z)` as `kpairMemF`'s `(a, f, y)` out of `(pt, v, g, u, y, z)`). -/
def appMapKZ : Fin 3 → Fin 6 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨2, by omega⟩
  | _ => ⟨5, by omega⟩

/-- `v = app g u` (variables `0 → pt`, `1 → v`, `2 → g`, `3 → u`):
at the proof point both sides are the point; otherwise
`app g u = sUnion ⦃z | kpair u z ∈ˢ g⦄`, so by extensionality and
`mem_appSep`. -/
def appEqF : Form 4 :=
  .or (.and (.equal ⟨2, by omega⟩ ⟨0, by omega⟩)
      (.equal ⟨1, by omega⟩ ⟨0, by omega⟩))
    (.and (.not (.equal ⟨2, by omega⟩ ⟨0, by omega⟩))
      (.all (.iff (.mem ⟨4, by omega⟩ ⟨1, by omega⟩)
        (.ex (.and (Form.relabel appMapKZ kpairMemF)
          (.mem ⟨4, by omega⟩ ⟨5, by omega⟩))))))

theorem realize_appEqF {v g u : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => pt) v) g) u) appEqF ↔
      v = app g u := by
  have hKZ : ∀ y z : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => pt) v) g) u) y) z) ∘ appMapKZ =
        Form.snoc (Form.snoc (fun _ => u) g) z := by
    intro y z
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [appEqF, Form.realize_or, Form.realize_and, Form.realize_equal,
    Form.realize_not, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_relabel, hKZ, realize_kpairMemF, Form.snoc_mk]
  simp
  by_cases hg : g = pt
  · rw [hg, app_pt]
    simp
  · have happ : app g u = sUnion (sepF (sUnion (sUnion g)) kpairMemF (Form.snoc (fun _ => u) g)) := by
      unfold app
      exact ite_eq_right hg
    rw [happ]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, hall⟩)
      · exact absurd h hg
      · apply SetTheory.ext
        intro y
        rw [(hall y)]
        constructor
        · rintro ⟨z, hz, hy⟩
          exact mem_sUnion.mpr ⟨z, mem_appSep.mpr ⟨mem_sUnion.mpr ⟨upair u z,
            mem_sUnion.mpr ⟨kpair u z, hz, mem_upair_right _ _⟩, mem_upair_right u z⟩, hz⟩, hy⟩
        · intro hy
          obtain ⟨z, hz, hy⟩ := mem_sUnion.mp hy
          exact ⟨z, (mem_appSep.mp hz).2, hy⟩
    · intro h
      refine Or.inr ⟨hg, fun y => ?_⟩
      have hy : y ∈ˢ v ↔ ∃ z, kpair u z ∈ˢ g ∧ y ∈ˢ z := by
        constructor
        · intro hyv
          obtain ⟨z, hz, hy⟩ := mem_sUnion.mp (h ▸ hyv)
          exact ⟨z, (mem_appSep.mp hz).2, hy⟩
        · rintro ⟨z, hz, hy⟩
          exact h ▸ mem_sUnion.mpr ⟨z, mem_appSep.mpr ⟨mem_sUnion.mpr ⟨upair u z,
            mem_sUnion.mpr ⟨kpair u z, hz, mem_upair_right _ _⟩, mem_upair_right u z⟩, hz⟩, hy⟩
      exact hy

/-! ## Attempts at `ω`-recursion -/

/-- Variable map `Fin 3 → Fin 4`, `0 → 2`, `1 → 1`, `2 → 3`
(reads `(x, f, y)` as `kpairMemF`'s `(a, f, y)` out of `(n, f, x, y)`). -/
def domVSuccMap : Fin 3 → Fin 4 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨1, by omega⟩
  | _ => ⟨3, by omega⟩

/-- `dom f = vsucc n` (variables `0 → n`, `1 → f`, bound `2 → x`),
via `mem_vsucc`. -/
def domVSuccF : Form 2 :=
  .all (.iff (.or (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
      (.equal ⟨2, by omega⟩ ⟨0, by omega⟩))
    (.ex (Form.relabel domVSuccMap kpairMemF)))

theorem realize_domVSuccF {n f : V} :
    Form.Realize Mem (Form.snoc (fun _ => n) f) domVSuccF ↔
      ∀ x, (x ∈ˢ n ∨ x = n) ↔ ∃ y, kpair x y ∈ˢ f := by
  have hM : ∀ x y : V,
      (Form.snoc (Form.snoc (Form.snoc (fun _ => n) f) x) y) ∘ domVSuccMap =
        Form.snoc (Form.snoc (fun _ => x) f) y := by
    intro x y
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [domVSuccF, Form.realize_all, Form.realize_iff, Form.realize_or,
    Form.realize_mem, Form.realize_equal, Form.realize_ex, Form.realize_relabel,
    hM, realize_kpairMemF, Form.snoc_mk]
  simp

/-! ### The attempt formula -/

/-- Variable map `Fin 1 → Fin 6`, `0 → 5`
(reads `F` out of `(e, z, s, pt, n, F)`). -/
def attFMap : Fin 1 → Fin 6 := fun _ => ⟨5, by omega⟩

/-- Variable map `Fin 2 → Fin 6`, `0 → 4`, `1 → 5`
(reads `(n, F)` as `domVSuccF`'s `(n, f)`). -/
def attDMap : Fin 2 → Fin 6 := fun i =>
  match i.val with
  | 0 => ⟨4, by omega⟩
  | _ => ⟨5, by omega⟩

/-- Variable map `Fin 3 → Fin 7`, `0 → 6`, `1 → 0`, `2 → 1`
(reads `(c, e, z)` as `kpairEqF`'s `(z, x, y)` out of `(e, z, s, pt, n, F, c)`). -/
def baseKMap : Fin 3 → Fin 7 := fun i =>
  match i.val with
  | 0 => ⟨6, by omega⟩
  | 1 => ⟨0, by omega⟩
  | _ => ⟨1, by omega⟩

/-- Variable map `Fin 3 → Fin 7`, `0 → 0`, `1 → 5`, `2 → 1`
(reads `(e, F, z)` as `kpairMemF`'s `(a, f, y)`). -/
def baseMMap : Fin 3 → Fin 7 := fun i =>
  match i.val with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨5, by omega⟩
  | _ => ⟨1, by omega⟩

/-- Variable map `Fin 3 → Fin 8`, `0 → 6`, `1 → 5`, `2 → 7`
(reads `(m, F, u)` as `kpairMemF`'s `(a, f, y)`). -/
def stepMMap : Fin 3 → Fin 8 := fun i =>
  match i.val with
  | 0 => ⟨6, by omega⟩
  | 1 => ⟨5, by omega⟩
  | _ => ⟨7, by omega⟩

/-- Variable map `Fin 2 → Fin 10`, `0 → 9`, `1 → 6`
(reads `(ee, m)` as `vsuccEqF`'s `(e, m)`). -/
def stepVMap : Fin 2 → Fin 10 := fun i =>
  match i.val with
  | 0 => ⟨9, by omega⟩
  | _ => ⟨6, by omega⟩

/-- Variable map `Fin 3 → Fin 10`, `0 → 9`, `1 → 5`, `2 → 8`
(reads `(ee, F, v)` as `kpairMemF`'s `(a, f, y)`). -/
def stepKMap : Fin 3 → Fin 10 := fun i =>
  match i.val with
  | 0 => ⟨9, by omega⟩
  | 1 => ⟨5, by omega⟩
  | _ => ⟨8, by omega⟩

/-- Variable map `Fin 4 → Fin 11`, `0 → 3`, `1 → 9`, `2 → 2`, `3 → 6`
(reads `(pt, w, s, m)` as `appEqF`'s `(pt, v, g, u)`). -/
def stepWMap1 : Fin 4 → Fin 10 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨9, by omega⟩
  | 2 => ⟨2, by omega⟩
  | _ => ⟨6, by omega⟩

/-- Variable map `Fin 4 → Fin 11`, `0 → 3`, `1 → 8`, `2 → 9`, `3 → 7`
(reads `(pt, v, w, u)` as `appEqF`'s `(pt, v, g, u)`). -/
def stepWMap2 : Fin 4 → Fin 10 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨8, by omega⟩
  | 2 => ⟨9, by omega⟩
  | _ => ⟨7, by omega⟩

/-- Base clause of an attempt (at `F`, bound `6 → c`): some pair
`c = kpair e z` lies in `F`. -/
def attemptBaseF : Form 6 :=
  .ex (.and (Form.relabel baseKMap kpairEqF)
    (Form.relabel baseMMap kpairMemF))

/-- Successor clause, `vsucc`-part (bound `9 → ee`):
`ee = vsucc m ∧ kpair ee v ∈ˢ F`. -/
def attemptStepV : Form 10 :=
  .and (Form.relabel stepVMap vsuccEqF) (Form.relabel stepKMap kpairMemF)

/-- Successor clause, `app`-part (bound `9 → w`):
`w = app s m ∧ v = app w u`. -/
def attemptStepW : Form 10 :=
  .and (Form.relabel stepWMap1 appEqF) (Form.relabel stepWMap2 appEqF)

/-- Step clause of an attempt (at `F`, bound `6 → m`, `7 → u`,
`8 → v`): `m ∈ˢ n → kpair m u ∈ˢ F → ∃ v, ...`. -/
def attemptStepF : Form 6 :=
  .all (.imp (.mem ⟨6, by omega⟩ ⟨4, by omega⟩)
    (.all (.imp (Form.relabel stepMMap kpairMemF)
      (.ex (.and (.ex attemptStepV) (.ex attemptStepW))))))

/-- An *attempt* at `n`: a single-valued pair relation `F` with domain
`vsucc n`, base pair `kpair e z`, and step values along
`app (app s m) u`.  Variables `0 → e`, `1 → z`, `2 → s`, `3 → pt`,
`4 → n`; bound `5 → F`, then `6 → c` / `6 → m`, `7 → u`, `8 → v`,
`9 → ee` / `w`. -/
def attemptF : Form 5 :=
  .ex (.and (Form.relabel attFMap funcF)
    (.and (Form.relabel attDMap domVSuccF)
      (.and attemptBaseF attemptStepF)))

theorem realize_attemptF {e z s n : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) attemptF ↔
      ∃ f, (∀ p, p ∈ˢ f → (∃ a b, p = kpair a b) ∧
          ∀ a b b', kpair a b ∈ˢ f → kpair a b' ∈ˢ f → b = b') ∧
        (∀ x, (x ∈ˢ n ∨ x = n) ↔ ∃ y, kpair x y ∈ˢ f) ∧
        (∃ c, c = kpair e z ∧ kpair e z ∈ˢ f) ∧
        (∀ m, m ∈ˢ n → ∀ u, kpair m u ∈ˢ f →
          ∃ v, (∃ ee, ee = vsucc m ∧ kpair ee v ∈ˢ f) ∧
            (∃ w, w = app s m ∧ v = app w u)) := by
  have hF : ∀ f : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) ∘ attFMap = (fun _ => f : Fin 1 → V) := by
    intro f
    funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  have hD : ∀ f : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) ∘ attDMap = Form.snoc (fun _ => n) f := by
    intro f
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hBK : ∀ f c : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) c) ∘ baseKMap = Form.snoc (Form.snoc (fun _ => c) e) z := by
    intro f c
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hBM : ∀ f c : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) c) ∘ baseMMap = Form.snoc (Form.snoc (fun _ => e) f) z := by
    intro f c
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hSM : ∀ f m u : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) m) u) ∘ stepMMap = Form.snoc (Form.snoc (fun _ => m) f) u := by
    intro f m u
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hSV : ∀ f m u v ee : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) m) u) v) ee) ∘ stepVMap = Form.snoc (fun _ => ee) m := by
    intro f m u v ee
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hSK : ∀ f m u v ee : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) m) u) v) ee) ∘ stepKMap = Form.snoc (Form.snoc (fun _ => ee) f) v := by
    intro f m u v ee
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hSW1 : ∀ f m u v w : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) m) u) v) w) ∘ stepWMap1 =
        Form.snoc (Form.snoc (Form.snoc (fun _ => pt) w) s) m := by
    intro f m u v w
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hSW2 : ∀ f m u v w : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) m) u) v) w) ∘ stepWMap2 =
        Form.snoc (Form.snoc (Form.snoc (fun _ => pt) v) w) u := by
    intro f m u v w
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [attemptF, attemptBaseF, attemptStepF, attemptStepV, attemptStepW,
    Form.realize_ex, Form.realize_and, Form.realize_all, Form.realize_imp,
    Form.realize_mem, Form.realize_relabel, hF, hD, hBK, hBM, hSM, hSV, hSK, hSW1, hSW2,
    realize_funcF, realize_domVSuccF, realize_kpairEqF, realize_kpairMemF,
    realize_vsuccEqF, realize_appEqF, Form.snoc_mk]
  simp

end ConLeche.SetTheory
