module

public import ConLeche.SetTheory.Derive.Graphs
public import ConLeche.SetTheory.Derive.Omega

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

/-- Variable map `Fin 4 ↦ Fin 5`, `0 ↦ 3`, `1 ↦ 4`, `2 ↦ 1`, `3 ↦ 2`
(reads `appEqF`'s `(pt, v, g, u)` out of `(w, g, u, pt, v)`). -/
def appMemEqMap : Fin 4 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨4, by omega⟩
  | 2 => ⟨1, by omega⟩
  | _ => ⟨2, by omega⟩

/-- `w ∈ˢ app g u` (variables `0 ↦ w`, `1 ↦ g`, `2 ↦ u`, `3 ↦ pt`):
`∃ v, v = app g u ∧ w ∈ˢ v`. -/
def appMemF : Form 4 :=
  .ex (.and (Form.relabel appMemEqMap appEqF) (.mem ⟨0, by omega⟩ ⟨4, by omega⟩))

theorem realize_appMemF {w g u : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => w) g) u) (pt : V)) appMemF ↔
      w ∈ˢ app g u := by
  have hM : ∀ v : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => w) g) u) (pt : V)) v) ∘ appMemEqMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ => (pt : V)) v) g) u := by
    intro v
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [appMemF, Form.realize_ex, Form.realize_and, Form.realize_relabel, hM,
    realize_appEqF, Form.realize_mem, Form.snoc_mk]
  simp

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

/-- The body of an attempt at `n`, with the attempt `F` free
(variables `0 → e`, `1 → z`, `2 → s`, `3 → pt`, `4 → n`,
`5 → F`; then `6 → c` / `6 → m`, `7 → u`, `8 → v`,
`9 → ee` / `w`). -/
def attemptBodyF : Form 6 :=
  .and (Form.relabel attFMap funcF)
    (.and (Form.relabel attDMap domVSuccF)
      (.and attemptBaseF attemptStepF))

/-- An *attempt* at `n`: a single-valued pair relation `F` with domain
`vsucc n`, base pair `kpair e z`, and step values along
`app (app s m) u`.  Variables `0 → e`, `1 → z`, `2 → s`, `3 → pt`,
`4 → n`; bound `5 → F`. -/
def attemptF : Form 5 := .ex attemptBodyF

/-- The `Prop`-level reading of `attemptBodyF`, flattened, with base
parameter `e`. -/
def IsAttemptE (e z s n f : V) : Prop :=
  (∀ p, p ∈ˢ f → (∃ a b, p = kpair a b) ∧
      ∀ a b b', kpair a b ∈ˢ f → kpair a b' ∈ˢ f → b = b') ∧
    (∀ x, (x ∈ˢ n ∨ x = n) ↔ ∃ y, kpair x y ∈ˢ f) ∧
    (kpair e z ∈ˢ f) ∧
    (∀ m, m ∈ˢ n → ∀ u, kpair m u ∈ˢ f →
      ∃ v, kpair (vsucc m) v ∈ˢ f ∧ v = app (app s m) u)

/-- `f` is an attempt at `n` for base value `z` and step `s`: the
`Prop`-level reading of `attemptF` (with `e = empty`), flattened. -/
def IsAttempt (z s n f : V) : Prop := IsAttemptE (empty : V) z s n f


theorem realize_attemptBodyF {e z s n f : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f)
          attemptBodyF ↔
      IsAttemptE e z s n f := by
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
  simp only [IsAttemptE, attemptBodyF, attemptBaseF, attemptStepF, attemptStepV, attemptStepW,
    Form.realize_ex, Form.realize_and, Form.realize_all, Form.realize_imp,
    Form.realize_mem, Form.realize_relabel, hF, hD, hBK, hBM, hSM, hSV, hSK, hSW1, hSW2,
    realize_funcF, realize_domVSuccF, realize_kpairEqF, realize_kpairMemF,
    realize_vsuccEqF, realize_appEqF, Form.snoc_mk]
  simp

/-! ## Ordinal helpers -/

/-- Transitivity as a formula (bound variable `0 → x`). -/
def transF : Form 1 :=
  .all (.imp (.mem ⟨1, by omega⟩ ⟨0, by omega⟩)
    (.all (.imp (.mem ⟨2, by omega⟩ ⟨1, by omega⟩)
      (.mem ⟨2, by omega⟩ ⟨0, by omega⟩))))

theorem realize_transF {x : V} :
    Form.Realize Mem (fun _ => x) transF ↔
      ∀ y, y ∈ˢ x → ∀ z, z ∈ˢ y → z ∈ˢ x := by
  simp only [transF, Form.realize_all, Form.realize_imp, Form.realize_mem, Form.snoc_mk]
  simp

theorem omega_member_transitive {n : V} (hn : n ∈ˢ (omega : V)) :
    ∀ y, y ∈ˢ n → ∀ z, z ∈ˢ y → z ∈ˢ n := by
  have h := omega_induction (p := Form.nil (V := V)) (φ := transF)
    (by
      rw [Form.snoc_nil, realize_transF]
      intro y hy
      exact absurd hy (not_mem_empty y))
    (fun x _ hx => by
      rw [Form.snoc_nil, realize_transF]
      intro y hy z hz
      rcases (mem_vsucc (n := x)).mp hy with hy | hyx
      · exact (mem_vsucc (n := x)).mpr (Or.inl (realize_transF.mp hx y hy z hz))
      · rw [hyx] at hz
        exact (mem_vsucc (n := x)).mpr (Or.inl hz))
    hn
  rw [Form.snoc_nil] at h
  exact realize_transF.mp h

theorem vsucc_ne (n : V) : vsucc n ≠ n := by
  intro h
  have h2 : n ∈ˢ vsucc n := (mem_vsucc (z := n) (n := n)).mpr (Or.inr rfl)
  rw [h] at h2
  exact not_mem_self n h2

theorem vsucc_not_mem_of_mem_omega {n : V} (hn : n ∈ˢ (omega : V)) :
    ¬ vsucc n ∈ˢ n := by
  intro h
  exact not_mem_self n
    (omega_member_transitive hn (vsucc n) h n ((mem_vsucc (z := n) (n := n)).mpr (Or.inr rfl)))


/-! ## Ordinal helpers on `ω` (definable inductions) -/

/-- `x = e ∨ e ∈ˢ x` (variables `0 → e`, bound `1 → x`). -/
def hasEmptyF : Form 2 :=
  .or (.equal ⟨1, by omega⟩ ⟨0, by omega⟩)
    (.mem ⟨0, by omega⟩ ⟨1, by omega⟩)

theorem realize_hasEmptyF {e x : V} :
    Form.Realize Mem (Form.snoc (fun _ => e) x) hasEmptyF ↔ (x = e ∨ e ∈ˢ x) := by
  simp only [hasEmptyF, Form.realize_or, Form.realize_equal, Form.realize_mem, Form.snoc_mk]
  simp

/-- Every member of `ω` is `∅` or contains it. -/
theorem mem_omega_eq_empty_or {n : V} (hn : n ∈ˢ (omega : V)) :
    n = (empty : V) ∨ (empty : V) ∈ˢ n := by
  have h := omega_induction (p := fun _ => (empty : V)) (φ := hasEmptyF)
    (by rw [realize_hasEmptyF]; exact Or.inl rfl)
    (fun x _ hx => by
      rw [realize_hasEmptyF] at hx
      rw [realize_hasEmptyF]
      rcases hx with h | h
      · exact Or.inr ((mem_vsucc (z := (empty : V)) (n := x)).mpr (Or.inr h.symm))
      · exact Or.inr ((mem_vsucc (z := (empty : V)) (n := x)).mpr (Or.inl h)))
    hn
  exact realize_hasEmptyF.mp h

/-- `∅ ∈ˢ vsucc n` for `n ∈ˢ ω`. -/
theorem empty_mem_vsucc_of_mem_omega {n : V} (hn : n ∈ˢ (omega : V)) :
    (empty : V) ∈ˢ vsucc n :=
  (mem_vsucc (z := (empty : V)) (n := n)).mpr
    (Or.elim (mem_omega_eq_empty_or hn) (fun h => Or.inr h.symm) (fun h => Or.inl h))

/-- Variable map `Fin 2 → Fin 3`, `0 → 2`, `1 → 1`
(reads `(e, m)` as `vsuccEqF`'s `(e, m)` out of `(n, m, e)`). -/
def vleqMap : Fin 2 → Fin 3 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | _ => ⟨1, by omega⟩

/-- `∀ m ∈ˢ n, ∃ e, e = vsucc m ∧ (e ∈ˢ n ∨ e = n)`
(bound `0 → n`). -/
def vsuccLeF : Form 1 :=
  .all (.imp (.mem ⟨1, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (Form.relabel vleqMap vsuccEqF)
      (.or (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
        (.equal ⟨2, by omega⟩ ⟨0, by omega⟩)))))

theorem realize_vsuccLeF {n : V} :
    Form.Realize Mem (fun _ => n) vsuccLeF ↔
      ∀ m, m ∈ˢ n → ∃ e, e = vsucc m ∧ (e ∈ˢ n ∨ e = n) := by
  have hV : ∀ m e : V,
      (Form.snoc (Form.snoc (fun _ => n) m) e) ∘ vleqMap = Form.snoc (fun _ => e) m := by
    intro m e
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [vsuccLeF, Form.realize_all, Form.realize_imp, Form.realize_mem,
    Form.realize_ex, Form.realize_and, Form.realize_relabel, hV, realize_vsuccEqF,
    Form.realize_or, Form.realize_equal, Form.snoc_mk]
  simp

/-- For `n ∈ˢ ω`, `m ∈ˢ n` implies `vsucc m ∈ˢ vsucc n`. -/
theorem vsucc_mem_vsucc_of_mem_omega {m n : V} (hn : n ∈ˢ (omega : V))
    (hm : m ∈ˢ n) : vsucc m ∈ˢ vsucc n := by
  have h := omega_induction (p := Form.nil (V := V)) (φ := vsuccLeF)
    (by
      rw [Form.snoc_nil, realize_vsuccLeF]
      intro m hm
      exact absurd hm (not_mem_empty m))
    (fun x _ hx => by
      rw [Form.snoc_nil, realize_vsuccLeF] at hx
      rw [Form.snoc_nil, realize_vsuccLeF]
      intro m hm
      rcases (mem_vsucc (n := x)).mp hm with hm | hmx
      · obtain ⟨e, he, h⟩ := hx m hm
        exact ⟨e, he, Or.inl ((mem_vsucc (z := e) (n := x)).mpr h)⟩
      · rw [hmx]
        exact ⟨vsucc x, rfl, Or.inr rfl⟩)
    hn
  rw [Form.snoc_nil] at h
  obtain ⟨e, he, h⟩ := realize_vsuccLeF.mp h m hm
  rw [← he]
  exact (mem_vsucc (z := e) (n := n)).mpr h

/-- `m ≤ n` for `m, n ∈ˢ ω`, as `m ∈ˢ n ∨ m = n` (variables
`0 ↦ n`, `1 ↦ m`). -/
def vleqF : Form 2 :=
  .or (.mem ⟨1, by omega⟩ ⟨0, by omega⟩) (.equal ⟨1, by omega⟩ ⟨0, by omega⟩)

@[simp] theorem realize_vleqF {m n : V} :
    Form.Realize Mem (Form.cons2 n m Form.nil) vleqF ↔ m ∈ˢ n ∨ m = n := by
  simp [vleqF, Form.cons2]

/-- `∀ m ∈ˢ w, n ∈ˢ m ∨ n = m ∨ m ∈ˢ n` (variables `0 → w`,
bound `1 → n`, `2 → m`). -/
def triF : Form 2 :=
  .all (.imp (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
    (.or (.mem ⟨1, by omega⟩ ⟨2, by omega⟩)
      (.or (.equal ⟨1, by omega⟩ ⟨2, by omega⟩)
        (.mem ⟨2, by omega⟩ ⟨1, by omega⟩))))

theorem realize_triF {w n : V} :
    Form.Realize Mem (Form.snoc (fun _ => w) n) triF ↔
      ∀ m, m ∈ˢ w → (n ∈ˢ m ∨ n = m ∨ m ∈ˢ n) := by
  simp only [triF, Form.realize_all, Form.realize_imp, Form.realize_mem,
    Form.realize_or, Form.realize_equal, Form.snoc_mk]
  simp

/-- Trichotomy for members of `ω`. -/
theorem omega_trichotomy {n m : V} (hn : n ∈ˢ (omega : V))
    (hm : m ∈ˢ (omega : V)) : n ∈ˢ m ∨ n = m ∨ m ∈ˢ n := by
  have h := omega_induction (p := fun _ => (omega : V)) (φ := triF)
    (by
      rw [realize_triF]
      intro m hm
      rcases mem_omega_eq_empty_or hm with h | h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h)
    (fun x hx hIH => by
      rw [realize_triF] at hIH
      rw [realize_triF]
      intro m hm
      rcases hIH m hm with h | h | h
      · have hv := vsucc_mem_vsucc_of_mem_omega hm h
        rcases (mem_vsucc (z := vsucc x) (n := m)).mp hv with hv | hv
        · exact Or.inl hv
        · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr (by rw [← h]; exact self_mem_vsucc x))
      · exact Or.inr (Or.inr ((mem_vsucc (z := m) (n := x)).mpr (Or.inl h))))
    hn
  exact realize_triF.mp h m hm

/-! ## Attempts, existence -/

theorem realize_attemptF' {z s n : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => (empty : V)) z) s) pt) n) attemptF ↔
      ∃ f, IsAttempt z s n f := by
  rw [attemptF, Form.realize_ex]
  exact ⟨fun ⟨f, h⟩ => ⟨f, realize_attemptBodyF.mp h⟩,
    fun ⟨f, h⟩ => ⟨f, realize_attemptBodyF.mpr h⟩⟩

theorem attempt_empty (z s : V) :
    IsAttempt z s (empty : V) (sing (kpair (empty : V) z)) := by
  refine ⟨?_, ?_, mem_sing.mpr rfl, ?_⟩
  · intro p hp
    rw [mem_sing] at hp
    subst hp
    refine ⟨⟨empty, z, rfl⟩, ?_⟩
    intro a b b' h1 h2
    rw [mem_sing] at h1 h2
    obtain ⟨rfl, rfl⟩ := kpair_inj h1
    obtain ⟨-, rfl⟩ := kpair_inj h2
    rfl
  · intro x
    constructor
    · rintro (hx | rfl)
      · exact absurd hx (not_mem_empty x)
      · exact ⟨z, mem_sing.mpr rfl⟩
    · rintro ⟨y, hy⟩
      rw [mem_sing] at hy
      obtain ⟨rfl, -⟩ := kpair_inj hy
      exact Or.inr rfl
  · intro m hm
    exact absurd hm (not_mem_empty m)

/-- Extend an attempt at `n` (with `n ∈ˢ ω`) to an attempt at
`vsucc n`, by adjoining the step pair. -/
theorem attempt_vsucc {z s n f : V} (hn : n ∈ˢ (omega : V)) (hf : IsAttempt z s n f) :
    IsAttempt z s (vsucc n)
      (binUnion f (sing (kpair (vsucc n) (app (app s n) (app f n))))) := by
  obtain ⟨hfunc, hdom, hbase, hstep⟩ := hf
  have hvnot : ¬ vsucc n ∈ˢ n := vsucc_not_mem_of_mem_omega hn
  have hvne : vsucc n ≠ n := vsucc_ne n
  have hfne : f ≠ (pt : V) := by
    intro h
    exact ptTag_ne_kpair (empty : V) z ((mem_pt.mp (h ▸ hbase)).symm)
  have huniq : ∀ a b b',
      kpair a b ∈ˢ binUnion f (sing (kpair (vsucc n) (app (app s n) (app f n)))) →
      kpair a b' ∈ˢ binUnion f (sing (kpair (vsucc n) (app (app s n) (app f n)))) →
      b = b' := by
    intro a b b' h1 h2
    rw [mem_binUnion] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact (hfunc (kpair a b) h1).2 a b b' h1 h2
    · rw [mem_sing] at h2
      obtain ⟨rfl, rfl⟩ := kpair_inj h2
      rcases (hdom (vsucc n)).mpr ⟨b, h1⟩ with h | h
      · exact absurd h hvnot
      · exact absurd h hvne
    · rw [mem_sing] at h1
      obtain ⟨rfl, rfl⟩ := kpair_inj h1
      rcases (hdom (vsucc n)).mpr ⟨b', h2⟩ with h | h
      · exact absurd h hvnot
      · exact absurd h hvne
    · rw [mem_sing] at h1 h2
      obtain ⟨-, rfl⟩ := kpair_inj h1
      obtain ⟨-, rfl⟩ := kpair_inj h2
      rfl
  refine ⟨?_, ?_, mem_binUnion.mpr (Or.inl hbase), ?_⟩
  · intro p hp
    rw [mem_binUnion] at hp
    rcases hp with hp | hp
    · exact ⟨(hfunc p hp).1, huniq⟩
    · rw [mem_sing] at hp
      subst hp
      exact ⟨⟨vsucc n, app (app s n) (app f n), rfl⟩, huniq⟩
  · intro x
    rw [mem_vsucc (n := n)]
    constructor
    · rintro ((hx | hxn) | hxv)
      · obtain ⟨y, hy⟩ := (hdom x).mp (Or.inl hx)
        exact ⟨y, mem_binUnion.mpr (Or.inl hy)⟩
      · obtain ⟨y, hy⟩ := (hdom x).mp (Or.inr hxn)
        exact ⟨y, mem_binUnion.mpr (Or.inl hy)⟩
      · rw [hxv]
        exact ⟨app (app s n) (app f n), mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl))⟩
    · rintro ⟨y, hy⟩
      rw [mem_binUnion] at hy
      rcases hy with hy | hy
      · exact Or.inl ((hdom x).mpr ⟨y, hy⟩)
      · rw [mem_sing] at hy
        obtain ⟨hxv, -⟩ := kpair_inj hy
        rw [hxv]
        exact Or.inr rfl
  · intro m hm u hu
    rw [mem_vsucc (n := n)] at hm
    rw [mem_binUnion] at hu
    rcases hm with hm | hmn
    · rcases hu with hu | hu
      · obtain ⟨v, hkv, hv⟩ := hstep m hm u hu
        exact ⟨v, mem_binUnion.mpr (Or.inl hkv), hv⟩
      · rw [mem_sing] at hu
        obtain ⟨hmv, -⟩ := kpair_inj hu
        rw [hmv] at hm
        exact absurd hm hvnot
    · rw [hmn] at hu ⊢
      rcases hu with hu | hu
      · have hu' : app f n = u :=
          app_eq_of_unique hfne hu (fun y hy => (hfunc (kpair n u) hu).2 n y u hy hu)
        exact ⟨app (app s n) (app f n), mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl)), by rw [hu']⟩
      · rw [mem_sing] at hu
        obtain ⟨hnv, -⟩ := kpair_inj hu
        exact absurd hnv hvne.symm

/-- **Existence of attempts**: for every `n ∈ˢ ω` there is an
attempt at `n`, by definable induction on `ω`. -/
theorem exists_attempt (z s : V) {n : V} (hn : n ∈ˢ (omega : V)) :
    ∃ f, IsAttempt z s n f := by
  have hnil : Form.snoc (Form.nil (V := V)) (empty : V) = (fun _ => (empty : V)) :=
    Form.snoc_nil _
  have h := omega_induction
    (p := Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.nil (V := V)) (empty : V)) z) s) pt)
    (φ := attemptF)
    (by rw [hnil, realize_attemptF']; exact ⟨_, attempt_empty z s⟩)
    (fun x hx hf => by
      rw [hnil, realize_attemptF'] at hf
      obtain ⟨f, hf⟩ := hf
      rw [hnil, realize_attemptF']
      exact ⟨binUnion f (sing (kpair (vsucc x) (app (app s x) (app f x)))),
        attempt_vsucc hx hf⟩)
    hn
  rw [hnil] at h
  exact realize_attemptF'.mp h


/-! ## Restriction of attempts and uniqueness -/

/-- Variable map `Fin 3 → Fin 4`, `0 → 1`, `1 → 2`, `2 → 3`
(reads `(p, x, y)` as `kpairEqF`'s `(z, x, y)` out of `(a, p, x, y)`). -/
def rkMap : Fin 3 → Fin 4 := fun i =>
  match i.val with
  | 0 => ⟨1, by omega⟩
  | 1 => ⟨2, by omega⟩
  | _ => ⟨3, by omega⟩

/-- `p = kpair x y ∧ x ∈ˢ a` (variables `0 → a`, `1 → p`;
bound `2 → x`, `3 → y`). -/
def restrictF : Form 2 :=
  .ex (.ex (.and (Form.relabel rkMap kpairEqF)
    (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)))

theorem realize_restrictF {a p : V} :
    Form.Realize Mem (Form.snoc (fun _ => a) p) restrictF ↔
      ∃ x y, p = kpair x y ∧ x ∈ˢ a := by
  have hR : ∀ x y : V,
      (Form.snoc (Form.snoc (Form.snoc (fun _ => a) p) x) y) ∘ rkMap =
        Form.snoc (Form.snoc (fun _ => p) x) y := by
    intro x y
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [restrictF, Form.realize_ex, Form.realize_and, Form.realize_relabel, hR,
    realize_kpairEqF, Form.realize_mem, Form.snoc_mk]
  simp

/-- Restricting an attempt at `vsucc n` to pairs with first component
in `vsucc n` gives an attempt at `n`. -/
theorem attempt_restrict {z s n f : V} (hn : n ∈ˢ (omega : V))
    (hf : IsAttempt z s (vsucc n) f) :
    IsAttempt z s n (sepF f restrictF (fun _ => vsucc n)) := by
  obtain ⟨hfunc, hdom, hbase, hstep⟩ := hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [mem_sepF] at hp
    exact ⟨(hfunc p hp.1).1, fun a b b' h1 h2 =>
      (hfunc (kpair a b) (mem_sepF.mp h1).1).2 a b b' (mem_sepF.mp h1).1 (mem_sepF.mp h2).1⟩
  · intro x
    constructor
    · rintro (hx | hxn)
      · obtain ⟨y, hy⟩ := (hdom x).mp (Or.inl ((mem_vsucc (z := x) (n := n)).mpr (Or.inl hx)))
        exact ⟨y, mem_sepF.mpr ⟨hy, realize_restrictF.mpr ⟨x, y, rfl, (mem_vsucc (z := x) (n := n)).mpr (Or.inl hx)⟩⟩⟩
      · rw [hxn]
        obtain ⟨y, hy⟩ := (hdom n).mp (Or.inl ((mem_vsucc (z := n) (n := n)).mpr (Or.inr rfl)))
        exact ⟨y, mem_sepF.mpr ⟨hy, realize_restrictF.mpr ⟨n, y, rfl, (mem_vsucc (z := n) (n := n)).mpr (Or.inr rfl)⟩⟩⟩
    · rintro ⟨y, hy⟩
      rw [mem_sepF] at hy
      obtain ⟨a, b, hab, ha⟩ := realize_restrictF.mp hy.2
      have hxa : x = a := (kpair_inj hab).1
      rw [← hxa] at ha
      exact (mem_vsucc (z := x) (n := n)).mp ha
  · exact mem_sepF.mpr ⟨hbase, realize_restrictF.mpr ⟨empty, z, rfl, empty_mem_vsucc_of_mem_omega hn⟩⟩
  · intro m hm u hu
    rw [mem_sepF] at hu
    obtain ⟨v, hkv, hv⟩ := hstep m ((mem_vsucc (z := m) (n := n)).mpr (Or.inl hm)) u hu.1
    exact ⟨v, mem_sepF.mpr ⟨hkv, realize_restrictF.mpr ⟨vsucc m, v, rfl, vsucc_mem_vsucc_of_mem_omega hn hm⟩⟩, hv⟩

/-- Variable map `Fin 6 → Fin 7`, shifts the attempt variable
`5 → 6` (leaves `0..4`). -/
def attGMap : Fin 6 → Fin 7 := fun i =>
  if h : i.val = 5 then ⟨6, by omega⟩ else ⟨i.val, by omega⟩

/-- Uniqueness of attempts at `n` (variables `0 → e`, `1 → z`,
`2 → s`, `3 → pt`, `4 → n`; bound `5 → f`, `6 → g`). -/
def uniqF : Form 5 :=
  .all (.all (.imp (Form.relabel Fin.castSucc attemptBodyF)
    (.imp (Form.relabel attGMap attemptBodyF)
      (.equal ⟨5, by omega⟩ ⟨6, by omega⟩))))

theorem realize_uniqF {e z s n : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) uniqF ↔
      ∀ f g, IsAttemptE e z s n f → IsAttemptE e z s n g → f = g := by
  have hF : ∀ f g : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) g)
          ∘ (Fin.castSucc : Fin 6 → Fin 7) =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f := by
    intro f g
    funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hG : ∀ f g : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f) g)
          ∘ attGMap =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) g := by
    intro f g
    funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [uniqF, Form.realize_all, Form.realize_imp, Form.realize_relabel, hF, hG,
    realize_attemptBodyF, Form.realize_equal, Form.snoc_mk]
  simp

/-- **Uniqueness of attempts**: two attempts at the same `n ∈ˢ ω`
coincide, by definable induction on `ω`. -/
theorem attempt_unique {z s n f g : V} (hn : n ∈ˢ (omega : V))
    (hf : IsAttempt z s n f) (hg : IsAttempt z s n g) : f = g := by
  have h := omega_induction
    (p := Form.snoc (Form.snoc (Form.snoc (fun _ => (empty : V)) z) s) pt)
    (φ := uniqF)
    (by
      rw [realize_uniqF]
      intro f g hf hg
      have hfeq : ∀ f : V, IsAttempt z s (empty : V) f →
          f = sing (kpair (empty : V) z) := by
        intro f hf
        obtain ⟨hfunc, hdom, hbase, -⟩ := hf
        apply SetTheory.ext
        intro p
        constructor
        · intro hp
          obtain ⟨⟨a, b, hab⟩, huniq⟩ := hfunc p hp
          rw [hab] at hp
          have ha : a = (empty : V) := by
            rcases (hdom a).mpr ⟨b, hp⟩ with h | h
            · exact absurd h (not_mem_empty a)
            · exact h
          rw [ha] at hp
          have hbz : b = z := huniq empty b z hp hbase
          rw [hab, ha, hbz]
          exact mem_sing.mpr rfl
        · intro hp
          rw [mem_sing] at hp
          rw [hp]
          exact hbase
      rw [hfeq f hf, hfeq g hg])
    (fun x hx hIH => by
      rw [realize_uniqF] at hIH
      rw [realize_uniqF]
      intro f g hf hg
      have hsub : ∀ f g : V, IsAttempt z s (vsucc x) f → IsAttempt z s (vsucc x) g →
          f ⊆ˢ g := by
        intro f g hf hg
        have hrestr : sepF f restrictF (fun _ => vsucc x) = sepF g restrictF (fun _ => vsucc x) :=
          hIH _ _ (attempt_restrict hx hf) (attempt_restrict hx hg)
        obtain ⟨hfunc, hdom, hbase, hstep⟩ := hf
        obtain ⟨hfunc', hdom', hbase', hstep'⟩ := hg
        have hfne : f ≠ pt := fun h => ptTag_ne_kpair (empty : V) z ((mem_pt.mp (h ▸ hbase)).symm)
        have hgne : g ≠ pt := fun h => ptTag_ne_kpair (empty : V) z ((mem_pt.mp (h ▸ hbase')).symm)
        intro p hp
        obtain ⟨⟨a, b, hab⟩, huniq⟩ := hfunc p hp
        rw [hab] at hp
        have ha : a ∈ˢ vsucc x ∨ a = vsucc x := (hdom a).mpr ⟨b, hp⟩
        rcases ha with ha | ha
        · have h1 : kpair a b ∈ˢ sepF f restrictF (fun _ => vsucc x) :=
            mem_sepF.mpr ⟨hp, realize_restrictF.mpr ⟨a, b, rfl, ha⟩⟩
          rw [hrestr] at h1
          rw [mem_sepF] at h1
          rw [hab]
          exact h1.1
        · have hx' : x ∈ˢ vsucc x := (mem_vsucc (z := x) (n := x)).mpr (Or.inr rfl)
          obtain ⟨u, hu⟩ := (hdom x).mp (Or.inl hx')
          have huapp : app f x = u :=
            app_eq_of_unique hfne hu (fun y hy => (hfunc (kpair x u) hu).2 x y u hy hu)
          obtain ⟨v, hkv, hv⟩ := hstep x hx' u hu
          have hvb : v = b := huniq (vsucc x) v b hkv (by rw [← ha]; exact hp)
          obtain ⟨u', hu'⟩ := (hdom' x).mp (Or.inl hx')
          have hu'app : app g x = u' :=
            app_eq_of_unique hgne hu' (fun y hy => (hfunc' (kpair x u') hu').2 x y u' hy hu')
          obtain ⟨v', hkv', hv'⟩ := hstep' x hx' u' hu'
          rw [← hu'app] at hu'
          have hxu : kpair x (app f x) ∈ˢ f := by rw [huapp]; exact hu
          have hxu' : kpair x (app f x) ∈ˢ g := by
            have h1 : kpair x (app f x) ∈ˢ sepF f restrictF (fun _ => vsucc x) :=
              mem_sepF.mpr ⟨hxu, realize_restrictF.mpr ⟨x, app f x, rfl, hx'⟩⟩
            rw [hrestr] at h1
            rw [mem_sepF] at h1
            exact h1.1
          have happ : app g x = app f x :=
            (hfunc' (kpair x (app f x)) hxu').2 x (app g x) (app f x) hu' hxu'
          have hv2 : v = app (app s x) (app f x) := hv.trans (by rw [huapp])
          have hv'2 : v' = app (app s x) (app f x) := hv'.trans (by rw [← hu'app, happ])
          have hbv' : b = v' := hvb.symm.trans (hv2.trans hv'2.symm)
          rw [hab, ha, hbv']
          exact hkv'
      apply SetTheory.ext
      intro p
      constructor
      · intro hp; exact hsub f g hf hg p hp
      · intro hp; exact hsub g f hg hf p hp)
    hn
  exact realize_uniqF.mp h f g hf hg

/-- **Existence and uniqueness of attempts** at every `n ∈ˢ ω`. -/
theorem exists_unique_attempt (z s : V) {n : V} (hn : n ∈ˢ (omega : V)) :
    ∃ f, IsAttempt z s n f ∧ ∀ g, IsAttempt z s n g → g = f := by
  obtain ⟨f, hf⟩ := exists_attempt z s hn
  exact ⟨f, hf, fun g hg => attempt_unique hn hg hf⟩

/-! ## The chain lemma: attempts at smaller members of ω are subsets -/

/-- Variable map `Fin 6 → Fin 8` reading the attempt at `(n, f)` out of
`(e, z, s, pt, m, n, f, g)` (`0→0`, `1→1`, `2→2`, `3→3`, `4→5`, `5→6`). -/
def attNMap : Fin 6 → Fin 8 := fun i =>
  match i.val with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨1, by omega⟩
  | 2 => ⟨2, by omega⟩
  | 3 => ⟨3, by omega⟩
  | 4 => ⟨5, by omega⟩
  | _ => ⟨6, by omega⟩

/-- Variable map `Fin 6 → Fin 8` reading the attempt at `(m, g)` out of
`(e, z, s, pt, m, n, f, g)` (`0→0`, `1→1`, `2→2`, `3→3`, `4→4`, `5→7`). -/
def attMMap : Fin 6 → Fin 8 := fun i =>
  match i.val with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨1, by omega⟩
  | 2 => ⟨2, by omega⟩
  | 3 => ⟨3, by omega⟩
  | 4 => ⟨4, by omega⟩
  | _ => ⟨7, by omega⟩

/-- Chain property (variables `0 → e`, `1 → z`, `2 → s`, `3 → pt`,
bound `4 → m`, then `5 → n`, `6 → f`, `7 → g`, `8 → p`):
if `n ∈ˢ m` and `f`, `g` are attempts at `n`, `m`, then `f ⊆ˢ g`. -/
def chainF : Form 5 :=
  .all (.all (.all (.imp
    (.and (.mem ⟨5, by omega⟩ ⟨4, by omega⟩)
      (.and (Form.relabel attNMap attemptBodyF)
        (Form.relabel attMMap attemptBodyF)))
    (.all (.imp (.mem ⟨8, by omega⟩ ⟨6, by omega⟩)
      (.mem ⟨8, by omega⟩ ⟨7, by omega⟩))))))

theorem realize_chainF {e z s m : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) m) chainF ↔
      ∀ n f g, n ∈ˢ m → IsAttemptE e z s n f → IsAttemptE e z s m g → f ⊆ˢ g := by
  have hN : ∀ n f g : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) m) n) f) g)
          ∘ attNMap =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f := by
    intro n f g
    funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hM : ∀ n f g : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) m) n) f) g)
          ∘ attMMap =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) m) g := by
    intro n f g
    funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [chainF, Form.realize_all, Form.realize_imp, Form.realize_and, Form.realize_mem,
    Form.realize_relabel, hN, hM, realize_attemptBodyF, Form.snoc_mk, SetTheory.Subset]
  simp

/-- **Chain lemma**: for `n ∈ˢ m` with `m ∈ˢ ω`, an attempt at `n` is
a subset of an attempt at `m`. -/
theorem attempt_subset {z s n m f g : V} (hm : m ∈ˢ (omega : V)) (hn : n ∈ˢ m)
    (hf : IsAttempt z s n f) (hg : IsAttempt z s m g) : f ⊆ˢ g := by
  have h := omega_induction
    (p := Form.snoc (Form.snoc (Form.snoc (fun _ => (empty : V)) z) s) pt)
    (φ := chainF)
    (by
      rw [realize_chainF]
      intro n f g hn _ _
      exact absurd hn (not_mem_empty n))
    (fun x hx hIH => by
      rw [realize_chainF] at hIH
      rw [realize_chainF]
      intro n f g hn hf hg
      rcases (mem_vsucc (z := n) (n := x)).mp hn with hn | hn
      · exact Subset.trans
          (hIH n f (sepF g restrictF (fun _ => vsucc x)) hn hf (attempt_restrict hx hg))
          sepF_subset
      · rw [hn] at hf
        rw [attempt_unique hx hf (attempt_restrict hx hg)]
        exact sepF_subset)
    hm
  exact realize_chainF.mp h n f g hn hf hg

/-! ## The definable recursion graph -/

/-- Variable map `Fin 6 → Fin 6` into the `cons2` convention of
`imageF`: attempt variables `(e, z, s, pt, n, f)` → `(2, 3, 4, 5, 0, 1)`,
so the index `n` sits at `0`, the attempt `f` at `1`, parameters at `2..5`. -/
def attXMap : Fin 6 → Fin 6 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨3, by omega⟩
  | 2 => ⟨4, by omega⟩
  | 3 => ⟨5, by omega⟩
  | 4 => ⟨0, by omega⟩
  | _ => ⟨1, by omega⟩

/-- The attempt relation `(n, f)` in the `cons2` convention of
`imageF` (parameters `e, z, s, pt`). -/
def attemptRelF : Form 6 := Form.relabel attXMap attemptBodyF

theorem realize_attemptRelF {e z s x y : V} :
    Form.Realize Mem
        (Form.cons2 x y (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt))
          attemptRelF ↔
      IsAttemptE e z s x y := by
  have hX : ∀ x y : V,
      (Form.cons2 x y (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt)) ∘ attXMap =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) x) y := by
    intro x y
    funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [attemptRelF, Form.realize_relabel, hX, realize_attemptBodyF]

/-- The functionality witness for `recGraph`: at each `n ∈ˢ ω` pick the
unique attempt at `n`. -/
theorem recGraphHFun (z s : V) :
    ∀ x, x ∈ˢ (omega : V) → ∃ y,
      Form.Realize Mem (Form.cons2 x y (Form.snoc (Form.snoc (Form.snoc (fun _ => (empty : V)) z) s) pt)) attemptRelF ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' (Form.snoc (Form.snoc (Form.snoc (fun _ => (empty : V)) z) s) pt)) attemptRelF → y' = y :=
  fun n hn => by
    obtain ⟨f, hf, huniq⟩ := exists_unique_attempt z s hn
    exact ⟨f, realize_attemptRelF.mpr hf, fun y hy => huniq y (realize_attemptRelF.mp hy)⟩

/-- The recursion graph: the union of all attempts at members of `ω`,
formed by the definable replacement scheme (`imageF` over `ω`). -/
noncomputable def recGraph (z s : V) : V :=
  sUnion (imageF attemptRelF
    (Form.snoc (Form.snoc (Form.snoc (fun _ => (empty : V)) z) s) pt) (omega : V) (recGraphHFun z s))

theorem mem_recGraph {z s p : V} :
    p ∈ˢ recGraph z s ↔ ∃ f, (∃ n, n ∈ˢ (omega : V) ∧ IsAttempt z s n f) ∧ p ∈ˢ f := by
  unfold recGraph
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨n, hn, hrel⟩ := (mem_imageF (recGraphHFun z s)).mp hy
    exact ⟨y, ⟨n, hn, realize_attemptRelF.mp hrel⟩, hp⟩
  · rintro ⟨f, ⟨n, hn, hf⟩, hp⟩
    exact ⟨f, (mem_imageF (recGraphHFun z s)).mpr ⟨n, hn, realize_attemptRelF.mpr hf⟩, hp⟩

theorem mem_recGraph_base {z s : V} : kpair (empty : V) z ∈ˢ recGraph z s := by
  obtain ⟨f, hf⟩ := exists_attempt z s empty_mem_omega
  exact mem_recGraph.mpr ⟨f, ⟨(empty : V), empty_mem_omega, hf⟩, hf.2.2.1⟩

theorem recGraph_ne_pt {z s : V} : recGraph z s ≠ pt := by
  intro h
  have h2 : kpair (empty : V) z ∈ˢ (pt : V) := by
    rw [← h]
    exact mem_recGraph_base
  exact ptTag_ne_kpair (empty : V) z ((mem_pt.mp h2).symm)

/-- The recursion graph is single-valued. -/
theorem recGraph_func {z s : V} :
    ∀ p, p ∈ˢ recGraph z s → (∃ a b, p = kpair a b) ∧
      ∀ a b b', kpair a b ∈ˢ recGraph z s → kpair a b' ∈ˢ recGraph z s → b = b' := by
  intro p hp
  obtain ⟨f, ⟨m, hm, hf⟩, hpf⟩ := mem_recGraph.mp hp
  have hfunc := hf.1
  refine ⟨(hfunc p hpf).1, fun a b b' h1 h2 => ?_⟩
  obtain ⟨f1, ⟨m1, hm1, hf1⟩, h1f⟩ := mem_recGraph.mp h1
  have hfunc1 := hf1.1
  obtain ⟨f2, ⟨m2, hm2, hf2⟩, h2f⟩ := mem_recGraph.mp h2
  have hfunc2 := hf2.1
  rcases omega_trichotomy hm1 hm2 with h | h | h
  · have hsub := attempt_subset hm2 h hf1 hf2
    exact (hfunc2 (kpair a b) (hsub (kpair a b) h1f)).2 a b b' (hsub (kpair a b) h1f) h2f
  · rw [h] at hf1
    rw [attempt_unique hm2 hf1 hf2] at h1f
    exact (hfunc2 (kpair a b) h1f).2 a b b' h1f h2f
  · have hsub := attempt_subset hm1 h hf2 hf1
    exact (hfunc1 (kpair a b) h1f).2 a b b' h1f (hsub (kpair a b') h2f)

/-- Every `n ∈ˢ ω` lies in the domain of the recursion graph. -/
theorem recGraph_dom {z s n : V} (hn : n ∈ˢ (omega : V)) :
    ∃ y, kpair n y ∈ˢ recGraph z s := by
  obtain ⟨f, hf⟩ := exists_attempt z s hn
  obtain ⟨y, hy⟩ := (hf.2.1 n).mp (Or.inr rfl)
  exact ⟨y, mem_recGraph.mpr ⟨f, ⟨n, hn, hf⟩, hy⟩⟩

/-! ## Definable primitive recursion on `ω` -/

/-- Set-theoretic primitive recursion on `ω` via the recursion graph
`recGraph` (definable: `imageF` over `ω`, no meta-level `repl`). -/
noncomputable def natrecF (z s n : V) : V := app (recGraph z s) n

theorem natrecF_empty (z s : V) : natrecF z s (empty : V) = z := by
  unfold natrecF
  exact app_eq_of_unique recGraph_ne_pt mem_recGraph_base
    (fun y hy =>
      ((recGraph_func (kpair (empty : V) y) hy).2 (empty : V) z y mem_recGraph_base hy).symm)

theorem natrecF_vsucc (z s : V) {n : V} (hn : n ∈ˢ (omega : V)) :
    natrecF z s (vsucc n) = app (app s n) (natrecF z s n) := by
  unfold natrecF
  have hvn : vsucc n ∈ˢ (omega : V) := vsucc_mem_omega hn
  obtain ⟨f, hf⟩ := exists_attempt z s hvn
  have hnx : n ∈ˢ vsucc n := (mem_vsucc (z := n) (n := n)).mpr (Or.inr rfl)
  obtain ⟨u, hu⟩ := (hf.2.1 n).mp (Or.inl hnx)
  obtain ⟨v, hkv, hv⟩ := hf.2.2.2 n hnx u hu
  have hGnu : kpair n u ∈ˢ recGraph z s :=
    mem_recGraph.mpr ⟨f, ⟨vsucc n, hvn, hf⟩, hu⟩
  have hGkv : kpair (vsucc n) v ∈ˢ recGraph z s :=
    mem_recGraph.mpr ⟨f, ⟨vsucc n, hvn, hf⟩, hkv⟩
  have huapp : app (recGraph z s) n = u :=
    app_eq_of_unique recGraph_ne_pt hGnu
      (fun y hy => ((recGraph_func (kpair n y) hy).2 n u y hGnu hy).symm)
  have hvapp : app (recGraph z s) (vsucc n) = v :=
    app_eq_of_unique recGraph_ne_pt hGkv
      (fun y hy => ((recGraph_func (kpair (vsucc n) y) hy).2 (vsucc n) v y hGkv hy).symm)
  rw [hvapp, hv, huapp]

/-- Unfolding lemma (proved before `natrecF` is sealed). -/
theorem natrecF_eq (z s n : V) : natrecF z s n = app (recGraph z s) n := rfl

theorem recGraph_app_empty (z s : V) : app (recGraph z s) (empty : V) = z :=
  natrecF_empty z s

theorem recGraph_app_vsucc (z s : V) {n : V} (hn : n ∈ˢ (omega : V)) :
    app (recGraph z s) (vsucc n) = app (app s n) (app (recGraph z s) n) :=
  natrecF_vsucc z s hn

attribute [irreducible] natrecF

end ConLeche.SetTheory
