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

/-! ## The image of `app g`, in the `imageF`/`sigmaPairsF` convention -/

/-- Variable map `Fin 4 → Fin 4`, `0 ↦ 3`, `1 ↦ 1`, `2 ↦ 2`, `3 ↦ 0`
(reads `appEqF`'s `(pt, v, g, u)` out of the `imageF` convention
`(x, v, g, pt)`). -/
def appRepMap : Fin 4 → Fin 4 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨1, by omega⟩
  | 2 => ⟨2, by omega⟩
  | _ => ⟨0, by omega⟩

/-- `v = app g x` in the `imageF` convention (variables `0 ↦ x`, `1 ↦ v`,
parameters `g`, `pt`). -/
def appEqRepF : Form 4 := Form.relabel appRepMap appEqF

theorem realize_appEqRepF {x v g : V} :
    Form.Realize Mem (Form.cons2 x v (Form.snoc (fun _ => g) (pt : V))) appEqRepF ↔
      v = app g x := by
  have hcomp : (Form.cons2 x v (Form.snoc (fun _ => g) (pt : V)) : Fin 4 → V) ∘ appRepMap =
      Form.snoc (Form.snoc (Form.snoc (fun _ => (pt : V)) v) g) x := by
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk3 with rfl | rfl | rfl | rfl <;> rfl
  simp only [appEqRepF, Form.realize_relabel, hcomp, realize_appEqF]

/-- The definable image under `app g`: `{app g x | x ∈ˢ A}`. -/
noncomputable def appImageF (g A : V) : V :=
  imageF appEqRepF (Form.snoc (fun _ => g) (pt : V)) A
    (fun x _ => ⟨app g x, realize_appEqRepF.mpr rfl, fun _ hy => realize_appEqRepF.mp hy⟩)

theorem mem_appImageF {g A z : V} :
    z ∈ˢ appImageF g A ↔ ∃ x, x ∈ˢ A ∧ z = app g x := by
  unfold appImageF
  rw [mem_imageF]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, realize_appEqRepF.mp h⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, realize_appEqRepF.mpr rfl⟩

/-- The meta-level `image (app g) A` is exactly the definable
`appImageF g A`. -/
theorem image_app_eq {g A : V} : image (app g) A = appImageF g A :=
  ext fun z => by rw [mem_image, mem_appImageF]

/-- Variable map `Fin 4 → Fin 4`, `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 0`, `3 ↦ 3`
(reads `appMemF`'s `(w, g, u, pt)` out of the `cons2` convention
`(x, y, g, pt)`). -/
def appMemRepMap : Fin 4 → Fin 4 := fun i =>
  match i.val with
  | 0 => ⟨1, by omega⟩
  | 1 => ⟨2, by omega⟩
  | 2 => ⟨0, by omega⟩
  | _ => ⟨3, by omega⟩

/-- `y ∈ˢ app g x` in the `cons2` convention (variables `0 ↦ x`, `1 ↦ y`,
parameters `g`, `pt`) — the fibre predicate for `app g`-families. -/
def appMemRepF : Form 4 := Form.relabel appMemRepMap appMemF

theorem realize_appMemRepF {x y g : V} :
    Form.Realize Mem (Form.cons2 x y (Form.snoc (fun _ => g) (pt : V))) appMemRepF ↔
      y ∈ˢ app g x := by
  have hcomp : (Form.cons2 x y (Form.snoc (fun _ => g) (pt : V)) : Fin 4 → V) ∘ appMemRepMap =
      Form.snoc (Form.snoc (Form.snoc (fun _ => y) g) x) (pt : V) := by
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk3 with rfl | rfl | rfl | rfl <;> rfl
  simp only [appMemRepF, Form.realize_relabel, hcomp, realize_appMemF]

/-- Application of a member graph is a member. -/
theorem _root_.ConLeche.IsUniverse.app_mem {U g x : V} (hU : IsUniverse (Mem (V := V)) U)
    (he : (empty : V) ∈ˢ U) (hg : g ∈ˢ U) : app g x ∈ˢ U := by
  unfold app
  split
  · exact hU.pt_mem he
  · exact hU.sUnion_mem (hU.sepF_mem (hU.sUnion_mem (hU.sUnion_mem hg)))

/-- Definable application-image closure (clause 6): the definable image
of a member under `app g` at a member graph is a member — the
first-order twin of `image_mem` at `app g`. -/
theorem _root_.ConLeche.IsUniverse.appImageF_mem {U g A : V} (hU : IsUniverse (Mem (V := V)) U)
    (he : (empty : V) ∈ˢ U) (hg : g ∈ˢ U) (hA : A ∈ˢ U) : appImageF g A ∈ˢ U := by
  unfold appImageF
  exact hU.imageF_mem hA fun x _ z hz => by
    rw [realize_appEqRepF.mp hz]
    exact hU.app_mem he hg

/-- Definable application-image closure (clause 6) at the value level:
the first-order twin of `image_mem` at `app g` when only the values
`app g x` are members, not `g` itself. -/
theorem _root_.ConLeche.IsUniverse.appImageF_val_mem {U g A : V}
    (hU : IsUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hval : ∀ x, x ∈ˢ A → app g x ∈ˢ U) : appImageF g A ∈ˢ U := by
  unfold appImageF
  exact hU.imageF_mem hA fun x hx z hz => by
    rw [realize_appEqRepF.mp hz]
    exact hval x hx

/-- Definable union-of-app-image closure (clause 6) at the value level:
the first-order twin of `famUnion_mem` at `F = app g` with member
values `app g x` — stated at the definable `appImageF` twin
(stage 86: no meta `image`). -/
theorem _root_.ConLeche.IsUniverse.sUnion_appImageF_val_mem {U g A : V}
    (hU : IsUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hval : ∀ x, x ∈ˢ A → app g x ∈ˢ U) : sUnion (appImageF g A) ∈ˢ U :=
  hU.sUnion_mem (hU.appImageF_val_mem hA hval)

/-- The definable function space with fibres `app S j` over `A`: the
first-order twin of `piSet A (fun j => app S j)`, available when `S`
is single-valued on `A`. -/
noncomputable def piSetApp (S A : V)
    (hfun : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ app S x ∧ ∀ y', y' ∈ˢ app S x → y' = y) : V :=
  piSetD appMemRepF (Form.snoc (fun _ => S) (pt : V)) A
    (fun x hx => by
      obtain ⟨y, hy, huniq⟩ := hfun x hx
      exact ⟨y, realize_appMemRepF.mpr hy, fun y' hy' => huniq y' (realize_appMemRepF.mp hy')⟩)

theorem piSetApp_eq_piSet {S A : V}
    (hfun : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ app S x ∧ ∀ y', y' ∈ˢ app S x → y' = y) :
    piSetApp S A hfun = piSet A (fun j => app S j) :=
  piSetD_eq_piSet (fun _ _ => realize_appMemRepF)

/-- Definable app-fibre function-space closure (clause 6): the
first-order twin of `piSet_mem` at an `app S`-family. -/
theorem _root_.ConLeche.IsUniverse.piSetApp_mem {U S A : V} (hU : IsUniverse (Mem (V := V)) U)
    (he : (empty : V) ∈ˢ U) (hS : S ∈ˢ U) (hA : A ∈ˢ U)
    (hfun : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ app S x ∧ ∀ y', y' ∈ˢ app S x → y' = y) :
    piSetApp S A hfun ∈ˢ U := by
  unfold piSetApp
  exact hU.piSetD_mem hA fun x hx y hy =>
    hU.kpair_mem he (hU.transitive hA hx)
      (hU.transitive (hU.app_mem he hS) (realize_appMemRepF.mp hy))

/-! ## The graph of `app g`, in the `graphF` convention -/

/-- The definable graph of `app g` over `A`: `{<x, app g x> : x ∈ˢ A}`
the first-order twin of `graph (fun x => app g x) A`. -/
noncomputable def graphAppF (g A : V) : V :=
  graphF appEqRepF (Form.snoc (fun _ => g) (pt : V)) A
    (fun x _ => ⟨app g x, realize_appEqRepF.mpr rfl, fun _ hy => realize_appEqRepF.mp hy⟩)

theorem mem_graphAppF {g A z : V} :
    z ∈ˢ graphAppF g A ↔ ∃ x, x ∈ˢ A ∧ z = kpair x (app g x) := by
  unfold graphAppF
  rw [mem_graphF]
  constructor
  · rintro ⟨x, hx, w, rfl, hw⟩
    exact ⟨x, hx, by rw [realize_appEqRepF.mp hw]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, app g x, rfl, realize_appEqRepF.mpr rfl⟩

/-- The meta-level `graph (fun x => app g x) A` is exactly the definable
`graphAppF g A`. -/
theorem graphAppF_eq {g A : V} : graphAppF g A = graph (fun x => app g x) A :=
  ext fun z => by
    rw [mem_graphAppF, mem_graph]

/-- Beta on the definable app-graph. -/
theorem app_graphAppF {g A a : V} (ha : a ∈ˢ A) : app (graphAppF g A) a = app g a := by
  rw [graphAppF_eq]; exact app_graph ha

/-- Definable graph-of-app closure (clause 6): the first-order twin of
`image_mem` at the `fun x => kpair x (app g x)` family. -/
theorem _root_.ConLeche.IsUniverse.graphAppF_mem {U g A : V} (hU : IsUniverse (Mem (V := V)) U)
    (he : (empty : V) ∈ˢ U) (hg : g ∈ˢ U) (hA : A ∈ˢ U) : graphAppF g A ∈ˢ U := by
  unfold graphAppF
  exact hU.graphF_mem hA fun x hx w hw => by
    rw [realize_appEqRepF.mp hw]
    exact hU.kpair_mem he (hU.transitive hA hx) (hU.app_mem he hg)

/-- Definable graph-of-app closure (clause 6) at the value level: the
first-order twin of `image_mem` at `fun x => kpair x (app g x)` when
only the values `app g x` are members, not `g` itself. -/
theorem _root_.ConLeche.IsUniverse.graphAppF_val_mem {U g A : V}
    (hU : IsUniverse (Mem (V := V)) U) (he : (empty : V) ∈ˢ U) (hA : A ∈ˢ U)
    (hval : ∀ x, x ∈ˢ A → app g x ∈ˢ U) : graphAppF g A ∈ˢ U := by
  unfold graphAppF
  exact hU.graphF_mem hA fun x hx w hw => by
    rw [realize_appEqRepF.mp hw]
    exact hU.kpair_mem he (hU.transitive hA hx) (hval x hx)

/-- A definable app-graph lies in any function space whose fibres contain
the applications: the first-order shape of `graph_mem_piSet` at an
`app g`-family. -/
theorem graphAppF_mem_piSet {g A : V} {B : V → V}
    (h : ∀ x, x ∈ˢ A → app g x ∈ˢ B x) : graphAppF g A ∈ˢ piSet A B := by
  rw [graphAppF_eq]
  exact graph_mem_piSet h

/-- Eta at the definable app-graph: a member of `piSet A B` is the
definable graph of its own application (the `graphAppF` twin of
`eq_graph_app_of_mem_piSet`). -/
theorem eq_graphAppF_of_mem_piSet {A f : V} {B : V → V} (hf : f ∈ˢ piSet A B) :
    graphAppF f A = f := by
  rw [graphAppF_eq]
  exact eq_graph_app_of_mem_piSet hf

/-! ## The raw app-pair product and the functionality-free app function space

`sigmaPairs A (fun j => app S j)` and `piSet A (fun j => app S j)` at an
arbitrary family graph `S` — not necessarily single-valued on `A`.  The
pair set is the union of the images `x ↦ kpairImage x (app S x)`, and
that outer map is a function of `x` outright, so both sets have
definable (`replF`-only) twins with NO `hfun` hypothesis. -/

/-- Variable map `Fin 3 → Fin 6` reading `kpairEqF'`'s `(x, z, a)` out of
`(x, y, S, pt, w, z)` as `(z, w, x)`, asserting `w = kpair x z`. -/
def sigAppKMap : Fin 3 → Fin 6 := fun i =>
  match i.val with
  | 0 => ⟨5, by omega⟩
  | 1 => ⟨4, by omega⟩
  | _ => ⟨0, by omega⟩

/-- Variable map `Fin 4 → Fin 6` reading `appMemF`'s `(w, g, u, pt)` out of
`(x, y, S, pt, w, z)` as `(z, S, x, pt)`, asserting `z ∈ˢ app S x`. -/
def sigAppMMap : Fin 4 → Fin 6 := fun i =>
  match i.val with
  | 0 => ⟨5, by omega⟩
  | 1 => ⟨2, by omega⟩
  | 2 => ⟨0, by omega⟩
  | _ => ⟨3, by omega⟩

/-- `y = kpairImage x (app S x)` in the `imageF` convention (variables
`0 ↦ x`, `1 ↦ y`, parameters `S`, `pt`): `∀ w, w ∈ˢ y ↔ ∃ z, w = kpair x z
∧ z ∈ˢ app S x`. -/
def sigAppRelF : Form 4 :=
  .all (.iff (.mem ⟨4, by omega⟩ ⟨1, by omega⟩)
    (.ex (.and (Form.relabel sigAppKMap kpairEqF') (Form.relabel sigAppMMap appMemF))))

theorem realize_sigAppRelF {x y S : V} :
    Form.Realize Mem (Form.cons2 x y (Form.snoc (fun _ => S) (pt : V))) sigAppRelF ↔
      ∀ w, w ∈ˢ y ↔ ∃ z, w = kpair x z ∧ z ∈ˢ app S x := by
  have hK : ∀ w z : V,
      (Form.snoc (Form.snoc (Form.cons2 x y (Form.snoc (fun _ => S) (pt : V))) w) z) ∘ sigAppKMap =
        Form.cons2 z w (fun _ => x) := by
    intro w z
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk2 with rfl | rfl | rfl <;> rfl
  have hM : ∀ w z : V,
      (Form.snoc (Form.snoc (Form.cons2 x y (Form.snoc (fun _ => S) (pt : V))) w) z) ∘ sigAppMMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ => z) S) x) (pt : V) := by
    intro w z
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [sigAppRelF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, Form.realize_relabel, hK, hM,
    realize_kpairEqF', realize_appMemF, Form.snoc_mk, Form.cons2]
  simp

theorem sigAppRelF_eq_kpairImage {x y S : V} :
    Form.Realize Mem (Form.cons2 x y (Form.snoc (fun _ => S) (pt : V))) sigAppRelF ↔
      y = kpairImage x (app S x) := by
  rw [realize_sigAppRelF]
  constructor
  · intro h
    refine SetTheory.ext fun w => ?_
    rw [h w, mem_kpairImage]
    constructor
    · rintro ⟨z, hw, hz⟩; exact ⟨z, hz, hw⟩
    · rintro ⟨z, hz, hw⟩; exact ⟨z, hw, hz⟩
  · intro h w
    rw [h, mem_kpairImage]
    constructor
    · rintro ⟨z, hz, hw⟩; exact ⟨z, hw, hz⟩
    · rintro ⟨z, hw, hz⟩; exact ⟨z, hz, hw⟩

/-- The definable raw app-pair product `{⟨x, y⟩ : x ∈ˢ A, y ∈ˢ app S x}`:
the first-order twin of `sigmaPairs A (fun j => app S j)`, needing no
single-valuedness of `S` (the outer map `x ↦ kpairImage x (app S x)` is
functional outright). -/
noncomputable def sigmaPairsAppF (S A : V) : V :=
  sUnion (imageF sigAppRelF (Form.snoc (fun _ => S) (pt : V)) A
    (fun x _ => ⟨kpairImage x (app S x), sigAppRelF_eq_kpairImage.mpr rfl,
      fun _ hy => sigAppRelF_eq_kpairImage.mp hy⟩))

theorem mem_sigmaPairsAppF {S A z : V} :
    z ∈ˢ sigmaPairsAppF S A ↔ ∃ x, x ∈ˢ A ∧ ∃ y, y ∈ˢ app S x ∧ z = kpair x y := by
  unfold sigmaPairsAppF
  rw [mem_sUnion]
  constructor
  · rintro ⟨s, hs, hz⟩
    obtain ⟨x, hx, hrel⟩ := (mem_imageF _).mp hs
    rw [sigAppRelF_eq_kpairImage.mp hrel] at hz
    obtain ⟨y, hy, rfl⟩ := mem_kpairImage.mp hz
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨kpairImage x (app S x), (mem_imageF _).mpr ⟨x, hx, sigAppRelF_eq_kpairImage.mpr rfl⟩,
      mem_kpairImage.mpr ⟨y, hy, rfl⟩⟩

theorem sigmaPairsAppF_eq {S A : V} :
    sigmaPairsAppF S A = sigmaPairs A (fun j => app S j) := by
  refine SetTheory.ext fun z => ?_
  rw [mem_sigmaPairsAppF, mem_sigmaPairs]

/-- Stage 87: `mem_piSetApp` restated with the definable `sigmaPairsAppF` RHS
(no meta `sigmaPairs` in the statement). -/
theorem mem_piSetApp {S A f : V}
    (hfun : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ app S x ∧ ∀ y', y' ∈ˢ app S x → y' = y) :
    f ∈ˢ piSetApp S A hfun ↔ f ⊆ˢ sigmaPairsAppF S A ∧
      ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y := by
  rw [piSetApp_eq_piSet hfun, mem_piSet, ← sigmaPairsAppF_eq]

/-- Definable app-fibre function space WITHOUT a functionality hypothesis:
the first-order twin of `piSet A (fun j => app S j)` at any family graph
`S`. -/
noncomputable def piSetAppNF (S A : V) : V :=
  sepF (power (sigmaPairsAppF S A)) piSetF (fun _ => A)

theorem mem_piSetAppNF {S A f : V} :
    f ∈ˢ piSetAppNF S A ↔ f ⊆ˢ sigmaPairsAppF S A ∧
      ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y := by
  unfold piSetAppNF
  rw [mem_sepF, mem_power_iff_subset, realize_piSetF]

theorem piSetAppNF_eq_piSet {S A : V} :
    piSetAppNF S A = piSet A (fun j => app S j) := by
  unfold piSetAppNF piSet
  rw [sigmaPairsAppF_eq]

/-- Definable app-pair-product closure (clause 6): the first-order twin of
`sigmaPairs_mem` at an `app S`-family. -/
theorem _root_.ConLeche.IsUniverse.sigmaPairsAppF_mem {U S A : V}
    (hU : IsUniverse (Mem (V := V)) U) (he : (empty : V) ∈ˢ U) (hS : S ∈ˢ U) (hA : A ∈ˢ U) :
    sigmaPairsAppF S A ∈ˢ U := by
  unfold sigmaPairsAppF
  refine hU.sUnion_mem (hU.imageF_mem hA fun x hx y hy => ?_)
  rw [sigAppRelF_eq_kpairImage.mp hy]
  exact hU.kpairImage_mem he (hU.transitive hA hx) (hU.app_mem he hS)

/-- Definable app-pair-product closure (clause 6) at the value level:
the first-order twin of `sigmaPairs_mem` at an `app S`-family when only
the values `app S x` are known to be members, not `S` itself. -/
theorem _root_.ConLeche.IsUniverse.sigmaPairsAppF_val_mem {U S A : V}
    (hU : IsUniverse (Mem (V := V)) U) (he : (empty : V) ∈ˢ U) (hA : A ∈ˢ U)
    (hval : ∀ x, x ∈ˢ A → app S x ∈ˢ U) : sigmaPairsAppF S A ∈ˢ U := by
  unfold sigmaPairsAppF
  refine hU.sUnion_mem (hU.imageF_mem hA fun x hx y hy => ?_)
  rw [sigAppRelF_eq_kpairImage.mp hy]
  exact hU.kpairImage_mem he (hU.transitive hA hx) (hval x hx)

/-- Definable functionality-free app function-space closure (clause 6):
the first-order twin of `piSet_mem` at an `app S`-family. -/
theorem _root_.ConLeche.IsUniverse.piSetAppNF_mem {U S A : V}
    (hU : IsUniverse (Mem (V := V)) U) (he : (empty : V) ∈ˢ U) (hS : S ∈ˢ U) (hA : A ∈ˢ U) :
    piSetAppNF S A ∈ˢ U := by
  unfold piSetAppNF
  exact hU.sepF_mem (hU.power_mem (hU.sigmaPairsAppF_mem he hS hA))

/-- Definable functionality-free app function-space closure (clause 6)
at the value level: the first-order twin of `piSet_mem` at an
`app S`-family when only the values `app S x` are members, not `S`
itself. -/
theorem _root_.ConLeche.IsUniverse.piSetAppNF_val_mem {U S A : V}
    (hU : IsUniverse (Mem (V := V)) U) (he : (empty : V) ∈ˢ U) (hA : A ∈ˢ U)
    (hval : ∀ x, x ∈ˢ A → app S x ∈ˢ U) : piSetAppNF S A ∈ˢ U := by
  unfold piSetAppNF
  exact hU.sepF_mem (hU.power_mem (hU.sigmaPairsAppF_val_mem he hA hval))

/-- Application reading at a functionality-free app function space. -/
theorem app_mem_of_mem_piSetAppNF {S A f a : V} (hf : f ∈ˢ piSetAppNF S A) (ha : a ∈ˢ A) :
    app f a ∈ˢ app S a := by
  rw [piSetAppNF_eq_piSet] at hf
  exact app_mem_of_mem_piSet hf ha

/-- Extensionality at a functionality-free app function space. -/
theorem eq_of_mem_piSetAppNF_app_eq {S A f g : V} (hf : f ∈ˢ piSetAppNF S A)
    (hg : g ∈ˢ piSetAppNF S A) (h : ∀ x, x ∈ˢ A → app f x = app g x) : f = g := by
  rw [piSetAppNF_eq_piSet] at hf hg
  exact eq_of_mem_piSet_app_eq hf hg h

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

/-! ## The definable selector graph `recGraphF`

The first-order twin of the selector graph `graph (fun j => recSel G j) D`
(`recSel` is a `Classical.choose`, not first-order expressible): separate
`sigmaPairsAppF G D` by "`p = kpair j y` with `y` the unique value of
`app G j`". -/

/-- The parameters `(G, D, pt)` of `recPredF`. -/
noncomputable def recGraphParam (G D : V) : Fin 3 → V := fun i =>
  match i.val with
  | 0 => G
  | 1 => D
  | _ => (pt : V)

/-- Variable map `Fin 3 → Fin 6` reading `kpairEqF`'s `(z, x, y)` out of
`(G, D, pt, p, j, y)` as `(p, j, y)`. -/
def rgKMap : Fin 3 → Fin 6 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨4, by omega⟩
  | _ => ⟨5, by omega⟩

/-- Variable map `Fin 4 → Fin 6` reading `appMemF`'s `(w, g, u, pt)` out of
`(G, D, pt, p, j, y)` as `(y, G, j, pt)`. -/
def rgMMap : Fin 4 → Fin 6 := fun i =>
  match i.val with
  | 0 => ⟨5, by omega⟩
  | 1 => ⟨0, by omega⟩
  | 2 => ⟨4, by omega⟩
  | _ => ⟨2, by omega⟩

/-- Variable map `Fin 4 → Fin 7` reading `appMemF`'s `(w, g, u, pt)` out of
`(G, D, pt, p, j, y, z)` as `(z, G, j, pt)`. -/
def rgZMap : Fin 4 → Fin 7 := fun i =>
  match i.val with
  | 0 => ⟨6, by omega⟩
  | 1 => ⟨0, by omega⟩
  | 2 => ⟨4, by omega⟩
  | _ => ⟨2, by omega⟩

/-- `p = kpair j y` with `j ∈ˢ D` and `y` the unique value of `app G j`
(variable `3 ↦ p`, parameters `G`, `D`, `pt`). -/
def recPredF : Form 4 :=
  .ex (.ex (.and (Form.relabel rgKMap kpairEqF)
    (.and (.mem ⟨4, by omega⟩ ⟨1, by omega⟩)
      (.and (Form.relabel rgMMap appMemF)
        (.all (.imp (Form.relabel rgZMap appMemF) (.equal ⟨6, by omega⟩ ⟨5, by omega⟩)))))))

theorem realize_recPredF {p G D : V} :
    Form.Realize Mem (Form.snoc (recGraphParam G D) p) recPredF ↔
      ∃ j y, p = kpair j y ∧ j ∈ˢ D ∧ y ∈ˢ app G j ∧ ∀ z, z ∈ˢ app G j → z = y := by
  have hK : ∀ j y : V,
      (Form.snoc (Form.snoc (Form.snoc (recGraphParam G D) p) j) y) ∘ rgKMap =
        Form.snoc (Form.snoc (fun _ => p) j) y := by
    intro j y
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hM : ∀ j y : V,
      (Form.snoc (Form.snoc (Form.snoc (recGraphParam G D) p) j) y) ∘ rgMMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ => y) G) j) (pt : V) := by
    intro j y
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hZ : ∀ j y z : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (recGraphParam G D) p) j) y) z) ∘ rgZMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ => z) G) j) (pt : V) := by
    intro j y z
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [recPredF, Form.realize_ex, Form.realize_and, Form.realize_mem,
    Form.realize_all, Form.realize_imp, Form.realize_equal, Form.realize_relabel,
    hK, hM, hZ, realize_kpairEqF, realize_appMemF, Form.snoc_mk]
  simp [recGraphParam]

/-- The definable selector graph: the pairs `kpair j y` over `j ∈ˢ D`
whose second component is the unique value of `app G j` — the
first-order twin of `graph (fun j => recSel G j) D`. -/
noncomputable def recGraphF (G D : V) : V :=
  sepF (sigmaPairsAppF G D) recPredF (recGraphParam G D)

theorem mem_recGraphF {G D p : V} :
    p ∈ˢ recGraphF G D ↔ p ∈ˢ sigmaPairsAppF G D ∧
      ∃ j y, p = kpair j y ∧ j ∈ˢ D ∧ y ∈ˢ app G j ∧ ∀ z, z ∈ˢ app G j → z = y := by
  unfold recGraphF
  rw [mem_sepF, realize_recPredF]

theorem mem_recGraphF_of_single {G D j y : V} (hj : j ∈ˢ D) (hy : y ∈ˢ app G j)
    (huniq : ∀ z, z ∈ˢ app G j → z = y) : kpair j y ∈ˢ recGraphF G D :=
  mem_recGraphF.mpr ⟨mem_sigmaPairsAppF.mpr ⟨j, hj, y, hy, rfl⟩, j, y, rfl, hj, hy, huniq⟩

/-- Under single-valuedness of `G` on `D`, the selector graph is a
member of the definable function space `piSetAppNF G D`. -/
theorem recGraphF_mem_piSetAppNF {G D : V}
    (hS : ∀ j, j ∈ˢ D → ∃ y, y ∈ˢ app G j ∧ ∀ z, z ∈ˢ app G j → z = y) :
    recGraphF G D ∈ˢ piSetAppNF G D := by
  rw [mem_piSetAppNF]
  refine ⟨sepF_subset, fun j hj => ?_⟩
  obtain ⟨y, hy, huniq⟩ := hS j hj
  refine ⟨y, mem_recGraphF_of_single hj hy huniq, fun y' hy' => ?_⟩
  obtain ⟨-, j', y'', hp, -, hy2, -⟩ := mem_recGraphF.mp hy'
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  exact huniq y' hy2

/-- Under single-valuedness, `app (recGraphF G D) j` is the (unique)
value of `app G j`. -/
theorem app_recGraphF_eq {G D j v : V}
    (hS : ∀ j, j ∈ˢ D → ∃ y, y ∈ˢ app G j ∧ ∀ z, z ∈ˢ app G j → z = y)
    (hj : j ∈ˢ D) (hv : v ∈ˢ app G j) : app (recGraphF G D) j = v := by
  have hmem := recGraphF_mem_piSetAppNF hS
  have ha := app_mem_of_mem_piSetAppNF hmem hj
  obtain ⟨y, hy, huniq⟩ := hS j hj
  exact (huniq _ ha).trans (huniq _ hv).symm

/-- Definable selector-graph closure (clause 6): the first-order twin of
`graph_mem` for selector graphs. -/
theorem _root_.ConLeche.IsUniverse.recGraphF_mem {U G D : V}
    (hU : IsUniverse (Mem (V := V)) U) (he : (empty : V) ∈ˢ U) (hG : G ∈ˢ U) (hD : D ∈ˢ U) :
    recGraphF G D ∈ˢ U :=
  hU.sepF_mem (hU.sigmaPairsAppF_mem he hG hD)

/-! ## Standard-numeral bridge for `natrecF`

At the standard numerals `vnat n` the definable recursion graph agrees
with any meta family `f : Nat → V` satisfying the same base and step
equations.  At nonstandard members of `ω` the graph carries junk
values, so the bridge is one-sided — standard numerals only. -/

/-- If a meta family `f` has base value `z` and step
`f (n + 1) = app (app s (vnat n)) (f n)`, then the definable recursion
graph reads off `f` at every standard numeral. -/
theorem natrecF_vnat_eq (z s : V) (f : Nat → V) (h0 : f 0 = z)
    (hstep : ∀ n, f (n + 1) = app (app s (vnat n)) (f n)) :
    ∀ n, natrecF z s (vnat n) = f n := by
  intro n
  induction n with
  | zero =>
      show natrecF z s (empty : V) = f 0
      rw [h0]
      exact natrecF_empty z s
  | succ n ih =>
      show natrecF z s (vsucc (vnat n)) = f (n + 1)
      rw [natrecF_vsucc z s (vnat_mem_omega n), ih, hstep n]

/-! ## Universe closure of the recursion graph

`recGraph z s` is the `sUnion` of an `imageF` over `ω` (clause 6), so it
stays in a universe `U` once every attempt stays in `U` — proved by
definable induction on `ω` (`attemptMemF`), using that an attempt at
`vsucc x` is the `binUnion` of the attempt at `x` with the single step
pair. -/

/-- Variable map `Fin 6 → Fin 7` reading the attempt body's
`(e, z, s, pt, n, F)` out of `(e, z, s, pt, U, n, F)` (`4 ↦ 5`, `5 ↦ 6`). -/
def attUMMap : Fin 6 → Fin 7 := fun i =>
  match i.val with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨1, by omega⟩
  | 2 => ⟨2, by omega⟩
  | 3 => ⟨3, by omega⟩
  | 4 => ⟨5, by omega⟩
  | _ => ⟨6, by omega⟩

/-- "Every attempt at `n` is a member of `U`" (variables `0 ↦ e`,
`1 ↦ z`, `2 ↦ s`, `3 ↦ pt`, `4 ↦ U`, `5 ↦ n`; bound `6 ↦ F`). -/
def attemptMemF : Form 6 :=
  .all (.imp (Form.relabel attUMMap attemptBodyF)
    (.mem ⟨6, by omega⟩ ⟨4, by omega⟩))

theorem realize_attemptMemF {e z s U n : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) U) n)
          attemptMemF ↔
      ∀ f, IsAttemptE e z s n f → f ∈ˢ U := by
  have hX : ∀ f : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) U) n) f)
          ∘ attUMMap =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => e) z) s) pt) n) f := by
    intro f
    funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [attemptMemF, Form.realize_all, Form.realize_imp, Form.realize_relabel, hX,
    realize_attemptBodyF, Form.realize_mem, Form.snoc_mk]
  simp

/-- **Universe closure of attempts**: in a universe `U` containing the
base value `z` and `ω`, with every step value `app (app s m) u`
(`m ∈ˢ ω`, `u ∈ˢ U`) in `U`, every attempt at every `n ∈ˢ ω` is a member of `U`
— by definable induction on `ω` (`attemptMemF`). -/
theorem _root_.ConLeche.IsUniverse.attempt_mem {U z s : V} (hU : IsUniverse (Mem (V := V)) U)
    (hz : z ∈ˢ U) (ho : (omega : V) ∈ˢ U)
    (hstep : ∀ m, m ∈ˢ (omega : V) → ∀ u, u ∈ˢ U → app (app s m) u ∈ˢ U)
    {n f : V} (hn : n ∈ˢ (omega : V)) (hf : IsAttempt z s n f) : f ∈ˢ U := by
  have h := omega_induction
    (p := Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => (empty : V)) z) s) pt) U)
    (φ := attemptMemF)
    (by
      rw [realize_attemptMemF]
      intro f hf
      obtain ⟨hfunc, hdom, hbase, -⟩ := hf
      have hfeq : f = sing (kpair (empty : V) z) := by
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
      rw [hfeq]
      exact hU.sing_mem hz (hU.kpair_mem hz (hU.empty_mem hz) hz))
    (fun x hx hIH => by
      rw [realize_attemptMemF] at hIH
      rw [realize_attemptMemF]
      intro f hf
      have hvs : vsucc x ∈ˢ (omega : V) := vsucc_mem_omega hx
      have hg : IsAttempt z s x (sepF f restrictF (fun _ => vsucc x)) := attempt_restrict hx hf
      have hgU : sepF f restrictF (fun _ => vsucc x) ∈ˢ U := hIH _ hg
      have heq : f = binUnion (sepF f restrictF (fun _ => vsucc x))
          (sing (kpair (vsucc x)
            (app (app s x) (app (sepF f restrictF (fun _ => vsucc x)) x)))) :=
        attempt_unique hvs hf (attempt_vsucc hx hg)
      rw [heq]
      have hvsU : vsucc x ∈ˢ U := hU.transitive ho hvs
      obtain ⟨hfunc, hdom, hbase, -⟩ := hg
      have hg_ne : sepF f restrictF (fun _ => vsucc x) ≠ pt :=
        fun h => ptTag_ne_kpair (empty : V) z ((mem_pt.mp (h ▸ hbase)).symm)
      obtain ⟨y, hy⟩ := (hdom x).mp (Or.inr rfl)
      have hxyU : kpair x y ∈ˢ U := hU.transitive hgU hy
      have hyU : y ∈ˢ U :=
        hU.transitive (hU.transitive hxyU (mem_upair_right (sing x) (upair x y)))
          (mem_upair_right x y)
      have happ : app (sepF f restrictF (fun _ => vsucc x)) x = y :=
        app_eq_of_unique hg_ne hy (fun y' hy' => (hfunc (kpair x y') hy').2 x y' y hy' hy)
      have hstepU : app (app s x) (app (sepF f restrictF (fun _ => vsucc x)) x) ∈ˢ U := by
        rw [happ]; exact hstep x hx y hyU
      exact hU.binUnion_mem hz hgU (hU.sing_mem hz (hU.kpair_mem hz hvsU hstepU)))
    hn
  exact realize_attemptMemF.mp h f hf

/-- **Universe closure of the recursion graph**: in a universe `U`
containing the base `z` and `ω`, with every step value `app (app s m) u`
(`m ∈ˢ ω`, `u ∈ˢ U`) in `U`, the recursion graph `recGraph z s` is a
member of `U` (clause 6 on the attempt relation, then `sUnion`). -/
theorem _root_.ConLeche.IsUniverse.recGraph_mem {U z s : V} (hU : IsUniverse (Mem (V := V)) U)
    (hz : z ∈ˢ U) (ho : (omega : V) ∈ˢ U)
    (hstep : ∀ m, m ∈ˢ (omega : V) → ∀ u, u ∈ˢ U → app (app s m) u ∈ˢ U) :
    recGraph z s ∈ˢ U := by
  unfold recGraph
  refine hU.sUnion_mem (hU.imageF_mem ho fun x hx y hy => ?_)
  exact hU.attempt_mem hz ho hstep hx (realize_attemptRelF.mp hy)



/-! ## Stage 82: the double-application equality reader `app2EqF` -/

/-- Map of `appEqF`'s `(pt, v, g, u)` into the bound context
`(pt, v, g, a, b, w)` reading `(pt, w, g, a)`: `0 ↦ 0`, `1 ↦ 5`, `2 ↦ 2`,
`3 ↦ 3`. -/
def app2M1 : Fin 4 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨0, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `appEqF`'s `(pt, v, g, u)` into the bound context
`(pt, v, g, a, b, w)` reading `(pt, v, w, b)`: `0 ↦ 0`, `1 ↦ 1`, `2 ↦ 5`,
`3 ↦ 4`. -/
def app2M2 : Fin 4 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨0, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨5, by omega⟩ | _ => ⟨4, by omega⟩

/-- The double-application equality reader (variables `0 ↦ pt`, `1 ↦ v`,
`2 ↦ g`, `3 ↦ a`, `4 ↦ b`): `v = app (app g a) b`, by an existential
witness `w = app g a`. -/
def app2EqF : Form 5 :=
  .ex (.and (Form.relabel app2M1 appEqF) (Form.relabel app2M2 appEqF))

theorem realize_app2EqF {v g a b : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v) g) a) b)
        app2EqF ↔
      v = app (app g a) b := by
  have h1 : ∀ w : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v) g) a)
          b) w) ∘ app2M1 =
        Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) w) g) a := by
    intro w; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have h2 : ∀ w : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v) g) a)
          b) w) ∘ app2M2 =
        Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v) w) b := by
    intro w; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [app2EqF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    h1, h2, realize_appEqF]
  constructor
  · rintro ⟨w, hw, hv⟩; rw [hv, hw]
  · intro h; exact ⟨app g a, rfl, h⟩



/-! ## Stage 83: the definable double-application image `app2ImageF` -/

/-- Variable map `Fin 5 → Fin 5`, `0 ↦ 4`, `1 ↦ 1`, `2 ↦ 2`, `3 ↦ 3`, `4 ↦ 0`
(reads `app2EqF`'s `(pt, v, g, a, b)` out of the `imageF` convention
`(x, v, g, a, pt)`). -/
def app2RepMap : Fin 5 → Fin 5 :=
  fun k => match k.val with
  | 0 => ⟨4, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨2, by omega⟩
  | 3 => ⟨3, by omega⟩ | _ => ⟨0, by omega⟩

/-- `v = app (app g a) x` in the `imageF` convention (variables `0 ↦ x`,
`1 ↦ v`, parameters `g`, `a`, `pt`). -/
def app2EqRepF : Form 5 := Form.relabel app2RepMap app2EqF

theorem realize_app2EqRepF {x v g a : V} :
    Form.Realize Mem
        (Form.cons2 x v (Form.snoc (Form.snoc (fun _ : Fin 1 => g) a) (pt : V)))
        app2EqRepF ↔
      v = app (app g a) x := by
  have hcomp : (Form.cons2 x v (Form.snoc (Form.snoc (fun _ : Fin 1 => g) a) (pt : V)) :
      Fin 5 → V) ∘ app2RepMap =
      Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v) g) a) x := by
    funext ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [app2EqRepF, Form.realize_relabel, hcomp, realize_app2EqF]

/-- The definable image under `fun x => app (app g a) x`:
`{app (app g a) x | x ∈ˢ A}`. -/
noncomputable def app2ImageF (g a A : V) : V :=
  imageF app2EqRepF (Form.snoc (Form.snoc (fun _ : Fin 1 => g) a) (pt : V)) A
    (fun x _ => ⟨app (app g a) x, realize_app2EqRepF.mpr rfl,
      fun _ hy => realize_app2EqRepF.mp hy⟩)

theorem mem_app2ImageF {g a A z : V} :
    z ∈ˢ app2ImageF g a A ↔ ∃ x, x ∈ˢ A ∧ z = app (app g a) x := by
  unfold app2ImageF
  rw [mem_imageF]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, realize_app2EqRepF.mp h⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, realize_app2EqRepF.mpr rfl⟩

/-- The meta-level `image (fun x => app (app g a) x) A` is exactly the
definable `app2ImageF g a A`. -/
theorem image_app2_eq {g a A : V} :
    image (fun x => app (app g a) x) A = app2ImageF g a A :=
  ext fun z => by rw [mem_image, mem_app2ImageF]



/-! ## Stage 84: the triple-application equality reader `app3EqF` -/

/-- Map of `app2EqF`'s `(pt, v, g, a, b)` into the bound context
`(pt, v, F, a, m, i, w)` reading `(pt, w, F, a, m)`: `0 ↦ 0`, `1 ↦ 6`,
`2 ↦ 2`, `3 ↦ 3`, `4 ↦ 4`. -/
def app3M1 : Fin 5 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨0, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨2, by omega⟩
  | 3 => ⟨3, by omega⟩ | _ => ⟨4, by omega⟩

/-- Map of `appEqF`'s `(pt, v, g, u)` into the bound context
`(pt, v, F, a, m, i, w)` reading `(pt, v, w, i)`: `0 ↦ 0`, `1 ↦ 1`,
`2 ↦ 6`, `3 ↦ 5`. -/
def app3M2 : Fin 4 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨0, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨6, by omega⟩ | _ => ⟨5, by omega⟩

/-- The triple-application equality reader (variables `0 ↦ pt`, `1 ↦ v`,
`2 ↦ F`, `3 ↦ a`, `4 ↦ m`, `5 ↦ i`): `v = app (app (app F a) m) i`, by an
existential witness `w = app (app F a) m`. -/
def app3EqF : Form 6 :=
  .ex (.and (Form.relabel app3M1 app2EqF) (Form.relabel app3M2 appEqF))

theorem realize_app3EqF {v F a m i : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v)
          F) a) m) i)
        app3EqF ↔
      v = app (app (app F a) m) i := by
  have h1 : ∀ w : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 =>
          (pt : V)) v) F) a) m) i) w) ∘ app3M1 =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) w) F) a) m := by
    intro w; funext ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> rfl
  have h2 : ∀ w : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 =>
          (pt : V)) v) F) a) m) i) w) ∘ app3M2 =
        Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v) w) i := by
    intro w; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [app3EqF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    h1, h2, realize_app2EqF, realize_appEqF]
  constructor
  · rintro ⟨w, hw, hv⟩; rw [hv, hw]
  · intro h; exact ⟨app (app F a) m, rfl, h⟩



/-! ## Stage 85: the definable triple-application image `app3ImageF` -/

/-- Variable map `Fin 6 → Fin 6`, `0 ↦ 5`, `1 ↦ 1`, `2 ↦ 2`, `3 ↦ 3`,
`4 ↦ 4`, `5 ↦ 0` (reads `app3EqF`'s `(pt, v, F, a, m, i)` out of the
`imageF` convention `(x, v, F, a, m, pt)`). -/
def app3RepMap : Fin 6 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨5, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨2, by omega⟩
  | 3 => ⟨3, by omega⟩ | 4 => ⟨4, by omega⟩ | _ => ⟨0, by omega⟩

/-- `v = app (app (app F a) m) x` in the `imageF` convention (variables
`0 ↦ x`, `1 ↦ v`, parameters `F`, `a`, `m`, `pt`). -/
def app3EqRepF : Form 6 := Form.relabel app3RepMap app3EqF

theorem realize_app3EqRepF {x v F a m : V} :
    Form.Realize Mem
        (Form.cons2 x v
          (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => F) a) m) (pt : V)))
        app3EqRepF ↔
      v = app (app (app F a) m) x := by
  have hcomp : (Form.cons2 x v
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => F) a) m) (pt : V)) :
      Fin 6 → V) ∘ app3RepMap =
      Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v)
        F) a) m) x := by
    funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [app3EqRepF, Form.realize_relabel, hcomp, realize_app3EqF]

/-- The definable image under `fun x => app (app (app F a) m) x`:
`{app (app (app F a) m) x | x ∈ˢ A}`. -/
noncomputable def app3ImageF (F a m A : V) : V :=
  imageF app3EqRepF
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => F) a) m) (pt : V)) A
    (fun x _ => ⟨app (app (app F a) m) x, realize_app3EqRepF.mpr rfl,
      fun _ hy => realize_app3EqRepF.mp hy⟩)

theorem mem_app3ImageF {F a m A z : V} :
    z ∈ˢ app3ImageF F a m A ↔ ∃ x, x ∈ˢ A ∧ z = app (app (app F a) m) x := by
  unfold app3ImageF
  rw [mem_imageF]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, realize_app3EqRepF.mp h⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, realize_app3EqRepF.mpr rfl⟩

/-- The meta-level `image (fun x => app (app (app F a) m) x) A` is exactly
the definable `app3ImageF F a m A`. -/
theorem image_app3_eq {F a m A : V} :
    image (fun x => app (app (app F a) m) x) A = app3ImageF F a m A :=
  ext fun z => by rw [mem_image, mem_app3ImageF]


/-! ## Stage 93: the definable swapped triple-application image `app3sImageF` -/

/-- Variable map `Fin 6 → Fin 6`, `0 ↦ 5`, `1 ↦ 1`, `2 ↦ 2`,
`3 ↦ 0`, `4 ↦ 3`, `5 ↦ 4` (reads `app3EqF`'s `(pt, v, F, a, m, i)` out of the
`imageF` convention `(a, v, F, m, i, pt)`). -/
def app3sRepMap : Fin 6 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨5, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨2, by omega⟩
  | 3 => ⟨0, by omega⟩ | 4 => ⟨3, by omega⟩ | _ => ⟨4, by omega⟩

/-- `v = app (app (app F a) m) i` in the swapped `imageF` convention
(variables `0 ↦ a`, `1 ↦ v`, parameters `F`, `m`, `i`, `pt`). -/
def app3sEqRepF : Form 6 := Form.relabel app3sRepMap app3EqF

theorem realize_app3sEqRepF {a v F m i : V} :
    Form.Realize Mem
        (Form.cons2 a v
          (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => F) m) i) (pt : V)))
        app3sEqRepF ↔
      v = app (app (app F a) m) i := by
  have hcomp : (Form.cons2 a v
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => F) m) i) (pt : V)) :
      Fin 6 → V) ∘ app3sRepMap =
      Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v)
        F) a) m) i := by
    funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [app3sEqRepF, Form.realize_relabel, hcomp, realize_app3EqF]

/-- The definable image under `fun a => app (app (app F a) m) i`:
`{app (app (app F a) m) i | a ∈ˢ A}`. -/
noncomputable def app3sImageF (F m i A : V) : V :=
  imageF app3sEqRepF
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => F) m) i) (pt : V)) A
    (fun a _ => ⟨app (app (app F a) m) i, realize_app3sEqRepF.mpr rfl,
      fun _ hy => realize_app3sEqRepF.mp hy⟩)

theorem mem_app3sImageF {F m i A z : V} :
    z ∈ˢ app3sImageF F m i A ↔ ∃ a, a ∈ˢ A ∧ z = app (app (app F a) m) i := by
  unfold app3sImageF
  rw [mem_imageF]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, realize_app3sEqRepF.mp h⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, realize_app3sEqRepF.mpr rfl⟩

/-- The meta-level `image (fun a => app (app (app F a) m) i) A` is exactly
the definable `app3sImageF F m i A`. -/
theorem image_app3s_eq {F m i A : V} :
    image (fun a => app (app (app F a) m) i) A = app3sImageF F m i A :=
  ext fun z => by rw [mem_image, mem_app3sImageF]



/-! ## Stage 94: the definable `sUnion`-of-`app3sImageF` wrapper `sUnionApp3sImageF` -/

/-- The definable `sUnion (app3sImageF F m i A)`: the first-order twin of
`sUnion (image (fun a => app (app (app F a) m) i) A)`. -/
noncomputable def sUnionApp3sImageF (F m i A : V) : V := sUnion (app3sImageF F m i A)

theorem mem_sUnionApp3sImageF {F m i A z : V} :
    z ∈ˢ sUnionApp3sImageF F m i A ↔ ∃ s, s ∈ˢ app3sImageF F m i A ∧ z ∈ˢ s :=
  mem_sUnion

/-- Unpacked form: `z` is in some fibre `app (app (app F a) m) i` at
`a ∈ˢ A`. -/
theorem mem_sUnionApp3sImageF' {F m i A z : V} :
    z ∈ˢ sUnionApp3sImageF F m i A ↔
      ∃ a, a ∈ˢ A ∧ ∃ s, s = app (app (app F a) m) i ∧ z ∈ˢ s := by
  rw [mem_sUnionApp3sImageF]
  constructor
  · rintro ⟨s, hs, hz⟩
    obtain ⟨a, ha, hs'⟩ := mem_app3sImageF.mp hs
    exact ⟨a, ha, s, hs', hz⟩
  · rintro ⟨a, ha, s, hs, hz⟩
    exact ⟨s, mem_app3sImageF.mpr ⟨a, ha, hs⟩, hz⟩

/-- The meta-level `sUnion (image (fun a => app (app (app F a) m) i) A)` is
exactly the definable `sUnionApp3sImageF F m i A`. -/
theorem sUnion_image_app3s_eq {F m i A : V} :
    sUnion (image (fun a => app (app (app F a) m) i) A) = sUnionApp3sImageF F m i A := by
  unfold sUnionApp3sImageF
  rw [image_app3s_eq]



/-! ## Stage 95: the definable swapped double-application image `app2sImageF` -/

/-- Variable map `Fin 5 → Fin 5`, `0 ↦ 4`, `1 ↦ 1`, `2 ↦ 2`,
`3 ↦ 0`, `4 ↦ 3` (reads `app2EqF`'s `(pt, v, g, a, b)` out of the
`imageF` convention `(a, v, g, m, pt)`). -/
def app2sRepMap : Fin 5 → Fin 5 :=
  fun k => match k.val with
  | 0 => ⟨4, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨2, by omega⟩
  | 3 => ⟨0, by omega⟩ | _ => ⟨3, by omega⟩

/-- `v = app (app g a) m` in the swapped `imageF` convention (variables
`0 ↦ a`, `1 ↦ v`, parameters `g`, `m`, `pt`). -/
def app2sEqRepF : Form 5 := Form.relabel app2sRepMap app2EqF

theorem realize_app2sEqRepF {a v g m : V} :
    Form.Realize Mem
        (Form.cons2 a v (Form.snoc (Form.snoc (fun _ : Fin 1 => g) m) (pt : V)))
        app2sEqRepF ↔
      v = app (app g a) m := by
  have hcomp : (Form.cons2 a v (Form.snoc (Form.snoc (fun _ : Fin 1 => g) m) (pt : V)) :
      Fin 5 → V) ∘ app2sRepMap =
      Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v) g) a) m := by
    funext ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [app2sEqRepF, Form.realize_relabel, hcomp, realize_app2EqF]

/-- The definable image under `fun a => app (app g a) m`:
`{app (app g a) m | a ∈ˢ A}`. -/
noncomputable def app2sImageF (g m A : V) : V :=
  imageF app2sEqRepF
    (Form.snoc (Form.snoc (fun _ : Fin 1 => g) m) (pt : V)) A
    (fun a _ => ⟨app (app g a) m, realize_app2sEqRepF.mpr rfl,
      fun _ hy => realize_app2sEqRepF.mp hy⟩)

theorem mem_app2sImageF {g m A z : V} :
    z ∈ˢ app2sImageF g m A ↔ ∃ a, a ∈ˢ A ∧ z = app (app g a) m := by
  unfold app2sImageF
  rw [mem_imageF]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, realize_app2sEqRepF.mp h⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, realize_app2sEqRepF.mpr rfl⟩

/-- The meta-level `image (fun a => app (app g a) m) A` is exactly
the definable `app2sImageF g m A`. -/
theorem image_app2s_eq {g m A : V} :
    image (fun a => app (app g a) m) A = app2sImageF g m A :=
  ext fun z => by rw [mem_image, mem_app2sImageF]



/-! ## Stage 96: the `graphAppF` equality reader `graphAppEqF` -/

/-- Map of the `appEqF` conjunct (vars `0 ↦ pt`, `1 ↦ v'`, `2 ↦ g`, `3 ↦ u`)
into the bound context `(v, g, A, pt, z, x, y)`: `0 ↦ 3`, `1 ↦ 6`, `2 ↦ 1`,
`3 ↦ 5`. -/
def gaAppMap : Fin 4 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨3, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨1, by omega⟩
  | _ => ⟨5, by omega⟩

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ z'`, `1 ↦ x'`, `2 ↦ y'`) into the
bound context `(v, g, A, pt, z, x, y)`: `0 ↦ 4`, `1 ↦ 5`, `2 ↦ 6`. -/
def gaKpMap : Fin 3 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨4, by omega⟩ | 1 => ⟨5, by omega⟩ | _ => ⟨6, by omega⟩

/-- The `graphAppF` equality reader (variables `0 ↦ v`, `1 ↦ g`,
`2 ↦ A`, `3 ↦ pt`): `v = graphAppF g A`, by extensionality +
`mem_graphAppF`, with `y = app g x` read by `appEqF` and
`z = kpair x y` by `kpairEqF`. -/
def graphAppEqF : Form 4 :=
  .all (.iff (.mem ⟨4, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨5, by omega⟩ ⟨2, by omega⟩)
      (.ex (.and (Form.relabel gaAppMap appEqF) (Form.relabel gaKpMap kpairEqF))))))

theorem realize_graphAppEqF {v g A : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) A) (pt : V))
        graphAppEqF ↔
      v = graphAppF g A := by
  have hApp : ∀ z x y : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) g) A) (pt : V)) z) x) y)
          (Form.relabel gaAppMap appEqF) ↔ y = app g x := by
    intro z x y
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) g) A) (pt : V)) z) x) y : Fin 7 → V) ∘ gaAppMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) y) g) x := by
      funext ⟨k, hk⟩
      have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_appEqF
  have hKp : ∀ z x y : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) g) A) (pt : V)) z) x) y)
          (Form.relabel gaKpMap kpairEqF) ↔ z = kpair x y := by
    intro z x y
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) g) A) (pt : V)) z) x) y : Fin 7 → V) ∘ gaKpMap =
        Form.snoc (Form.snoc (fun _ : Fin 1 => z) x) y := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_kpairEqF
  have key : ∀ z : V, z ∈ˢ graphAppF g A ↔
      ∃ x : V, x ∈ˢ A ∧ ∃ y : V, y = app g x ∧ z = kpair x y := by
    intro z
    rw [mem_graphAppF]
    constructor
    · rintro ⟨x, hx, hz⟩
      exact ⟨x, hx, app g x, rfl, hz⟩
    · rintro ⟨x, hx, y, hy, hz⟩
      exact ⟨x, hx, hz.trans (congrArg (kpair x) hy)⟩
  simp only [graphAppEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hApp, hKp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (key z).symm
  · intro h z
    rw [h]
    exact key z



/-! ## Stage 97: the `sigmaPairsAppF` equality reader `sigmaPairsAppEqF` -/

/-- Map of the `appMemF` conjunct (vars `0 ↦ w`, `1 ↦ g`, `2 ↦ u`, `3 ↦ pt`)
into the bound context `(v, S, A, pt, z, x, y)`: `0 ↦ 6`, `1 ↦ 1`, `2 ↦ 5`,
`3 ↦ 3`. -/
def spAppMap : Fin 4 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨6, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨5, by omega⟩
  | _ => ⟨3, by omega⟩

/-- The `sigmaPairsAppF` equality reader (variables `0 ↦ v`, `1 ↦ S`,
`2 ↦ A`, `3 ↦ pt`): `v = sigmaPairsAppF S A`, by extensionality +
`mem_sigmaPairsAppF`, with `y ∈ app S x` read by `appMemF` and
`z = kpair x y` by `kpairEqF`. -/
def sigmaPairsAppEqF : Form 4 :=
  .all (.iff (.mem ⟨4, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨5, by omega⟩ ⟨2, by omega⟩)
      (.ex (.and (Form.relabel spAppMap appMemF) (Form.relabel gaKpMap kpairEqF))))))

theorem realize_sigmaPairsAppEqF {v S A : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) S) A) (pt : V))
        sigmaPairsAppEqF ↔
      v = sigmaPairsAppF S A := by
  have hApp : ∀ z x y : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) S) A) (pt : V)) z) x) y)
          (Form.relabel spAppMap appMemF) ↔ y ∈ˢ app S x := by
    intro z x y
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) S) A) (pt : V)) z) x) y : Fin 7 → V) ∘ spAppMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => y) S) x) (pt : V) := by
      funext ⟨k, hk⟩
      have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_appMemF
  have hKp : ∀ z x y : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) S) A) (pt : V)) z) x) y)
          (Form.relabel gaKpMap kpairEqF) ↔ z = kpair x y := by
    intro z x y
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) S) A) (pt : V)) z) x) y : Fin 7 → V) ∘ gaKpMap =
        Form.snoc (Form.snoc (fun _ : Fin 1 => z) x) y := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_kpairEqF
  simp only [sigmaPairsAppEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hApp, hKp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_sigmaPairsAppF (S := S) (A := A)).symm
  · intro h z
    rw [h]
    exact mem_sigmaPairsAppF



/-! ## Stage 98: the `appImageF` equality reader `appImageEqF` -/

/-- Map of the `appEqF` conjunct (vars `0 ↦ pt`, `1 ↦ v'`, `2 ↦ g`, `3 ↦ u`)
into the bound context `(v, g, A, pt, z, x)`: `0 ↦ 3`, `1 ↦ 4`, `2 ↦ 1`,
`3 ↦ 5`. -/
def aImAppMap : Fin 4 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨3, by omega⟩ | 1 => ⟨4, by omega⟩ | 2 => ⟨1, by omega⟩
  | _ => ⟨5, by omega⟩

/-- The `appImageF` equality reader (variables `0 ↦ v`, `1 ↦ g`,
`2 ↦ A`, `3 ↦ pt`): `v = appImageF g A`, by extensionality +
`mem_appImageF`, with `z = app g x` read by `appEqF`. -/
def appImageEqF : Form 4 :=
  .all (.iff (.mem ⟨4, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨5, by omega⟩ ⟨2, by omega⟩)
      (Form.relabel aImAppMap appEqF))))

theorem realize_appImageEqF {v g A : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) A) (pt : V))
        appImageEqF ↔
      v = appImageF g A := by
  have hApp : ∀ z x : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) A)
            (pt : V)) z) x)
          (Form.relabel aImAppMap appEqF) ↔ z = app g x := by
    intro z x
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) A)
        (pt : V)) z) x : Fin 6 → V) ∘ aImAppMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) z) g) x := by
      funext ⟨k, hk⟩
      have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_appEqF
  simp only [appImageEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hApp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_appImageF (g := g) (A := A)).symm
  · intro h z
    rw [h]
    exact mem_appImageF



/-! ## Stage 99: the `app2ImageF` equality reader `app2ImageEqF` -/

/-- Map of the `app2EqF` conjunct (vars `0 ↦ pt`, `1 ↦ v'`, `2 ↦ g`,
`3 ↦ a`, `4 ↦ b`) into the bound context `(v, g, a, A, pt, z, x)`:
`0 ↦ 4`, `1 ↦ 5`, `2 ↦ 1`, `3 ↦ 2`, `4 ↦ 6`. -/
def a2ImMap : Fin 5 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨4, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨1, by omega⟩
  | 3 => ⟨2, by omega⟩ | _ => ⟨6, by omega⟩

/-- The `app2ImageF` equality reader (variables `0 ↦ v`, `1 ↦ g`,
`2 ↦ a`, `3 ↦ A`, `4 ↦ pt`): `v = app2ImageF g a A`, by extensionality +
`mem_app2ImageF`, with `z = app (app g a) x` read by `app2EqF`. -/
def app2ImageEqF : Form 5 :=
  .all (.iff (.mem ⟨5, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨6, by omega⟩ ⟨3, by omega⟩)
      (Form.relabel a2ImMap app2EqF))))

theorem realize_app2ImageEqF {v g a A : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) a) A) (pt : V))
        app2ImageEqF ↔
      v = app2ImageF g a A := by
  have hApp : ∀ z x : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) g) a) A) (pt : V)) z) x)
          (Form.relabel a2ImMap app2EqF) ↔ z = app (app g a) x := by
    intro z x
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) g) a) A) (pt : V)) z) x : Fin 7 → V) ∘ a2ImMap =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) z) g) a) x := by
      funext ⟨k, hk⟩
      have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_app2EqF
  simp only [app2ImageEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hApp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_app2ImageF (g := g) (a := a) (A := A)).symm
  · intro h z
    rw [h]
    exact mem_app2ImageF



/-! ## Stage 100: the `app3ImageF` equality reader `app3ImageEqF` -/

/-- Map of the `app3EqF` conjunct (vars `0 ↦ pt`, `1 ↦ v'`, `2 ↦ F`,
`3 ↦ a`, `4 ↦ m`, `5 ↦ i`) into the bound context `(v, F, a, m, A, pt, z, x)`:
`0 ↦ 5`, `1 ↦ 6`, `2 ↦ 1`, `3 ↦ 2`, `4 ↦ 3`, `5 ↦ 7`. -/
def a3ImMap : Fin 6 → Fin 8 :=
  fun k => match k.val with
  | 0 => ⟨5, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨1, by omega⟩
  | 3 => ⟨2, by omega⟩ | 4 => ⟨3, by omega⟩ | _ => ⟨7, by omega⟩

/-- The `app3ImageF` equality reader (variables `0 ↦ v`, `1 ↦ F`,
`2 ↦ a`, `3 ↦ m`, `4 ↦ A`, `5 ↦ pt`): `v = app3ImageF F a m A`, by extensionality +
`mem_app3ImageF`, with `z = app (app (app F a) m) x` read by `app3EqF`. -/
def app3ImageEqF : Form 6 :=
  .all (.iff (.mem ⟨6, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨7, by omega⟩ ⟨4, by omega⟩)
      (Form.relabel a3ImMap app3EqF))))

theorem realize_app3ImageEqF {v F a m A : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) F) a) m) A) (pt : V))
        app3ImageEqF ↔
      v = app3ImageF F a m A := by
  have hApp : ∀ z x : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) F) a) m) A) (pt : V)) z) x)
          (Form.relabel a3ImMap app3EqF) ↔ z = app (app (app F a) m) x := by
    intro z x
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) F) a) m) A) (pt : V)) z) x : Fin 8 → V) ∘ a3ImMap =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
          (fun _ : Fin 1 => (pt : V)) z) F) a) m) x := by
      funext ⟨k, hk⟩
      have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
      rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_app3EqF
  simp only [app3ImageEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hApp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_app3ImageF (F := F) (a := a) (m := m) (A := A)).symm
  · intro h z
    rw [h]
    exact mem_app3ImageF



/-! ## Stage 101: the `sUnionApp3sImageF` equality reader `sUnionApp3sImageEqF` -/

/-- Map of the `app3EqF` conjunct (vars `0 ↦ pt`, `1 ↦ v'`, `2 ↦ F`,
`3 ↦ a`, `4 ↦ m`, `5 ↦ i`) into the bound context `(v, F, m, i, A, pt, z, a, s)`:
`0 ↦ 5`, `1 ↦ 8`, `2 ↦ 1`, `3 ↦ 7`, `4 ↦ 2`, `5 ↦ 3`. -/
def suA3Map : Fin 6 → Fin 9 :=
  fun k => match k.val with
  | 0 => ⟨5, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨1, by omega⟩
  | 3 => ⟨7, by omega⟩ | 4 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `sUnionApp3sImageF` equality reader (variables `0 ↦ v`, `1 ↦ F`,
`2 ↦ m`, `3 ↦ i`, `4 ↦ A`, `5 ↦ pt`): `v = sUnionApp3sImageF F m i A`, by
extensionality + `mem_sUnionApp3sImageF'`, with `s = app (app (app F a) m) i`
read by `app3EqF`. -/
def sUnionApp3sImageEqF : Form 6 :=
  .all (.iff (.mem ⟨6, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨7, by omega⟩ ⟨4, by omega⟩)
      (.ex (.and (Form.relabel suA3Map app3EqF) (.mem ⟨6, by omega⟩ ⟨8, by omega⟩))))))

theorem realize_sUnionApp3sImageEqF {v F m i A : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) F) m) i) A) (pt : V))
        sUnionApp3sImageEqF ↔
      v = sUnionApp3sImageF F m i A := by
  have hApp : ∀ z a s : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) F) m) i) A) (pt : V)) z) a) s)
          (Form.relabel suA3Map app3EqF) ↔ s = app (app (app F a) m) i := by
    intro z a s
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) F) m) i) A) (pt : V)) z) a) s : Fin 9 → V) ∘ suA3Map =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
          (fun _ : Fin 1 => (pt : V)) s) F) a) m) i := by
      funext ⟨k, hk⟩
      have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
      rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_app3EqF
  simp only [sUnionApp3sImageEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hApp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z =>
      (h z).trans (mem_sUnionApp3sImageF' (F := F) (m := m) (i := i) (A := A)).symm
  · intro h z
    rw [h]
    exact mem_sUnionApp3sImageF'



/-! ## Stage 102: the `constGraphF` equality reader `constGraphEqF` -/

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ z'`, `1 ↦ x'`, `2 ↦ y'`)
into the bound context `(v, c, A, pt, z, x)`: `0 ↦ 4`, `1 ↦ 5`, `2 ↦ 1`
(reads `z = kpair x c`). -/
def cgKpMap : Fin 3 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨4, by omega⟩ | 1 => ⟨5, by omega⟩ | _ => ⟨1, by omega⟩

/-- The `constGraphF` equality reader (variables `0 ↦ v`, `1 ↦ c`,
`2 ↦ A`, `3 ↦ pt`): `v = constGraphF c A`, by extensionality +
`mem_constGraphF`, with `z = kpair x c` read by `kpairEqF`. -/
def constGraphEqF : Form 4 :=
  .all (.iff (.mem ⟨4, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨5, by omega⟩ ⟨2, by omega⟩)
      (Form.relabel cgKpMap kpairEqF))))

theorem realize_constGraphEqF {v c A : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) c) A) (pt : V))
        constGraphEqF ↔
      v = constGraphF c A := by
  have hKp : ∀ z x : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) c) A) (pt : V)) z) x)
          (Form.relabel cgKpMap kpairEqF) ↔ z = kpair x c := by
    intro z x
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) c) A) (pt : V)) z) x : Fin 6 → V) ∘ cgKpMap =
        Form.snoc (Form.snoc (fun _ : Fin 1 => z) x) c := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_kpairEqF
  simp only [constGraphEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hKp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_constGraphF (c := c) (A := A)).symm
  · intro h z
    rw [h]
    exact mem_constGraphF



/-! ## Stage 103: the `app2sImageF` equality reader `app2sImageEqF` -/

/-- Map of the `app2EqF` conjunct (vars `0 ↦ pt`, `1 ↦ v'`, `2 ↦ g`,
`3 ↦ a`, `4 ↦ b`) into the bound context `(v, g, m, A, pt, z, a)`:
`0 ↦ 4`, `1 ↦ 5`, `2 ↦ 1`, `3 ↦ 6`, `4 ↦ 2`. -/
def a2sImMap : Fin 5 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨4, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨1, by omega⟩
  | 3 => ⟨6, by omega⟩ | _ => ⟨2, by omega⟩

/-- The `app2sImageF` equality reader (variables `0 ↦ v`, `1 ↦ g`,
`2 ↦ m`, `3 ↦ A`, `4 ↦ pt`): `v = app2sImageF g m A`, by extensionality +
`mem_app2sImageF`, with `z = app (app g a) m` read by `app2EqF`. -/
def app2sImageEqF : Form 5 :=
  .all (.iff (.mem ⟨5, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨6, by omega⟩ ⟨3, by omega⟩)
      (Form.relabel a2sImMap app2EqF))))

theorem realize_app2sImageEqF {v g m A : V} :
    Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) m) A) (pt : V))
        app2sImageEqF ↔
      v = app2sImageF g m A := by
  have hApp : ∀ z a : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) g) m) A) (pt : V)) z) a)
          (Form.relabel a2sImMap app2EqF) ↔ z = app (app g a) m := by
    intro z a
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) g) m) A) (pt : V)) z) a : Fin 7 → V) ∘ a2sImMap =
        Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) z) g) a) m := by
      funext ⟨k, hk⟩
      have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_app2EqF
  simp only [app2sImageEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hApp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_app2sImageF (g := g) (m := m) (A := A)).symm
  · intro h z
    rw [h]
    exact mem_app2sImageF



/-! ## Stage 104: the `piSetAppNF` equality reader `piSetAppNFEqF` -/

/-- Map of the `appMemF` conjunct (vars `0 ↦ w`, `1 ↦ g`, `2 ↦ u`,
`3 ↦ pt`) into the bound context `(v, S, A, pt, z, w, x, y)`:
`0 ↦ 7`, `1 ↦ 1`, `2 ↦ 6`, `3 ↦ 3` (reads `y ∈ˢ app S x`). -/
def psAmMap : Fin 4 → Fin 8 :=
  fun k => match k.val with
  | 0 => ⟨7, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨6, by omega⟩
  | _ => ⟨3, by omega⟩

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ z'`, `1 ↦ x'`, `2 ↦ y'`)
into the bound context `(v, S, A, pt, z, w, x, y)`: `0 ↦ 5`, `1 ↦ 6`,
`2 ↦ 7` (reads `w = kpair x y`). -/
def psKp1Map : Fin 3 → Fin 8 :=
  fun k => match k.val with
  | 0 => ⟨5, by omega⟩ | 1 => ⟨6, by omega⟩ | _ => ⟨7, by omega⟩

/-- Map of the `kpairEqF` conjunct into the bound context `(v, S, A, pt, z, x, y, p)`:
`0 ↦ 7`, `1 ↦ 5`, `2 ↦ 6` (reads `p = kpair x y`). -/
def psKp2Map : Fin 3 → Fin 8 :=
  fun k => match k.val with
  | 0 => ⟨7, by omega⟩ | 1 => ⟨5, by omega⟩ | _ => ⟨6, by omega⟩

/-- Map of the `kpairEqF` conjunct into the bound context
`(v, S, A, pt, z, x, y, y', p')`: `0 ↦ 8`, `1 ↦ 5`, `2 ↦ 7`
(reads `p' = kpair x y'`). -/
def psKp3Map : Fin 3 → Fin 9 :=
  fun k => match k.val with
  | 0 => ⟨8, by omega⟩ | 1 => ⟨5, by omega⟩ | _ => ⟨7, by omega⟩

/-- The `piSetAppNF` equality reader (variables `0 ↦ v`, `1 ↦ S`,
`2 ↦ A`, `3 ↦ pt`): `v = piSetAppNF S A`, by extensionality +
`mem_piSetAppNF` + `mem_sigmaPairsAppF`, with `y ∈ˢ app S x` read by
`appMemF` and the `kpair` equalities by `kpairEqF`. -/
def piSetAppNFEqF : Form 4 :=
  .all (.iff (.mem ⟨4, by omega⟩ ⟨0, by omega⟩)
    (.and
      (.all (.imp (.mem ⟨5, by omega⟩ ⟨4, by omega⟩)
        (.ex (.and (.mem ⟨6, by omega⟩ ⟨2, by omega⟩)
          (.ex (.and (Form.relabel psAmMap appMemF) (Form.relabel psKp1Map kpairEqF)))))))
      (.all (.imp (.mem ⟨5, by omega⟩ ⟨2, by omega⟩)
        (.ex (.and
          (.ex (.and (Form.relabel psKp2Map kpairEqF) (.mem ⟨7, by omega⟩ ⟨4, by omega⟩)))
          (.all (.imp
            (.ex (.and (Form.relabel psKp3Map kpairEqF) (.mem ⟨8, by omega⟩ ⟨4, by omega⟩)))
            (.equal ⟨7, by omega⟩ ⟨6, by omega⟩)))))))))

theorem realize_piSetAppNFEqF {v S A : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) S) A) (pt : V))
        piSetAppNFEqF ↔
      v = piSetAppNF S A := by
  have hAm : ∀ z w x y : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) S) A) (pt : V)) z) w) x) y)
          (Form.relabel psAmMap appMemF) ↔ y ∈ˢ app S x := by
    intro z w x y
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) S) A) (pt : V)) z) w) x) y : Fin 8 → V) ∘ psAmMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => y) S) x) (pt : V) := by
      funext ⟨k, hk⟩
      have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_appMemF
  have hKp1 : ∀ z w x y : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) S) A) (pt : V)) z) w) x) y)
          (Form.relabel psKp1Map kpairEqF) ↔ w = kpair x y := by
    intro z w x y
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) S) A) (pt : V)) z) w) x) y : Fin 8 → V) ∘ psKp1Map =
        Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) y := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_kpairEqF
  have hKp2 : ∀ z x y p : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) S) A) (pt : V)) z) x) y) p)
          (Form.relabel psKp2Map kpairEqF) ↔ p = kpair x y := by
    intro z x y p
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) S) A) (pt : V)) z) x) y) p : Fin 8 → V) ∘ psKp2Map =
        Form.snoc (Form.snoc (fun _ : Fin 1 => p) x) y := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_kpairEqF
  have hKp3 : ∀ z x y y' p' : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) S) A) (pt : V)) z) x) y) y') p')
          (Form.relabel psKp3Map kpairEqF) ↔ p' = kpair x y' := by
    intro z x y y' p'
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) S) A) (pt : V)) z) x) y) y') p' : Fin 9 → V) ∘ psKp3Map =
        Form.snoc (Form.snoc (fun _ : Fin 1 => p') x) y' := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_kpairEqF
  have key : ∀ z : V, z ∈ˢ piSetAppNF S A ↔
      (∀ w, w ∈ˢ z → ∃ x, x ∈ˢ A ∧ ∃ y, y ∈ˢ app S x ∧ w = kpair x y) ∧
      (∀ x, x ∈ˢ A → ∃ y, (∃ p, p = kpair x y ∧ p ∈ˢ z) ∧
        ∀ y', (∃ p', p' = kpair x y' ∧ p' ∈ˢ z) → y' = y) := by
    intro z
    rw [mem_piSetAppNF]
    constructor
    · rintro ⟨hsub, hfun⟩
      constructor
      · intro w hw
        exact mem_sigmaPairsAppF.mp (hsub w hw)
      · intro x hx
        obtain ⟨y, hky, huniq⟩ := hfun x hx
        exact ⟨y, ⟨kpair x y, rfl, hky⟩,
          fun y' h => huniq y' (by obtain ⟨p', hp', hz'⟩ := h; rw [← hp']; exact hz')⟩
    · rintro ⟨hsub, hfun⟩
      constructor
      · intro w hw
        exact mem_sigmaPairsAppF.mpr (hsub w hw)
      · intro x hx
        obtain ⟨y, ⟨p, hp, hz⟩, huniq⟩ := hfun x hx
        exact ⟨y, by rw [← hp]; exact hz,
          fun y' hy' => huniq y' ⟨kpair x y', rfl, hy'⟩⟩
  simp only [piSetAppNFEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, Form.realize_imp, Form.realize_equal,
    hAm, hKp1, hKp2, hKp3, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (key z).symm
  · intro h z
    rw [h]
    exact key z



/-! ## Stage 105: the `sigmaConstGraphF` equality reader `sigmaConstGraphEqF` -/

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ z'`, `1 ↦ x'`, `2 ↦ y'`)
into the bound context `(v, A, D, pt, z, x, w)`: `0 ↦ 4`, `1 ↦ 5`,
`2 ↦ 6` (reads `z = kpair x w`). -/
def scgKpMap : Fin 3 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨4, by omega⟩ | 1 => ⟨5, by omega⟩ | _ => ⟨6, by omega⟩

/-- Map of the `sigmaConstEqF` conjunct (vars `0 ↦ x'`, `1 ↦ z'`, `2 ↦ A'`)
into the bound context `(v, A, D, pt, z, x, w)`: `0 ↦ 5`, `1 ↦ 6`,
`2 ↦ 1` (reads `w = sigmaConstF A x`). -/
def scgScMap : Fin 3 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨5, by omega⟩ | 1 => ⟨6, by omega⟩ | _ => ⟨1, by omega⟩

/-- The `sigmaConstGraphF` equality reader (variables `0 ↦ v`, `1 ↦ A`,
`2 ↦ D`, `3 ↦ pt`): `v = sigmaConstGraphF A D`, by extensionality +
`mem_sigmaConstGraphF`, with `z = kpair x w` read by `kpairEqF` and
`w = sigmaConstF A x` by `sigmaConstEqF`. -/
def sigmaConstGraphEqF : Form 4 :=
  .all (.iff (.mem ⟨4, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨5, by omega⟩ ⟨2, by omega⟩)
      (.ex (.and (Form.relabel scgKpMap kpairEqF) (Form.relabel scgScMap sigmaConstEqF))))))

theorem realize_sigmaConstGraphEqF {v A D : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) A) D) (pt : V))
        sigmaConstGraphEqF ↔
      v = sigmaConstGraphF A D := by
  have hKp : ∀ z x w : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) A) D) (pt : V)) z) x) w)
          (Form.relabel scgKpMap kpairEqF) ↔ z = kpair x w := by
    intro z x w
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) A) D) (pt : V)) z) x) w : Fin 7 → V) ∘ scgKpMap =
        Form.snoc (Form.snoc (fun _ : Fin 1 => z) x) w := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_kpairEqF
  have hSc : ∀ z x w : V,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
            (fun _ : Fin 1 => v) A) D) (pt : V)) z) x) w)
          (Form.relabel scgScMap sigmaConstEqF) ↔ w = sigmaConstF A x := by
    intro z x w
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (fun _ : Fin 1 => v) A) D) (pt : V)) z) x) w : Fin 7 → V) ∘ scgScMap =
        Form.cons2 x w (fun _ : Fin 1 => A) := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_sigmaConstEqF
  have key : ∀ z : V, z ∈ˢ sigmaConstGraphF A D ↔
      ∃ x, x ∈ˢ D ∧ ∃ w, z = kpair x w ∧ w = sigmaConstF A x := by
    intro z
    rw [mem_sigmaConstGraphF]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, sigmaConstF A x, rfl, rfl⟩
    · rintro ⟨x, hx, w, rfl, rfl⟩
      exact ⟨x, hx, rfl⟩
  simp only [sigmaConstGraphEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hKp, hSc, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (key z).symm
  · intro h z
    rw [h]
    exact key z


end ConLeche.SetTheory
