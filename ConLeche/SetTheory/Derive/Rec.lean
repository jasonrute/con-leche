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

end ConLeche.SetTheory
