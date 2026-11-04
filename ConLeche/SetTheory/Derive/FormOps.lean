module

public import ConLeche.SetTheory.Derive.Universe

@[expose] public section

/-!
# Definable (first-order) set notions

Encodings of the basic set-theoretic predicates as `Form`s of the
language `L = {∈}` (`ConLeche.Form`), each with a `Realize` lemma ---
the toolkit for migrating the `sep`/`image` call sites to the
definable `sepF`/`imageF` (`Derive/Sep.lean`).  First-order ZFC supplies
replacement only for *definable* relations
(`ConLecheBridge.replF_of_ZFC_model`), so every set construction must
eventually be phrased by a `Form` plus parameters; this file starts the
library of encodings with the notions around `ω` (`Derive/Omega.lean`):
`emptyF`, `subsetF`, `inductiveF`, `omegaF`.

The set-level primitives `vsucc` and `Inductive` live here (moved from
`Derive/Omega.lean`) so the encodings can be related to them by
`Realize` lemmas.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The von Neumann successor `n ∪ {n}`. -/
noncomputable def vsucc (n : V) : V := binUnion n (sing n)

theorem mem_vsucc {z n : V} : z ∈ˢ vsucc n ↔ z ∈ˢ n ∨ z = n := by
  rw [vsucc, mem_binUnion, mem_sing]

theorem self_mem_vsucc (n : V) : n ∈ˢ vsucc n := mem_vsucc.mpr (Or.inr rfl)

theorem vsucc_ne_empty (n : V) : vsucc n ≠ empty :=
  ne_empty_of_mem (self_mem_vsucc n)

/-- An inductive set: contains `∅`, closed under the successor. -/
def Inductive (I : V) : Prop :=
  (empty : V) ∈ˢ I ∧ ∀ n, n ∈ˢ I → vsucc n ∈ˢ I

/-! ## Definable encodings -/

/-- `x` is empty: `∀ w, w ∉ x`. -/
def emptyF : Form 1 := .all (.not (.mem ⟨1, by omega⟩ ⟨0, by omega⟩))

theorem realize_emptyF {x : V} :
    Form.Realize Mem (Form.snoc Form.nil x) emptyF ↔ ∀ w, ¬ w ∈ˢ x := by
  simp only [emptyF, Form.realize_all, Form.realize_not, Form.realize_mem, Form.snoc_mk]
  simp

/-- `x ⊆ y`: `∀ w, w ∈ x → w ∈ y` (variable `0` is `x`, variable `1` is `y`). -/
def subsetF : Form 2 :=
  .all (.imp (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
      (.mem ⟨2, by omega⟩ ⟨1, by omega⟩))

theorem realize_subsetF {x y : V} :
    Form.Realize Mem (Form.snoc (fun _ => x) y) subsetF ↔ x ⊆ˢ y := by
  simp only [subsetF, SetTheory.Subset, Form.realize_all, Form.realize_imp,
    Form.realize_mem, Form.snoc_mk]
  simp

/-- `x` is inductive, in raw first-order form: some member of `x` is
empty, and every member `n` of `x` has a member `s` whose members are
exactly `w ∈ n ∨ w = n` (i.e. `s = n ∪ {n}`). -/
def inductiveF : Form 1 :=
  .and
    (.ex (.and (.mem ⟨1, by omega⟩ ⟨0, by omega⟩)
        (.all (.not (.mem ⟨2, by omega⟩ ⟨1, by omega⟩)))))
    (.all (.imp (.mem ⟨1, by omega⟩ ⟨0, by omega⟩)
        (.ex (.and (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
            (.all (.iff (.mem ⟨3, by omega⟩ ⟨2, by omega⟩)
                (.or (.mem ⟨3, by omega⟩ ⟨1, by omega⟩)
                  (.equal ⟨3, by omega⟩ ⟨1, by omega⟩))))))))

theorem realize_inductiveF {x : V} :
    Form.Realize Mem (Form.snoc Form.nil x) inductiveF ↔
      (∃ e, e ∈ˢ x ∧ ∀ w, ¬ w ∈ˢ e) ∧
      ∀ n, n ∈ˢ x → ∃ s, s ∈ˢ x ∧ ∀ w, w ∈ˢ s ↔ (w ∈ˢ n ∨ w = n) := by
  simp only [inductiveF, Form.realize_and, Form.realize_ex, Form.realize_all,
    Form.realize_imp, Form.realize_not, Form.realize_mem, Form.realize_iff,
    Form.realize_or, Form.realize_equal, Form.snoc_mk]
  simp

theorem inductive_iff_realize {I : V} :
    Inductive I ↔ Form.Realize Mem (Form.snoc Form.nil I) inductiveF := by
  rw [realize_inductiveF]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨empty, h1, not_mem_empty⟩, fun n hn => ⟨vsucc n, h2 n hn, fun w => ?_⟩⟩
    rw [mem_vsucc]
  · rintro ⟨⟨e, he, hempty⟩, h2⟩
    refine ⟨?_, fun n hn => ?_⟩
    · have heq : e = empty := eq_empty hempty
      rw [← heq]; exact he
    · obtain ⟨s, hs, hsm⟩ := h2 n hn
      have hsv : s = vsucc n := by
        refine SetTheory.ext fun w => ?_
        rw [mem_vsucc]
        exact hsm w
      rw [← hsv]; exact hs

omit [SetTheory V] in
theorem snoc_relabel_succ {n : V} (I : V) :
    (Form.snoc (fun _ => n) I) ∘ (fun _ => (⟨1, by omega⟩ : Fin 2)) =
      Form.snoc Form.nil I := by
  funext ⟨k, hk⟩
  have hk0 : k = 0 := by omega
  subst hk0
  show Form.snoc (fun _ => n) I (⟨1, by omega⟩ : Fin 2) = Form.snoc Form.nil I ⟨0, hk⟩
  simp only [Form.snoc_mk]
  simp

/-- `n` belongs to every inductive set: `∀ I, inductiveF I → n ∈ I`. -/
def omegaF : Form 1 :=
  .all (.imp (Form.relabel (fun _ => (⟨1, by omega⟩ : Fin 2)) inductiveF)
      (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))

theorem realize_omegaF {n : V} :
    Form.Realize Mem (Form.snoc Form.nil n) omegaF ↔ ∀ I, Inductive I → n ∈ˢ I := by
  have hrel : ∀ I : V, Form.Realize Mem (Form.snoc (fun _ => n) I)
      (Form.relabel (fun _ => (⟨1, by omega⟩ : Fin 2)) inductiveF) ↔ Inductive I := by
    intro I
    rw [Form.realize_relabel, snoc_relabel_succ]
    exact inductive_iff_realize.symm
  simp only [Form.snoc_nil, omegaF, Form.realize_all, Form.realize_imp, hrel,
    Form.realize_mem, Form.snoc_mk]
  simp

end ConLeche.SetTheory
