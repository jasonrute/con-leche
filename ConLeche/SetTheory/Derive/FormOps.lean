module

public import ConLeche.SetTheory.Derive.Pair

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

/-! ## Kuratowski pairs -/

/-- `z = ⟨x, y⟩` in raw first-order form (variables `0 ↦ z`,
`1 ↦ x`, `2 ↦ y`): `z = {s, t}` with `s = {x}` and `t = {x, y}`. -/
def kpairEqF : Form 3 :=
  .ex (.and (.mem ⟨3, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨4, by omega⟩ ⟨0, by omega⟩)
      (.and (.all (.iff (.mem ⟨5, by omega⟩ ⟨3, by omega⟩)
            (.equal ⟨5, by omega⟩ ⟨1, by omega⟩)))
        (.and (.all (.iff (.mem ⟨5, by omega⟩ ⟨4, by omega⟩)
              (.or (.equal ⟨5, by omega⟩ ⟨1, by omega⟩)
                (.equal ⟨5, by omega⟩ ⟨2, by omega⟩))))
          (.all (.imp (.mem ⟨5, by omega⟩ ⟨0, by omega⟩)
              (.or (.equal ⟨5, by omega⟩ ⟨3, by omega⟩)
                (.equal ⟨5, by omega⟩ ⟨4, by omega⟩)))))))))

theorem realize_kpairEqF {z x y : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ => z) x) y) kpairEqF ↔
      z = kpair x y := by
  simp only [kpairEqF, Form.realize_ex, Form.realize_and, Form.realize_mem,
    Form.realize_all, Form.realize_iff, Form.realize_equal, Form.realize_imp,
    Form.realize_or, Form.snoc_mk]
  simp
  constructor
  · rintro ⟨s, hs, t, ht, hseq, hut, hall⟩
    have hsx : s = sing x :=
      SetTheory.ext fun u => (hseq u).trans (mem_sing (a := x)).symm
    have htx : t = upair x y :=
      SetTheory.ext fun u => (hut u).trans (mem_upair (a := x) (b := y)).symm
    have hz : z = upair s t :=
      SetTheory.ext fun w =>
        ⟨fun h => mem_upair.mpr (hall w h), fun h => by
          rcases mem_upair.mp h with rfl | rfl
          · exact hs
          · exact ht⟩
    rw [hz, hsx, htx, kpair]
  · intro h
    rw [h]
    exact ⟨sing x, mem_upair_left _ _, upair x y, mem_upair_right _ _,
      fun u => mem_sing, fun u => mem_upair, fun w hw => mem_upair.mp hw⟩

/-- Variable map `Fin 3 → Fin 4` for `kpairMemF`: `(z, x, y) ↦ (3, 0, 2)`. -/
def kpairMemMap : Fin 3 → Fin 4 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨0, by omega⟩
  | _ => ⟨2, by omega⟩

/-- `⟨a, y⟩ ∈ f` (variables `0 ↦ a`, `1 ↦ f`, `2 ↦ y`). -/
def kpairMemF : Form 3 :=
  .ex (.and (.mem ⟨3, by omega⟩ ⟨1, by omega⟩)
      (Form.relabel kpairMemMap kpairEqF))

theorem realize_kpairMemF {a f y : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ => a) f) y) kpairMemF ↔
      kpair a y ∈ˢ f := by
  have hcomp : ∀ z : V, (Form.snoc (Form.snoc (Form.snoc (fun _ => a) f) y) z) ∘ kpairMemMap =
      Form.snoc (Form.snoc (fun _ => z) a) y := by
    intro z
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
  simp only [kpairMemF, Form.realize_ex, Form.realize_and, Form.realize_mem,
    Form.realize_relabel, hcomp, realize_kpairEqF]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact hz
  · intro h; exact ⟨kpair a y, h, rfl⟩

/-- Variable map `Fin 3 → Fin 3`, `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 0`, turning
`kpairEqF` into the replacement convention. -/
def kpairSwapMap : Fin 3 → Fin 3 := fun i =>
  match i.val with
  | 0 => ⟨1, by omega⟩
  | 1 => ⟨2, by omega⟩
  | _ => ⟨0, by omega⟩

/-- `z = kpair a x` in the replacement convention (variables `0 ↦ x`,
`1 ↦ z`, parameter `2 ↦ a`). -/
def kpairEqF' : Form 3 := Form.relabel kpairSwapMap kpairEqF

theorem realize_kpairEqF' {x z a : V} :
    Form.Realize Mem (Form.cons2 x z (fun _ => a)) kpairEqF' ↔ z = kpair a x := by
  have h : Form.cons2 x z (fun _ => a) = (Form.snoc (Form.snoc (fun _ => x) z) a : Fin 3 → V) := by
    funext ⟨k, hk⟩
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl <;> rfl
  rw [h]
  have hcomp : (Form.snoc (Form.snoc (fun _ => x) z) a : Fin 3 → V) ∘ kpairSwapMap =
      (Form.snoc (Form.snoc (fun _ => z) a) x : Fin 3 → V) := by
    funext ⟨k, hk⟩
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl <;> rfl
  simp only [kpairEqF', Form.realize_relabel, hcomp, realize_kpairEqF]

/-- Variable map `Fin 3 ↦ Fin 5`, `0 ↦ 2`, `1 ↦ 3`, `2 ↦ 4` (reads
`kpairEqF`'s `(z, x, y)` out of the context `(A, c, z, x, y)`). -/
def sigmaConstMap : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨3, by omega⟩
  | _ => ⟨4, by omega⟩

/-- `z` is a pair ⟨x, y⟩ with `x ∈ˢ A` and `y ∈ˢ c` (variables
`0 ↦ A`, `1 ↦ c`, bound `2 ↦ z`, then bound `3 ↦ x`, `4 ↦ y`). -/
def sigmaConstForm : Form 3 :=
  .ex (.ex (.and (Form.relabel sigmaConstMap kpairEqF)
    (.and (.mem ⟨3, by omega⟩ ⟨0, by omega⟩) (.mem ⟨4, by omega⟩ ⟨1, by omega⟩))))

theorem realize_sigmaConstForm {A c z : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ => A) c) z) sigmaConstForm ↔
      ∃ x, x ∈ˢ A ∧ ∃ y, y ∈ˢ c ∧ z = kpair x y := by
  have hcomp : ∀ x y : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => A) c) z) x) y) ∘ sigmaConstMap =
        Form.snoc (Form.snoc (fun _ => z) x) y := by
    intro x y
    funext ⟨k, hk⟩
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl <;> rfl
  simp only [sigmaConstForm, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hcomp, realize_kpairEqF, Form.realize_mem, Form.snoc_mk]
  constructor
  · rintro ⟨x, y, h, hx, hy⟩; exact ⟨x, hx, y, hy, h⟩
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨x, y, rfl, hx, hy⟩

/-! ## Total single-valued graphs (`piSet`) -/

/-- Variable map `Fin 2 → Fin 3`, `0 ↦ 2`, `1 ↦ 1` (used to read
`(x, f)` out of the context `(A, f, x)`). -/
def piMap1 : Fin 2 → Fin 3 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | _ => ⟨1, by omega⟩

/-- Variable map `Fin 2 → Fin 4`, `0 ↦ 2`, `1 ↦ 1` (used to read
`(x, f)` out of the context `(A, f, x, y, y')`). -/
def piMap2 : Fin 2 → Fin 4 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | _ => ⟨1, by omega⟩

/-- `f` is a total single-valued graph over `A` (variables `0 ↦ A`,
`1 ↦ f`): every `x ∈ A` has a unique `y` with `⟨x, y⟩ ∈ f`. -/
def piSetF : Form 2 :=
  .all (.imp (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (Form.relabel (Form.liftRelabel piMap1) kpairMemF)
        (.all (.imp (Form.relabel (Form.liftRelabel piMap2) kpairMemF)
            (.equal ⟨4, by omega⟩ ⟨3, by omega⟩))))))

theorem realize_piSetF {A f : V} :
    Form.Realize Mem (Form.snoc (fun _ => A) f) piSetF ↔
      ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y := by
  have e1 : ∀ x y : V,
      (Form.snoc (Form.snoc (Form.snoc (fun _ => A) f) x) y) ∘ Form.liftRelabel piMap1 =
        Form.snoc (Form.snoc (fun _ => x) f) y := by
    intro x y
    rw [Form.snoc_comp_liftRelabel]
    congr 1
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have e2 : ∀ x y y' : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => A) f) x) y) y') ∘ Form.liftRelabel piMap2 =
        Form.snoc (Form.snoc (fun _ => x) f) y' := by
    intro x y y'
    rw [Form.snoc_comp_liftRelabel]
    congr 1
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [piSetF, Form.realize_all, Form.realize_imp, Form.realize_ex,
    Form.realize_and, Form.realize_relabel, e1, e2, realize_kpairMemF,
    Form.realize_equal, Form.realize_mem, Form.snoc_mk]
  simp

/-! ## Equality and strictness -/

/-- `a = b` as a formula (variables `0 ↦ a`, `1 ↦ b`), by
extensionality: `∀ w, w ∈ a ↔ w ∈ b`. -/
def equalF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
      (.mem ⟨2, by omega⟩ ⟨1, by omega⟩))

theorem realize_equalF {a b : V} :
    Form.Realize Mem (Form.snoc (fun _ => a) b) equalF ↔ a = b := by
  simp only [equalF, Form.realize_all, Form.realize_iff, Form.realize_mem, Form.snoc_mk]
  simp
  constructor
  · exact SetTheory.ext
  · intro h; subst h; simp

/-- `X` is strict (variables `0 ↦ pt`, `1 ↦ X`): `X ≠ pt` and
`pt ∉ X`. -/
def strictF : Form 2 :=
  .and (.not equalF) (.not (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))

theorem realize_strictF {p X : V} :
    Form.Realize Mem (Form.snoc (fun _ => p) X) strictF ↔ X ≠ p ∧ ¬ p ∈ˢ X := by
  simp only [strictF, Form.realize_and, Form.realize_not, equalF,
    Form.realize_all, Form.realize_iff, Form.realize_mem, Form.snoc_mk]
  simp
  intro h2
  constructor
  · rintro ⟨w, hw⟩ hEq
    subst hEq
    exact hw Iff.rfl
  · intro hne
    refine Classical.byContradiction fun hc => ?_
    apply hne
    exact (SetTheory.ext fun w => Classical.not_not.mp fun h => hc ⟨w, h⟩).symm

/-- `X` is a type (variables `0 ↦ univZero`, `1 ↦ pt`, `2 ↦ X`):
a truth value or strict. -/
def tyF : Form 3 :=
  .or (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
    (Form.relabel (Form.liftRelabel (fun _ => (⟨1, by omega⟩ : Fin 2))) strictF)

theorem realize_tyF {U p X : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ => U) p) X) tyF ↔
      X ∈ˢ U ∨ X ≠ p ∧ ¬ p ∈ˢ X := by
  have e : ∀ X : V, (Form.snoc (Form.snoc (fun _ => U) p) X) ∘
      (Form.liftRelabel (fun _ => (⟨1, by omega⟩ : Fin 2)) : Fin 2 → Fin 3) =
      Form.snoc (fun _ => p) X := by
    intro X
    rw [Form.snoc_comp_liftRelabel]
    congr 1
  simp only [tyF, Form.realize_or, Form.realize_mem, Form.realize_relabel, e,
    realize_strictF, Form.snoc_mk]
  simp

/-- `z ∈ b` as a formula (variables `0 ↦ b`, `1 ↦ z`): the
membership atom with a parameter. -/
def memPF : Form 2 := .mem ⟨1, by omega⟩ ⟨0, by omega⟩

theorem realize_memPF {b z : V} :
    Form.Realize Mem (Form.snoc (fun _ => b) z) memPF ↔ z ∈ˢ b := by
  simp only [memPF, Form.realize_mem, Form.snoc_mk]
  simp

/-- `y = vsucc x` as a formula (variables `0 ↦ x`, `1 ↦ y`), by
extensionality: `∀ w, w ∈ y ↔ w ∈ x ∨ w = x`. -/
def vsuccEqMap : Fin 2 → Fin 3 :=
  fun i => if i.val = 0 then ⟨2, by omega⟩ else ⟨0, by omega⟩

def vsuccF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨1, by omega⟩)
    (.or (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
      (Form.relabel vsuccEqMap equalF)))

theorem realize_vsuccF {x y : V} :
    Form.Realize Mem (Form.cons2 x y Form.nil) vsuccF ↔ y = vsucc x := by
  have h : Form.cons2 x y Form.nil = Form.snoc (fun _ => x) y := by
    funext ⟨k, hk⟩
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl <;> rfl
  rw [h]
  have hg : ∀ w : V, (Form.snoc (Form.snoc (fun _ => x) y) w) ∘ vsuccEqMap =
      Form.snoc (fun _ => w) x := by
    intro w
    funext ⟨k, hk⟩
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl <;> rfl
  have hEq : ∀ w x : V, (w = x) ↔ ∀ w', w' ∈ˢ w ↔ w' ∈ˢ x :=
    fun w x => ⟨fun h w' => by rw [h], fun h => SetTheory.ext h⟩
  have hVs : y = vsucc x ↔ ∀ w, w ∈ˢ y ↔ w ∈ˢ x ∨ w = x :=
    ⟨fun h w => by rw [h, mem_vsucc],
      fun h => SetTheory.ext fun w => (h w).trans mem_vsucc.symm⟩
  simp only [vsuccF, Form.realize_all, Form.realize_iff, Form.realize_or,
    Form.realize_mem, Form.realize_relabel, hg, equalF, Form.realize_all,
    Form.realize_iff, Form.snoc_mk]
  simp
  simp only [← hEq, hVs]

end ConLeche.SetTheory
