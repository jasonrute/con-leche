module

public import ConLeche.SetTheory.Derive.Univ
public import ConLeche.SetTheory.Derive.Rec

@[expose] public section

/-!
# Quotients

`quotSet u A R` is, for `u ≠ 0`, the set of equivalence classes of the
equivalence closure of "`app (app R a) b` is inhabited" on `A` (classes
by definable separation `qclassF`, the class set by definable
replacement `imageF` — no meta-level scheme), each class **tagged** as
the pair `kpair ∅ (qclass A R a)` (task #342: a raw class can be the
point, see the end of the file; a tagged one is a pair, so the quotient
is strict); for `u = 0` the base
lives in `Prop`, everything collapses to the proof point, and the
quotient is `constImageF pt A` — the truth value `[A inhabited]`.

The lift (`quotLiftR`, `SetModel/Value.lean`) lifts `f` to the quotient as the graph of
`q ↦ app f (representative of q)` (representatives by choice) — except
when `f` is the proof point, where the lift is the proof point too.
That tag is what makes the beta law `app (quotLiftR …) (quotClass … a) =
app f a` hold with *no typing premise on `f`* (matching the interface):
a `pt`-tagged `f` beta-reduces to `pt` on both sides, any other `f`
goes through the representative and the invariance premise, with the
`u = 0` collapse handled by `A ⊆ {pt}` (from `A ∈ univ 0`).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The equivalence closure, on `A`, of "`app (app R a) b` is
inhabited". -/
inductive QuotRel (A R : V) : V → V → Prop where
  | base {a b : V} : a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) →
      QuotRel A R a b
  | refl {a : V} : a ∈ˢ A → QuotRel A R a a
  | symm {a b : V} : QuotRel A R a b → QuotRel A R b a
  | trans {a b c : V} : QuotRel A R a b → QuotRel A R b c → QuotRel A R a c

/-! ## The equivalence closure as a first-order formula -/

/- The class of `a` (`qclass`, defined below as the *definable* class
`qclassF`) is introduced after `qsatF`, its first-order formula. -/

/-- The generating step of `QuotRel`: `x ∈ˢ A ∧ y ∈ˢ A ∧ ∃ w, w ∈ˢ app (app R x) y`. -/
def qstep (A R x y : V) : Prop :=
  x ∈ˢ A ∧ y ∈ˢ A ∧ ∃ w, w ∈ˢ app (app R x) y

/-- Variable map `Fin 4 → Fin 10` reading `appEqF`'s `(pt, v, g, u)` as `(A, R, a, pt, b, S, x, y, w, g')`: `0 ↦ 3`, `1 ↦ 9`, `2 ↦ 1`, `3 ↦ 6`. -/
def qsatEqMap : Fin 4 → Fin 10 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨9, by omega⟩
  | 2 => ⟨1, by omega⟩
  | _ => ⟨6, by omega⟩

/-- Variable map `Fin 4 → Fin 10` reading `appMemF`'s `(w, g, u, pt)` as `(A, R, a, pt, b, S, x, y, w, g')`: `0 ↦ 8`, `1 ↦ 9`, `2 ↦ 7`, `3 ↦ 3`. -/
def qsatMemMap : Fin 4 → Fin 10 := fun i =>
  match i.val with
  | 0 => ⟨8, by omega⟩
  | 1 => ⟨9, by omega⟩
  | 2 => ⟨7, by omega⟩
  | _ => ⟨3, by omega⟩

/-- The generating step as a `Form 8` (variables `0 ↦ A`, `1 ↦ R`, `3 ↦ pt`, `6 ↦ x`, `7 ↦ y`; bound `8 ↦ w`, `9 ↦ g'`). -/
def qsatStepF : Form 8 :=
  .and (.mem ⟨6, by omega⟩ ⟨0, by omega⟩)
    (.and (.mem ⟨7, by omega⟩ ⟨0, by omega⟩)
      (.ex (.ex (.and (Form.relabel qsatEqMap appEqF) (Form.relabel qsatMemMap appMemF)))))

/-- Variable map `Fin 8 → Fin 8` swapping `6` and `7` (for the backward step). -/
def qsatSwapMap : Fin 8 → Fin 8 := fun i =>
  if i.val = 6 then ⟨7, by omega⟩ else if i.val = 7 then ⟨6, by omega⟩ else i

/-- The class formula's parameters: `0 ↦ A`, `1 ↦ R`, `2 ↦ a`, `3 ↦ pt`. -/
noncomputable def qclassParam (A R a : V) : Fin 4 → V := fun i =>
  match i.val with
  | 0 => A
  | 1 => R
  | 2 => a
  | _ => (pt : V)

theorem realize_qsatStepF {A R a b S x y : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc (qclassParam A R a) b) S) x) y) qsatStepF ↔ qstep A R x y := by
  have hE : ∀ w g' : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (qclassParam A R a) b) S) x) y) w) g') ∘ qsatEqMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ => (pt : V)) g') R) x := by
    intro w g'
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hM : ∀ w g' : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (qclassParam A R a) b) S) x) y) w) g') ∘ qsatMemMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ => w) g') y) (pt : V) := by
    intro w g'
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [qsatStepF, Form.realize_and, Form.realize_mem, Form.realize_ex,
    Form.realize_relabel, hE, hM, realize_appEqF, realize_appMemF, Form.snoc_mk,
    qclassParam, qstep]
  constructor
  · rintro ⟨hxA, hyA, w, g', rfl, hw⟩
    exact ⟨hxA, hyA, w, hw⟩
  · rintro ⟨hxA, hyA, w, hw⟩
    exact ⟨hxA, hyA, w, app R x, rfl, hw⟩

/-- The saturated-set characterization of `QuotRel A R a b`, as a `Form 5` (variables `0 ↦ A`, `1 ↦ R`, `2 ↦ a`, `3 ↦ pt`, bound `4 ↦ b`): `a ∈ˢ A ∧ ∀ S, S ⊆ˢ A → a ∈ˢ S → (∀ x y, x ∈ˢ S → (qstep A R x y ∨ qstep A R y x) → y ∈ˢ S) → b ∈ˢ S`. -/
def qsatF : Form 5 :=
  .and (.mem ⟨2, by omega⟩ ⟨0, by omega⟩) (.all (.imp (.all (.imp (.mem ⟨6, by omega⟩ ⟨5, by omega⟩) (.mem ⟨6, by omega⟩ ⟨0, by omega⟩))) (.imp (.mem ⟨2, by omega⟩ ⟨5, by omega⟩) (.imp (.all (.all (.imp (.mem ⟨6, by omega⟩ ⟨5, by omega⟩) (.imp (.or qsatStepF (Form.relabel qsatSwapMap qsatStepF)) (.mem ⟨7, by omega⟩ ⟨5, by omega⟩))))) (.mem ⟨4, by omega⟩ ⟨5, by omega⟩)))))

theorem realize_qsatF {A R a b : V} :
    Form.Realize Mem (Form.snoc (qclassParam A R a) b) qsatF ↔
      a ∈ˢ A ∧ ∀ S : V, S ⊆ˢ A → a ∈ˢ S →
        (∀ x y : V, x ∈ˢ S → (qstep A R x y ∨ qstep A R y x) → y ∈ˢ S) → b ∈ˢ S := by
  have hSw : ∀ S x y : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (qclassParam A R a) b) S) x) y) ∘ qsatSwapMap = Form.snoc (Form.snoc (Form.snoc (Form.snoc (qclassParam A R a) b) S) y) x := by
    intro S x y
    funext ⟨k, hk⟩
    have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [qsatF, Form.realize_and, Form.realize_mem, Form.realize_all,
    Form.realize_imp, Form.realize_or, Form.realize_relabel, hSw,
    realize_qsatStepF, Form.snoc_mk, qclassParam, SetTheory.Subset]
  simp

/-- The equivalence closure implies the saturated-set characterization.
Only this direction is available without the meta-level scheme: the
converse (`qsat → QuotRel`) is false in nonstandard models, so the class
`qclassF` below is characterized by `qsatF` alone. -/
theorem quotRel_qsat {A R a b : V} (h : QuotRel A R a b) :
    a ∈ˢ A ∧ ∀ S : V, S ⊆ˢ A → a ∈ˢ S →
      (∀ x y : V, x ∈ˢ S → (qstep A R x y ∨ qstep A R y x) → y ∈ˢ S) → b ∈ˢ S := by
  have key : ∀ a' b' : V, QuotRel A R a' b' →
      a' ∈ˢ A ∧ b' ∈ˢ A ∧ ∀ S : V,
        (∀ x y : V, x ∈ˢ S → (qstep A R x y ∨ qstep A R y x) → y ∈ˢ S) →
        (a' ∈ˢ S ↔ b' ∈ˢ S) := by
    intro a' b' h'
    induction h' with
    | base ha hb hw => exact ⟨ha, hb, fun S hcl => ⟨fun h => hcl _ _ h (Or.inl ⟨ha, hb, hw⟩), fun h => hcl _ _ h (Or.inr ⟨ha, hb, hw⟩)⟩⟩
    | refl ha => exact ⟨ha, ha, fun S hcl => Iff.rfl⟩
    | symm _ ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      exact ⟨h2, h1, fun S hcl => (h3 S hcl).symm⟩
    | trans _ _ ih1 ih2 =>
      obtain ⟨h1, h2, h3⟩ := ih1
      obtain ⟨h4, h5, h6⟩ := ih2
      exact ⟨h1, h5, fun S hcl => (h3 S hcl).trans (h6 S hcl)⟩
  obtain ⟨ha, hb, hiff⟩ := key a b h
  exact ⟨ha, fun S hSA haS hcl => (hiff S hcl).mp haS⟩

/-- The class of `a` in `A` by *definable* separation: the first-order
class `sepF A qsatF (qclassParam A R a)`.  This is what `qclass` (below)
is defined as — no meta-level `sep` anywhere. -/
noncomputable def qclassF (A R a : V) : V := sepF A qsatF (qclassParam A R a)

/-- Membership in the definable class, read through `qsatF` alone (no
`QuotRel`, no meta-level scheme). -/
theorem mem_qclassF {A R a b : V} :
    b ∈ˢ qclassF A R a ↔ b ∈ˢ A ∧ Form.Realize Mem (Form.snoc (qclassParam A R a) b) qsatF := by
  rw [qclassF]
  exact mem_sepF

/-- `QuotRel` relates members of `A`. -/
theorem quotRel_mem {A R a b : V} (h : QuotRel A R a b) : a ∈ˢ A ∧ b ∈ˢ A := by
  induction h with
  | base ha hb _ => exact ⟨ha, hb⟩
  | refl ha => exact ⟨ha, ha⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩

/-- `QuotRel` implies the `qsatF` realization (the forward direction of
the old equivalence; the converse needs the meta-level scheme and is
false in nonstandard models). -/
theorem realize_qsatF_of_quotRel {A R a b : V} (h : QuotRel A R a b) :
    Form.Realize Mem (Form.snoc (qclassParam A R a) b) qsatF :=
  realize_qsatF.mpr (quotRel_qsat h)

theorem qclassF_subset {A R a : V} : qclassF A R a ⊆ˢ A := by
  rw [qclassF]
  exact sepF_subset

/-- A saturated point contains itself. -/
theorem self_realize_qsatF {A R a : V} (ha : a ∈ˢ A) :
    Form.Realize Mem (Form.snoc (qclassParam A R a) a) qsatF := by
  rw [realize_qsatF]
  exact ⟨ha, fun S _ haS _ => haS⟩

/-- Saturation is closed under a generating step, in both directions. -/
theorem realize_qsatF_step_closed {A R a x y : V}
    (hx : Form.Realize Mem (Form.snoc (qclassParam A R a) x) qsatF)
    (hstep : qstep A R x y ∨ qstep A R y x) :
    Form.Realize Mem (Form.snoc (qclassParam A R a) y) qsatF := by
  rw [realize_qsatF] at hx ⊢
  obtain ⟨haA, hsat⟩ := hx
  exact ⟨haA, fun S hSA haS hcl => hcl x y (hsat S hSA haS hcl) hstep⟩

theorem self_mem_qclassF {A R a : V} (ha : a ∈ˢ A) : a ∈ˢ qclassF A R a :=
  mem_qclassF.mpr ⟨ha, self_realize_qsatF ha⟩

theorem qclassF_step_closed {A R a x y : V} (hx : x ∈ˢ qclassF A R a)
    (hstep : qstep A R x y ∨ qstep A R y x) : y ∈ˢ qclassF A R a := by
  have hyA : y ∈ˢ A := by
    rcases hstep with ⟨-, h, -⟩ | ⟨h, -, -⟩ <;> exact h
  exact mem_qclassF.mpr
    ⟨hyA, realize_qsatF_step_closed (mem_qclassF.mp hx).2 hstep⟩

/-- **Symmetry of the definable class, repl-free**: the complement of a
saturated set is saturated (the generating steps are symmetric), so
`b ∈ˢ qclassF A R a` forces `a ∈ˢ qclassF A R b`. -/
theorem qclassF_symm {A R a b : V} (ha : a ∈ˢ A) (hb : b ∈ˢ qclassF A R a) :
    a ∈ˢ qclassF A R b := by
  obtain ⟨hbA, hreal⟩ := mem_qclassF.mp hb
  by_cases h : a ∈ˢ qclassF A R b
  · exact h
  · rw [mem_qclassF] at h
    have hnot : ¬ Form.Realize Mem (Form.snoc (qclassParam A R b) a) qsatF := by
      intro hr
      exact h ⟨ha, hr⟩
    have hSclosed : ∀ x y : V, x ∈ˢ sepF A (.not qsatF) (qclassParam A R b) →
        (qstep A R x y ∨ qstep A R y x) → y ∈ˢ sepF A (.not qsatF) (qclassParam A R b) := by
      intro x y hxS hor
      obtain ⟨hxA, hxnot⟩ := mem_sepF.mp hxS
      have hyA : y ∈ˢ A := by rcases hor with ⟨-, h, -⟩ | ⟨h, -, -⟩ <;> exact h
      refine mem_sepF.mpr ⟨hyA, ?_⟩
      rw [Form.realize_not]
      intro hyreal
      have hyT : y ∈ˢ qclassF A R b := mem_qclassF.mpr ⟨hyA, hyreal⟩
      have hxT : x ∈ˢ qclassF A R b := by
        rcases hor with hxy | hyx
        · exact qclassF_step_closed hyT (Or.inr hxy)
        · exact qclassF_step_closed hyT (Or.inl hyx)
      exact hxnot (mem_qclassF.mp hxT).2
    have haS : a ∈ˢ sepF A (.not qsatF) (qclassParam A R b) :=
      mem_sepF.mpr ⟨ha, by rw [Form.realize_not]; exact hnot⟩
    have hbS : b ∈ˢ sepF A (.not qsatF) (qclassParam A R b) :=
      (realize_qsatF.mp hreal).2 _ sepF_subset haS hSclosed
    obtain ⟨-, hbnot⟩ := mem_sepF.mp hbS
    rw [Form.realize_not] at hbnot
    exact absurd (mem_qclassF.mp (self_mem_qclassF hbA)).2 hbnot

/-- **Transitivity of the definable class, repl-free**. -/
theorem qclassF_trans {A R a b c : V} (hb : b ∈ˢ qclassF A R a) (hc : c ∈ˢ qclassF A R b) :
    c ∈ˢ qclassF A R a := by
  obtain ⟨-, hreal⟩ := mem_qclassF.mp hb
  obtain ⟨-, hreal'⟩ := mem_qclassF.mp hc
  obtain ⟨haA, hsat⟩ := realize_qsatF.mp hreal
  refine mem_qclassF.mpr ⟨(mem_qclassF.mp hc).1, realize_qsatF.mpr ⟨haA, ?_⟩⟩
  intro S hSA haS hcl
  exact (realize_qsatF.mp hreal').2 S hSA (hsat S hSA haS hcl) hcl

/-- Equal classes from a member: repl-free. -/
theorem qclassF_eq_of_mem {A R a b : V} (ha : a ∈ˢ A) (hb : b ∈ˢ qclassF A R a) :
    qclassF A R a = qclassF A R b :=
  have hsymm : a ∈ˢ qclassF A R b := qclassF_symm ha hb
  ext fun _ => ⟨fun hz => qclassF_trans hsymm hz, fun hz => qclassF_trans hb hz⟩

/-- Equal classes from a `QuotRel` step (via the forward `qsat` direction). -/
theorem qclassF_eq_of_rel {A R a b : V} (h : QuotRel A R a b) :
    qclassF A R a = qclassF A R b :=
  qclassF_eq_of_mem (quotRel_mem h).1
    (mem_qclassF.mpr ⟨(quotRel_mem h).2, realize_qsatF_of_quotRel h⟩)

/-! ## The saturation toolkit, without the meta-level scheme

The lemmas below read the definable class `qclassF = sepF A qsatF
(qclassParam A R a)` through `qsatF` alone — definable separation only,
no meta-level `sep`/`image`/`repl`: invariance of a base-relation
invariant function along a definable class (`app_eq_of_realize_qsatF`,
proved through the definable saturated set `sepF A appFixF
(appFixParam f a)`). -/

/-- Parameters of "the value at the element equals the value at `a`":
`0 ↦ f`, `1 ↦ a`, `2 ↦ pt`. -/
noncomputable def appFixParam (f a : V) : Fin 3 → V := fun i =>
  match i.val with
  | 0 => f
  | 1 => a
  | _ => (pt : V)

/-- Variable map `Fin 4 → Fin 5` reading `appEqF`'s `(pt, v, g, u)` out of
`(f, a, pt, x, v)` with the element `x` as the argument: `0 ↦ 2`,
`1 ↦ 4`, `2 ↦ 0`, `3 ↦ 3`. -/
def appFixXMap : Fin 4 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨4, by omega⟩
  | 2 => ⟨0, by omega⟩
  | _ => ⟨3, by omega⟩

/-- Variable map `Fin 4 → Fin 5` reading `appEqF`'s `(pt, v, g, u)` out of
`(f, a, pt, x, v)` with the fixed argument `a`: `0 ↦ 2`, `1 ↦ 4`,
`2 ↦ 0`, `3 ↦ 1`. -/
def appFixAMap : Fin 4 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨4, by omega⟩
  | 2 => ⟨0, by omega⟩
  | _ => ⟨1, by omega⟩

/-- `app f x = app f a` as a `Form 4` (parameters `0 ↦ f`, `1 ↦ a`,
`2 ↦ pt`, element variable `3 ↦ x`, bound `4 ↦ v`). -/
def appFixF : Form 4 :=
  .ex (.and (Form.relabel appFixXMap appEqF) (Form.relabel appFixAMap appEqF))

theorem realize_appFixF {f a x : V} :
    Form.Realize Mem (Form.snoc (appFixParam f a) x) appFixF ↔ app f x = app f a := by
  have hX : ∀ v : V,
      (Form.snoc (Form.snoc (appFixParam f a) x) v) ∘ appFixXMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ => (pt : V)) v) f) x := by
    intro v
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hA : ∀ v : V,
      (Form.snoc (Form.snoc (appFixParam f a) x) v) ∘ appFixAMap =
        Form.snoc (Form.snoc (Form.snoc (fun _ => (pt : V)) v) f) a := by
    intro v
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [appFixF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hX, hA, realize_appEqF]
  constructor
  · rintro ⟨v, hv1, hv2⟩
    exact hv1.symm.trans hv2
  · intro h
    exact ⟨app f x, rfl, h⟩

/-- **Invariance inside a definable class, repl-free**: a function
invariant under the base relation is constant on the `qsatF`-class of
`a`, read through the definable saturated set `sepF A appFixF
(appFixParam f a)`. -/
theorem app_eq_of_realize_qsatF {A R f a b : V}
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') → app f a' = app f b')
    (ha : a ∈ˢ A)
    (hb : Form.Realize Mem (Form.snoc (qclassParam A R a) b) qsatF) :
    app f b = app f a := by
  rw [realize_qsatF] at hb
  obtain ⟨-, hsat⟩ := hb
  have hS : b ∈ˢ sepF A appFixF (appFixParam f a) :=
    hsat (sepF A appFixF (appFixParam f a)) sepF_subset
      (mem_sepF.mpr ⟨ha, realize_appFixF.mpr rfl⟩)
      (fun x y hxS hor => by
        obtain ⟨-, hxeq⟩ := mem_sepF.mp hxS
        rw [realize_appFixF] at hxeq
        have hyA : y ∈ˢ A := by rcases hor with ⟨-, h, -⟩ | ⟨h, -, -⟩ <;> exact h
        rw [mem_sepF, realize_appFixF]
        rcases hor with ⟨hxA, -, hw⟩ | ⟨-, hxA, hw⟩
        · exact ⟨hyA, (hinv x y hxA hyA hw).symm.trans hxeq⟩
        · exact ⟨hyA, (hinv y x hyA hxA hw).trans hxeq⟩)
  rw [mem_sepF, realize_appFixF] at hS
  exact hS.2

/-- The same invariance at the definable class itself. -/
theorem app_eq_of_mem_qclassF {A R f a b : V}
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') → app f a' = app f b')
    (ha : a ∈ˢ A) (hb : b ∈ˢ qclassF A R a) : app f b = app f a :=
  app_eq_of_realize_qsatF hinv ha (mem_qclassF.mp hb).2

/-- The `QuotRel`-class of `a` in `A` — the definable class `qclassF`
(no meta-level `sep`). -/
noncomputable def qclass (A R a : V) : V := qclassF A R a

theorem mem_qclass {A R a b : V} :
    b ∈ˢ qclass A R a ↔ b ∈ˢ A ∧ Form.Realize Mem (Form.snoc (qclassParam A R a) b) qsatF :=
  mem_qclassF

theorem self_mem_qclass {A R a : V} (ha : a ∈ˢ A) : a ∈ˢ qclass A R a :=
  self_mem_qclassF ha

theorem qclass_eq_of_rel {A R a b : V} (h : QuotRel A R a b) :
    qclass A R a = qclass A R b :=
  qclassF_eq_of_rel h

/-- Membership in the class is the definable realization. -/
theorem mem_qclass_realize {A R a b : V} :
    b ∈ˢ qclass A R a ↔ Form.Realize Mem (Form.snoc (qclassParam A R a) b) qsatF := by
  rw [mem_qclass]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨haA, hsat⟩ := realize_qsatF.mp h
    refine ⟨hsat A (fun z hz => hz) haA (fun x y _ hor => ?_), h⟩
    rcases hor with ⟨-, hyA, -⟩ | ⟨hyA, -, -⟩ <;> exact hyA

/-- Parameters of the quotient-image relation: `0 ↦ A`, `1 ↦ R`, `2 ↦ empty`, rest `pt`. -/
noncomputable def quotParam (A R : V) : Fin 5 → V := fun i =>
  match i.val with
  | 0 => A
  | 1 => R
  | 2 => (empty : V)
  | _ => (pt : V)

/-- Variable map `Fin 3 → Fin 8` reading `kpairEqF`'s `(z, x, y)` as `(z, empty, c)` out of `(x, z, A, R, empty, pt, pt, c)`. -/
def quotKMap : Fin 3 → Fin 8 := fun i =>
  match i.val with
  | 0 => ⟨1, by omega⟩
  | 1 => ⟨4, by omega⟩
  | _ => ⟨7, by omega⟩

/-- Variable map `Fin 5 → Fin 9` reading `qsatF`'s `(A, R, a, pt, b)` out of `(x, z, A, R, empty, pt, pt, c, b)`. -/
def quotGMap : Fin 5 → Fin 9 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨3, by omega⟩
  | 2 => ⟨0, by omega⟩
  | 3 => ⟨5, by omega⟩
  | _ => ⟨8, by omega⟩

/-- The definable quotient-class relation (replacement convention: variables `0 ↦ x`, `1 ↦ z`, parameters `2 ↦ A`, `3 ↦ R`, `4 ↦ empty`): `z = kpair empty c` where `c` is the `qsatF`-class of `x`. -/
def quotRelF : Form 7 :=
  .ex (.and (Form.relabel quotKMap kpairEqF)
    (.all (.iff (.mem ⟨8, by omega⟩ ⟨7, by omega⟩) (Form.relabel quotGMap qsatF))))

theorem realize_quotRelF {A R x z : V} :
    Form.Realize Mem (Form.cons2 x z (quotParam A R)) quotRelF ↔
      ∃ c : V, z = kpair (empty : V) c ∧
        ∀ b : V, b ∈ˢ c ↔ Form.Realize Mem (Form.snoc (qclassParam A R x) b) qsatF := by
  have hK : ∀ c : V,
      (Form.snoc (Form.cons2 x z (quotParam A R)) c) ∘ quotKMap =
        Form.snoc (Form.snoc (fun _ => z) (empty : V)) c := by
    intro c
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hG : ∀ c b : V,
      (Form.snoc (Form.snoc (Form.cons2 x z (quotParam A R)) c) b) ∘ quotGMap =
        Form.snoc (qclassParam A R x) b := by
    intro c b
    funext ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> rfl
  have h8 : ∀ c b : V, ∀ h : 8 < 5 + 2 + 1 + 1,
      (Form.snoc (Form.snoc (Form.cons2 x z (quotParam A R)) c) b) ⟨8, h⟩ = b := by
    intro c b h
    rfl
  have h7 : ∀ c b : V, ∀ h : 7 < 5 + 2 + 1 + 1,
      (Form.snoc (Form.snoc (Form.cons2 x z (quotParam A R)) c) b) ⟨7, h⟩ = c := by
    intro c b h
    rfl
  constructor
  · intro h
    simp only [quotRelF, Form.realize_ex, Form.realize_and, Form.realize_all,
      Form.realize_iff, Form.realize_mem, Form.realize_relabel, hK, hG, h8, h7,
      realize_kpairEqF] at h
    exact h
  · intro h
    simp only [quotRelF, Form.realize_ex, Form.realize_and, Form.realize_all,
      Form.realize_iff, Form.realize_mem, Form.realize_relabel, hK, hG, h8, h7,
      realize_kpairEqF]
    exact h

theorem quotRelF_fun (A R : V) :
    ∀ x, x ∈ˢ A → ∃ y, Form.Realize Mem (Form.cons2 x y (quotParam A R)) quotRelF ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' (quotParam A R)) quotRelF → y' = y := by
  intro x _
  refine ⟨kpair (empty : V) (qclass A R x), realize_quotRelF.mpr ⟨qclass A R x, rfl, fun b => mem_qclass_realize⟩, ?_⟩
  intro y' hy'
  obtain ⟨c, hy', hc⟩ := realize_quotRelF.mp hy'
  have hcq : c = qclass A R x := ext fun b => by rw [hc b, mem_qclass_realize]
  rw [hy', hcq]


open Classical in
/-- The quotient (see module docs). -/
noncomputable def quotSet (u : Nat) (A R : V) : V :=
  if u = 0 then constImageF pt A
  else imageF quotRelF (quotParam A R) A (quotRelF_fun A R)

open Classical in
/-- The class of `a` in the quotient: at `u ≠ 0` the `QuotRel`-class,
tagged as a pair (`kpair ∅ ·`; `sing` would not do, as the class can be
`ptTag` itself and `sing ptTag = pt`). -/
noncomputable def quotClass (u : Nat) (A R a : V) : V :=
  if u = 0 then pt else kpair empty (qclass A R a)

theorem quotClass_mem {u : Nat} {A R a : V} (ha : a ∈ˢ A) :
    quotClass u A R a ∈ˢ quotSet u A R := by
  unfold quotClass quotSet
  split
  · exact mem_constImageF.mpr ⟨a, ha, rfl⟩
  · exact mem_imageF (quotRelF_fun A R) |>.mpr ⟨a, ha, realize_quotRelF.mpr ⟨qclass A R a, rfl, fun b => mem_qclass_realize⟩⟩

theorem quotClass_surj {u : Nat} {A R q : V} (hq : q ∈ˢ quotSet u A R) :
    ∃ a, a ∈ˢ A ∧ q = quotClass u A R a := by
  unfold quotSet at hq
  unfold quotClass
  split at hq
  · next h =>
    obtain ⟨a, ha, rfl⟩ := mem_constImageF.mp hq
    exact ⟨a, ha, (ite_eq_left h).symm⟩
  · next h =>
    obtain ⟨a, ha, hreal⟩ := mem_imageF (quotRelF_fun A R) |>.mp hq
    obtain ⟨c, hqc, hc⟩ := realize_quotRelF.mp hreal
    have hcq : c = qclass A R a := ext fun b => by rw [hc b, mem_qclass_realize]
    exact ⟨a, ha, (hqc.trans (congrArg (kpair (empty : V)) hcq)).trans (ite_eq_right h).symm⟩

/-- A class formed at ONE pair of parameters that lands in the quotient
of ANOTHER: its representative lies in the second parameter's carrier,
and the class is the second quotient's class of that same
representative.  Nothing relates the two parameter pairs — at a positive
level the first (tagged) class is a (tagged) `qclass` of the second's,
and at level zero
both classes are the point and the second carrier is inhabited because
the quotient is. -/
theorem quotClass_of_mem_quotSet {u : Nat} {Aset R A' R' a : V}
    (hAset : Aset ∈ˢ (univ u : V)) (hA' : A' ∈ˢ (univ u : V)) (ha : a ∈ˢ A')
    (hmem : quotClass u A' R' a ∈ˢ quotSet u Aset R) :
    a ∈ˢ Aset ∧ quotClass u A' R' a = quotClass u Aset R a := by
  obtain ⟨b, hb, hcls⟩ := quotClass_surj hmem
  by_cases hu : u = 0
  · subst hu
    refine ⟨?_, by unfold quotClass; rw [ite_eq_left rfl, ite_eq_left rfl]⟩
    rw [univ_zero] at hA' hAset
    rw [eq_pt_of_mem_univZero hA' ha, ← eq_pt_of_mem_univZero hAset hb]
    exact hb
  · unfold quotClass at hcls ⊢
    rw [ite_eq_right hu, ite_eq_right hu] at hcls
    rw [ite_eq_right hu, ite_eq_right hu]
    have hcls' := (kpair_inj hcls).2
    have hab : a ∈ˢ qclass Aset R b := by rw [← hcls']; exact self_mem_qclass ha
    obtain ⟨haA, -⟩ := mem_qclass.mp hab
    exact ⟨haA, hcls.trans (congrArg (kpair empty) (qclassF_eq_of_mem hb hab))⟩

/-- **`quotClass_of_mem_quotSet` across two positive levels**: a class
formed at one positive level and one pair of parameters that lands in
the quotient of another positive level and pair is, there, the class of
the same representative.  Above `Prop` the class reads no level. -/
theorem quotClass_of_mem_quotSet_pos {u u' : Nat} (hu : u ≠ 0) (hu' : u' ≠ 0)
    {Aset R A' R' a : V} (ha : a ∈ˢ A')
    (hmem : quotClass u' A' R' a ∈ˢ quotSet u Aset R) :
    a ∈ˢ Aset ∧ quotClass u' A' R' a = quotClass u Aset R a := by
  have hl : quotClass u' A' R' a = quotClass u A' R' a := by
    unfold quotClass; rw [ite_eq_right hu, ite_eq_right hu']
  rw [hl] at hmem ⊢
  obtain ⟨b, hb, hcls⟩ := quotClass_surj hmem
  unfold quotClass at hcls ⊢
  rw [ite_eq_right hu, ite_eq_right hu] at hcls
  rw [ite_eq_right hu, ite_eq_right hu]
  have hcls' := (kpair_inj hcls).2
  have hab : a ∈ˢ qclass Aset R b := by rw [← hcls']; exact self_mem_qclass ha
  obtain ⟨haA, -⟩ := mem_qclass.mp hab
  exact ⟨haA, hcls.trans (congrArg (kpair empty) (qclassF_eq_of_mem hb hab))⟩

theorem quotSound {u : Nat} {A R a b w : V} (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hw : w ∈ˢ app (app R a) b) : quotClass u A R a = quotClass u A R b := by
  unfold quotClass
  split
  · rfl
  · exact congrArg (kpair empty) (qclass_eq_of_rel (QuotRel.base ha hb ⟨w, hw⟩))

open Classical in
/-- A representative of a quotient class, by choice. -/
noncomputable def qrep (u : Nat) (A R q : V) : V :=
  if h : ∃ a, a ∈ˢ A ∧ q = quotClass u A R a then Classical.choose h else empty

theorem qrep_spec {u : Nat} {A R q : V} (hq : q ∈ˢ quotSet u A R) :
    qrep u A R q ∈ˢ A ∧ q = quotClass u A R (qrep u A R q) := by
  unfold qrep
  rw [dite_eq_left (quotClass_surj hq)]
  exact Classical.choose_spec (quotClass_surj hq)

/-- The invariance premise extends from the base relation to its
equivalence closure. -/
theorem app_eq_of_rel {A R f a b : V}
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') →
      app f a' = app f b')
    (h : QuotRel A R a b) : app f a = app f b := by
  induction h with
  | base ha hb hw => exact hinv _ _ ha hb hw
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Equal classes have equal `f`-values: by closure invariance at
`u ≠ 0`, and by the `A ⊆ {pt}` collapse at `u = 0`. -/
theorem app_eq_of_quotClass_eq {u : Nat} {A R f a b : V}
    (hA : A ∈ˢ (univ u : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') →
      app f a' = app f b')
    (hq : quotClass u A R a = quotClass u A R b) : app f a = app f b := by
  unfold quotClass at hq
  split at hq
  · next h =>
    subst h
    rw [univ_zero] at hA
    rw [eq_pt_of_mem_univZero hA ha, eq_pt_of_mem_univZero hA hb]
  · have hab : a ∈ˢ qclass A R b := by
      have hs : a ∈ˢ qclass A R a := self_mem_qclass ha
      rw [(kpair_inj hq).2] at hs
      exact hs
    exact app_eq_of_mem_qclassF hinv hb hab

/-! ## The class is never the point above `Prop` (tasks #109, #342)

Raw classes are arbitrary nonempty subsets of the base, so with base
`ptTag` itself and a total relation the one class is `ptTag` and the
untagged class set is exactly `{ptTag} = pt` — for *any* singleton
proof point.  The base `ptTag`
is not the interpretation of any *writable* type; the obstruction is
semantic, in the ∀-A-R quantification of the model lemmas.  Up to task
#342 the classes were raw and this was the quotient itself; since then
a class above `Prop` is the pair `kpair ∅ (qclass A R a)`, so it is
never the point, and the quotient never is nor
contains it (`strict_quotSet`). -/

/-- Above `Prop` the quotient is strict: its members are pairs. -/
theorem strict_quotSet {u : Nat} (hu : u ≠ 0) (A R : V) : Strict (quotSet u A R) :=
  strict_of_kpairs fun z hz => by
    unfold quotSet at hz; rw [ite_eq_right hu] at hz
    obtain ⟨x, hx, hreal⟩ := mem_imageF (quotRelF_fun A R) |>.mp hz
    obtain ⟨c, hz', -⟩ := realize_quotRelF.mp hreal
    exact ⟨empty, c, hz'⟩

attribute [irreducible] quotSet quotClass

theorem quotSet_mem_univ {u : Nat} {A R : V} (hA : A ∈ˢ (univ u : V)) :
    quotSet u A R ∈ˢ (univ u : V) := by
  by_cases h : u = 0
  · subst h
    unfold quotSet
    rw [ite_eq_left rfl, univ_zero]
    refine mem_univZero.mpr fun z hz => ?_
    obtain ⟨-, -, rfl⟩ := mem_constImageF.mp hz
    exact pt_mem_unitSet
  · refine mem_univ_of_tg_strict ?_ (strict_quotSet h A R)
    have hA' := mem_tg_of_mem_univ hA
    have hU := tg_isUniverse (V := V) h
    unfold quotSet
    rw [ite_eq_right h]
    refine hU.imageF_mem hA' ?_
    intro x _ y hy
    obtain ⟨c, rfl, hc⟩ := realize_quotRelF.mp hy
    have hcq : c = qclassF A R x := ext fun b => by
      rw [hc b]
      exact mem_qclass_realize.symm
    rw [hcq]
    exact hU.kpair_mem hA' (hU.empty_mem hA') (hU.sepF_mem hA')

end ConLeche.SetTheory
