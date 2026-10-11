module

public import Fragment.Univ
public import Fragment.Interp
public import Fragment.EnvModel

@[expose] public section

/-!
# Uniform β: the model with restricted universes (tasks #338, #339)

A variant of the fragment's model in which **no member of a type whose
sort is nonzero is the proof point** — property (P) of task #337 — so
that β can fire at every binder, with no certificate and no comparison
of the binder's annotation with anything.

What changes against the fragment's model (`Lib.lean`, `Interp.lean`,
`WellDenoted.lean`):

* **Three laws about the point** (`PtLib`): it is not a truth value, it
  has at most one member, and no graph is its member.  (The standard
  model can take `pt := {{∅}}`.)
* **Restricted universes** (`typeU`): `Sort 0` is the truth values, as
  before; `Sort (n+1)` is the members of `univ (n+1)` that are not the
  point and do not contain it ("strict" sets).  `univ` stays the
  Grothendieck universe that sizes things; `typeU` is what a sort
  denotes (`interpU`).
* **The semantic invariant records what is a type** (`WDU`): a binder's
  domain and an application's (graph-regime) slot domain are types
  (`IsTy`: a truth value or strict), and a function-regime binder's
  codomain fibres are strict.  The typed rules establish exactly this.
* **The claims become conditional on the point**: a reduction claims
  nothing about a subject that denotes the point, and a definitional
  equality nothing about two sides one of which does.  Proof
  irrelevance needs no claim at all: two proofs are the point.

* **The ι laws take the comparisons conditionally** (`RecRuleLawU`,
  `RecRuleLawNU`): the constructor's parameters and index values equal
  the recursor's only where neither is the point, and the law is asked
  only where the recursor's application is not the point.

`Uniform/Sound.lean` proves the fragment's env-free rules — β, δ and ι
— sound with uniform β against this model.
-/

namespace Fragment.Uniform

open SetLib UnivLib

universe u

/-- **The library with the point's laws.** -/
class PtLib (V : Type u) extends UnivLib V where
  /-- The point is not a truth value: it has a member other than itself. -/
  pt_not_mem_univ_zero : ¬ Mem pt (univ 0)
  /-- The point has at most one member. -/
  pt_subsingleton : ∀ {x y : V}, Mem x pt → Mem y pt → x = y
  /-- No graph is a member of the point. -/
  graph_not_mem_pt : ∀ {F : V → V} {A : V}, ¬ Mem (graph F A) pt

variable {V : Type u} [PtLib V]

open PtLib

/-! ## Strict sets, types, the restricted universes -/

/-- A **strict** set: not the point, and the point is not a member. -/
def Strict (X : V) : Prop := X ≠ pt ∧ ¬ pt ∈ˢ X

/-- A **type**: a truth value, or a strict set. -/
def IsTy (X : V) : Prop := X ∈ˢ univ 0 ∨ Strict X

/-- **What `Sort n` denotes**: the truth values at `0`, the strict
members of `univ n` above. -/
def typeU (n : Nat) : V := if n = 0 then univ 0 else sep (univ n) Strict

/-- The regime of a fibre: a truth value at a proposition, strict above. -/
def Fib : Bool → V → Prop
  | true, X => X ∈ˢ univ 0
  | false, X => Strict X

theorem ne_pt_of_mem_univ_zero {T : V} (h : T ∈ˢ univ 0) : T ≠ pt := by
  rintro rfl; exact pt_not_mem_univ_zero h

theorem IsTy.ne_pt {T : V} (h : IsTy T) : T ≠ pt := by
  rcases h with h | h
  · exact ne_pt_of_mem_univ_zero h
  · exact h.1

theorem IsTy_of_Fib {p : Bool} {X : V} (h : Fib p X) : IsTy X := by
  cases p
  · exact Or.inr h
  · exact Or.inl h

theorem Fib.ne_pt {p : Bool} {X : V} (h : Fib p X) : X ≠ pt := (IsTy_of_Fib h).ne_pt

theorem mem_typeU_zero {T : V} : T ∈ˢ typeU 0 ↔ T ∈ˢ univ 0 := by
  simp [typeU]

theorem mem_typeU_pos {n : Nat} (hn : n ≠ 0) {T : V} :
    T ∈ˢ typeU n ↔ T ∈ˢ univ n ∧ Strict T := by
  simp only [typeU, hn, ↓reduceIte]
  exact mem_sep

theorem mem_univ_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ typeU n) : T ∈ˢ univ n := by
  by_cases hn : n = 0
  · subst hn; exact mem_typeU_zero.mp h
  · exact ((mem_typeU_pos hn).mp h).1

theorem IsTy_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ typeU n) : IsTy T := by
  by_cases hn : n = 0
  · subst hn; exact Or.inl (mem_typeU_zero.mp h)
  · exact Or.inr ((mem_typeU_pos hn).mp h).2

/-- A member of `typeU n` is in the regime of `n`'s zero-ness. -/
theorem Fib_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ typeU n) :
    Fib (decide (n = 0)) T := by
  by_cases hn : n = 0
  · subst hn; exact mem_typeU_zero.mp h
  · simp only [hn, decide_false]; exact ((mem_typeU_pos hn).mp h).2

/-- **(P)**: a member of a type of a positive sort is not the point. -/
theorem ne_pt_of_mem_strict {T x : V} (hT : Strict T) (hx : x ∈ˢ T) : x ≠ pt := by
  rintro rfl; exact hT.2 hx

/-! ### The point's neighbours -/

theorem pt_ne_empty : (pt : V) ≠ empty := by
  intro h
  apply pt_not_mem_univ_zero (V := V)
  rw [h]
  exact mem_univ_zero.mpr fun z hz => absurd hz (not_mem_empty z)

theorem exists_mem_pt : ∃ z, z ∈ˢ (pt : V) :=
  Classical.byContradiction fun h => pt_ne_empty (ext fun z =>
    ⟨fun hz => absurd ⟨z, hz⟩ h, fun hz => absurd hz (not_mem_empty z)⟩)

theorem eq_pt_of_two {X a b : V} (ha : a ∈ˢ X) (hb : b ∈ˢ X) (hab : a ≠ b) : X ≠ pt := by
  rintro rfl; exact hab (pt_subsingleton ha hb)

theorem one_ne_empty : (one : V) ≠ empty := by
  intro h
  have : (pt : V) ∈ˢ one := mem_one.mpr rfl
  rw [h] at this
  exact not_mem_empty _ this

theorem univ_zero_ne_pt : (univ 0 : V) ≠ pt :=
  eq_pt_of_two one_mem_univ_zero (empty_mem_univ 0) one_ne_empty

theorem strict_univ_zero : Strict (univ 0 : V) := ⟨univ_zero_ne_pt, pt_not_mem_univ_zero⟩

theorem strict_empty : Strict (empty : V) := ⟨pt_ne_empty.symm, not_mem_empty _⟩

/-- `Sort n` is strict. -/
theorem strict_typeU (n : Nat) : Strict (typeU n : V) := by
  by_cases hn : n = 0
  · subst hn; simpa [typeU] using strict_univ_zero
  · refine ⟨?_, fun h => ((mem_typeU_pos hn).mp h).2.1 rfl⟩
    -- `typeU n` has two distinct members, the point at most one
    have h1 : (empty : V) ∈ˢ typeU n :=
      (mem_typeU_pos hn).mpr ⟨empty_mem_univ n, strict_empty⟩
    have h2 : (univ 0 : V) ∈ˢ typeU n :=
      (mem_typeU_pos hn).mpr ⟨univ_mono (by omega) (univ_mem_succ 0), strict_univ_zero⟩
    refine eq_pt_of_two h1 h2 fun h => ?_
    have h3 : (one : V) ∈ˢ univ 0 := one_mem_univ_zero
    rw [← h] at h3
    exact not_mem_empty _ h3

/-- `Sort n : Sort (n+1)`. -/
theorem typeU_mem_typeU_succ (n : Nat) : (typeU n : V) ∈ˢ typeU (n + 1) := by
  refine (mem_typeU_pos (Nat.succ_ne_zero n)).mpr ⟨?_, strict_typeU n⟩
  by_cases hn : n = 0
  · subst hn; simpa [typeU] using univ_mem_succ 0
  · simp only [typeU, hn, ↓reduceIte]
    exact sep_mem_univ (univ_mem_succ n)

/-- A function space is strict: its members are graphs, and the point's
member is not one. -/
theorem strict_piSet {A : V} {B : V → V} : Strict (piSet A B) := by
  refine ⟨?_, fun h => graph_ne_pt (graph_app_eq h)⟩
  intro he
  obtain ⟨z, hz⟩ := exists_mem_pt (V := V)
  have hz' : z ∈ˢ piSet A B := by rw [he]; exact hz
  have := graph_app_eq hz'
  rw [← this] at hz
  exact graph_not_mem_pt hz

theorem IsTy_piR {p : Bool} {A : V} {B : V → V} : IsTy (piR p A B) := by
  cases p
  · exact Or.inr strict_piSet
  · exact Or.inl piR_true_mem_univ_zero

/-- **`∀`-formation in the restricted universes.** -/
theorem piR_mem_typeU {u v : Nat} {p : Bool} {A : V} {B : V → V}
    (hp : p = true ↔ v = 0) (hA : A ∈ˢ typeU u) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ typeU v) :
    piR p A B ∈ˢ typeU (Level.imaxNat u v) := by
  by_cases hv : v = 0
  · rw [(Level.imaxNat_eq_zero_iff u v).mpr hv, hp.mpr hv, mem_typeU_zero]
    exact piR_true_mem_univ_zero
  · have hpf : p = false := by cases p <;> simp_all
    rw [Level.imaxNat_of_ne_zero hv, hpf, mem_typeU_pos (by omega)]
    refine ⟨piR_false_mem_univ (by omega) (univ_mono (Nat.le_max_left _ _)
      (mem_univ_of_mem_typeU hA)) fun x hx => univ_mono (Nat.le_max_right _ _)
      (mem_univ_of_mem_typeU (hB x hx)), strict_piSet⟩

/-! ## The interpretation, with sorts restricted -/

/-- **The interpretation**: `interp` with `Sort u` denoting `typeU`. -/
def interpU (M : Name → List Nat → V) (φ : Name → Nat) : (Nat → V) → Expr → V
  | ρ, .bvar i => ρ i
  | _, .sort u => typeU (u.eval φ)
  | _, .const c ls => M c (ls.map (Level.eval φ))
  | ρ, .app f a => app (interpU M φ ρ f) (interpU M φ ρ a)
  | ρ, .lam A pw b => lamR (pw.holds φ) (interpU M φ ρ A) fun x => interpU M φ (cons x ρ) b
  | ρ, .pi A pw B => piR (pw.holds φ) (interpU M φ ρ A) fun x => interpU M φ (cons x ρ) B

variable (M : Name → List Nat → V) (φ : Name → Nat)

@[simp] theorem interpU_bvar (ρ : Nat → V) (i : Nat) : interpU M φ ρ (.bvar i) = ρ i := rfl
@[simp] theorem interpU_sort (ρ : Nat → V) (u : Level) :
    interpU M φ ρ (.sort u) = typeU (u.eval φ) := rfl
@[simp] theorem interpU_const (ρ : Nat → V) (c : Name) (ls : List Level) :
    interpU M φ ρ (.const c ls) = M c (ls.map (Level.eval φ)) := rfl
@[simp] theorem interpU_app (ρ : Nat → V) (f a : Expr) :
    interpU M φ ρ (.app f a) = app (interpU M φ ρ f) (interpU M φ ρ a) := rfl
@[simp] theorem interpU_lam (ρ : Nat → V) (A : Expr) (pw : PropWhen) (b : Expr) :
    interpU M φ ρ (.lam A pw b) =
      lamR (pw.holds φ) (interpU M φ ρ A) fun x => interpU M φ (cons x ρ) b := rfl
@[simp] theorem interpU_pi (ρ : Nat → V) (A : Expr) (pw : PropWhen) (B : Expr) :
    interpU M φ ρ (.pi A pw B) =
      piR (pw.holds φ) (interpU M φ ρ A) fun x => interpU M φ (cons x ρ) B := rfl

theorem interpU_liftN (n : Nat) :
    ∀ (e : Expr) (k : Nat) (ρ : Nat → V),
      interpU M φ ρ (e.liftN n k) = interpU M φ (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [Expr.liftN_bvar, interpU_bvar, shiftE]
    split <;> rfl
  | sort u => intro k ρ; rfl
  | const c ls => intro k ρ; rfl
  | app f a ihf iha => intro k ρ; simp [ihf, iha]
  | lam A pw b ihA ihb =>
    intro k ρ
    simp only [Expr.liftN_lam, interpU_lam, ihA]
    congr 1
    funext x
    rw [ihb, cons_shiftE]
  | pi A pw B ihA ihB =>
    intro k ρ
    simp only [Expr.liftN_pi, interpU_pi, ihA]
    congr 1
    funext x
    rw [ihB, cons_shiftE]

theorem interpU_inst :
    ∀ (e a : Expr) (k : Nat) (ρ : Nat → V),
      interpU M φ ρ (e.inst a k) =
        interpU M φ (instE k (interpU M φ (shiftE k 0 ρ) a) ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ
    simp only [Expr.inst_bvar, interpU_bvar, instE]
    by_cases h : i < k
    · simp [h]
    · by_cases h2 : i = k
      · simp only [ite_eq_right h, ite_eq_left h2]
        rw [interpU_liftN]
      · simp [h, h2]
  | sort u => intro a k ρ; rfl
  | const c ls => intro a k ρ; rfl
  | app f b ihf ihb => intro a k ρ; simp [ihf, ihb]
  | lam A pw b ihA ihb =>
    intro a k ρ
    simp only [Expr.inst_lam, interpU_lam, ihA]
    congr 1
    funext x
    rw [ihb, shiftE_succ_cons, cons_instE]
  | pi A pw B ihA ihB =>
    intro a k ρ
    simp only [Expr.inst_pi, interpU_pi, ihA]
    congr 1
    funext x
    rw [ihB, shiftE_succ_cons, cons_instE]

theorem interpU_inst0 (e a : Expr) (ρ : Nat → V) :
    interpU M φ ρ (e.inst a) = interpU M φ (cons (interpU M φ ρ a) ρ) e := by
  rw [interpU_inst, shiftE_zero_zero, instE_zero]

/-! ## The typed invariant -/

/-- **The semantic invariant, recording types.**  As `WellDenoted`,
and: a binder's domain is a type; a binder's codomain fibres are in the
regime of its annotation (truth values where it holds, strict sets
where it does not); an application in the graph regime has a type as
its slot's domain. -/
def WDU : (Nat → V) → Expr → Prop
  | _, .bvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | ρ, .app f a =>
    WDU ρ f ∧ WDU ρ a ∧
      ∃ (p : Bool) (A : V) (B : V → V),
        interpU M φ ρ f ∈ˢ piR p A B ∧ interpU M φ ρ a ∈ˢ A ∧
        (p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) ∧ (p = false → IsTy A)
  | ρ, .lam A pw b =>
    WDU ρ A ∧ IsTy (interpU M φ ρ A) ∧
      (∀ x, x ∈ˢ interpU M φ ρ A → WDU (cons x ρ) b) ∧
      ∃ B : V → V,
        (∀ x, x ∈ˢ interpU M φ ρ A → interpU M φ (cons x ρ) b ∈ˢ B x) ∧
        (∀ x, x ∈ˢ interpU M φ ρ A → Fib (pw.holds φ) (B x))
  | ρ, .pi A pw B =>
    WDU ρ A ∧ IsTy (interpU M φ ρ A) ∧
      (∀ x, x ∈ˢ interpU M φ ρ A → WDU (cons x ρ) B) ∧
      (∀ x, x ∈ˢ interpU M φ ρ A → Fib (pw.holds φ) (interpU M φ (cons x ρ) B))

@[simp] theorem WDU_bvar (ρ : Nat → V) (i : Nat) : WDU M φ ρ (.bvar i) := trivial
@[simp] theorem WDU_sort (ρ : Nat → V) (u : Level) : WDU M φ ρ (.sort u) := trivial
@[simp] theorem WDU_const (ρ : Nat → V) (c : Name) (ls : List Level) :
    WDU M φ ρ (.const c ls) := trivial

theorem WDU_app (ρ : Nat → V) (f a : Expr) :
    WDU M φ ρ (.app f a) ↔
      (WDU M φ ρ f ∧ WDU M φ ρ a ∧
        ∃ (p : Bool) (A : V) (B : V → V),
          interpU M φ ρ f ∈ˢ piR p A B ∧ interpU M φ ρ a ∈ˢ A ∧
          (p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) ∧ (p = false → IsTy A)) := by
  rw [WDU]

theorem WDU_lam (ρ : Nat → V) (A : Expr) (pw : PropWhen) (b : Expr) :
    WDU M φ ρ (.lam A pw b) ↔
      (WDU M φ ρ A ∧ IsTy (interpU M φ ρ A) ∧
        (∀ x, x ∈ˢ interpU M φ ρ A → WDU M φ (cons x ρ) b) ∧
        ∃ B : V → V,
          (∀ x, x ∈ˢ interpU M φ ρ A → interpU M φ (cons x ρ) b ∈ˢ B x) ∧
          (∀ x, x ∈ˢ interpU M φ ρ A → Fib (pw.holds φ) (B x))) := by
  rw [WDU]

theorem WDU_pi (ρ : Nat → V) (A : Expr) (pw : PropWhen) (B : Expr) :
    WDU M φ ρ (.pi A pw B) ↔
      (WDU M φ ρ A ∧ IsTy (interpU M φ ρ A) ∧
        (∀ x, x ∈ˢ interpU M φ ρ A → WDU M φ (cons x ρ) B) ∧
        (∀ x, x ∈ˢ interpU M φ ρ A → Fib (pw.holds φ) (interpU M φ (cons x ρ) B))) := by
  rw [WDU]

theorem WDU_liftN (n : Nat) :
    ∀ (e : Expr) (k : Nat) (ρ : Nat → V),
      WDU M φ ρ (e.liftN n k) ↔ WDU M φ (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i => intro k ρ; simp
  | sort u => intro k ρ; simp
  | const c ls => intro k ρ; simp
  | app f a ihf iha =>
    intro k ρ
    rw [Expr.liftN_app, WDU_app, WDU_app, ihf, iha, interpU_liftN, interpU_liftN]
  | lam A pw b ihA ihb =>
    intro k ρ
    rw [Expr.liftN_lam, WDU_lam, WDU_lam, ihA, interpU_liftN]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl)))
    · rw [ihb, cons_shiftE]
    · rw [interpU_liftN, cons_shiftE]
  | pi A pw B ihA ihB =>
    intro k ρ
    rw [Expr.liftN_pi, WDU_pi, WDU_pi, ihA, interpU_liftN]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · rw [ihB, cons_shiftE]
    · rw [interpU_liftN, cons_shiftE]

/-- The invariant through instantiation, given the substituted term's. -/
theorem WDU_inst :
    ∀ (e a : Expr) (k : Nat) (ρ : Nat → V),
      WDU M φ (shiftE k 0 ρ) a →
      (WDU M φ ρ (e.inst a k) ↔
        WDU M φ (instE k (interpU M φ (shiftE k 0 ρ) a) ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ ha
    simp only [Expr.inst_bvar, WDU_bvar, iff_true]
    by_cases h : i < k
    · rw [ite_eq_left h]; exact trivial
    · rw [ite_eq_right h]
      by_cases h2 : i = k
      · rw [ite_eq_left h2]; exact (WDU_liftN M φ k a 0 ρ).mpr ha
      · rw [ite_eq_right h2]; exact trivial
  | sort u => intro a k ρ _; simp
  | const c ls => intro a k ρ _; simp
  | app f b ihf ihb =>
    intro a k ρ ha
    rw [Expr.inst_app, WDU_app, WDU_app, ihf a k ρ ha, ihb a k ρ ha, interpU_inst, interpU_inst]
  | lam A pw b ihA ihb =>
    intro a k ρ ha
    rw [Expr.inst_lam, WDU_lam, WDU_lam, ihA a k ρ ha, interpU_inst]
    have ha' : ∀ x, WDU M φ (shiftE (k + 1) 0 (cons x ρ)) a := by
      intro x; rwa [shiftE_succ_cons]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl)))
    · rw [ihb a (k + 1) (cons x ρ) (ha' x), shiftE_succ_cons, cons_instE]
    · rw [interpU_inst, shiftE_succ_cons, cons_instE]
  | pi A pw B ihA ihB =>
    intro a k ρ ha
    rw [Expr.inst_pi, WDU_pi, WDU_pi, ihA a k ρ ha, interpU_inst]
    have ha' : ∀ x, WDU M φ (shiftE (k + 1) 0 (cons x ρ)) a := by
      intro x; rwa [shiftE_succ_cons]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · rw [ihB a (k + 1) (cons x ρ) (ha' x), shiftE_succ_cons, cons_instE]
    · rw [interpU_inst, shiftE_succ_cons, cons_instE]

theorem WDU_inst0 {e a : Expr} {ρ : Nat → V} (ha : WDU M φ ρ a) :
    WDU M φ ρ (e.inst a) ↔ WDU M φ (cons (interpU M φ ρ a) ρ) e := by
  have h := WDU_inst M φ e a 0 ρ (by rwa [shiftE_zero_zero])
  rwa [shiftE_zero_zero, instE_zero] at h

/-! ## Contexts -/

/-- A context is satisfied: every entry is a well-denoted type and the
environment's value is a member of it. -/
def SatU : List Expr → (Nat → V) → Prop
  | [], _ => True
  | A :: Γ, ρ =>
    SatU Γ (fun i => ρ (i + 1)) ∧ WDU M φ (fun i => ρ (i + 1)) A ∧
      IsTy (interpU M φ (fun i => ρ (i + 1)) A) ∧ ρ 0 ∈ˢ interpU M φ (fun i => ρ (i + 1)) A

@[simp] theorem SatU_nil (ρ : Nat → V) : SatU M φ [] ρ := trivial

theorem SatU_cons {Γ : List Expr} {A : Expr} {ρ : Nat → V} {x : V} :
    SatU M φ (A :: Γ) (cons x ρ) ↔
      SatU M φ Γ ρ ∧ WDU M φ ρ A ∧ IsTy (interpU M φ ρ A) ∧ x ∈ˢ interpU M φ ρ A := Iff.rfl

theorem SatU_get : ∀ {Γ : List Expr} {ρ : Nat → V} {i : Nat} {A : Expr},
    SatU M φ Γ ρ → Γ[i]? = some A →
    WDU M φ (shiftE (i + 1) 0 ρ) A ∧ IsTy (interpU M φ (shiftE (i + 1) 0 ρ) A) ∧
      ρ i ∈ˢ interpU M φ (shiftE (i + 1) 0 ρ) A
  | [], _, _, _, _, h => by simp at h
  | B :: Γ, ρ, 0, A, hs, h => by
    simp at h
    subst h
    rw [shiftE_zero]
    exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2⟩
  | B :: Γ, ρ, i + 1, A, hs, h => by
    simp at h
    have := SatU_get (ρ := fun j => ρ (j + 1)) hs.1 h
    rw [shiftE_zero] at this ⊢
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-! ## Telescopes on values, and the ι laws -/

/-- **Values fitting a telescope**, read by `interpU` (`TeleFitV`). -/
def TeleFitVU : (Nat → V) → Expr → List V → Prop
  | _, _, [] => True
  | ρ, .pi A _ B, v :: vs => v ∈ˢ interpU M φ ρ A ∧ TeleFitVU (cons v ρ) B vs
  | _, _, _ :: _ => False

theorem TeleFitVU_nil (ρ : Nat → V) (e : Expr) : TeleFitVU M φ ρ e [] := by
  cases e <;> exact trivial

theorem TeleFitVU_pi_cons (ρ : Nat → V) (A : Expr) (pw : PropWhen) (B : Expr) (v : V)
    (vs : List V) :
    TeleFitVU M φ ρ (.pi A pw B) (v :: vs) ↔
      v ∈ˢ interpU M φ ρ A ∧ TeleFitVU M φ (cons v ρ) B vs := Iff.rfl

/-- **A well-formed application chain on values**, with `WDU`'s typed
application clause: in the graph regime the slot's domain is a type. -/
def SpineOkU : V → List V → Prop
  | _, [] => True
  | f, v :: vs =>
    (∃ (p : Bool) (A : V) (B : V → V),
      f ∈ˢ piR p A B ∧ v ∈ˢ A ∧ (p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) ∧
        (p = false → IsTy A)) ∧
    SpineOkU (app f v) vs

/-- **The ι law of one recursor rule**, for the restricted universes
(`RecRuleLaw`, with three changes).  The comparisons of the
constructor's parameters with the recursor's and of the residual's
index values with the recursor's index arguments are **conditional on
the point**, as `DefEqU` claims them; and the law is asked only where
the recursor's application is not the point, as `RedU` claims ι.
Deriving the equalities the recursion equation needs from the
conditional comparisons is the installation's business: the two
telescopes are generated from one parameter and index context, so the
two sides of each comparison lie in one type, whose members are all the
point or none (`IsTy`). -/
def RecRuleLawU (c : Name) (ci : ConstInfo)
    (numParams numBefore majorIdx : Nat) (rl : RecRule) (cij : ConstInfo) : Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (us usj : List Level) (xs ys : List V),
    us.length = ci.lparams.length → usj.length = cij.lparams.length →
    xs.length = majorIdx → ys.length = numParams + rl.nfields →
    TeleFitVU M φ ρ (ci.type.instL ci.lparams us)
      (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys]) →
    TeleFitVU M φ ρ (cij.type.instL cij.lparams usj) ys →
    usj.map (Level.eval φ) = (us.drop (us.length - usj.length)).map (Level.eval φ) →
    (∀ p ∈ (ys.take numParams).zip (xs.take numParams), p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
    (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
      piBodyV ρ (cij.type.instL cij.lparams usj) ys = some (B, ρ') →
      B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = numParams →
      ∀ p ∈ (ridx.map (interpU M φ ρ')).zip (xs.drop numBefore),
        p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
    appList (M c (us.map (Level.eval φ)))
        (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys]) ≠ pt →
    appList (M c (us.map (Level.eval φ)))
        (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys])
      = appList (interpU M φ ρ (rl.rhs.instL ci.lparams us))
          (xs.take numBefore ++ ys.drop numParams) ∧
    WDU M φ ρ (rl.rhs.instL ci.lparams us) ∧
    SpineOkU (interpU M φ ρ (rl.rhs.instL ci.lparams us)) (xs.take numBefore ++ ys.drop numParams)

/-- **The ι law of a nested rule** (`RecRuleLawN`), with the index
comparisons conditional on the point and asked only where the
recursor's application is not the point. -/
def RecRuleLawNU (c : Name) (ci : ConstInfo)
    (nPc numBefore majorIdx : Nat) (rl : RecRule) (cij : ConstInfo) : Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (us usj : List Level) (xs ys : List V),
    us.length = ci.lparams.length → usj.length = cij.lparams.length →
    xs.length = majorIdx → ys.length = nPc + rl.nfields →
    TeleFitVU M φ ρ (ci.type.instL ci.lparams us)
      (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys]) →
    TeleFitVU M φ ρ (cij.type.instL cij.lparams usj) ys →
    (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
      piBodyV ρ (cij.type.instL cij.lparams usj) ys = some (B, ρ') →
      B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nPc →
      ∀ p ∈ (ridx.map (interpU M φ ρ')).zip (xs.drop numBefore),
        p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
    appList (M c (us.map (Level.eval φ)))
        (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys]) ≠ pt →
    appList (M c (us.map (Level.eval φ)))
        (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys])
      = appList (interpU M φ ρ (rl.rhs.instL ci.lparams us))
          (xs.take numBefore ++ ys.drop nPc) ∧
    WDU M φ ρ (rl.rhs.instL ci.lparams us) ∧
    SpineOkU (interpU M φ ρ (rl.rhs.instL ci.lparams us)) (xs.take numBefore ++ ys.drop nPc)

/-! ## The environment model and the claims -/

/-- **A model of an environment**: every stored constant's type is a
well-denoted type with the constant a member, a definition's value
denotes the constant, and every recursor rule satisfies its ι law. -/
structure EnvModelU (V : Type u) [PtLib V] (env : Env) where
  M : Name → List Nat → V
  type_ok : ∀ (c : Name) (ci : ConstInfo), env.find? c = some ci →
    ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
      WDU M φ ρ (ci.type.instL ci.lparams ls) ∧
      IsTy (interpU M φ ρ (ci.type.instL ci.lparams ls)) ∧
      M c (ls.map (Level.eval φ)) ∈ˢ interpU M φ ρ (ci.type.instL ci.lparams ls)
  unfold : ∀ (c : Name) (ci : ConstInfo) (v : Expr), env.find? c = some ci →
    ci.value? = some v →
    ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
      WDU M φ ρ (v.instL ci.lparams ls) ∧
      interpU M φ ρ (v.instL ci.lparams ls) = M c (ls.map (Level.eval φ))
  rec_rules : ∀ (c : Name) (ci : ConstInfo) (numParams numMotives numMinors numIndices : Nat)
    (rules : List RecRule),
    env.find? c = some ci →
    ci.kind = .recursor numParams numMotives numMinors numIndices rules →
    ∀ rl ∈ rules, rl.inst = none → ∀ cij : ConstInfo, env.find? rl.ctor = some cij →
      RecRuleLawU M c ci numParams (numParams + numMotives + numMinors)
        (numParams + numMotives + numMinors + numIndices) rl cij
  rec_rules_nested : ∀ (c : Name) (ci : ConstInfo)
    (numParams numMotives numMinors numIndices : Nat) (rules : List RecRule),
    env.find? c = some ci →
    ci.kind = .recursor numParams numMotives numMinors numIndices rules →
    ∀ rl ∈ rules, ∀ (lvs : List Level) (pinst : List Expr), rl.inst = some (lvs, pinst) →
      ∀ (cij : ConstInfo) (I : Name) (nPc nf : Nat), env.find? rl.ctor = some cij →
        cij.kind = .ctor I nPc nf →
        RecRuleLawNU M c ci nPc (numParams + numMotives + numMinors)
          (numParams + numMotives + numMinors + numIndices) rl cij

/-- The empty environment has a model: any assignment, vacuous laws. -/
def EnvModelU.empty (M : Name → List Nat → V) : EnvModelU V Env.empty where
  M := M
  type_ok := fun _ _ h => by simp at h
  unfold := fun _ _ _ h => by simp at h
  rec_rules := fun _ _ _ _ _ _ _ h => by simp at h
  rec_rules_nested := fun _ _ _ _ _ _ _ h => by simp at h

variable {env : Env}

/-- **A reduction's claim**: on a subject that is not the point, the
invariant and the denotation are kept.  Nothing is claimed of a proof. -/
def RedSemU (m : EnvModelU V env) (φ : Name → Nat) (Γ : List Expr) (e e' : Expr) : Prop :=
  ∀ ρ : Nat → V, SatU m.M φ Γ ρ → WDU m.M φ ρ e → interpU m.M φ ρ e ≠ pt →
    WDU m.M φ ρ e' ∧ interpU m.M φ ρ e = interpU m.M φ ρ e'

/-- **A definitional equality's claim**: two sides that are not the point
have equal denotations.  (Two proofs are the point.) -/
def DefEqSemU (m : EnvModelU V env) (φ : Name → Nat) (Γ : List Expr) (a b : Expr) : Prop :=
  ∀ ρ : Nat → V, SatU m.M φ Γ ρ → WDU m.M φ ρ a → WDU m.M φ ρ b →
    interpU m.M φ ρ a ≠ pt → interpU m.M φ ρ b ≠ pt → interpU m.M φ ρ a = interpU m.M φ ρ b

/-- **An inference's claim**: the term and its type are well-denoted,
the type is a type, and the term is a member of it. -/
def InferSemU (m : EnvModelU V env) (φ : Name → Nat) (Γ : List Expr) (e T : Expr) : Prop :=
  ∀ ρ : Nat → V, SatU m.M φ Γ ρ →
    WDU m.M φ ρ e ∧ WDU m.M φ ρ T ∧ IsTy (interpU m.M φ ρ T) ∧
      interpU m.M φ ρ e ∈ˢ interpU m.M φ ρ T

end Fragment.Uniform
