module

public import Fragment.Level

@[expose] public section

/-!
# The set-theoretic library

Everything the fragment's proof uses of set theory, stated
declaratively as ONE class: sets and membership with extensionality
and separation, a point `pt` with its singleton, dependent function
spaces with graphs and application and their β/η/extensionality laws,
a universe chain with its closure laws, and three laws of the point
(it is not a truth value, it has at most one member, no graph is its
member; true of `pt := {{∅}}`).  There is no construction here, and
nothing beyond these laws is used — every theorem of the fragment is
proved against the class.

The truth values are not laws but an abbreviation: a proposition `P`
denotes `truthVal P`, the members of `{pt}` that satisfy `P` — the
singleton if `P` holds, empty if not — and its membership law is a
theorem of separation.

Con-leche derives all of this from a much smaller axiomatic core
(`ConLeche/SetTheory/Core.lean`: ZF⁻ plus an ω-chain of Grothendieck
universes; `ConLeche/SetTheory/Derive/*` builds the operators).  The
fragment takes the derived surface as its interface, which is what the
proof reads anyway.

Below the class, the **two-regime operators** `piR`/`lamR` of
`ConLeche/SetModel/Ops.lean`: the dependent product and abstraction at
a `Bool` saying whether the body is a proposition — a truth value and
the one proof when it is, a graph space and a graph when it is not.
The interpretation (`Interp.lean`) applies them to the annotation's
readout, and nowhere else does the regime enter.

Last, the **restricted universes** (`typeU`): what a sort denotes —
the truth values at `0`, above it the members of the universe that are
neither the point nor contain it.  The universe chain `univ` sizes
things; `typeU` is what the typing reads.
-/

namespace Fragment

universe u

/-- **The set theory we assume.**  A type of sets `V` with the
operators and laws the fragment's proof uses.  The theory is stated in
Lean's logic, so separation is available for every predicate of that
logic, and the function-space laws quantify over functions on the
sets. -/
class SetLib (V : Type u) where
  /-- Membership. -/
  Mem : V → V → Prop
  /-- Extensionality. -/
  ext : ∀ {x y : V}, (∀ z, Mem z x ↔ Mem z y) → x = y
  /-- Separation: the members of `A` that satisfy `P`. -/
  sep : V → (V → Prop) → V
  /-- The members of a separation. -/
  mem_sep : ∀ {A : V} {P : V → Prop} {z : V}, Mem z (sep A P) ↔ Mem z A ∧ P z
  /-- A distinguished set, subject to the point's three laws below.  It
  is the one proof of every true proposition. -/
  pt : V
  /-- The one-element set `{pt}`. -/
  one : V
  /-- The members of `{pt}`. -/
  mem_one : ∀ {z : V}, Mem z one ↔ z = pt
  /-- The universe chain: `univ n` sizes `Sort n`, which denotes its
  restricted part `typeU n`. -/
  univ : Nat → V
  /-- `univ 0` is the set of subsets of `{pt}` — the truth values. -/
  mem_univ_zero : ∀ {T : V}, Mem T (univ 0) ↔ ∀ z, Mem z T → z = pt
  /-- Each universe is a member of the next. -/
  univ_mem_succ : ∀ n : Nat, Mem (univ n) (univ (n + 1))
  /-- Cumulativity. -/
  univ_mono : ∀ {m n : Nat} {x : V}, m ≤ n → Mem x (univ m) → Mem x (univ n)
  /-- The graph of a function on a domain. -/
  graph : (V → V) → V → V
  /-- The dependent function space: the graphs over `A` with values
  in the fibres `B`. -/
  piSet : V → (V → V) → V
  /-- Application.  On the point it is the point (a proof applied to
  anything is a proof); on a graph it reads the graph. -/
  app : V → V → V
  /-- A proof applied is the proof. -/
  app_pt : ∀ a : V, app pt a = pt
  /-- β: a graph applied on its domain computes. -/
  app_graph : ∀ {F : V → V} {A a : V}, Mem a A → app (graph F A) a = F a
  /-- A graph is never the point. -/
  graph_ne_pt : ∀ {F : V → V} {A : V}, graph F A ≠ pt
  /-- A graph depends only on the function's values on the domain. -/
  graph_congr : ∀ {F F' : V → V} {A : V}, (∀ x, Mem x A → F x = F' x) → graph F A = graph F' A
  /-- A function space depends only on the fibres over the domain. -/
  piSet_congr : ∀ {A : V} {B B' : V → V}, (∀ x, Mem x A → B x = B' x) → piSet A B = piSet A B'
  /-- Introduction: fibre-wise members abstract into the space. -/
  graph_mem_piSet : ∀ {A : V} {F B : V → V},
    (∀ x, Mem x A → Mem (F x) (B x)) → Mem (graph F A) (piSet A B)
  /-- Elimination. -/
  app_mem_piSet : ∀ {A f a : V} {B : V → V}, Mem f (piSet A B) → Mem a A → Mem (app f a) (B a)
  /-- η: a member of a function space is the graph of its applications. -/
  graph_app_eq : ∀ {A f : V} {B : V → V}, Mem f (piSet A B) → graph (fun x => app f x) A = f
  /-- A graph determines its domain. -/
  piSet_dom_unique : ∀ {A A' f : V} {B B' : V → V},
    Mem f (piSet A B) → Mem f (piSet A' B') → A = A'
  /-- Closure of the positive universes under dependent function
  spaces. -/
  piSet_mem_univ : ∀ {n : Nat} {A : V} {B : V → V}, n ≠ 0 →
    Mem A (univ n) → (∀ x, Mem x A → Mem (B x) (univ n)) → Mem (piSet A B) (univ n)
  /-- Closure of the universes under separation. -/
  sep_mem_univ : ∀ {n : Nat} {A : V} {P : V → Prop}, Mem A (univ n) → Mem (sep A P) (univ n)
  /-- **The point's laws** (1): the point is not a truth value — it has
  a member other than itself. -/
  pt_not_mem_univ_zero : ¬ Mem pt (univ 0)
  /-- (2): the point has at most one member. -/
  pt_subsingleton : ∀ {x y : V}, Mem x pt → Mem y pt → x = y
  /-- (3): no graph is a member of the point. -/
  graph_not_mem_pt : ∀ {F : V → V} {A : V}, ¬ Mem (graph F A) pt

namespace SetLib

@[inherit_doc] scoped infix:50 " ∈ˢ " => Mem

variable {V : Type u} [SetLib V]

theorem mem_sep_of {A : V} {P : V → Prop} {x : V} (hx : x ∈ˢ A) (hp : P x) : x ∈ˢ sep A P :=
  mem_sep.mpr ⟨hx, hp⟩

/-! ## Truth values

An abbreviation, not a law: the truth value of a proposition is the
separation of `{pt}` by it. -/

/-- The truth value of a proposition: `{pt}` if it holds, `∅` if
not. -/
def truthVal (P : Prop) : V := sep one (fun _ => P)

/-- The members of a truth value. -/
theorem mem_truthVal {p : Prop} {z : V} : z ∈ˢ truthVal p ↔ z = pt ∧ p := by
  unfold truthVal; rw [mem_sep, mem_one]

theorem pt_mem_truthVal {p : Prop} (hp : p) : (pt : V) ∈ˢ truthVal p :=
  mem_truthVal.mpr ⟨rfl, hp⟩

theorem of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ˢ truthVal p) : p :=
  (mem_truthVal.mp hz).2

theorem eq_pt_of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ˢ truthVal p) : z = pt :=
  (mem_truthVal.mp hz).1

theorem truthVal_mem_univ_zero (p : Prop) : (truthVal p : V) ∈ˢ univ 0 :=
  mem_univ_zero.mpr fun _ hz => eq_pt_of_mem_truthVal hz

theorem eq_pt_of_mem_univ_zero {T x : V} (hT : T ∈ˢ univ 0) (hx : x ∈ˢ T) : x = pt :=
  mem_univ_zero.mp hT x hx

/-- An inhabited truth value is `{pt}`. -/
theorem eq_one_of_mem_univ_zero {T x : V} (hT : T ∈ˢ univ 0) (hx : x ∈ˢ T) : T = one :=
  ext fun z => ⟨fun hz => mem_one.mpr (eq_pt_of_mem_univ_zero hT hz),
    fun hz => by rw [mem_one.mp hz, ← eq_pt_of_mem_univ_zero hT hx]; exact hx⟩

theorem one_mem_univ_zero : (one : V) ∈ˢ univ 0 :=
  mem_univ_zero.mpr fun _ hz => mem_one.mp hz

theorem truthVal_congr {p q : Prop} (h : p ↔ q) : (truthVal p : V) = truthVal q :=
  ext fun z => by rw [mem_truthVal, mem_truthVal, h]

theorem ne_pt_of_mem_piSet {A f : V} {B : V → V} (hf : f ∈ˢ piSet A B) : f ≠ pt := by
  rw [← graph_app_eq hf]; exact graph_ne_pt

/-! ## The two regimes

`piR`/`lamR` read a `Bool` — "is the body a proposition here?", the
annotation's readout at the current valuation — and nothing else. -/

/-- **The propositional product** `Π₀(A, B)`: the truth value "every
fibre is `{pt}`".  When the fibres are truth values it is their
intersection `⋂ x ∈ A, B x` (the empty intersection being `{pt}`):
`{pt}` exactly when every fibre is, `∅` otherwise — the product of
subsets of a singleton.  Reducible, so proofs that unfold `piR true`
keep working. -/
abbrev piProp (A : V) (B : V → V) : V := truthVal (∀ x, x ∈ˢ A → B x = one)

/-- The dependent product at regime `p`: the propositional product
when `p`, the graph space above it. -/
def piR (p : Bool) (A : V) (B : V → V) : V :=
  if p then piProp A B else piSet A B

/-- Abstraction at regime `p`: the point when `p`, the graph above it. -/
def lamR (p : Bool) (A : V) (F : V → V) : V :=
  if p then pt else graph F A

theorem piR_true {A : V} {B : V → V} :
    piR true A B = truthVal (∀ x, x ∈ˢ A → B x = one) := rfl
theorem piR_false {A : V} {B : V → V} : piR false A B = piSet A B := rfl
theorem lamR_true {A : V} {F : V → V} : lamR true A F = (pt : V) := rfl
theorem lamR_false {A : V} {F : V → V} : lamR false A F = graph F A := rfl

theorem piR_congr {p : Bool} {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piR p A B = piR p A B' := by
  cases p
  · exact piSet_congr h
  · exact truthVal_congr
      ⟨fun hi x hx => (h x hx).symm.trans (hi x hx), fun hi x hx => (h x hx).trans (hi x hx)⟩

theorem lamR_congr {p : Bool} {A : V} {F F' : V → V}
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lamR p A F = lamR p A F' := by
  cases p
  · exact graph_congr h
  · rfl

/-- Introduction: fibre-wise members abstract into the product.  The
fibre premise is used only at a proposition, where the fibres must be
truth values for the inhabited ones to be `{pt}`. -/
theorem lamR_mem {p : Bool} {A : V} {F B : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x)
    (hB : p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) : lamR p A F ∈ˢ piR p A B := by
  cases p
  · exact graph_mem_piSet hF
  · exact pt_mem_truthVal fun x hx => eq_one_of_mem_univ_zero (hB rfl x hx) (hF x hx)

/-- **Proof irrelevance at products**: an inhabitant of a
propositional product is the point. -/
theorem eq_pt_of_mem_piR_true {A f : V} {B : V → V} (hf : f ∈ˢ piR true A B) :
    f = pt := eq_pt_of_mem_truthVal hf

/-- Elimination.  At a proposition the member is the point and the
fibre is `{pt}`: no premise on the fibres is needed. -/
theorem app_mem_piR {p : Bool} {A f a : V} {B : V → V}
    (hf : f ∈ˢ piR p A B) (ha : a ∈ˢ A) : app f a ∈ˢ B a := by
  cases p
  · exact app_mem_piSet hf ha
  · rw [eq_pt_of_mem_piR_true hf, app_pt, of_mem_truthVal hf a ha]
    exact mem_one.mpr rfl

/-- β, conditional on domain membership. -/
theorem app_lamR {p : Bool} {A a : V} {F B : V → V}
    (ha : a ∈ˢ A) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x)
    (hB : p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) :
    app (lamR p A F) a = F a := by
  cases p
  · exact app_graph ha
  · rw [lamR_true, app_pt]
    exact (eq_pt_of_mem_univ_zero (hB rfl a ha) (hF a ha)).symm

/-- **β in the graph regime**: no typing premise whatsoever. -/
theorem app_lamR_false {A a : V} {F : V → V} (ha : a ∈ˢ A) :
    app (lamR false A F) a = F a := app_graph ha

/-- A graph-regime abstraction is never the point. -/
theorem lamR_false_ne_pt {A : V} {F : V → V} : lamR false A F ≠ (pt : V) := graph_ne_pt

/-- η: a member of a product is the abstraction of its applications. -/
theorem lamR_eta {p : Bool} {A f : V} {B : V → V} (hf : f ∈ˢ piR p A B) :
    lamR p A (fun x => app f x) = f := by
  cases p
  · exact graph_app_eq hf
  · rw [lamR_true, eq_pt_of_mem_piR_true hf]

/-- **Domain uniqueness** in the graph regime: a graph determines its
domain. -/
theorem piR_dom_unique {A A' f : V} {B B' : V → V}
    (h1 : f ∈ˢ piR false A B) (h2 : f ∈ˢ piR false A' B') : A = A' :=
  piSet_dom_unique h1 h2

/-- **Impredicativity**: a product landing in `Prop` is a truth value,
whatever its domain. -/
theorem piR_true_mem_univ_zero {A : V} {B : V → V} :
    piR true A B ∈ˢ (univ 0 : V) := truthVal_mem_univ_zero _

/-- The graph regime's universe membership. -/
theorem piR_false_mem_univ {n : Nat} {A : V} {B : V → V} (hn : n ≠ 0)
    (hA : A ∈ˢ univ n) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ n) :
    piR false A B ∈ˢ (univ n : V) := piSet_mem_univ hn hA hB

/-! ## The restricted universes

`univ` sizes things; what a sort *denotes* is `typeU`: `Sort 0` the
truth values, `Sort (n+1)` the members of `univ (n+1)` that are not
the point and do not contain it (**strict** sets).  A **type** is a
truth value or a strict set; its members are all the point (a truth
value) or none of them (a strict set).  This is what makes β sound at
every binder without a certificate: a member of a type of positive
sort is never the point (`ne_pt_of_mem_strict`). -/

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

@[simp] theorem Fib_true {X : V} : Fib true X ↔ X ∈ˢ univ 0 := Iff.rfl
@[simp] theorem Fib_false {X : V} : Fib false X ↔ Strict X := Iff.rfl

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

/-- A truth value or strict member of `univ n` in the right regime is
a member of `typeU n`. -/
theorem mem_typeU_of {n : Nat} {T : V} (hT : T ∈ˢ univ n) (hf : Fib (decide (n = 0)) T) :
    T ∈ˢ typeU n := by
  by_cases hn : n = 0
  · subst hn; exact mem_typeU_zero.mpr hf
  · simp only [hn, decide_false, Fib_false] at hf
    exact (mem_typeU_pos hn).mpr ⟨hT, hf⟩

/-- **(P)**: a member of a strict set is not the point. -/
theorem ne_pt_of_mem_strict {T x : V} (hT : Strict T) (hx : x ∈ˢ T) : x ≠ pt := by
  rintro rfl; exact hT.2 hx

/-- The members of a type are all the point or none of them. -/
theorem IsTy.eq_of_ne_pt {T x y : V} (hT : IsTy T) (hx : x ∈ˢ T) (hy : y ∈ˢ T)
    (h : x ≠ pt → y ≠ pt → x = y) : x = y := by
  rcases hT with hT | hT
  · rw [eq_pt_of_mem_univ_zero hT hx, eq_pt_of_mem_univ_zero hT hy]
  · exact h (ne_pt_of_mem_strict hT hx) (ne_pt_of_mem_strict hT hy)

/-! ### The point's neighbours -/

theorem pt_ne_truthVal_false : (pt : V) ≠ truthVal False := by
  intro h
  apply pt_not_mem_univ_zero (V := V)
  rw [h]
  exact truthVal_mem_univ_zero False

theorem exists_mem_pt : ∃ z, z ∈ˢ (pt : V) :=
  Classical.byContradiction fun h => pt_ne_truthVal_false (ext fun z =>
    ⟨fun hz => absurd ⟨z, hz⟩ h, fun hz => absurd (of_mem_truthVal hz) id⟩)

theorem ne_pt_of_two {X a b : V} (ha : a ∈ˢ X) (hb : b ∈ˢ X) (hab : a ≠ b) : X ≠ pt := by
  rintro rfl; exact hab (pt_subsingleton ha hb)

theorem one_ne_truthVal_false : (one : V) ≠ truthVal False := by
  intro h
  have : (pt : V) ∈ˢ one := mem_one.mpr rfl
  rw [h] at this
  exact of_mem_truthVal this

theorem univ_zero_ne_pt : (univ 0 : V) ≠ pt :=
  ne_pt_of_two one_mem_univ_zero (truthVal_mem_univ_zero False) one_ne_truthVal_false

theorem strict_univ_zero : Strict (univ 0 : V) := ⟨univ_zero_ne_pt, pt_not_mem_univ_zero⟩

theorem strict_truthVal_false : Strict (truthVal False : V) :=
  ⟨pt_ne_truthVal_false.symm, fun h => of_mem_truthVal h⟩

/-- `Sort n` is strict. -/
theorem strict_typeU (n : Nat) : Strict (typeU n : V) := by
  by_cases hn : n = 0
  · subst hn; simpa [typeU] using strict_univ_zero
  · refine ⟨?_, fun h => ((mem_typeU_pos hn).mp h).2.1 rfl⟩
    -- `typeU n` has two distinct members, the point at most one
    have h1 : (truthVal False : V) ∈ˢ typeU n :=
      (mem_typeU_pos hn).mpr ⟨univ_mono (Nat.zero_le n) (truthVal_mem_univ_zero False),
        strict_truthVal_false⟩
    have h2 : (univ 0 : V) ∈ˢ typeU n :=
      (mem_typeU_pos hn).mpr ⟨univ_mono (by omega) (univ_mem_succ 0), strict_univ_zero⟩
    refine ne_pt_of_two h1 h2 fun h => ?_
    have h3 : (one : V) ∈ˢ univ 0 := one_mem_univ_zero
    rw [← h] at h3
    exact of_mem_truthVal h3

theorem IsTy_typeU (n : Nat) : IsTy (typeU n : V) := Or.inr (strict_typeU n)

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

theorem Fib_piR {p : Bool} {A : V} {B : V → V} : Fib p (piR p A B) := by
  cases p
  · exact strict_piSet
  · exact piR_true_mem_univ_zero

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

/-- A truth value that is strict has no member. -/
theorem not_mem_of_univ_zero_strict {T z : V} (h0 : T ∈ˢ univ 0) (hs : Strict T) :
    ¬ z ∈ˢ T := fun hz => hs.2 (eq_pt_of_mem_univ_zero h0 hz ▸ hz)

/-- **The two regimes agree inside one sort** (task #343).  Two
products over one domain, with fibres that are in both regimes, and
that are members of one `typeU n`, are equal.  Where the regimes
differ: the fibres are truth values and strict, so empty; over an
inhabited domain both products are then empty, and over an empty
domain the propositional product is `{pt}`, which no `typeU (n+1)`
holds, and the function space holds a graph, which no truth value
does. -/
theorem piR_eq_of_mem_typeU {p q : Bool} {n : Nat} {A : V} {B : V → V}
    (hp : ∀ x, x ∈ˢ A → Fib p (B x)) (hq : ∀ x, x ∈ˢ A → Fib q (B x))
    (h₁ : piR p A B ∈ˢ typeU n) (h₂ : piR q A B ∈ˢ typeU n) :
    piR p A B = piR q A B := by
  -- the regimes differ, the first one propositional, without loss of generality
  suffices key : ∀ {p q : Bool}, p = true → q = false →
      (∀ x, x ∈ˢ A → Fib p (B x)) → (∀ x, x ∈ˢ A → Fib q (B x)) →
      piR p A B ∈ˢ typeU n → piR q A B ∈ˢ typeU n → piR p A B = piR q A B by
    cases p <;> cases q
    · rfl
    · exact (key rfl rfl hq hp h₂ h₁).symm
    · exact key rfl rfl hp hq h₁ h₂
    · rfl
  intro p q hpt hqf hp hq h₁ h₂
  subst hpt hqf
  -- every fibre over the domain is empty
  have hemp : ∀ x, x ∈ˢ A → ∀ z, ¬ z ∈ˢ B x := fun x hx _ =>
    not_mem_of_univ_zero_strict (hp x hx) (hq x hx)
  -- the domain is inhabited
  have hA : ∃ x, x ∈ˢ A := by
    refine Classical.byContradiction fun hne => ?_
    have hnA : ∀ x, ¬ x ∈ˢ A := fun x hx => hne ⟨x, hx⟩
    by_cases hn : n = 0
    · subst hn
      rw [piR_false, mem_typeU_zero] at h₂
      have hg : graph (fun x => x) A ∈ˢ piSet A B :=
        graph_mem_piSet fun x hx => absurd hx (hnA x)
      exact not_mem_of_univ_zero_strict h₂ strict_piSet hg
    · rw [mem_typeU_pos hn] at h₁
      exact h₁.2.2 (by rw [piR_true]; exact pt_mem_truthVal fun x hx => absurd hx (hnA x))
  obtain ⟨x₀, hx₀⟩ := hA
  refine ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · rw [piR_true] at hz
    have h1 := of_mem_truthVal hz x₀ hx₀
    exact absurd (mem_one.mpr rfl : (pt : V) ∈ˢ one) (h1 ▸ hemp x₀ hx₀ pt)
  · rw [piR_false] at hz
    exact absurd (app_mem_piSet hz hx₀) (hemp x₀ hx₀ _)

end SetLib

end Fragment
