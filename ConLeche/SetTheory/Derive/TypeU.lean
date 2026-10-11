module

public import ConLeche.SetTheory.Derive.Graphs
public import ConLeche.SetTheory.Derive.Tg

@[expose] public section

/-!
# The restricted universes (task #342)

What a sort denotes, in the target design of task #342 (the whitepaper
fragment's `typeU`, `whitepaper/Fragment/Lib.lean` on `agent/340-brave`):
`Sort 0` the truth values, `Sort (n+1)` the members of the axiomatic
level `tg (n+1)` that are not the proof point and do not contain it
(**strict** sets).  A **type** is a truth value or a strict set; its
members are all the point (a truth value) or none of them (a strict
set).  That dichotomy is what makes β sound at every binder without a
certificate: a member of a type of positive sort is never the point
(`ne_pt_of_mem_strict`).

The chain `tg` (`Derive/Tg.lean`) sizes things; `typeU` is what the
typing will read.  Nothing reads `typeU` yet: stage 1b flips `univ`
(`Derive/Univ.lean`) to it (ruling R2).  The zero regime is stated
with `univZero`, which is `tg 0`, `typeU 0` and `univ 0` alike, before
and after the flip.

Also here, the last point law: `pt ∉ ω` (the others are in
`Derive/Pt.lean` and `Derive/Graphs.lean`).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The point is not a natural number -/

/-- `pt ∉ ω`: every nonzero von Neumann numeral has `∅` as a member,
and the point's one member `ptTag` is not `∅` (it has `∅` as a member). -/
theorem pt_not_mem_omega : ¬ (pt : V) ∈ˢ omega := by
  intro h
  obtain ⟨k, hk⟩ := mem_omega_iff.mp h
  match k, hk with
  | 0, hk => exact pt_ne_empty hk
  | k + 1, hk =>
    have h0 : (vnat 0 : V) ∈ˢ pt := hk ▸ vnat_mem_vnat_of_lt (Nat.succ_pos k)
    have h1 : (empty : V) = ptTag := mem_pt.mp h0
    have h2 := empty_mem_ptTag (V := V)
    rw [← h1] at h2
    exact not_mem_empty _ h2

/-! ## Strict sets, types, fibres -/

/-- A **strict** set: not the point, and the point is not a member. -/
def Strict (X : V) : Prop := X ≠ pt ∧ ¬ pt ∈ˢ X

/-- A **type**: a truth value, or a strict set. -/
def IsTy (X : V) : Prop := X ∈ˢ univZero ∨ Strict X

/-- The regime of a fibre: a truth value at a proposition, strict above. -/
def Fib : Bool → V → Prop
  | true, X => X ∈ˢ univZero
  | false, X => Strict X

@[simp] theorem Fib_true {X : V} : Fib true X ↔ X ∈ˢ univZero := Iff.rfl
@[simp] theorem Fib_false {X : V} : Fib false X ↔ Strict X := Iff.rfl

open Classical in
/-- **What `Sort n` will denote**: the truth values at `0`, the strict
members of the axiomatic level `tg n` above. -/
noncomputable def typeU (n : Nat) : V := if n = 0 then tg 0 else sep (tg n) Strict

theorem typeU_zero : (typeU 0 : V) = univZero := by
  unfold typeU; rw [ite_eq_left rfl, tg_zero]

theorem mem_typeU_zero {T : V} : T ∈ˢ (typeU 0 : V) ↔ T ∈ˢ univZero := by
  rw [typeU_zero]

theorem mem_typeU_pos {n : Nat} (hn : n ≠ 0) {T : V} :
    T ∈ˢ (typeU n : V) ↔ T ∈ˢ tg n ∧ Strict T := by
  unfold typeU; rw [ite_eq_right hn]; exact mem_sep

theorem typeU_subset_tg (n : Nat) : (typeU n : V) ⊆ˢ tg n := by
  by_cases hn : n = 0
  · subst hn; intro T hT; rw [tg_zero]; exact mem_typeU_zero.mp hT
  · intro T hT; exact ((mem_typeU_pos hn).mp hT).1

theorem mem_tg_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ (typeU n : V)) : T ∈ˢ tg n :=
  typeU_subset_tg n T h

theorem ne_pt_of_mem_univZero {T : V} (h : T ∈ˢ (univZero : V)) : T ≠ pt := by
  rintro rfl; exact pt_not_mem_univZero h

theorem Strict.ne_pt {X : V} (h : Strict X) : X ≠ pt := h.1

theorem IsTy.ne_pt {T : V} (h : IsTy T) : T ≠ pt := by
  rcases h with h | h
  · exact ne_pt_of_mem_univZero h
  · exact h.1

theorem IsTy_of_Fib {p : Bool} {X : V} (h : Fib p X) : IsTy X := by
  cases p
  · exact Or.inr h
  · exact Or.inl h

theorem Fib.ne_pt {p : Bool} {X : V} (h : Fib p X) : X ≠ pt := (IsTy_of_Fib h).ne_pt

theorem IsTy_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ (typeU n : V)) : IsTy T := by
  by_cases hn : n = 0
  · subst hn; exact Or.inl (mem_typeU_zero.mp h)
  · exact Or.inr ((mem_typeU_pos hn).mp h).2

/-- A member of `typeU n` is in the regime of `n`'s zero-ness. -/
theorem Fib_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ (typeU n : V)) :
    Fib (decide (n = 0)) T := by
  by_cases hn : n = 0
  · subst hn; exact mem_typeU_zero.mp h
  · simp only [hn, decide_false]; exact ((mem_typeU_pos hn).mp h).2

/-- A truth value or strict member of `tg n` in the right regime is a
member of `typeU n`. -/
theorem mem_typeU_of {n : Nat} {T : V} (hT : T ∈ˢ tg n) (hf : Fib (decide (n = 0)) T) :
    T ∈ˢ (typeU n : V) := by
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
  · rw [eq_pt_of_mem_univZero hT hx, eq_pt_of_mem_univZero hT hy]
  · exact h (ne_pt_of_mem_strict hT hx) (ne_pt_of_mem_strict hT hy)

/-! ## Strict sets -/

/-- A set with two distinct members is not the point. -/
theorem ne_pt_of_two {X a b : V} (ha : a ∈ˢ X) (hb : b ∈ˢ X) (hab : a ≠ b) : X ≠ pt := by
  rintro rfl; exact hab (eq_of_mem_pt ha hb)

/-- A set whose members are all Kuratowski pairs (tagged values) is
strict: the point's one member `ptTag` is not a pair, and the point
itself is not a pair. -/
theorem strict_of_kpairs {X : V} (h : ∀ z, z ∈ˢ X → ∃ a b, z = kpair a b) : Strict X := by
  refine ⟨?_, fun hp => ?_⟩
  · rintro rfl
    obtain ⟨a, b, hab⟩ := h ptTag ptTag_mem_pt
    exact ptTag_ne_kpair a b hab
  · obtain ⟨a, b, hab⟩ := h pt hp
    exact pt_ne_kpair a b hab

theorem strict_empty : Strict (empty : V) :=
  ⟨pt_ne_empty.symm, not_mem_empty _⟩

theorem univZero_ne_pt : (univZero : V) ≠ pt :=
  ne_pt_of_two (mem_univZero.mpr (Subset.refl _)) (mem_univZero.mpr (empty_subset _))
    unitSet_ne_empty

theorem strict_univZero : Strict (univZero : V) := ⟨univZero_ne_pt, pt_not_mem_univZero⟩

theorem strict_omega : Strict (omega : V) := by
  refine ⟨?_, pt_not_mem_omega⟩
  refine ne_pt_of_two empty_mem_omega (vsucc_mem_omega empty_mem_omega) ?_
  exact fun h => vsucc_ne_empty _ h.symm

/-- A function space is strict: its members are graphs, and the point's
member is not one. -/
theorem strict_piSet {A : V} {B : V → V} : Strict (piSet A B) := by
  refine ⟨?_, fun h => ne_pt_of_mem_piSet h rfl⟩
  intro he
  have hz : (ptTag : V) ∈ˢ piSet A B := he ▸ ptTag_mem_pt
  have h1 := eq_graph_app_of_mem_piSet hz
  have h2 : graph (fun x => app ptTag x) A ∈ˢ (pt : V) := by rw [h1]; exact ptTag_mem_pt
  exact graph_not_mem_pt h2

/-- A dependent pair set is strict: its members are pairs. -/
theorem strict_sigmaPairs {A : V} {B : V → V} : Strict (sigmaPairs A B) :=
  strict_of_kpairs fun z hz => by
    obtain ⟨x, -, y, -, rfl⟩ := mem_sigmaPairs.mp hz
    exact ⟨x, y, rfl⟩

theorem IsTy_of_strict {X : V} (h : Strict X) : IsTy X := Or.inr h

/-! ## The sorts themselves -/

theorem univZero_mem_tg_succ (n : Nat) : (univZero : V) ∈ˢ tg (n + 1) := by
  have h := tg_mem_tg (V := V) 0
  rw [tg_zero] at h
  exact tg_mono (Nat.succ_le_succ (Nat.zero_le n)) _ h

/-- `Sort n` is strict. -/
theorem strict_typeU (n : Nat) : Strict (typeU n : V) := by
  by_cases hn : n = 0
  · subst hn; rw [typeU_zero]; exact strict_univZero
  · refine ⟨?_, fun h => ((mem_typeU_pos hn).mp h).2.1 rfl⟩
    -- `typeU n` has two distinct members, the point at most one
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have h1 : (empty : V) ∈ˢ typeU (m + 1) :=
      (mem_typeU_pos hn).mpr ⟨empty_mem_tg _, strict_empty⟩
    have h2 : (univZero : V) ∈ˢ typeU (m + 1) :=
      (mem_typeU_pos hn).mpr ⟨univZero_mem_tg_succ m, strict_univZero⟩
    refine ne_pt_of_two h1 h2 fun h => ?_
    have h3 : (unitSet : V) ∈ˢ univZero := mem_univZero.mpr (Subset.refl _)
    rw [← h] at h3
    exact not_mem_empty _ h3

theorem IsTy_typeU (n : Nat) : IsTy (typeU n : V) := Or.inr (strict_typeU n)

theorem typeU_mem_tg_succ (n : Nat) : (typeU n : V) ∈ˢ tg (n + 1) := by
  by_cases hn : n = 0
  · subst hn; rw [typeU_zero]; exact univZero_mem_tg_succ 0
  · unfold typeU; rw [ite_eq_right hn]
    exact (tg_isTGUniverse (Nat.succ_ne_zero n)).sep_mem (tg_mem_tg n)

/-- `Sort n : Sort (n+1)`. -/
theorem typeU_mem_typeU_succ (n : Nat) : (typeU n : V) ∈ˢ typeU (n + 1) :=
  (mem_typeU_pos (Nat.succ_ne_zero n)).mpr ⟨typeU_mem_tg_succ n, strict_typeU n⟩

/-- `ω` is a type of every positive sort. -/
theorem omega_mem_typeU_succ (n : Nat) : (omega : V) ∈ˢ typeU (n + 1) :=
  (mem_typeU_pos (Nat.succ_ne_zero n)).mpr ⟨omega_mem_tg_succ n, strict_omega⟩

/-- The empty type is a type of every sort. -/
theorem empty_mem_typeU (n : Nat) : (empty : V) ∈ˢ typeU n := by
  by_cases hn : n = 0
  · subst hn; exact mem_typeU_zero.mpr (mem_univZero.mpr (empty_subset _))
  · exact (mem_typeU_pos hn).mpr ⟨empty_mem_tg n, strict_empty⟩

/- `typeU` is the opaque operator stage 1b's `univ` will be; its laws
are the lemmas above. -/
attribute [irreducible] typeU

end ConLeche.SetTheory
