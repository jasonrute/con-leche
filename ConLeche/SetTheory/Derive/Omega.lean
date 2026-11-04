module

public import ConLeche.SetTheory.Derive.FormOps
public import ConLeche.SetTheory.Derive.Universe

@[expose] public section

/-!
# Infinity, derived: the finite ordinals

Infinity is derived from the universe chain + Replacement: an
*inhabited* Grothendieck universe is an inductive *set* — it contains
`∅` and is closed under the von Neumann successor `n ↦ n ∪ {n}`
(von Neumann 1923) by the pairing/union closures — so `ω` can be
separated out of one as the members of *every* inductive set.
Leastness is then definitional.  The inductive universe used is
`univChain 1`: it is inhabited by `univChain 0` (note `univChain 0`
itself need not be — the empty set satisfies `IsUniverse`
vacuously).

`vnat : Nat → V` names the members of `ω` from the meta-level; every
member of `ω` is a unique `vnat k` (`mem_omega_iff`, `vnat_inj`),
which is what makes recursion on `ω` cheap in `Derive/Natrec.lean`.

`ω` itself is a *member* of any universe that has the inductive
universe `univChain 1` as a member — arranged for the tower in
`Derive/Univ.lean`.  (Mere universehood does not suffice: `V_ω` is a
Tarski universe without `ω`.)
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]


/-- An inhabited Grothendieck universe is an inductive set. -/
theorem _root_.ConLeche.IsUniverse.inductive_self {U y : V}
    (hU : IsUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) : Inductive U :=
  ⟨hU.empty_mem hy, fun _n hn =>
    hU.binUnion_mem hy hn (hU.sing_mem hy hn)⟩

theorem univChain_one_inductive : Inductive (univChain 1 : V) :=
  (univChain_univ 1).inductive_self (univChain_mem 0)

/-- The finite ordinals: the members of every inductive set, separated
from the inductive universe `univChain 1` by the *definable* formula
`omegaF` (so first-order replacement applies to it). -/
noncomputable def omega : V :=
  sepF (univChain 1) omegaF Form.nil

theorem mem_omega {n : V} : n ∈ˢ (omega : V) ↔ ∀ I : V, Inductive I → n ∈ˢ I := by
  rw [omega, mem_sepF, realize_omegaF]
  exact ⟨fun h => h.2, fun h => ⟨h _ univChain_one_inductive, h⟩⟩

theorem omega_subset_inductive {I : V} (hI : Inductive I) : (omega : V) ⊆ˢ I :=
  fun _ hn => mem_omega.mp hn I hI

theorem omega_inductive : Inductive (omega : V) := by
  constructor
  · exact mem_omega.mpr fun I hI => hI.1
  · intro n hn
    exact mem_omega.mpr fun I hI => hI.2 n (mem_omega.mp hn I hI)

theorem empty_mem_omega : (empty : V) ∈ˢ omega := omega_inductive.1

theorem vsucc_mem_omega {n : V} (hn : n ∈ˢ (omega : V)) : vsucc n ∈ˢ (omega : V) :=
  omega_inductive.2 n hn

/-- **Definable induction on `ω`** (the first-order induction scheme,
from `replF` via `sepF`): if a definable property with parameters `p`
holds at `∅` and is closed under `vsucc` on `ω`, it holds at every
member of `ω`.  The induction set `sepF ω φ p` is inductive, and
every member of `ω` lies in every inductive set (`mem_omega`). -/
theorem omega_induction {n : Nat} {φ : Form (n + 1)} {p : Fin n → V}
    (h0 : Form.Realize Mem (Form.snoc p (empty : V)) φ)
    (hstep : ∀ x : V, x ∈ˢ (omega : V) →
      Form.Realize Mem (Form.snoc p x) φ →
      Form.Realize Mem (Form.snoc p (vsucc x)) φ)
    {x : V} (hx : x ∈ˢ (omega : V)) :
    Form.Realize Mem (Form.snoc p x) φ := by
  have hind : Inductive (sepF (omega : V) φ p) := by
    constructor
    · exact mem_sepF.mpr ⟨empty_mem_omega, h0⟩
    · intro y hy
      obtain ⟨hyo, hyph⟩ := mem_sepF.mp hy
      exact mem_sepF.mpr ⟨vsucc_mem_omega hyo, hstep y hyo hyph⟩
  exact (mem_sepF.mp (mem_omega.mp hx _ hind)).2

/-- The `k`-th von Neumann natural. -/
noncomputable def vnat : Nat → V
  | 0 => empty
  | k + 1 => vsucc (vnat k)

theorem vnat_mem_omega : ∀ k, (vnat k : V) ∈ˢ omega
  | 0 => empty_mem_omega
  | k + 1 => vsucc_mem_omega (vnat_mem_omega k)

/-- Every finite ordinal is named by a meta-level natural. -/
theorem mem_omega_iff {n : V} : n ∈ˢ (omega : V) ↔ ∃ k, n = vnat k := by
  constructor
  · intro hn
    have hind : Inductive (sep (omega : V) (fun n => ∃ k, n = vnat k)) := by
      constructor
      · exact mem_sep.mpr ⟨empty_mem_omega, 0, rfl⟩
      · intro m hm
        obtain ⟨hmo, k, rfl⟩ := mem_sep.mp hm
        exact mem_sep.mpr ⟨vsucc_mem_omega hmo, k + 1, rfl⟩
    exact (mem_sep.mp (omega_subset_inductive hind n hn)).2
  · rintro ⟨k, rfl⟩
    exact vnat_mem_omega k

theorem vnat_mem_vnat_of_lt : ∀ {k l : Nat}, k < l → (vnat k : V) ∈ˢ vnat l := by
  intro k l hkl
  induction l with
  | zero => exact absurd hkl (Nat.not_lt_zero k)
  | succ l ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hkl with h | rfl
    · exact mem_vsucc.mpr (Or.inl (ih h))
    · exact self_mem_vsucc _

theorem vnat_inj {k l : Nat} (h : (vnat k : V) = vnat l) : k = l := by
  rcases Nat.lt_trichotomy k l with hlt | heq | hgt
  · exact absurd (h ▸ vnat_mem_vnat_of_lt (V := V) hlt) (not_mem_self _)
  · exact heq
  · exact absurd (h ▸ vnat_mem_vnat_of_lt (V := V) hgt) (not_mem_self _)


/-- Membership in a numeral is exactly the smaller numerals (proved by
meta-level induction on the name `k`, no `mem_omega_iff` needed). -/
theorem mem_vnat_iff {k : Nat} {a : V} :
    a ∈ˢ (vnat k : V) ↔ ∃ n, n < k ∧ a = vnat n := by
  induction k with
  | zero =>
    exact ⟨fun h => absurd h (not_mem_empty _),
      fun ⟨n, hn, _⟩ => absurd hn (Nat.not_lt_zero n)⟩
  | succ k ih =>
    rw [show (vnat (k + 1) : V) = vsucc (vnat k) from rfl, mem_vsucc, ih]
    constructor
    · rintro (⟨n, hn, rfl⟩ | rfl)
      · exact ⟨n, Nat.lt_succ_of_lt hn, rfl⟩
      · exact ⟨k, Nat.lt_succ_self k, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | rfl
      · exact Or.inl ⟨n, h, rfl⟩
      · exact Or.inr rfl

theorem omega_subset_univChain_one : (omega : V) ⊆ˢ univChain 1 := sepF_subset

/-- `ω` is a member of any universe having the inductive universe
`univChain 1` as a member. -/
theorem _root_.ConLeche.IsUniverse.omega_mem {U : V}
    (hU : IsUniverse (Mem (V := V)) U) (h1 : (univChain 1 : V) ∈ˢ U) :
    (omega : V) ∈ˢ U :=
  hU.mem_of_subset_mem h1 omega_subset_univChain_one

/- Opaque interface operator (see `Derive/Empty.lean`).  `vsucc` stays
reducible: `Derive/Natrec.lean` computes with it through `vnat`. -/
attribute [irreducible] omega

end ConLeche.SetTheory
