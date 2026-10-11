module

public import ConLeche.SetTheory.Derive.Graphs
public import ConLeche.SetTheory.Derive.Omega

@[expose] public section

/-!
# The universe tower

`tg 0` is the set of truth values (`univZero`, the `U₀` of Mario
Carneiro, *The Type Theory of Lean*, master's thesis, Carnegie Mellon
University, 2019);
`tg (n+1)` is the chain universe `univChain (n+2)`.  The tower
starts two levels up the chain so that every positive level has the
inductive set `univChain 1` as a member — which is what puts `ω`
inside every positive level (a bare universe need not contain `ω`;
`V_ω` is one — and `univChain 0` need not be inhabited, the empty set
satisfying `IsTGUniverse` vacuously, so `univChain 1` is the first chain
member known to be inductive).  `tg 0 ∈ tg 1` because `univZero`
is built from `∅` by pairing/power closure inside the inhabited
universe `univChain 1 ∈ univChain 2`.  Cumulativity holds because
positive levels are transitive and each level is a member of the
next.

`tg` is the axiomatic Grothendieck chain — task #342's stepping
stones, named for Tarski–Grothendieck set theory (ruling R2, 2026-10-11).
`univ` is, for now, the very same tower: stage 1b of task #342 will
redefine it as the *restricted* universe (truth values at `0`, and
above the members of `tg n` that are neither the proof point nor
contain it), touching only this alias and the handful of lemmas just
below it — every site that reads `univ` today keeps reading it
unchanged.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The axiomatic chain interpreting `Sort n`, before task #342's
restriction (ruling R2) — the stepping stones `univ` is built from. -/
noncomputable def tg : Nat → V
  | 0 => univZero
  | n + 1 => univChain (n + 2)

theorem tg_zero : (tg 0 : V) = univZero := by rfl

/-- Positive levels are Grothendieck universes. -/
theorem tg_isTGUniverse {n : Nat} (hn : n ≠ 0) :
    IsTGUniverse (Mem (V := V)) (tg n) := by
  match n, hn with
  | m + 1, _ => exact univChain_tg _

theorem univChain_one_mem_tg_succ (n : Nat) :
    (univChain 1 : V) ∈ˢ tg (n + 1) :=
  univChain_mem_of_lt (Nat.succ_lt_succ n.succ_pos)

theorem tg_mem_tg (n : Nat) : (tg n : V) ∈ˢ tg (n + 1) := by
  match n with
  | 0 =>
    exact (univChain_tg 2).transitive (univChain_mem 1)
      ((univChain_tg 1).univZero_mem (univChain_mem 0))
  | m + 1 => exact univChain_mem (m + 2)

theorem tg_subset_succ (n : Nat) : (tg n : V) ⊆ˢ tg (n + 1) :=
  (tg_isTGUniverse (Nat.succ_ne_zero n)).subset_of_mem (tg_mem_tg n)

theorem tg_mono {m n : Nat} (h : m ≤ n) : (tg m : V) ⊆ˢ tg n := by
  induction n with
  | zero => cases Nat.le_zero.mp h; exact Subset.refl _
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (tg_subset_succ n)
    · exact Subset.refl _

theorem omega_mem_tg_succ (n : Nat) : (omega : V) ∈ˢ tg (n + 1) :=
  (tg_isTGUniverse (Nat.succ_ne_zero n)).omega_mem (univChain_one_mem_tg_succ n)

theorem empty_mem_tg : ∀ n : Nat, (empty : V) ∈ˢ tg n
  | 0 => mem_univZero.mpr (empty_subset _)
  | n + 1 =>
    (tg_isTGUniverse (Nat.succ_ne_zero n)).empty_mem (univChain_one_mem_tg_succ n)

theorem unitSet_mem_tg : ∀ n : Nat, (unitSet : V) ∈ˢ tg n
  | 0 => mem_univZero.mpr (Subset.refl _)
  | n + 1 =>
    (tg_isTGUniverse (Nat.succ_ne_zero n)).unitSet_mem (univChain_one_mem_tg_succ n)

/- Opaque interface operator (see `Derive/Empty.lean`). -/
attribute [irreducible] tg

/-! ## `univ`, for now the same tower (task #342, ruling R2)

Every site below reads "what `Sort u` means" (type-former formation,
checked-term typing, basis-law installation) and is routed through
`univ`, so stage 1b's redefinition touches only this definition and
these corollaries — not every call site.  `univ` itself is left at
the default transparency (unlike `tg`) exactly so these corollaries
discharge by `rfl`/direct defeq against the `tg` facts above; 1b may
reconsider that once `univ` is no longer literally `tg`. -/

/-- `univ` will become, at stage 1b, the restricted universe (the
whitepaper fragment's `typeU`); until then it is literally `tg`. -/
noncomputable def univ : Nat → V := tg

theorem univ_zero : (univ 0 : V) = univZero := tg_zero

theorem univ_isTGUniverse {n : Nat} (hn : n ≠ 0) :
    IsTGUniverse (Mem (V := V)) (univ n) := tg_isTGUniverse hn

theorem univChain_one_mem_univ_succ (n : Nat) :
    (univChain 1 : V) ∈ˢ univ (n + 1) := univChain_one_mem_tg_succ n

theorem univ_mem_univ (n : Nat) : (univ n : V) ∈ˢ univ (n + 1) := tg_mem_tg n

theorem univ_subset_succ (n : Nat) : (univ n : V) ⊆ˢ univ (n + 1) := tg_subset_succ n

theorem univ_mono {m n : Nat} (h : m ≤ n) : (univ m : V) ⊆ˢ univ n := tg_mono h

theorem omega_mem_univ_succ (n : Nat) : (omega : V) ∈ˢ univ (n + 1) := omega_mem_tg_succ n

theorem empty_mem_univ (n : Nat) : (empty : V) ∈ˢ univ n := empty_mem_tg n

theorem unitSet_mem_univ (n : Nat) : (unitSet : V) ∈ˢ univ n := unitSet_mem_tg n

end ConLeche.SetTheory
