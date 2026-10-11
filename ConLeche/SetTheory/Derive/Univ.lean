module

public import ConLeche.SetTheory.Derive.TypeU

@[expose] public section

/-!
# `univ`: what `Sort n` means

The axiomatic chain `tg` (`Derive/Tg.lean`) is the stepping stones;
the restricted universes `typeU` (`Derive/TypeU.lean`) are what a
sort will denote.  `univ` is, for now, still `tg`: stage 1b of task
#342 (ruling R2) flips this one definition to `typeU`.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

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
