module

public import ConLeche.Semantics.Tower.TowerKit

public section

/-!
# Comparisons off the point need one type (task #342 L7)

Under conditional claims a comparison says "equal where neither side is
the point".  Inside ONE type that is equality (`IsTy.eq_of_ne_pt`,
`spineFit_eq_of_cond`); across two types it is not: `True = {pt}` and
`ω` are both types of `Sort 1` (the universe is cumulative), and the
point in the first and `0 = ∅` in the second are "conditionally equal"
but different.  This is why a ι comparison is upgraded only between fits
of one telescope — and why a `.plain` rule's index comparison outside
case 3, whose
two sides sit at two parameter frames, is not.
-/

namespace ConLeche.Semantics.CondCompareTest

open SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- Two types of `Sort 1`, one value each, conditionally equal and
different. -/
example :
    (unitSet : V) ∈ˢ (univ 1 : V) ∧ (omega : V) ∈ˢ (univ 1 : V) ∧
      (pt : V) ∈ˢ (unitSet : V) ∧ (empty : V) ∈ˢ (omega : V) ∧
      ((pt : V) ≠ pt → (empty : V) ≠ pt → (pt : V) = empty) ∧ (pt : V) ≠ empty :=
  ⟨univ_mono (Nat.zero_le 1) _ (unitSet_mem_univ 0), omega_mem_univ_succ 0,
    pt_mem_unitSet, empty_mem_omega, fun h => absurd rfl h, pt_ne_empty⟩

/-- Inside one type, conditional equality is equality. -/
example {T x y : V} (hT : IsTy T) (hx : x ∈ˢ T) (hy : y ∈ˢ T)
    (h : x ≠ pt → y ≠ pt → x = y) : x = y :=
  hT.eq_of_ne_pt hx hy h

/-- And along one telescope of types (`FitsVals_eq_of_cond`). -/
example {Fs : List AnnotTerm} {ρ : Nat → V} {as bs : List V}
    (hT : SpineTy ρ Fs) (ha : SpineFit ρ Fs as) (hb : SpineFit ρ Fs bs)
    (h : ∀ p ∈ as.zip bs, p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) : as = bs :=
  spineFit_eq_of_cond hT ha hb h

end ConLeche.Semantics.CondCompareTest
