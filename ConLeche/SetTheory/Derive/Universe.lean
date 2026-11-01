module

public import ConLeche.SetTheory.Derive.Pair

@[expose] public section

/-!
# Grothendieck universes: the closure laws

The engine room, recovering the Grothendieck-universe closure laws
(SGA 4, Exp. I, Appendix) from the five first-order clauses
`IsUniverse` — applied downstream to the chain members `univChain n`.
Pairing, power, binary union, `⋃` of a member, and replacement
images all reduce to the clauses: `⋃` and the image closures are
instances of the union and fibre-wise replacement clauses (the former
via a subset argument, the latter directly), and pairing is fibre-wise
replacement over the two-element member `power (power ∅)`.  No
diagonal argument is needed anywhere.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

section IsUniverse

variable {U : V} (hU : IsUniverse (Mem (V := V)) U)

include hU

theorem _root_.ConLeche.IsUniverse.transitive : ∀ {y z : V}, y ∈ˢ U → z ∈ˢ y → z ∈ˢ U :=
  fun {y z} hy hz => hU.1 y z hy hz

theorem _root_.ConLeche.IsUniverse.mem_of_subset_mem : ∀ {y z : V}, y ∈ˢ U → z ⊆ˢ y → z ∈ˢ U :=
  fun {y z} hy hz => hU.2.1 y z hy hz

theorem _root_.ConLeche.IsUniverse.subset_of_mem {y : V} (hy : y ∈ˢ U) : y ⊆ˢ U :=
  fun _ hz => hU.transitive hy hz

theorem _root_.ConLeche.IsUniverse.power_mem {y : V} (hy : y ∈ˢ U) : power y ∈ˢ U := by
  obtain ⟨p, hp, hsub⟩ := hU.2.2.1 y hy
  exact hU.mem_of_subset_mem hp fun z hz => hsub z (mem_power.mp hz)

/-- Replacement closure: the image of a member under a fibre-wise
member-valued function is a member.  Direct instance of the
fibre-wise replacement clause. -/
theorem _root_.ConLeche.IsUniverse.image_mem {A : V} {F : V → V}
    (hA : A ∈ˢ U) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ U) : image F A ∈ˢ U := by
  have hfun : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ U ∧ (y = F x) ∧ ∀ y', (y' = F x) → y' = y := by
    intro x hx
    exact ⟨F x, hF x hx, rfl, fun y' h => h⟩
  obtain ⟨b, hb, hspec⟩ := hU.2.2.2.2 A hA (fun x y => (y = F x)) hfun
  have heq : image F A = b := ext fun z => by
    rw [mem_image]
    constructor
    · rintro ⟨w, hw, hz⟩
      exact (hspec z).mpr ⟨w, hw, hz⟩
    · intro hz
      obtain ⟨w, hw, hzw⟩ := (hspec z).mp hz
      exact ⟨w, hw, hzw⟩
  rw [heq]
  exact hb

theorem _root_.ConLeche.IsUniverse.empty_mem {y : V} (hy : y ∈ˢ U) : (empty : V) ∈ˢ U :=
  hU.mem_of_subset_mem hy (empty_subset y)

open Classical in
/-- Pairing closure: fibre-wise replacement over the two-element member
`power (power ∅) = {∅, {∅}}`, via the relation
`x ↦ (if x = ∅ then a else b)`. -/
theorem _root_.ConLeche.IsUniverse.upair_mem {a b y : V} (hy : y ∈ˢ U)
    (ha : a ∈ˢ U) (hb : b ∈ˢ U) : upair a b ∈ˢ U := by
  have h2 : power (power (empty : V)) ∈ˢ U :=
    (hU.empty_mem hy |> hU.power_mem) |> hU.power_mem
  have hfun : ∀ x, x ∈ˢ power (power (empty : V)) →
      ∃ y, y ∈ˢ U ∧ (y = if x = empty then a else b) ∧
        ∀ y', (y' = if x = empty then a else b) → y' = y := by
    intro x hx
    by_cases hx0 : x = empty
    · refine ⟨a, ha, ?_, fun y' hy' => ?_⟩
      · rw [ite_eq_left hx0]
      · rw [ite_eq_left hx0] at hy'; exact hy'
    · refine ⟨b, hb, ?_, fun y' hy' => ?_⟩
      · rw [ite_eq_right hx0]
      · rw [ite_eq_right hx0] at hy'; exact hy'
  obtain ⟨c, hc, hspec⟩ :=
    hU.2.2.2.2 (power (power (empty : V))) h2 (fun x y => (y = if x = empty then a else b)) hfun
  have heq : upair a b = c := ext fun z => by
    constructor
    · intro hz
      rcases mem_upair.mp hz with h | h
      · rw [h]
        exact (hspec a).mpr ⟨empty, mem_power.mpr (empty_subset _), by simp⟩
      · rw [h]
        have hne : power (empty : V) ≠ empty :=
          ne_empty_of_mem (mem_power.mpr (Subset.refl _))
        exact (hspec b).mpr ⟨power empty, mem_power.mpr (Subset.refl _), by simp [hne]⟩
    · intro hz
      obtain ⟨x, hx, hzw⟩ := (hspec z).mp hz
      by_cases hx0 : x = empty
      · rw [ite_eq_left hx0] at hzw; rw [hzw]; exact mem_upair.mpr (Or.inl rfl)
      · rw [ite_eq_right hx0] at hzw; rw [hzw]; exact mem_upair.mpr (Or.inr rfl)
  rw [heq]
  exact hc

theorem _root_.ConLeche.IsUniverse.sing_mem {a y : V} (hy : y ∈ˢ U) (ha : a ∈ˢ U) :
    sing a ∈ˢ U := hU.upair_mem hy ha ha

/-- `⋃` closure.  The union clause hands back a member `q` whose
members are exactly the members of the members of `s`; `sUnion s ⊆ q`
then closes by the subset clause. -/
theorem _root_.ConLeche.IsUniverse.sUnion_mem {s : V} (hs : s ∈ˢ U) : sUnion s ∈ˢ U := by
  obtain ⟨q, hq, hqmem⟩ := hU.2.2.2.1 s hs
  refine hU.mem_of_subset_mem hq fun z hz => ?_
  exact (hqmem z).mpr (mem_sUnion.mp hz)

theorem _root_.ConLeche.IsUniverse.binUnion_mem {a b y : V} (hy : y ∈ˢ U)
    (ha : a ∈ˢ U) (hb : b ∈ˢ U) : binUnion a b ∈ˢ U :=
  hU.sUnion_mem (hU.upair_mem hy ha hb)

theorem _root_.ConLeche.IsUniverse.kpair_mem {a b y : V} (hy : y ∈ˢ U)
    (ha : a ∈ˢ U) (hb : b ∈ˢ U) : kpair a b ∈ˢ U :=
  hU.upair_mem hy (hU.sing_mem hy ha) (hU.upair_mem hy ha hb)

theorem _root_.ConLeche.IsUniverse.sep_mem {a : V} {p : V → Prop} (ha : a ∈ˢ U) :
    sep a p ∈ˢ U :=
  hU.mem_of_subset_mem ha sep_subset

/-- Union of a member-indexed family of members. -/
theorem _root_.ConLeche.IsUniverse.famUnion_mem {A : V} {F : V → V}
    (hA : A ∈ˢ U) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ U) :
    sUnion (image F A) ∈ˢ U :=
  hU.sUnion_mem (hU.image_mem hA hF)

end IsUniverse

/-- Chain membership generalizes along the ordering, by transitivity
of the higher universe. -/
theorem univChain_mem_of_lt {m n : Nat} (h : m < n) :
    (univChain m : V) ∈ˢ univChain n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · exact (univChain_univ (n + 1)).transitive (univChain_mem n) (ih h')
    · exact univChain_mem m

end ConLeche.SetTheory
