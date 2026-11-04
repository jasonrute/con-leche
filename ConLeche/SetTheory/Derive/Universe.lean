module

public import ConLeche.SetTheory.Derive.Pair

@[expose] public section

/-!
# Grothendieck universes: the closure laws

The engine room, recovering the Grothendieck-universe closure laws
(SGA 4, Exp. I, Appendix) from the first-order clauses
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
  obtain ⟨b, hb, hspec⟩ := hU.2.2.2.2.1 A hA (fun x y => (y = F x)) hfun
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

/-- Definable version of `image_mem`: the `imageF` of a member under a
functional definable relation with member values is a member.  Direct
instance of the *definable* fibre-replacement clause (clause 6) — no
meta-level relation is involved, so this is first-order. -/
theorem _root_.ConLeche.IsUniverse.imageF_mem {A : V} {n : Nat} {ψ : Form (n + 2)}
    {p : Fin n → V} {hfun : ∀ x, x ∈ˢ A → ∃ y, Form.Realize Mem (Form.cons2 x y p) ψ ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' p) ψ → y' = y}
    (hA : A ∈ˢ U)
    (hval : ∀ x, x ∈ˢ A → ∀ y, Form.Realize Mem (Form.cons2 x y p) ψ → y ∈ˢ U) :
    imageF ψ p A hfun ∈ˢ U := by
  have hfunU : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ U ∧ Form.Realize Mem (Form.cons2 x y p) ψ ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' p) ψ → y' = y := by
    intro x hx
    obtain ⟨y, hyp, huniq⟩ := hfun x hx
    exact ⟨y, hval x hx y hyp, hyp, huniq⟩
  obtain ⟨b, hb, hspec⟩ := hU.2.2.2.2.2 n ψ p A hA hfunU
  have heq : imageF ψ p A hfun = b := ext fun z => by
    rw [mem_imageF hfun, hspec]
  rw [heq]
  exact hb

theorem _root_.ConLeche.IsUniverse.empty_mem {y : V} (hy : y ∈ˢ U) : (empty : V) ∈ˢ U :=
  hU.mem_of_subset_mem hy (empty_subset y)

omit hU in
/-- `x` is empty, as a formula in a 4-variable context (variable `0`). -/
def emptyAt4 : Form 4 :=
  .all (.not (.mem (Fin.last 4) (Fin.castSucc (⟨0, by omega⟩ : Fin 4))))

omit hU in
theorem realize_emptyAt4 {v : Fin 4 → V} :
    Form.Realize Mem v emptyAt4 ↔ v ⟨0, by omega⟩ = (empty : V) := by
  simp only [emptyAt4, Form.realize_all, Form.realize_not, Form.realize_mem,
    Form.snoc_last, Form.snoc_castSucc]
  constructor
  · exact eq_empty
  · intro h w hw
    rw [h] at hw
    exact not_mem_empty w hw

omit hU in
/-- The pairing relation `x ↦ (if x = ∅ then a else b)` as a formula, in
the replacement convention: variables `0 ↦ x`, `1 ↦ y`, parameters
`2 ↦ a`, `3 ↦ b`. -/
def upairRelF : Form 4 :=
  Form.or
    (Form.and (Form.relabel (fun _ => (⟨0, by omega⟩ : Fin 4)) emptyAt4)
      (Form.equal ⟨1, by omega⟩ ⟨2, by omega⟩))
    (Form.and (Form.not (Form.relabel (fun _ => (⟨0, by omega⟩ : Fin 4)) emptyAt4))
      (Form.equal ⟨1, by omega⟩ ⟨3, by omega⟩))

omit hU in
theorem realize_upairRelF {x y a b : V} :
    Form.Realize Mem (Form.cons2 x y (fun i : Fin 2 => if i.val = 0 then a else b)) upairRelF ↔
      (x = (empty : V) ∧ y = a) ∨ (x ≠ (empty : V) ∧ y = b) := by
  have hrel : ∀ v : Fin 4 → V,
      Form.Realize Mem v (Form.relabel (fun _ => (⟨0, by omega⟩ : Fin 4)) emptyAt4) ↔
        v ⟨0, by omega⟩ = (empty : V) := by
    intro v
    rw [Form.realize_relabel]
    exact realize_emptyAt4
  have e0 : (Form.cons2 x y (fun i : Fin 2 => if i.val = 0 then a else b)) ⟨0, by omega⟩ = x := by
    simp [Form.cons2]
  have e1 : (Form.cons2 x y (fun i : Fin 2 => if i.val = 0 then a else b)) ⟨1, by omega⟩ = y := by
    simp [Form.cons2]
  have e2 : (Form.cons2 x y (fun i : Fin 2 => if i.val = 0 then a else b)) ⟨2, by omega⟩ = a := by
    simp [Form.cons2]
  have e3 : (Form.cons2 x y (fun i : Fin 2 => if i.val = 0 then a else b)) ⟨3, by omega⟩ = b := by
    simp [Form.cons2]
  simp only [upairRelF, Form.realize_or, Form.realize_and, Form.realize_not,
    hrel, Form.realize_equal, e0, e1, e2, e3]

/-- **Definable pairing closure**: `upair a b` is a member, via the
*definable* fibre-replacement clause (clause 6) applied to `upairRelF`
over the two-element member `power (power ∅)`.  First-order: no
meta-level relation is involved. -/
theorem _root_.ConLeche.IsUniverse.upairF_mem {a b y : V} (hy : y ∈ˢ U)
    (ha : a ∈ˢ U) (hb : b ∈ˢ U) : upair a b ∈ˢ U := by
  have h2 : power (power (empty : V)) ∈ˢ U :=
    (hU.empty_mem hy |> hU.power_mem) |> hU.power_mem
  have hfun : ∀ x, x ∈ˢ power (power (empty : V)) →
      ∃ y', y' ∈ˢ U ∧
        Form.Realize Mem (Form.cons2 x y' (fun i : Fin 2 => if i.val = 0 then a else b)) upairRelF ∧
        ∀ y'', Form.Realize Mem (Form.cons2 x y'' (fun i : Fin 2 => if i.val = 0 then a else b)) upairRelF →
          y'' = y' := by
    intro x _
    by_cases hx0 : x = empty
    · refine ⟨a, ha, by rw [realize_upairRelF]; exact Or.inl ⟨hx0, rfl⟩, fun y'' hy'' => ?_⟩
      rw [realize_upairRelF] at hy''
      rcases hy'' with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd hx0 h
    · refine ⟨b, hb, by rw [realize_upairRelF]; exact Or.inr ⟨hx0, rfl⟩, fun y'' hy'' => ?_⟩
      rw [realize_upairRelF] at hy''
      rcases hy'' with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h hx0
      · exact h
  obtain ⟨c, hc, hspec⟩ :=
    hU.2.2.2.2.2 2 upairRelF (fun i : Fin 2 => if i.val = 0 then a else b)
      (power (power (empty : V))) h2 hfun
  have heq : upair a b = c := ext fun z => by
    constructor
    · intro hz
      rcases mem_upair.mp hz with h | h
      · rw [h]
        exact (hspec a).mpr ⟨empty, mem_power.mpr (empty_subset _),
          by rw [realize_upairRelF]; exact Or.inl ⟨rfl, rfl⟩⟩
      · rw [h]
        have hne : power (empty : V) ≠ empty :=
          ne_empty_of_mem (mem_power.mpr (Subset.refl _))
        exact (hspec b).mpr ⟨power empty, mem_power.mpr (Subset.refl _),
          by rw [realize_upairRelF]; exact Or.inr ⟨hne, rfl⟩⟩
    · intro hz
      obtain ⟨x, hx, hxr⟩ := (hspec z).mp hz
      rw [realize_upairRelF] at hxr
      rcases hxr with ⟨-, hzw⟩ | ⟨-, hzw⟩
      · rw [hzw]; exact mem_upair.mpr (Or.inl rfl)
      · rw [hzw]; exact mem_upair.mpr (Or.inr rfl)
  rw [heq]
  exact hc

/-- Pairing closure: via the definable clause 6 (`upairF_mem`) — the
relation `x ↦ (if x = ∅ then a else b)` over `power (power ∅)` is
the formula `upairRelF`, so no meta-level relation is involved. -/
theorem _root_.ConLeche.IsUniverse.upair_mem {a b y : V} (hy : y ∈ˢ U)
    (ha : a ∈ˢ U) (hb : b ∈ˢ U) : upair a b ∈ˢ U :=
  hU.upairF_mem hy ha hb

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

/-- Definable separation closure: a definable separation of a member is
a member (subset clause, no replacement needed). -/
theorem _root_.ConLeche.IsUniverse.sepF_mem {a : V} {n : Nat} {φ : Form (n + 1)}
    {q : Fin n → V} (ha : a ∈ˢ U) : sepF a φ q ∈ˢ U :=
  hU.mem_of_subset_mem ha sepF_subset

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
