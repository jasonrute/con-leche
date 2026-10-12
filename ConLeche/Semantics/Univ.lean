module

public import ConLeche.Semantics.Kit

@[expose] public section

/-!
# The universe question, in the `pt`-free world (task #151, tier B)

Under `interp` there is no `pt` in the positive regime, and the
universe question reads:

> Do `interp`'s universes contain values that break the graph
> inversion at universe-codomain function spaces — i.e. can something the
> `SetTheory` universe tower happens to contain sneak into
> `⟦(x : A) → Sort k⟧` without being a graph?

**No, and the reason is structural rather than arithmetic.**
`piR v A B` at `v ≠ 0` is `piSet A B`, which is *carved out by
separation*: `f ∈ piSet A B` **iff** `f ⊆ sigmaPairs A B` and `f` is
total and single-valued on `A` (`mem_piR_pos_iff` below).  That is a
property of `f`, quantified over `f`'s own members.  Nothing about `B`,
about universe transitivity, or about what a universe contains can add
a member to it: universe transitivity says members of members of `U`
are in `U`, which enlarges `U`, never `piSet A B`.  So
`interp_mem_pi_ne_pt` holds at universe-valued fibres exactly as it
does anywhere else.

A `Type`-level abstraction is never `pt` (`lamR_ne_pt`), and the proof
point inhabits no graph-regime function space (`not_pt_mem_piR_pos`), so
`ConLeche/SetTheory/Core.lean`'s transitivity clause and the ω-chain
need no change for this layer.

Two further facts are proved below:

* **The formation law is the `imax` rule, exactly** (`piR_mem_univ`),
  and it is *sharp*: a graph-regime function space with inhabited fibres is
  never a truth value (`piR_pos_not_mem_univZero`).
* **The proof point is not in `univ 0` at all**
  (`pt_not_mem_univZero`), and the empty-domain graph-regime function space
  `piR v ∅ B = {∅}` does not contain it.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## Formation along the tower -/

/-- **The `imax` rule, exactly.**  `Prop`-valued function spaces land in
`univ 0` whatever their domain (impredicativity); above `0` they land
at `max u v`. -/
theorem piR_mem_univ {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ (univ u : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V)) :
    piR v A B ∈ˢ (univ (if v = 0 then 0 else Nat.max u v) : V) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [ite_eq_left rfl, univ_zero]
    exact piR_zero_mem_univZero
  · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
    have hw : (Nat.max u v : Nat) ≠ 0 :=
      fun h => hv' (Nat.le_zero.mp (h ▸ Nat.le_max_right u v))
    rw [ite_eq_right hv', piR_pos hv']
    exact mem_univ_of_tg_strict ((tg_isTGUniverse hw).piSet_mem
      (tg_mono (Nat.le_max_left u v) A (mem_tg_of_mem_univ hA))
      (fun x hx => tg_mono (Nat.le_max_right u v) _ (mem_tg_of_mem_univ (hB x hx))))
      strict_piSet


open Classical in
/-- Sharpness of the regime split: a graph-regime function space whose fibres
are all inhabited is **not** a truth value.  So the regime numeral is
not merely an upper bound on where the value lands — the two regimes are
genuinely disjoint, and a `Type`-level function space never sneaks into
`Prop`. -/
theorem piR_pos_not_mem_univZero {v : Nat} (hv : v ≠ 0) {A : V} {B : V → V}
    (hinh : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) : ¬ piR v A B ∈ˢ (univZero : V) := by
  intro h
  have hchoice : ∃ F : V → V, ∀ x, x ∈ˢ A → F x ∈ˢ B x :=
    ⟨fun x => if hx : x ∈ˢ A then Classical.choose (hinh x hx) else empty,
     fun x hx => by
       show (if h : x ∈ˢ A then Classical.choose (hinh x h) else empty) ∈ˢ B x
       rw [dite_eq_left hx]
       exact Classical.choose_spec (hinh x hx)⟩
  obtain ⟨F, hF⟩ := hchoice
  have hg : graph F A ∈ˢ piR v A B := by
    rw [piR_pos hv]; exact graph_mem_piSet hF
  exact graph_ne_pt (eq_pt_of_mem_univZero h hg)

/-! ## The inversion is fibre-blind -/

/-- Membership in a graph-regime function space **is** graph-hood: separation
from `power (sigmaPairs A B)`, a property of `f`'s own members.  This
is the formal content of "nothing a universe contains can break the
inversion". -/
theorem mem_piR_pos_iff {v : Nat} (hv : v ≠ 0) {A f : V} {B : V → V} :
    f ∈ˢ piR v A B ↔ f ⊆ˢ sigmaPairs A B ∧
      ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y := by
  rw [piR_pos hv]; exact mem_piSet

/-! ## The proof point and the universes -/

/- `pt_not_mem_univZero` (the proof point is not a truth value) is a
point law of `SetTheory/Derive/Pt.lean`. -/

/-- The empty-domain graph-regime function space is `{∅}`, whose only member
is the empty graph. -/
theorem not_pt_mem_piR_empty {v : Nat} (hv : v ≠ 0) (B : V → V) :
    ¬ (pt : V) ∈ˢ piR v (empty : V) B := not_pt_mem_piR_pos hv

/-! ## Placement of the sorts themselves -/

theorem interp_sort_mem (V : Type w) [SetTheory V] (ρ : Nat → V) (n : Nat) :
    interp V ρ (.sort n) ∈ˢ interp V ρ (.sort (n + 1)) := univ_mem_univ n

end ConLeche.Semantics
