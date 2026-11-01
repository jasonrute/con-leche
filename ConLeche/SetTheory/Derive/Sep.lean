module

public import ConLeche.SetTheory.Derive.Empty

@[expose] public section

/-!
# Separation and the image operator, derived from the replacement scheme

The classical trick: to separate `{x ∈ a : p x}`, either the result is
empty (take `empty`), or some witness `w₀ ∈ a` with `p w₀` exists and
the relation `x ↦ (if p x then x else w₀)` replaces `a` onto exactly
the separated set (the default value `w₀` is already a member of
it).  The detour is forced because the scheme's antecedent demands
totality.

The same scheme derives the **image of a set under a function**
(`image`/`mem_image`): the graph relation `p x y := y = f x` is
functional by reflexivity, so `repl` hands back the image set.  The
`SetTheory` class carries no function-valued image operator — that
would be second-order content (a class *function*), where a
first-order replacement scheme suffices.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

open Classical in
/-- Separation: `{x ∈ a : p x}`, for an arbitrary meta-level predicate. -/
noncomputable def sep (a : V) (p : V → Prop) : V :=
  if h : ∃ x, x ∈ˢ a ∧ p x then
    Classical.choose (repl a (fun x y => (y = if p x then x else Classical.choose h))
      (fun x hx => ⟨if p x then x else Classical.choose h, rfl,
        fun y' hy' => by
          by_cases hp : p x
          · rw [ite_eq_left hp] at hy' ⊢; exact hy'
          · rw [ite_eq_right hp] at hy' ⊢; exact hy'⟩))
  else empty

/-- The image of a set under a function: the replacement scheme applied
to the graph relation `p x y := y = f x`. -/
noncomputable def image (f : V → V) (a : V) : V :=
  Classical.choose (repl a (fun x y => (y = f x)) (fun x _ => ⟨f x, rfl, fun _ h => h⟩))

theorem mem_image {f : V → V} {a z : V} :
    z ∈ˢ image f a ↔ ∃ w, w ∈ˢ a ∧ z = f w :=
  Classical.choose_spec (repl a (fun x y => (y = f x))
    (fun x _ => ⟨f x, rfl, fun _ h => h⟩)) z

open Classical in
theorem mem_sep {a z : V} {p : V → Prop} : z ∈ˢ sep a p ↔ z ∈ˢ a ∧ p z := by
  unfold sep
  split
  · next h =>
    obtain ⟨hw₀a, hw₀p⟩ := Classical.choose_spec h
    have hspec := Classical.choose_spec
      (repl a (fun x y => (y = if p x then x else Classical.choose h))
        (fun x hx => ⟨if p x then x else Classical.choose h, rfl,
          fun y' hy' => by
            by_cases hp : p x
            · rw [ite_eq_left hp] at hy' ⊢; exact hy'
            · rw [ite_eq_right hp] at hy' ⊢; exact hy'⟩)) z
    constructor
    · intro hz
      obtain ⟨w, hw, hpw⟩ := hspec.mp hz
      by_cases hpw' : p w
      · rw [ite_eq_left hpw'] at hpw
        have hwp : z = w := hpw
        rw [hwp]
        exact ⟨hw, hpw'⟩
      · rw [ite_eq_right hpw'] at hpw
        have hze : z = Classical.choose h := hpw
        rw [hze]
        exact ⟨hw₀a, hw₀p⟩
    · rintro ⟨hz, hp⟩
      exact hspec.mpr ⟨z, hz, by rw [ite_eq_left hp]⟩
  · next h =>
    constructor
    · intro hz; exact absurd hz (not_mem_empty z)
    · intro ⟨hz, hp⟩; exact absurd ⟨z, hz, hp⟩ h

theorem sep_subset {a : V} {p : V → Prop} : sep a p ⊆ˢ a :=
  fun _ hz => (mem_sep.mp hz).1

/-- Image congruence, the companion fact. -/
theorem image_congr {a : V} {f g : V → V} (h : ∀ x, x ∈ˢ a → f x = g x) :
    image f a = image g a :=
  ext fun z => by
    rw [mem_image, mem_image]
    exact ⟨fun ⟨w, hw, hz⟩ => ⟨w, hw, hz.trans (h w hw)⟩,
           fun ⟨w, hw, hz⟩ => ⟨w, hw, hz.trans (h w hw).symm⟩⟩

end ConLeche.SetTheory
