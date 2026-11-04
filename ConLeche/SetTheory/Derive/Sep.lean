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

/-! ## Definable (first-order) separation and image

The same operators over `Form`s, derived from the definable
replacement scheme `replF` (the scheme a first-order model `M ⊨ ZFC`
actually supplies — `ConLecheBridge.replF_of_ZFC_model`).  Migrating
the `sep`/`image` call sites to `sepF`/`imageF` is what removes the
`replScheme_of_ZFC_model` bridge axiom. -/

/-- The image of `a` under the *functional* definable relation `ψ`
(first two free variables the related pair `(x, y)`, the remaining `n`
the parameters `p`): the definable replacement scheme `replF` applied
to `ψ`. -/
noncomputable def imageF {n : Nat} (ψ : Form (n + 2)) (p : Fin n → V) (a : V)
    (hfun : ∀ x, x ∈ˢ a → ∃ y, Form.Realize Mem (Form.cons2 x y p) ψ ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' p) ψ → y' = y) : V :=
  Classical.choose (replF n ψ p a hfun)

theorem mem_imageF {n : Nat} {ψ : Form (n + 2)} {p : Fin n → V} {a z : V}
    (hfun : ∀ x, x ∈ˢ a → ∃ y, Form.Realize Mem (Form.cons2 x y p) ψ ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' p) ψ → y' = y) :
    z ∈ˢ imageF ψ p a hfun ↔ ∃ x, x ∈ˢ a ∧ Form.Realize Mem (Form.cons2 x z p) ψ :=
  Classical.choose_spec (replF n ψ p a hfun) z

/-- Maps a separation formula's variables into the replacement
convention: the bound variable `n` ↦ `0` (the `x` of `cons2`), and
parameter `i < n` ↦ `i + 2`. -/
def sepLift (n : Nat) : Fin (n + 1) → Fin (n + 2) :=
  fun i => if h : i.val = n then ⟨0, by omega⟩ else ⟨i.val + 2, by omega⟩

theorem cons2_sepLift {V : Type u} {n : Nat} (x y : V) (q : Fin n → V) :
    (Form.cons2 x y q) ∘ sepLift n = Form.snoc q x := by
  funext i
  by_cases h : i.val = n
  · simp [Form.cons2, sepLift, Form.snoc, h]
  · have hlt : i.val < n := by omega
    simp [Form.cons2, sepLift, Form.snoc, h, hlt]

/-- The definable relation used for separation, with one extra
parameter `w` (the last): `ψ(x, y; q, w) := (φ(x, q) ∧ x = y) ∨
(¬φ(x, q) ∧ y = w)` — total and functional in `y` for every `x`
(classically). -/
def sepRel {n : Nat} (φ : Form (n + 1)) : Form (n + 1 + 2) :=
  let φx := Form.relabel (fun i => Fin.castSucc (sepLift n i)) φ
  Form.or (Form.and φx (Form.equal ⟨0, by omega⟩ ⟨1, by omega⟩))
    (Form.and φx.not (Form.equal ⟨1, by omega⟩ ⟨n + 2, by omega⟩))

theorem cons2_sepRel_lift {V : Type u} {n : Nat} (x y w : V) (q : Fin n → V) :
    (Form.cons2 x y (Form.snoc q w)) ∘ (fun i => Fin.castSucc (sepLift n i))
      = Form.snoc q x := by
  funext i
  by_cases h : i.val = n
  · simp [Form.cons2, sepLift, Form.snoc, h]
  · have hlt : i.val < n := by omega
    simp [Form.cons2, sepLift, Form.snoc, h, hlt]

theorem realize_sepRel {n : Nat} {φ : Form (n + 1)} {q : Fin n → V} {w x y : V} :
    Form.Realize Mem (Form.cons2 x y (Form.snoc q w)) (sepRel φ) ↔
      (Form.Realize Mem (Form.snoc q x) φ ∧ x = y) ∨
      (¬ Form.Realize Mem (Form.snoc q x) φ ∧ y = w) := by
  have hφx : Form.Realize Mem (Form.cons2 x y (Form.snoc q w))
      (Form.relabel (fun i => Fin.castSucc (sepLift n i)) φ)
      ↔ Form.Realize Mem (Form.snoc q x) φ := by
    rw [Form.realize_relabel, cons2_sepRel_lift]
  have e1 : (Form.cons2 x y (Form.snoc q w)) ⟨0, by omega⟩ = x := by simp [Form.cons2]
  have e2 : (Form.cons2 x y (Form.snoc q w)) ⟨1, by omega⟩ = y := by simp [Form.cons2]
  have e3 : (Form.cons2 x y (Form.snoc q w)) ⟨n + 2, by omega⟩ = w := by
    simp [Form.cons2, Form.snoc]
  simp only [sepRel, Form.realize_or, Form.realize_and, Form.realize_not, hφx,
    Form.realize_equal, e1, e2, e3]

/-- The separation relation is total and functional in `y` on any
`a`. -/
theorem sepRel_fun {n : Nat} {φ : Form (n + 1)} {q : Fin n → V} {a w : V} :
    ∀ x, x ∈ˢ a → ∃ y, Form.Realize Mem (Form.cons2 x y (Form.snoc q w)) (sepRel φ) ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' (Form.snoc q w)) (sepRel φ) → y' = y := by
  intro x _
  by_cases hp : Form.Realize Mem (Form.snoc q x) φ
  · exact ⟨x, by rw [realize_sepRel]; exact Or.inl ⟨hp, rfl⟩, fun y' hy' => by
      rw [realize_sepRel] at hy'
      rcases hy' with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2.symm
      · exact absurd hp h1⟩
  · exact ⟨w, by rw [realize_sepRel]; exact Or.inr ⟨hp, rfl⟩, fun y' hy' => by
      rw [realize_sepRel] at hy'
      rcases hy' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1 hp
      · exact h2⟩

open Classical in
/-- Separation for a definable predicate: `{x ∈ a | φ(x, q)}`, where
`φ : Form (n + 1)` has the bound variable as its LAST variable and `q`
the `n` parameters — the image of `a` under the total functional
definable relation `sepRel φ` with witness parameter
`Classical.choose h` (mirroring `sep`). -/
noncomputable def sepF (a : V) {n : Nat} (φ : Form (n + 1)) (q : Fin n → V) : V :=
  if h : ∃ x, x ∈ˢ a ∧ Form.Realize Mem (Form.snoc q x) φ then
    imageF (sepRel φ) (Form.snoc q (Classical.choose h)) a (sepRel_fun (w := Classical.choose h))
  else empty

open Classical in
theorem mem_sepF {a z : V} {n : Nat} {φ : Form (n + 1)} {q : Fin n → V} :
    z ∈ˢ sepF a φ q ↔ z ∈ˢ a ∧ Form.Realize Mem (Form.snoc q z) φ := by
  unfold sepF
  split
  · next h =>
    obtain ⟨hw₀a, hw₀φ⟩ := Classical.choose_spec h
    have hspec := mem_imageF (ψ := sepRel φ) (p := Form.snoc q (Classical.choose h))
      (sepRel_fun (w := Classical.choose h)) (a := a) (z := z)
    constructor
    · intro hz
      obtain ⟨x, hx, hψ⟩ := hspec.mp hz
      rw [realize_sepRel] at hψ
      rcases hψ with ⟨hφ, hxz⟩ | ⟨_, hzw⟩
      · rw [← hxz]
        exact ⟨hx, hφ⟩
      · rw [hzw]
        exact ⟨hw₀a, hw₀φ⟩
    · rintro ⟨hz, hφ⟩
      exact hspec.mpr ⟨z, hz, by rw [realize_sepRel]; exact Or.inl ⟨hφ, rfl⟩⟩
  · next h =>
    constructor
    · intro hz; exact absurd hz (not_mem_empty z)
    · intro ⟨hz, hφ⟩; exact absurd ⟨z, hz, hφ⟩ h

theorem sepF_subset {a : V} {n : Nat} {φ : Form (n + 1)} {q : Fin n → V} :
    sepF a φ q ⊆ˢ a :=
  fun _ hz => (mem_sepF.mp hz).1

/-- Definable image congruence. -/
theorem imageF_congr {n : Nat} {ψ ψ' : Form (n + 2)} {p : Fin n → V} {a : V}
    (hfun : ∀ x, x ∈ˢ a → ∃ y, Form.Realize Mem (Form.cons2 x y p) ψ ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' p) ψ → y' = y)
    (hfun' : ∀ x, x ∈ˢ a → ∃ y, Form.Realize Mem (Form.cons2 x y p) ψ' ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' p) ψ' → y' = y)
    (h : ∀ x y, x ∈ˢ a →
      (Form.Realize Mem (Form.cons2 x y p) ψ ↔ Form.Realize Mem (Form.cons2 x y p) ψ')) :
    imageF ψ p a hfun = imageF ψ' p a hfun' :=
  ext fun z => by
    rw [mem_imageF hfun, mem_imageF hfun']
    exact ⟨fun ⟨x, hx, hψ⟩ => ⟨x, hx, (h x z hx).mp hψ⟩,
           fun ⟨x, hx, hψ'⟩ => ⟨x, hx, (h x z hx).mpr hψ'⟩⟩

end ConLeche.SetTheory
