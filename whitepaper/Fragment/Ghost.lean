module

public import Fragment.UniformBeta

public section

/-!
# Which checker decisions read an annotation, and why the rest stay (task #341)

The question: could the annotations be **ghost data**, present for the
proof only, supplied by a specification function or an existential,
with no decision of the checker reading them?  The decisions that read
one are four:

* `Infer.pi`, `Infer.lam` check the annotation against the body's sort.
  That check is what makes an annotation honest; with ghost
  annotations it would be the ghost's definition.
* `DefEq.lam` compared the two λs' annotations, and `DefEq.eta` the λ's
  with the `∀`'s.  **Neither comparison is needed** and both are gone
  (`Rules.lean`, `Sound.lean`: `DefEq.lam_sound`, `DefEq.eta_sound`): a
  λ whose annotation holds denotes the point, and the claims are
  conditional on the point.
* `DefEq.pi` compared the two `∀`s' annotations.  **Something must
  tell the two regimes apart**, and this file shows what (task #341,
  sharpened by #343).  Since #343 it is **the two sides' types**, not
  their annotations (`Rules.lean`, `DefEq.pi`).

Over an empty domain the two regimes give two different types: the
propositional product is `{pt}` and the function space holds one
graph.  Nothing about the domain or the codomain tells them apart:
`(h : ∀ P : Prop, P) → Prop` is well-denoted under either annotation,
in every model, at every valuation (`pi_datum_needed`).  So `∀`-
congruence with only its domain and body premises has true premises
and a false conclusion (`pi_congr_without_datum`).

**What information is missing** (#343).  Every claim made under the
extended context `(h : ∀ P : Prop, P) :: Γ` is vacuously true, because
no valuation satisfies it (`codomain_claims_vacuous`).  So no premise
about the bodies — their equality, their inferred types, the sorts of
those types, compared however — can exclude the witness: comparing
the codomains' inferred sorts instead of the annotations is unsound
for the same reason (both bodies are `Prop : Sort 1`).  What does tell
the two apart is a claim at `Γ` about the `∀`s themselves: no sort holds
both denotations (`pi_over_false_sorts`), and inside one sort the
regimes agree (`SetLib.piR_eq_of_mem_typeU`).  The sort of a `∀` is what
`Infer.pi` computes, after checking the annotation against the body's
sort; so the honesty check in inference, followed by "both sides have
equal types" in the defeq, replaces the comparison of the data.

The λ's annotation is not determined by the semantics either
(`lam_datum_free`): over the same empty domain both annotations are
well-denoted, one the point and the other the empty graph — and only
the latter is a member of the honest type, so the λ's annotation must
come from its typing (`lam_datum_from_type`).
-/

namespace Fragment

open SetLib Expr

/-- `(h : ∀ P : Prop, P) → Prop`, annotated `pw` (honestly `never`). -/
@[expose] def piOverFalse (pw : PropWhen) : Expr := .pi falseE pw (.sort .zero)

/-- `fun (h : ∀ P : Prop, P) => Prop`, annotated `pw` (honestly `never`). -/
@[expose] def lamOverFalse (pw : PropWhen) : Expr := .lam falseE pw (.sort .zero)

universe w

variable {V : Type w} [SetLib V]

section
variable (M : Name → List Nat → V) (φ : Name → Nat)

/-- `∀ P : Prop, P` denotes a set with no member. -/
theorem not_mem_falseE (ρ : Nat → V) (z : V) : ¬ z ∈ˢ interp M φ ρ falseE := by
  intro hz
  simp only [falseE, interp_pi, interp_sort, Level.eval, PropWhen.holds_always, piR_true]
    at hz
  have h := of_mem_truthVal hz
  have hf := h (truthVal False) (by
    exact mem_typeU_zero.mpr (truthVal_mem_univ_zero False))
  exact one_ne_truthVal_false hf.symm

theorem WellDenoted_falseE (ρ : Nat → V) : WellDenoted M φ ρ falseE := by
  simp only [falseE]
  rw [WellDenoted_pi]
  refine ⟨trivial, ?_, fun _ _ => trivial, fun x hx => ?_⟩
  · simpa [Level.eval] using (IsTy_typeU 0 : IsTy (typeU 0 : V))
  · simp only [interp_sort, Level.eval, interp_bvar, cons_zero, PropWhen.holds_always,
      Fib_true] at hx ⊢
    exact mem_typeU_zero.mp hx

theorem IsTy_falseE (ρ : Nat → V) : IsTy (interp M φ ρ falseE) := by
  simp only [falseE, interp_pi]; exact IsTy_piR

/-- **Both annotations of a `∀` over an empty domain are well-denoted,
neither denotes the point, and the two denotations differ** — in every
model, at every valuation and environment. -/
theorem pi_datum_needed (ρ : Nat → V) :
    WellDenoted M φ ρ (piOverFalse .always) ∧ WellDenoted M φ ρ (piOverFalse .never) ∧
    interp M φ ρ (piOverFalse .always) ≠ pt ∧ interp M φ ρ (piOverFalse .never) ≠ pt ∧
    interp M φ ρ (piOverFalse .always) ≠ interp M φ ρ (piOverFalse .never) := by
  have hwd : ∀ pw, WellDenoted M φ ρ (piOverFalse pw) := fun pw => by
    simp only [piOverFalse]
    rw [WellDenoted_pi]
    exact ⟨WellDenoted_falseE M φ ρ, IsTy_falseE M φ ρ, fun _ _ => trivial,
      fun x hx => absurd hx (not_mem_falseE M φ ρ x)⟩
  refine ⟨hwd _, hwd _, ?_, ?_, ?_⟩
  · simp only [piOverFalse, interp_pi]; exact IsTy_piR.ne_pt
  · simp only [piOverFalse, interp_pi]; exact IsTy_piR.ne_pt
  · intro he
    -- the propositional product over an empty domain holds the point …
    have hpt : (pt : V) ∈ˢ interp M φ ρ (piOverFalse .always) := by
      simp only [piOverFalse, interp_pi, PropWhen.holds_always, piR_true]
      exact pt_mem_truthVal fun x hx => absurd hx (not_mem_falseE M φ ρ x)
    -- … and the function space never does
    rw [he] at hpt
    simp only [piOverFalse, interp_pi, PropWhen.holds_never, piR_false] at hpt
    exact strict_piSet.2 hpt

/-- **Both annotations of a λ over an empty domain are well-denoted**:
the semantics does not determine a λ's annotation either.  One
denotes the point, the other a graph. -/
theorem lam_datum_free (ρ : Nat → V) :
    WellDenoted M φ ρ (lamOverFalse .always) ∧ WellDenoted M φ ρ (lamOverFalse .never) ∧
    interp M φ ρ (lamOverFalse .always) = pt ∧ interp M φ ρ (lamOverFalse .never) ≠ pt := by
  have hwd : ∀ pw, WellDenoted M φ ρ (lamOverFalse pw) := fun pw => by
    simp only [lamOverFalse]
    rw [WellDenoted_lam]
    exact ⟨WellDenoted_falseE M φ ρ, IsTy_falseE M φ ρ, fun _ _ => trivial,
      fun _ => pt, fun x hx => absurd hx (not_mem_falseE M φ ρ x),
      fun x hx => absurd hx (not_mem_falseE M φ ρ x)⟩
  refine ⟨hwd _, hwd _, ?_, ?_⟩
  · simp [lamOverFalse, interp_lam, PropWhen.holds_always, lamR_true]
  · simp only [lamOverFalse, interp_lam, PropWhen.holds_never]; exact lamR_false_ne_pt

/-- **Only the honest annotation of the λ is a member of its honest
type** `(h : ∀ P : Prop, P) →[never] Prop`: the λ's annotation must be
the one its typing gives. -/
theorem lam_datum_from_type (ρ : Nat → V) :
    interp M φ ρ (lamOverFalse .never) ∈ˢ interp M φ ρ (piOverFalse .never) ∧
    ¬ interp M φ ρ (lamOverFalse .always) ∈ˢ interp M φ ρ (piOverFalse .never) := by
  constructor
  · simp only [lamOverFalse, piOverFalse, interp_lam, interp_pi, PropWhen.holds_never]
    exact lamR_mem (B := fun x => interp M φ (cons x ρ) (.sort .zero))
      (fun x hx => absurd hx (not_mem_falseE M φ ρ x)) (fun h => nomatch h)
  · rw [(lam_datum_free M φ ρ).2.2.1]
    simp only [piOverFalse, interp_pi, PropWhen.holds_never, piR_false]
    exact strict_piSet.2

end

/-- **`∀`-congruence without the comparison of the annotations is
unsound**: in any model of any environment, its premises' claims hold
(the same domain, the same body) and its conclusion's fails. -/
theorem pi_congr_without_datum {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) :
    DefEqSem m φ [] falseE falseE ∧ DefEqSem m φ [falseE] (.sort .zero) (.sort .zero) ∧
    ¬ DefEqSem m φ [] (piOverFalse .always) (piOverFalse .never) := by
  refine ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun h => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := pi_datum_needed m.M φ (fun _ => pt)
  exact h5 (h (fun _ => pt) trivial h1 h2 h3 h4)

/-- **No valuation satisfies a context that binds a proof of
`∀ P : Prop, P`**, so every claim made under it holds: no premise about
the bodies of a `∀`-congruence over that domain — their equality, their
inferred types or the sorts of those — excludes anything (task #343). -/
theorem codomain_claims_vacuous {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (Γ : List Expr) :
    (∀ e T, InferSem m φ (falseE :: Γ) e T) ∧
    (∀ a b, DefEqSem m φ (falseE :: Γ) a b) ∧
    (∀ e e', RedSem m φ (falseE :: Γ) e e') := by
  have hno : ∀ ρ : Nat → V, ¬ Sat m.M φ (falseE :: Γ) ρ := fun ρ hs =>
    not_mem_falseE m.M φ _ _ hs.2.2.2
  exact ⟨fun _ _ ρ hs => absurd hs (hno ρ), fun _ _ ρ hs => absurd hs (hno ρ),
    fun _ _ ρ hs => absurd hs (hno ρ)⟩

/-- **No sort holds both readings of the witness** (task #343): the
propositional one only in `Sort 0`, the function space only above it.
This is what `DefEq.pi`'s type premises read instead of the annotations. -/
theorem pi_over_false_sorts (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V)
    (n : Nat) :
    (interp M φ ρ (piOverFalse .always) ∈ˢ typeU n → n = 0) ∧
    (interp M φ ρ (piOverFalse .never) ∈ˢ typeU n → n ≠ 0) := by
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    rw [mem_typeU_pos hn] at h
    apply h.2.2
    simp only [piOverFalse, interp_pi, PropWhen.holds_always, piR_true]
    exact pt_mem_truthVal fun x hx => absurd hx (not_mem_falseE M φ ρ x)
  · rintro h rfl
    rw [mem_typeU_zero] at h
    simp only [piOverFalse, interp_pi, PropWhen.holds_never, piR_false] at h
    have hg : graph (fun x => x) (interp M φ ρ falseE) ∈ˢ
        piSet (interp M φ ρ falseE) (fun x => interp M φ (cons x ρ) (.sort .zero)) :=
      graph_mem_piSet fun x hx => absurd hx (not_mem_falseE M φ ρ x)
    exact not_mem_of_univ_zero_strict h strict_piSet hg

end Fragment
