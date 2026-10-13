module

public import Fragment.Rules
public import Fragment.EnvModel

@[expose] public section

/-!
# The three claims

One motive per relation, in the currency of the model: `interp`
equality, membership, and the invariant `WellDenoted`.  Each is
stated at a model `m` of the environment, a valuation `φ`, and for
every environment `ρ` satisfying the context:

* **`RedSem`** — a reduction of a well-denoted term that is not the
  point yields a well-denoted term with the same denotation;
* **`DefEqSem`** — two well-denoted terms that are not the point and
  that the checker calls equal have equal denotations;
* **`InferSem`** — an inferred term is well-denoted, its type is
  well-denoted and a type, and the term's denotation is a member of the
  type's;
* **`DefEqInSem`** (task #345) — two well-denoted members of one
  well-denoted type that the checker compares at that type have equal
  denotations;
* **`LamsSem`** (task #349) — two well-denoted λ-telescopes that the
  checker compares level by level, typing only the innermost bodies,
  have equal denotations, unconditionally.

The first two are **conditional on the point**: they say nothing about
proofs, which is what lets β fire at every binder with no premise
(`Sound.lean`).  The third is not: an inferred type is a type, never
the point, so the reductions and comparisons of types the rules run
are claimed outright.

These are the claims of `ConLeche/Model/Claims.lean` (made conditional), in the shape of
`ConLeche/Model/Rules/Motive.lean`.  Two of that file's three
strengthenings are unnecessary here — there is no reading to
establish (the interpretation is total) and no frame to carry (no
free variables) — and the third is the single grade: `InferSem`
always *establishes* the subject's invariant, never consumes it.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V] {env : Env}

/-- **`Red`'s claim**: on a subject that is not the point, reduction
preserves the invariant and the denotation.  Nothing is claimed of a
proof. -/
def RedSem (m : EnvModel V env) (φ : Name → Nat) (Γ : List Expr) (e e' : Expr) : Prop :=
  ∀ ρ : Nat → V, Sat m.M φ Γ ρ → WellDenoted m.M φ ρ e → interp m.M φ ρ e ≠ pt →
    WellDenoted m.M φ ρ e' ∧ interp m.M φ ρ e = interp m.M φ ρ e'

/-- **`DefEqLams`' claim**: two well-denoted sides have
equal denotations — unconditionally, the point included. -/
def LamsSem (m : EnvModel V env) (φ : Name → Nat) (Γ : List Expr) (a b : Expr) : Prop :=
  ∀ ρ : Nat → V, Sat m.M φ Γ ρ → WellDenoted m.M φ ρ a → WellDenoted m.M φ ρ b →
    interp m.M φ ρ a = interp m.M φ ρ b

/-- **`DefEq`'s claim**: two well-denoted sides that are not the point
have equal denotations.  (Two proofs are the point.) -/
def DefEqSem (m : EnvModel V env) (φ : Name → Nat) (Γ : List Expr) (a b : Expr) : Prop :=
  ∀ ρ : Nat → V, Sat m.M φ Γ ρ → WellDenoted m.M φ ρ a → WellDenoted m.M φ ρ b →
    interp m.M φ ρ a ≠ pt → interp m.M φ ρ b ≠ pt → interp m.M φ ρ a = interp m.M φ ρ b

/-- **`DefEqIn`'s claim**: two well-denoted members of one
well-denoted type have equal denotations — unconditionally, since a
type's members are all the point or none. -/
def DefEqInSem (m : EnvModel V env) (φ : Name → Nat) (Γ : List Expr) (T a b : Expr) : Prop :=
  ∀ ρ : Nat → V, Sat m.M φ Γ ρ → WellDenoted m.M φ ρ T → IsTy (interp m.M φ ρ T) →
    WellDenoted m.M φ ρ a → WellDenoted m.M φ ρ b →
    interp m.M φ ρ a ∈ˢ interp m.M φ ρ T → interp m.M φ ρ b ∈ˢ interp m.M φ ρ T →
    interp m.M φ ρ a = interp m.M φ ρ b

/-- **`Infer`'s claim**: the term and its type are well-denoted, the
type is a type, and the term's denotation is a member of the type's. -/
def InferSem (m : EnvModel V env) (φ : Name → Nat) (Γ : List Expr) (e T : Expr) : Prop :=
  ∀ ρ : Nat → V, Sat m.M φ Γ ρ →
    WellDenoted m.M φ ρ e ∧ WellDenoted m.M φ ρ T ∧ IsTy (interp m.M φ ρ T) ∧
      interp m.M φ ρ e ∈ˢ interp m.M φ ρ T

end Fragment
