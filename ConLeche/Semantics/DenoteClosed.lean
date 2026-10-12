module

public import ConLeche.Semantics.Canon
public import ConLeche.Verify.Denote.Shift

@[expose] public section

/-!
# Lift and substitution invariance of `ITerm`s, via the erasure

Lifting or instantiating an `ITerm` is the `Term` operation on the
erasure (`erase_liftN`; `ITerm` is `Term` node for node), so an `ITerm`
is invariant exactly when its erasure is.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche (Env Expr Name CheckMode)

namespace ITerm

/-- **A lift that does not move the erasure does not move the term.**
`liftN` is `Term.liftN` clause for clause, so an `ITerm` is
lift-invariant exactly when its erasure is — and the erasure's
invariance is `Term.bvarsBelow`. -/
theorem liftN_eq_self : ∀ (e : ITerm) {k : Nat},
    Term.bvarsBelow k e.erase → ∀ n : Nat, liftN n e k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k h n
    have h' : i < k := h
    simp [liftN, h']
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha =>
    intro k h n; rw [liftN_app, ihf h.1 n, iha h.2 n]
  | lam A b ihA ihb =>
    intro k h n; rw [liftN_lam, ihA h.1 n, ihb h.2 n]
  | pi A B ihA ihB =>
    intro k h n; rw [liftN_pi, ihA h.1 n, ihB h.2 n]
  | letE v b ihv ihb =>
    intro k h n; rw [liftN_letE, ihv h.1 n, ihb h.2 n]
  | eqE a b iha ihb =>
    intro k h n; rw [liftN_eqE, iha h.1 n, ihb h.2 n]
  | fst e ihe =>
    intro k h n; rw [liftN_fst, ihe h n]
  | snd e ihe =>
    intro k h n; rw [liftN_snd, ihe h n]

/-- **`liftN_eq_self`'s substitution twin.**  `inst` touches a term only
at the `bvar`
whose index *is* the cut — so a term with no bound variable at or
above `k` is `inst`-invariant at `k`, for every substituend.

Stated with the substituend last (and universally quantified) because
that is the shape the leaf premise of `denoteMeta_substFvarAt` wants: the
stored constants' readings are invariant under *any* substitution, which is
what makes the `.const` and `.lit` clauses of the walk close. -/
theorem inst_eq_self : ∀ (e : ITerm) {k : Nat},
    Term.bvarsBelow k e.erase → ∀ x : ITerm, inst e x k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k h x
    have h' : i < k := h
    simp [inst, h']
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha =>
    intro k h x; rw [inst_app, ihf h.1 x, iha h.2 x]
  | lam A b ihA ihb =>
    intro k h x; rw [inst_lam, ihA h.1 x, ihb h.2 x]
  | pi A B ihA ihB =>
    intro k h x; rw [inst_pi, ihA h.1 x, ihB h.2 x]
  | letE v b ihv ihb =>
    intro k h x; rw [inst_letE, ihv h.1 x, ihb h.2 x]
  | eqE a b iha ihb =>
    intro k h x; rw [inst_eqE, iha h.1 x, ihb h.2 x]
  | fst e ihe =>
    intro k h x; rw [inst_fst, ihe h x]
  | snd e ihe =>
    intro k h x; rw [inst_snd, ihe h x]

end ITerm


end ConLeche.Semantics
