module

public import ConLeche.Model.Currency
import ConLeche.Semantics.DenoteClosed
public section

/-!
# `WellDenotedV`'s substitution metatheory (task #161, P3 batch 2)

`WellDenotedV` (`Model/Currency.lean`) is the P-tier name of the
semantic invariant `WellDenoted`; these are its transport laws in that
currency: lifting, outermost substitution, ζ, and the hoisting forms.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]

variable (V)

/-- **The currency through lifting** — both halves at the same
rewrite. -/
theorem WellDenotedV_liftN (n : Nat) (e : AnnotTerm) (k : Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (e.liftN n k) ↔ WellDenotedV V (shiftE n k ρ) e :=
  WellDenoted_liftN V n e k ρ

variable {V}

/-- **The currency through outermost substitution** — the β/ζ
transport form, the shape every reduction clause consumes. -/
theorem WellDenotedV_inst0 {e a : AnnotTerm} {ρ : Nat → V}
    (ha : WellDenotedV V ρ a) :
    WellDenotedV V ρ (e.inst a) ↔
      WellDenotedV V (cons (interp V ρ a) ρ) e :=
  WellDenoted_inst0 V ha

/-- A graded `let` has a graded value. -/
theorem WellDenotedV.letE_val {v b : AnnotTerm} {ρ : Nat → V}
    (h : WellDenotedV V ρ (.letE v b)) : WellDenotedV V ρ v := by
  rw [WellDenotedV, WellDenoted_letE] at h
  exact h.1

/-- **ζ in the currency**: with its value graded, a `let` is graded
exactly when its reduct is (`interp_zeta`: it interprets as the
reduct at every valuation). -/
theorem WellDenotedV_zeta {v b : AnnotTerm} {ρ : Nat → V}
    (hv : WellDenotedV V ρ v) :
    WellDenotedV V ρ (.letE v b) ↔ WellDenotedV V ρ (b.inst v) := by
  exact WellDenoted_zeta V hv

/-- **Weakening a hoisted fact under one more binder**, in the P
currency: `WellDenoted.hoist_lift`'s mirror, and what `CtxOk.weakenTop`
uses to move a leaf's fourth conjunct across the new head. -/
theorem WellDenotedV.hoist_lift {Δa : List AnnotTerm} {X e : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ e) :
    ∀ ρ : Nat → V, Sat V (X :: Δa) ρ → WellDenotedV V ρ e.lift := by
  intro ρ hρ
  refine (WellDenotedV_liftN V 1 e 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact h _ (Sat_tail hρ)

/-- **A graded type through lifting.** -/
theorem WellDenotedTy_liftN (n : Nat) (e : AnnotTerm) (k : Nat) (ρ : Nat → V) :
    WellDenotedTy V (ρ) (e.liftN n k) ↔ WellDenotedTy V (shiftE n k ρ) e := by
  unfold WellDenotedTy
  rw [WellDenotedV_liftN, interp_liftN]

/-- **A graded type through outermost substitution.** -/
theorem WellDenotedTy_inst0 {e a : AnnotTerm} {ρ : Nat → V}
    (ha : WellDenotedV V ρ a) :
    WellDenotedTy V ρ (e.inst a) ↔
      WellDenotedTy V (cons (interp V ρ a) ρ) e := by
  unfold WellDenotedTy
  rw [WellDenotedV_inst0 ha, interp_inst0]

/-- `WellDenotedV.hoist_lift` for graded types. -/
theorem WellDenotedTy.hoist_lift {Δa : List AnnotTerm} {X e : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ e) :
    ∀ ρ : Nat → V, Sat V (X :: Δa) ρ → WellDenotedTy V ρ e.lift := by
  intro ρ hρ
  refine (WellDenotedTy_liftN 1 e 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact h _ (Sat_tail hρ)

/-- **The stored leaves are `inst`-invariant** — `denoteMeta_beta`'s
second leaf premise, discharged from the erasure link and the
collapse-lane closedness field.  (Shared home: both the infer and the
whnf quarters proved this independently at their batches; deduplicated
here at the merge.) -/
theorem acval_inst_self {env : ConLeche.Env}
    (m : EnvModel V env) (n : ConLeche.Name)
    (ψ : ConLeche.Name → Nat) (y : AnnotTerm) (k : Nat) :
    (m.acval n ψ).inst y k = m.acval n ψ :=
  AnnotTerm.inst_eq_self _
    (by rw [m.acval_erase]
        exact Term.bvarsBelow.mono (Nat.zero_le k)
          (m.cval_closed n ψ)) y

end ConLeche.Model
