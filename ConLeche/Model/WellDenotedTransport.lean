module

public import ConLeche.Model.Currency
import ConLeche.Semantics.DenoteClosed
public section

/-!
# `WellDenoted`'s substitution metatheory (task #161, P3 batch 2)

The transport laws of the semantic invariant `WellDenoted` that the
P tier reads beyond `Semantics/WellDenoted.lean`'s: the graded `let`
value and the hoisting forms.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (ITerm)
open ConLeche (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]

/-- A graded `let` has a graded value. -/
theorem _root_.ConLeche.Semantics.WellDenoted.letE_val {v b : ITerm} {ρ : Nat → V}
    (h : WellDenoted V ρ (.letE v b)) : WellDenoted V ρ v := by
  rw [WellDenoted_letE] at h
  exact h.1

/-- **Weakening a hoisted fact under one more binder**, what
`CtxOk.weakenTop` uses to move a leaf's fourth conjunct across the new head. -/
theorem _root_.ConLeche.Semantics.WellDenoted.hoist_lift {Δa : List ITerm} {X e : ITerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ e) :
    ∀ ρ : Nat → V, Sat V (X :: Δa) ρ → WellDenoted V ρ e.lift := by
  intro ρ hρ
  refine (WellDenoted_liftN V 1 e 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact h _ (Sat_tail hρ)

/-- **A graded type through lifting.** -/
theorem WellDenotedTy_liftN (n : Nat) (e : ITerm) (k : Nat) (ρ : Nat → V) :
    WellDenotedTy V (ρ) (e.liftN n k) ↔ WellDenotedTy V (shiftE n k ρ) e := by
  unfold WellDenotedTy
  rw [WellDenoted_liftN, interp_liftN]

/-- **A graded type through outermost substitution.** -/
theorem WellDenotedTy_inst0 {e a : ITerm} {ρ : Nat → V}
    (ha : WellDenoted V ρ a) :
    WellDenotedTy V ρ (e.inst a) ↔
      WellDenotedTy V (cons (interp V ρ a) ρ) e := by
  unfold WellDenotedTy
  rw [WellDenoted_inst0 _ ha, interp_inst0]

/-- `WellDenoted.hoist_lift` for graded types. -/
theorem WellDenotedTy.hoist_lift {Δa : List ITerm} {X e : ITerm}
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
    (ψ : ConLeche.Name → Nat) (y : ITerm) (k : Nat) :
    (m.acval n ψ).inst y k = m.acval n ψ :=
  ITerm.inst_eq_self _
    (by rw [m.acval_erase]
        exact Term.bvarsBelow.mono (Nat.zero_le k)
          (m.cval_closed n ψ)) y

end ConLeche.Model
