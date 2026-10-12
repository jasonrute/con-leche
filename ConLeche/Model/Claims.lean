module

public import ConLeche.Verify.InferLeaves
public import ConLeche.Semantics.Skeleton
import ConLeche.Model.Annot.Valid
import ConLeche.Model.Annot.EnvModel
public import ConLeche.Model.Currency

public section

/-!
# The P-generation claims: the ladder over `denoteMeta` (task #161, P3.3)

The soundness ladder over **`denoteMeta`**, the validated-annotation
reading (no annotation fuel: there is no run to pay for):

* the truthfulness currency is `WellDenotedV := WellDenoted ∧ AnnotValid`:
  the hereditary invariant plus bit validity — the claims *establish*
  the regime bits they dispatch on, clause by clause, from the run
  inversions (never from a validity metatheorem);
* the context discipline is `CtxOk`, with leaf truthfulness
  `WellDenotedV`.

The **dual-success** shape: every `denoteMeta` sits in a premise, never
a conclusion, so the smallest-fuel refutation rule has nothing to bite
on.  Where a sort run's residue would be consumed, the P tier consumes
the validation sites' run-inversion conjuncts instead: binder bits are
equal data (`==` ⇒ equal bits, canonical in `{0,1}`); the λ front door
is `inferTypeCore_lam_inv`'s conjunct + `pwBit_zero_mem_univZero`, the
chain case `piR_zero_mem_univZero`; level instantiation is
`denotePInstLevels`; the environment crossing is `denoteMeta_envExtend`
(`FindPreserved`/`LitGuardsAgree`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-- Two types are equal when they are equal away from the point:
neither is the point.  The consumers of a `DefEqClaim` between two
types route through it (task #342 L8): the claim is conditional on the
point (L9); between two members of one type, `IsTy.eq_of_ne_pt` plays
the same part. -/
theorem eq_of_IsTy_of_ne_pt {x y : V} (hx : IsTy x) (hy : IsTy y)
    (h : x ≠ pt → y ≠ pt → x = y) : x = y :=
  h hx.ne_pt hy.ne_pt

/-- Head normalisation, dual success, P currency, conditional on the
point (task #342, L9): the reduct is graded and equal where the subject
is not the point. -/
@[expose] def WhnfCoreClaim (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AnnotTerm},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ea' : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ≠ pt →
          WellDenotedV V ρ ea') ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ≠ pt →
          interp V ρ ea = interp V ρ ea'

/-- The reduction loop, dual success, P currency, conditional on the
point (task #342, L9). -/
@[expose] def WhnfClaim (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AnnotTerm},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ea' : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ≠ pt →
          WellDenotedV V ρ ea') ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ≠ pt →
          interp V ρ ea = interp V ρ ea'

/-- Definitional equality, P currency, conditional on the point (task
#342, L9): two sides that are not the point are equal.  A consumer
comparing two types or two members of one type closes with
`eq_of_IsTy_of_ne_pt` / `IsTy.eq_of_ne_pt`. -/
@[expose] def DefEqClaim (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AnnotTerm},
    ConLeche.isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a →
      CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ aa ≠ pt → interp V ρ ba ≠ pt →
        interp V ρ aa = interp V ρ ba

/-- Inference, dual success, P currency: the subject's and the
type's truthfulness — bit validity included — are *conclusions*, and
the type denotes a type. -/
@[expose] def InferClaim (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AnnotTerm},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ta : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d t = some ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ ta) ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea ∈ˢ interp V ρ ta

end ConLeche.Model
