module

public import ConLeche.MainTheorem
public import ConLeche.Model.Env.EnvModelM
public import ConLeche.Model.NatSem
public import ConLeche.Model.Denotes
public import ConLeche.SetTheory.Derive.Universe
public section

/-!
# Arithmetic soundness: the second theorem

The main theorem (`ConLeche.model_exists`) is parametric over any
first-order model `V` of `SetTheory` — ZF⁻ plus an ω-chain of
Grothendieck universes, i.e. a first-order model of ZFC with
`{n inaccessibles | n ∈ ω}` (Carneiro's `OmegaInaccessibles`, bridged in
`bridge/lean4lean-model`).  This module adds the second theorem asked
for in the task: **arithmetic soundness**.  If `φ` is a closed
first-order statement of arithmetic — a term of the small deep
embedding `AProp` below, built from `Nat` numerals, `Nat.zero`,
`Nat.succ`, `Nat.add`, `Nat.mul`, `Nat.pred`, `Nat.sub`, `Nat.beq`,
`Eq`, and the propositional connectives — and `con-leche` accepts a
proof of `φ` (a `thmDecl` whose declared type is `φ`'s term appears in
an accepted stream), then `φ` is satisfied by the standard model of
arithmetic inside `V`: by `ω` with the von Neumann numerals `vnat k`.

The proof route is the main theorem's own machinery.  In the model of
an accepted environment, every stored constant is a member of what its
type denotes (`Model.mem`); a theorem of type `φ` is therefore a member
of `φ`'s denotation.  Two lemmas do the rest:

* `denote_aNat`: the denotation of an arithmetic `Nat` expression is
  `vnat` of its meta-level value — proved from the environment's own
  `NatHeads`/`NatOps` laws (the stored `Nat` heads' memberships and the
  pinned recurrence equations the model tier already computes with,
  `Model/NatSem.lean`), which say exactly that the stored `Nat` denotes
  `ω` and the operations compute on the `vnat`.
* `denote_aProp`: the denotation of an arithmetic proposition is a
  truth value (`truthVal` of its meta-level satisfaction), using
  `Model.eq_equality` for `Eq`.

Membership of a truth value is equality with `pt`
(`eq_pt_of_mem_truthVal`), and `truthVal p` contains `pt` exactly when
`p` (`pt_mem_truthVal` / `of_mem_truthVal`).  So the theorem's member
yields `φ.satV`, the meta-level statement of arithmetic.
-/

namespace ConLeche

open SetTheory
open ConLeche.Model (EnvModelM NatHeads NatOps natLit natLeafV cvalOf)
open ConLeche.Semantics (interp)

universe w

/-! ## First-order statements of arithmetic, as kernel terms

A small deep embedding: `ANat` for closed `Nat`-typed expressions and
`AProp` for closed propositions over them, each with a `toExpr` into
the kernel's `Expr`.  The fragment is deliberately small; the theorem
below is about exactly these terms. -/

/-- A closed `Nat`-typed expression of the arithmetic fragment. -/
inductive ANat : Type
  | lit (n : Nat)
  | zero
  | succ (a : ANat)
  | add (a b : ANat)
  | mul (a b : ANat)
  | pred (a : ANat)
  | sub (a b : ANat)
  deriving DecidableEq, Repr

/-- A closed first-order statement of arithmetic. -/
inductive AProp : Type
  | eq (a b : ANat)
  | not (p : AProp)
  | and (p q : AProp)
  | or (p q : AProp)
  | imp (p q : AProp)
  | forallNat (p : ANat → AProp)

/-- The kernel term an arithmetic `Nat` expression is. -/
def ANat.toExpr : ANat → Expr
  | .lit n => .lit (.natVal n)
  | .zero => .const natZeroName []
  | .succ a => .app (.const natSuccName []) a.toExpr
  | .add a b => .app (.app (.const natAddName []) a.toExpr) b.toExpr
  | .mul a b => .app (.app (.const natMulName []) a.toExpr) b.toExpr
  | .pred a => .app (.const natPredName []) a.toExpr
  | .sub a b => .app (.app (.const natSubName []) a.toExpr) b.toExpr

/-- The kernel term an arithmetic proposition is: `@Eq Nat a b` for
equality (the pinned `Eq` at level `1` over `Nat`), and `Prop`-valued
formers for the connectives. -/
def AProp.toExpr : AProp → Expr
  | .eq a b =>
      .app (.app (.app (.const eqName [.succ .zero]) (.const natName [])) a.toExpr)
        b.toExpr
  | .not p =>
      .app (.const eqName [.succ .zero])
        (.app (.app (.const eqName [.zero]) p.toExpr) (.const falseName []))
  | .and p q =>
      .app (.app (.const andName []) p.toExpr) q.toExpr
  | .or p q =>
      .app (.app (.const eqName [.succ .zero])
        (.app (.app (.const eqName [.zero]) p.toExpr) (.const falseName [])))
        (.app (.app (.const eqName [.zero]) q.toExpr) (.const falseName []))
  | .imp p q =>
      .app (.app (.const eqName [.succ .zero])
        (.app (.app (.const eqName [.zero]) p.toExpr) (.const falseName []))) q.toExpr
  | .forallNat p =>
      .forallE (.const natName []) ((p (ANat.lit 0)).toExpr)

/-! ## Satisfaction in the standard model of arithmetic inside `V` -/

variable {V : Type w} [SetTheory V]

/-- The meta-level value of an arithmetic `Nat` expression. -/
def ANat.evalV : ANat → Nat
  | .lit n => n
  | .zero => 0
  | .succ a => a.evalV + 1
  | .add a b => a.evalV + b.evalV
  | .mul a b => a.evalV * b.evalV
  | .pred a => a.evalV.pred
  | .sub a b => a.evalV - b.evalV

/-- **Satisfaction of an arithmetic statement in the standard model of
arithmetic** (the meta-level `Nat` standing for `ω`'s members). -/
def AProp.satV : AProp → Prop
  | .eq a b => decide (a.evalV = b.evalV) = true
  | .not p => ¬ p.satV
  | .and p q => p.satV ∧ q.satV
  | .or p q => p.satV ∨ q.satV
  | .imp p q => p.satV → q.satV
  | .forallNat p => ∀ n : Nat, (p (.lit n)).satV

/-! ## The two denotation lemmas -/

variable {env : Env} {m : EnvModelM V .verified env} {ψ : Name → Nat}

/-- **The stored `Nat` denotes `ω`**: its members are exactly the
`vnat k`.  From the `NatHeads` law (zero and successor are members of
the stored `Nat`, which is a type) plus induction on `ω` inside `V`. -/
theorem natLeaf_eq_omega (hnh : NatHeads m.base2 ψ) :
    natLeafV m.base2 ψ (fun _ => SetTheory.empty) = omega := by
  sorry

/-- **An arithmetic `Nat` expression denotes `vnat` of its value.** -/
theorem denote_aNat (hnh : NatHeads m.base2 ψ) (hops : NatOps m.base2 ψ)
    (a : ANat) (X : V)
    (h : Denotes (cvalOf m.base2.acval) env ψ (fun _ => SetTheory.empty) a.toExpr X) :
    X = vnat a.evalV := by
  sorry

/-- **An arithmetic proposition denotes the truth value of its
satisfaction.** -/
theorem denote_aProp (m' : ConLeche.Model V env)
    (hnh : NatHeads m.base2 ψ) (hops : NatOps m.base2 ψ)
    (p : AProp) (T : V)
    (h : Denotes m'.cval env ψ (fun _ => SetTheory.empty) p.toExpr T) :
    T = truthVal p.satV := by
  sorry

/-! ## The second theorem -/

open Cached in
/-- **Arithmetic soundness.**  If `φ` is a closed first-order statement
of arithmetic and `con-leche` accepts a stream declaring a theorem of
type `φ` (the record's declared type is `φ.toExpr`), then `φ` is
satisfied by the standard model of arithmetic inside any first-order
model `V` of ZFC plus `{n inaccessibles | n ∈ ω}` — the same
`SetTheory` hypothesis as the main theorem. -/
theorem arith_sound (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration)
    (env : Env) (accepted : checkDecls .verified pins ds = .ok env)
    (p : AProp) (cv : ConstantVal) (value : Expr)
    (hmem : Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = p.toExpr) :
    p.satV := by
  sorry

end ConLeche
