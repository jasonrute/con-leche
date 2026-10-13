module

public import ConLeche.Denotes
public import ConLeche.Semantics.WellDenoted

public section

/-!
# The `let` rule of `Denotes` (task #342, L-let)

A stored `let` denotes its body at its value; its type is not read, so
a `let` whose type denotes nothing (here a free variable, which no rule
reads) still denotes.  And the reading's ζ: a `let` interprets as its
reduct at every valuation.
-/

namespace ConLeche.LetDenotesTest
open ConLeche.Term (Term)

open ConLeche.Semantics

universe u

variable {V : Type u} [SetTheory V]
  {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
  {ρ : BVarIdx → V}

/-- `let x := Prop; x` denotes the universe of truth values. -/
example : Denotes cval env φ ρ (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0))
    (SetTheory.univ (Level.eval φ .zero)) :=
  .letE .sort .bvar

/-- The type is not read: a type that denotes nothing does not block
the `let`. -/
example : Denotes cval env φ ρ (.letE (.fvar 0 (.sort .zero)) (.sort .zero) (.bvar 0))
    (SetTheory.univ (Level.eval φ .zero)) :=
  .letE .sort .bvar

/-- …and the denotation is still unique. -/
example {X : V}
    (h : Denotes cval env φ ρ (.letE (.fvar 0 (.sort .zero)) (.sort .zero) (.bvar 0)) X) :
    X = SetTheory.univ (Level.eval φ .zero) :=
  Denotes_functional h (.letE .sort .bvar)

/-- ζ in the reading, at every valuation. -/
example (v b : Term) (σ : Nat → V) :
    interp V σ (.letE v b) = interp V σ (b.inst v) :=
  interp_zeta V v b σ

end ConLeche.LetDenotesTest
