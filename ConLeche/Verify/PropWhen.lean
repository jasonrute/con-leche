module

public import ConLeche.Verify.Level
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern): its constructors are `public` but the module is
not `@[expose]`d, so a `cases`-then-`rfl` proof about a datum cannot
see the reduct.  `import all` gives that view HERE only; nothing this
module exports depends on it. -/
import ConLeche.Kernel.PropWhen
import all ConLeche.Kernel.PropWhen

public section

/-!
# The zero-ness datum against `Level` (task #161)

`ConLeche/Kernel/PropWhen.lean` owns the datum: its representation, its
API, and every law about the datum *alone*.  This file is a *consumer*
of that API; it proves what the datum alone cannot say, namely how it
relates to `Level`:

* **Soundness of the readout** — `zeronessOf_sound`:
  `(zeronessOf l).holds φ = (eval φ l == 0)`.
* **The substitution's semantic reading** — `holds_substPW`: the
  instantiated datum's bit is the datum's bit at the composed
  valuation.

Nothing here unfolds the datum's representation: every step goes
through the exported `casesZ` view and the `_never`/`_ifAllZero`
equations.
-/

namespace ConLeche.PropWhen

/-! ## Soundness of the readout -/

private theorem beq_zero_and (x y : Nat) :
    ((x == 0) && (y == 0)) = (Max.max x y == 0) := by
  cases hx : x == 0 <;> cases hy : y == 0 <;> simp_all <;> omega

theorem zeronessOf_sound (φ : Name → Nat) :
    ∀ l : Level, (Level.zeronessOf l).holds φ = (Level.eval φ l == 0)
  | .zero => by simp [Level.zeronessOf, Level.eval]
  | .succ l => by simp [Level.zeronessOf, Level.eval]
  | .param n => by simp [Level.zeronessOf, Level.eval]
  | .max a b => by
    rw [Level.zeronessOf, holds_inter, zeronessOf_sound φ a,
      zeronessOf_sound φ b, beq_zero_and]
    rfl
  | .imax a b => by
    rw [Level.zeronessOf, zeronessOf_sound φ b]
    show _ = ((if Level.eval φ b = 0 then 0
      else Max.max (Level.eval φ a) (Level.eval φ b)) == 0)
    by_cases hb : Level.eval φ b = 0
    · simp [hb]
    · have hm : ¬ Max.max (Level.eval φ a) (Level.eval φ b) = 0 := by
        omega
      have h1 : (Level.eval φ b == 0) = false := by simpa using hb
      have h2 : (Max.max (Level.eval φ a) (Level.eval φ b) == 0) = false :=
        by simpa using hm
      rw [h1, ite_eq_right hb, h2]

end ConLeche.PropWhen

namespace ConLeche.Level

open ConLeche.PropWhen

/-- **The pushforward's semantic reading** (task #161 P3): the
instantiated datum's bit at `φ` is the datum's bit at the composed
valuation `Level.substFn φ ks vs` — the same composed valuation
`denoteMeta`'s constant clause uses; its level crossing rides this. -/
theorem holds_substPW (φ : Name → Nat) (ks : List Name)
    (vs : List Level) : ∀ pw : PropWhen,
    (substPW ks vs pw).holds φ = pw.holds (substFn φ ks vs) := by
  intro pw
  cases pw with
  | never => rfl
  | ifAllZero ps =>
    rw [show substPW ks vs (PropWhen.ifAllZero ps)
          = PropWhen.bindZ.go (fun n => zeronessOf (subst.go ks vs n)) ps from
        bindZ_ifAllZero _ _,
      holds_bindZ_go, PropWhen.holds_ifAllZero]
    induction ps with
    | nil => rfl
    | cons n rest ih =>
      simp only [List.all_cons, ih]
      rw [zeronessOf_sound, eval_subst_go]

end ConLeche.Level
