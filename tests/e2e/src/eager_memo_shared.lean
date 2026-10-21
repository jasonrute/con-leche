--#export t
import Lean
/-! Task #361, the eager tower's memos persist across the eager
comparisons of a declaration.  `t` proves a conjunction of two
`eagerReduce` arguments (`eager_open_nat`'s comparison, at two bounds):
`@id (Nat.ble (x*0 + 1000000) 999999 = false) (eagerReduce (Eq.refl
false))` and the same at `999998`, under the binder `x : Nat`.  Each is
an eager comparison (the knot's `defeqE` slot); the second finds what
the first learned (the head normal form of `x*0 + 1000000`, the
unfoldings of `Nat.ble`) in the eager tower's stored memos, and
neither leaves an entry in the plain memos (`withEagerMemos`).  Both
official and con-leche accept instantly.

`hint_eager` is `eager_open_nat`'s. -/
open Lean Elab Term Meta in
elab "hint_eager" : term <= T => do
  let T ← instantiateMVars T
  let some (α, _, rhs) := T.eq? | throwError "hint_eager: expected an equation"
  let u ← getLevel α
  let refl := mkApp2 (mkConst ``Eq.refl [u]) α rhs
  let arg := mkApp2 (mkConst ``eagerReduce [levelZero]) (mkApp3 (mkConst ``Eq [u]) α rhs rhs) refl
  return mkApp2 (mkConst ``id [levelZero]) T arg

set_option debug.skipKernelTC true in
theorem t (x : Nat) : Nat.ble (x*0 + 1000000) (1000000 - 1) = false ∧
    Nat.ble (x*0 + 1000000) (1000000 - 2) = false :=
  ⟨hint_eager, hint_eager⟩
