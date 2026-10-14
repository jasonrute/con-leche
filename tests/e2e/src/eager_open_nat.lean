--#export t
import Lean
/-! Task #353, official's `eagerReduce` flag (`m_eager_reduce`): an
argument of the form `eagerReduce _ _` has its type compared with the
domain in eager mode, where the lazy-delta Nat-literal fold (and the
`Bool.true` shortcut) fire although the terms have free variables.

`t` checks `@id (Nat.ble (x*0 + 1000000) 999999 = false)
(eagerReduce (Eq.refl false))`, under the binder `x : Nat`.  In eager
mode `Nat.ble (x*0 + 1000000) 999999 =?= false` folds at once: the
whnf of `x*0 + 1000000` is the literal (`Nat.mul x 0` unfolds to `0`
on its second argument), and `Nat.ble` on two literals is computed.
Without the flag the fold is blocked by the free `x`, and lazy delta
unfolds `Nat.ble` into its structural recursion, which peels the
literal in unary (`eager_open_nat_control`, the same without
`eagerReduce`).  Official accepts instantly; con-leche before task #353
peeled (83 s at this size), since then it accepts instantly as well.

`hint_eager` builds the term without the elaborator deciding the
equation (the kernel does); `debug.skipKernelTC` keeps the elaborator's
own kernel off it. -/
open Lean Elab Term Meta in
elab "hint_eager" : term <= T => do
  let T ← instantiateMVars T
  let some (α, _, rhs) := T.eq? | throwError "hint_eager: expected an equation"
  let u ← getLevel α
  let refl := mkApp2 (mkConst ``Eq.refl [u]) α rhs
  let arg := mkApp2 (mkConst ``eagerReduce [levelZero]) (mkApp3 (mkConst ``Eq [u]) α rhs rhs) refl
  return mkApp2 (mkConst ``id [levelZero]) T arg

set_option debug.skipKernelTC true in
theorem t (x : Nat) : Nat.ble (x*0 + 1000000) (1000000 - 1) = false := hint_eager
