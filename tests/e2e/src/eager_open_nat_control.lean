--#export t
import Lean
/-! Task #353, the control of `eager_open_nat`: the same comparison
without `eagerReduce`, at a tenth of the size.  `t` checks
`@id (Nat.ble (x*0 + 100000) 99999 = false) (Eq.refl false)` under
`x : Nat`: the free `x` blocks the lazy-delta Nat-literal fold, so
`Nat.ble` is unfolded into its structural recursion and the literal
peeled in unary — in official and in con-leche alike (both accept;
official in ~1 s, con-leche in ~6 s). -/
open Lean Elab Term Meta in
elab "hint_plain" : term <= T => do
  let T ← instantiateMVars T
  let some (α, _, rhs) := T.eq? | throwError "hint_plain: expected an equation"
  let u ← getLevel α
  return mkApp2 (mkConst ``id [levelZero]) T (mkApp2 (mkConst ``Eq.refl [u]) α rhs)

set_option debug.skipKernelTC true in
theorem t (x : Nat) : Nat.ble (x*0 + 100000) (100000 - 1) = false := hint_plain
