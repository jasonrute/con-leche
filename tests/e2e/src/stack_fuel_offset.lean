--#export t
import Lean
/-! Tasks #353 and #354 (`checkFuel`, `ConLeche/Kernel/Core.lean`): a
recursion through the checker's knot deeper than the native stack holds.

`h 3000000 ≡ 3000000` unfolds `h` into a 3000000-deep successor chain and
compares it with the literal one `succ` at a time (`defeqOffset`): about
0.8 KB of native stack per knot level, the deepest measured path, so the
run overflows the worker thread's 1 GiB stack and aborts (exit 134).
Task #353's `checkFuel` of 500000 ran out first (a clean exit 3); since
task #354 the fuel is effectively unbounded and the stack is the limit.
Official accepts (it recurses 3000000 levels on its native stack).

`hint_rfl` builds `@id (h 3000000 = 3000000) (Eq.refl (h 3000000))`
without the elaborator deciding the equation (the kernel does);
`debug.skipKernelTC` keeps the elaborator's own kernel off it. -/
open Lean Elab Term Meta in
elab "hint_rfl" : term <= T => do
  let T ← instantiateMVars T
  let some (α, lhs, _) := T.eq? | throwError "hint_rfl: expected an equation"
  let u ← getLevel α
  return mkApp2 (mkConst ``id [levelZero]) T (mkApp2 (mkConst ``Eq.refl [u]) α lhs)

def h : Nat → Nat
  | 0 => 0
  | n+1 => Nat.succ (h n)

set_option debug.skipKernelTC true in
theorem t : h 3000000 = 3000000 := hint_rfl
