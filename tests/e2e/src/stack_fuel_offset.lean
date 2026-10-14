--#export t
import Lean
/-! Task #353, the stack policy (`checkFuel`, `ConLeche/Kernel/Core.lean`):
a recursion through the checker's knot that is deeper than the fuel must
end in a clean exit 3 (`fuel exhausted`), never in a native stack overflow
(abort, exit 134).

`h 3000000 ≡ 3000000` unfolds `h` into a 3000000-deep successor chain and
compares it with the literal one `succ` at a time (`defeqOffset`): about
0.8 KB of native stack per knot level, the deepest measured path.  At the
`checkFuel` of 500000 the run exhausts the fuel at about 0.4 GB of the
worker thread's 1 GiB stack and exits 3; at a `checkFuel` of 2000000 the
same run overflows the stack and aborts (exit 134).  The verdict pinned
is 3; official accepts (it recurses 3000000 levels on its native stack).

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
