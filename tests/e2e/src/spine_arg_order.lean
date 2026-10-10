--#export s1
/-! Found by the openai/math completeness run (2026-10-10; real instance
`OAI.MeanPayoff.DetRealizer.total_formula`, a `simp only` closing
`2*(3*L+5+3+n*(4*(L+n)+2*5+6)) = 2*(3*L+8+n*(4*(L+n)+16))` by `rfl`).

The lazy-delta same-head shortcut compares `Nat.add (M+1) 1` with
`Nat.add M 2` (`M := 2*(x+5000000)`) argument by argument.  Official
`is_def_eq_args` walks the spine from the LAST argument (`app_arg`
first), so `1 =?= 2` fails at once and both sides unfold.  con-leche's
`defeqSpine` walks it from the first, so it decides `M+1 =?= M` first:
correct, but by unary descent through the `succ`s of `2*(x+5000000)`
(`defeqOffset`, two knot levels per `succ`), and dies of `checkFuel`
(exit 3) after 50000 `succ`s (already at `x+30000`).  Official accepts
instantly.  Walking `defeqSpine`'s arguments last-first (both twins)
accepts; raising `checkFuel` to 2000000 instead overflows the native
stack (SIGSEGV), so this is an order divergence, not a budget one. -/
theorem s1 (x : Nat) : 2*(x+5000000)+1+1 = 2*(x+5000000)+2 := rfl
