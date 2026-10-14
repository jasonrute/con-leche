--#export s2
/-! Found by the openai/math completeness run (2026-10-10; real instances
`OAI.SourceBurnside.RawNumberPrep.seed_run` (challenge PeriodicGroup; a
register store holding `List.replicate (W*(10000*(D+20)+33)) false`),
`OAI.ExactDerandomization.Vessel.Basket.Sack.Ground.advances._proof_1_2`
(challenge LogspaceEquality) and, by the same cause,
`OAI.MatchingFPRAS.ExecutableEstimator.upperRealizer` (MatchingFPRAS)).
Exit 3 until task #353, which raised `checkFuel` to 500000 (task #354:
effectively unbounded, see its docstring): accepted.

The comparison reaches the ι-reduction of `List.replicate (W*200033) false`,
whose major `W*200033` is put through `whnf`: each `Nat.add (Nat.mul W k) W`
step's literal acceleration head-normalises its first argument, the next
`Nat.mul`, one knot level per unit of the literal — 200033 levels against
the old `checkFuel = 100000` (exit 3).  The official kernel performs the
same recursion on its native stack and accepts (the v4.34.1
elaborator-side kernel reports deep recursion only at `W*20000033`), and
so does con-leche, on its native stack too.

`debug.skipKernelTC`: the pinned v4.29.1 elaborator's own kernel check
runs out of native stack on this term already at `W*50000`; the stream
is checked by the official kernel (v4.34.1 arena checker: accepts). -/
def st (n : Nat) : Fin 3 → List Bool
  | 0 => List.replicate n false
  | 1 => []
  | _ => []
set_option debug.skipKernelTC true in
theorem s2 (W : Nat) : st 0 1 = st (W*200033) 1 := rfl
