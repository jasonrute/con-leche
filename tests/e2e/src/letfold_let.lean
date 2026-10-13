--#export letfold
/-! Task #348, the mechanism of the openai/math SquareDifference blow-up
(`OAI.SquareDifference.source_ordered_contraction`): a `let` bound to a
closed Nat that is expensive to head-normalise, whose variable then meets
the lazy-delta Nat-literal fold.

`bits 14 0` makes 2^14 distinct calls before it is a literal.  Under the
`let`, the comparison `d + 0 =?= Nat.add d 0` reaches lazy delta, whose
literal fold (official `lazy_delta_reduction` → `reduce_nat`) fires only
when neither side has a free variable.  The official kernel checks the
body with `d` as a let-fvar, so the fold does not fire: it unfolds
`HAdd.hAdd` to `Nat.add d 0` and is done, never evaluating `d` (flat in
the size).  con-leche's annotate pass ζ-substitutes the `let` (as do the
S0 prototype's inference and nanoda's `infer_let`), the comparison is
closed, and the fold head-normalises `bits 14 0` (cost 2^n: at n = 14,
~7.2e9 instructions and 0.2 GB, against official's ~3.5e8 at every n;
at n = 16, 2.7e10 and 0.7 GB).  In SquareDifference the value is
`Fintype.card TupleVertex`, whose whnf enumerates permutations: over
6 GB.  See `letfold_inline` (the control) and `letfold_pair_let`. -/
def bits : Nat → Nat → Nat
  | 0, k => k % 2
  | n+1, k => bits n (2*k) + bits n (2*k+1)

theorem letfold : bits 14 0 + 0 = Nat.add (bits 14 0) 0 :=
  let d := bits 14 0
  @id (d + 0 = Nat.add d 0) rfl
