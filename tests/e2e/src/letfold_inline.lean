--#export letfold_inline
/-! Task #348, the control for `letfold_let`: the same comparison with the
closed term written inline, no `let`.  Here the official kernel folds too
(`reduce_nat` head-normalises `bits 14 0`, 2^14 calls; ~3.4e9 instructions
at n = 14 against ~3.5e8 at n = 0), so both checkers fold closed terms
and their costs grow alike; only under a `let` do they differ. -/
def bits : Nat → Nat → Nat
  | 0, k => k % 2
  | n+1, k => bits n (2*k) + bits n (2*k+1)

set_option maxRecDepth 100000 in
theorem letfold_inline : bits 14 0 + 0 = Nat.add (bits 14 0) 0 :=
  @id (bits 14 0 + 0 = Nat.add (bits 14 0) 0) rfl
