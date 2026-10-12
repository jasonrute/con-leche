--#export letfold_pair
/-! Task #348, `letfold_let` with a closed NON-Nat let value: the `let`
binds a pair, and the Nat in the comparison is its projection `p.1`.
The official kernel's fold guard sees the let-fvar `p` and does not
fire (flat in the size); after ζ-substitution con-leche's fold
head-normalises `(bits 14 0, 1).1`, projection and all (the same 2^14
cost as `letfold_let`). -/
def bits : Nat → Nat → Nat
  | 0, k => k % 2
  | n+1, k => bits n (2*k) + bits n (2*k+1)

theorem letfold_pair : (bits 14 0, 1).1 + 0 = Nat.add (bits 14 0, 1).1 0 :=
  let p : Nat × Nat := (bits 14 0, 1)
  @id (p.1 + 0 = Nat.add p.1 0) rfl
