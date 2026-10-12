--#export T.rec
/- A `let` on the type former's telescope spine. -/
inductive T : let X := Nat; X → Type where
  | mk : (x : Nat) → T x
