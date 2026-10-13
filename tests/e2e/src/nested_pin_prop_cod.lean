--#export T.rec T.rec_1

-- a pin component that is a ∀ with a Prop CODOMAIN: its sort's
-- zero-ness datum is `ifAllZero []`, not `.never`.
inductive Wrap (A : Prop) : Prop where
  | mk : A → Wrap A
inductive T : Prop where
  | mk : Wrap (True → T) → T
