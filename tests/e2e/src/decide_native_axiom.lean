-- A `decide +native` proof: the axiom is `dn._native.decide.ax_1_1`
-- (`Lean.Meta.nativeEqTrue` with tactic name `decide`); declined,
-- naming `decide +native` (task #360).
--#export dn
theorem dn : 123456 * 654321 = 80779853376 := by decide +native
