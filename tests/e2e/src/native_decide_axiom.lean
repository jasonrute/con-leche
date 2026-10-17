-- A `native_decide` proof: the tactic asserts its compiled computation
-- as the axiom `nd._native.native_decide.ax_1_1`, which con-leche
-- declines, naming the tactic (task #360).
--#export nd
theorem nd : 123456 * 654321 = 80779853376 := by native_decide
