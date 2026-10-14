module

public import ConLeche.Kernel.Core

public section

/-!
# The mode functions (task #185; the eager towers, task #353)

`CheckMode.verifiedChecks` (`ConLeche/Kernel/Env.lean`) is the cores'
whole configuration besides the eager flag (`CheckMode.eager`): every
read a shipped core makes is one of the two, a `match` on the enum.
These are the forms the proofs consume: the model tier's
`hμ : μ.isVerified = true` names `.verified` itself
(`CheckMode.eq_verified`); the mode-parametric simulation tower
(`ConLeche/Verify/Cached/*`) and the bridges run inside the eager
tower too and take the weaker `hμ : mode.verifiedChecks = true`
(`CheckMode.verified_cases`).

The module imports `Kernel.Core` and nothing else: it is base-tier.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- **The `--verified` mode is `.verified`** — the model tier's way
through a cached body's certificate switches: after
`obtain rfl := CheckMode.eq_verified hμ` every `certAtI` read is at the
literal `.verified` and reduces by `rfl`. -/
theorem CheckMode.eq_verified (h : mode.isVerified = true) :
    mode = .verified := by
  cases mode <;> simp_all [CheckMode.isVerified]

/-- The `--verified` mode runs the verified checks. -/
theorem CheckMode.vc (h : mode.isVerified = true) :
    mode.verifiedChecks = true := by
  cases mode <;> simp_all [CheckMode.isVerified, CheckMode.verifiedChecks]

/-- **A mode running the verified checks is `.verified` or its eager
tower** (task #353): the simulation tower's way through a cached
body's certificate switches — after `rcases CheckMode.verified_cases hμ
with rfl | rfl` every `certAtI` read is at a literal mode and reduces
by `rfl`. -/
theorem CheckMode.verified_cases (h : mode.verifiedChecks = true) :
    mode = .verified ∨ mode = .verifiedEager := by
  cases mode <;> simp_all [CheckMode.verifiedChecks]

/-- The eager tower runs the checks its mode runs. -/
@[simp] theorem CheckMode.verifiedChecks_toEager :
    mode.toEager.verifiedChecks = mode.verifiedChecks := by
  cases mode <;> rfl

end ConLeche
