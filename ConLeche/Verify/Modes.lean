module

public import ConLeche.Kernel.Core

public section

/-!
# The mode functions at the two constructors (task #185)

`CheckMode.verifiedChecks` (`ConLeche/Kernel/Env.lean`) is the cores'
whole configuration: every read a shipped core makes is that function,
a `match` on the enum.  These are its values at the two constructors —
both `rfl` — plus the conditional form the mode-parametric simulation
tower (`ConLeche/Verify/Cached/*`) consumes under its
`hμ : mode.verifiedChecks = true`.

The module imports `Kernel.Core` and nothing else: it is base-tier.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- **A mode running the verified checks is `.verified`** — the enum has
two constructors and the other one does not.  This is the simulation
tower's way through a cached body's certificate switches: after
`obtain rfl := CheckMode.eq_verified hμ` every `certAtI` read is at the
literal `.verified` and reduces by `rfl`. -/
theorem CheckMode.eq_verified (h : mode.verifiedChecks = true) :
    mode = .verified := by
  cases mode <;> simp_all [CheckMode.verifiedChecks]

end ConLeche
