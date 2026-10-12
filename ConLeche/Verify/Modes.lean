module

public import ConLeche.Kernel.Core

public section

/-!
# The mode functions at the two constructors (task #185)

`CheckMode`'s functions (`ConLeche/Kernel/Env.lean`) are the cores'
whole configuration: every read a shipped core makes is one of
`verifiedChecks` and `certs`, each a `match` on the enum.
These are their values at the two constructors — all `rfl` — plus the
conditional forms the mode-parametric simulation tower
(`ConLeche/Verify/Cached/*`) consumes under its
`hμ : mode.verifiedChecks = true`: at such a mode the certificate
families are on.

The module imports `Kernel.Core` and nothing else: it is base-tier.
-/

namespace ConLeche

variable {mode : CheckMode}

@[simp] theorem verifiedChecks_verified :
    CheckMode.verifiedChecks .verified = true := rfl
@[simp] theorem verifiedChecks_trusted :
    CheckMode.verifiedChecks .trusted = false := rfl
@[simp] theorem certs_verified : CheckMode.certs .verified = true := rfl
@[simp] theorem certs_trusted : CheckMode.certs .trusted = false := rfl

/-- The two certification-only switches agree at both constructors;
they stay two functions because they gate different work (see
`CheckMode.certs`). -/
theorem certs_eq_verifiedChecks : mode.certs = mode.verifiedChecks := by
  cases mode <;> rfl

/-- **A mode running the verified checks is `.verified`** — the enum has
two constructors and the other one does not.  This is the simulation
tower's way through a cached body's certificate switches: after
`obtain rfl := CheckMode.eq_verified hμ` every `certAtI` read is at the
literal `.verified` and reduces by `rfl`. -/
theorem CheckMode.eq_verified (h : mode.verifiedChecks = true) :
    mode = .verified := by
  cases mode <;> simp_all [CheckMode.verifiedChecks]

/-- A mode running the verified checks runs the certificate families. -/
@[simp] theorem certs_of_verifiedChecks (h : mode.verifiedChecks = true) :
    mode.certs = true := by
  rw [certs_eq_verifiedChecks, h]

end ConLeche
