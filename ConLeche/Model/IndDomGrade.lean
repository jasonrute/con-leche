module

public import ConLeche.Model.Currency
import ConLeche.Model.Rules.RedSoundKit
public section

/-!
# Gradings read back out of `.pi` readings and application spines

`WellDenoted`/`AnnotValid` are conjunctive at `.pi` and `.app`, so a
graded reading's domain, body and arguments are graded — each one
projection.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (ITerm)
open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → ITerm}

/-! ## The `.pi` split, in the P currency -/

/-- A `.pi` reading's domain is graded when the reading is. -/
theorem WellDenoted_pi_dom {ρ : Nat → V} {A B : ITerm}
    (h : WellDenoted V ρ (.pi A B)) : WellDenoted V ρ A :=
  (cast (WellDenoted_pi V ρ A B) h).1

/-- A `.pi` reading's domain is a graded type when the reading is
graded (task #342, L5: the `.pi` clause carries the domain's `IsTy`). -/
theorem WellDenotedTy_pi_dom {ρ : Nat → V} {A B : ITerm}
    (h : WellDenoted V ρ (.pi A B)) : WellDenotedTy V ρ A :=
  ⟨WellDenoted_pi_dom h, (cast (WellDenoted_pi V ρ A B) h).2.1⟩

/-- A `.pi` reading's body is graded at every extension by an element
of the domain. -/
theorem WellDenoted_pi_body {ρ : Nat → V} {A B : ITerm}
    (h : WellDenoted V ρ (.pi A B)) {x : V}
    (hx : x ∈ˢ interp V ρ A) : WellDenoted V (cons x ρ) B :=
  (cast (WellDenoted_pi V ρ A B) h).2.2.1 x hx

/-! ## Application spines, graded backwards -/

/-- An application's argument is graded when the application is. -/
theorem WellDenoted_app_arg {ρ : Nat → V} {g a : ITerm}
    (h : WellDenoted V ρ (.app g a)) : WellDenoted V ρ a :=
  (cast (WellDenoted_app V ρ g a) h).2.1

/-- **Every argument of a graded application spine is graded.** -/
theorem WellDenoted_mkAppN_args {ρ : Nat → V} :
    ∀ (as : List ITerm) {g : ITerm},
      WellDenoted V ρ (ITerm.mkAppN g as) → ∀ a ∈ as, WellDenoted V ρ a := by
  intro as
  induction as with
  | nil => intro g _ a ha; exact nomatch ha
  | cons x xs ih =>
    intro g h a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact WellDenoted_app_arg (Rules.mkAppN_head xs h)
    · exact ih (g := .app g x) h a ha'

end ConLeche.Model
