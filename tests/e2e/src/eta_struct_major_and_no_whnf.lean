--#export andMajorNoWhnf
/- Task #342 R2, the arena's `corner-cases/eta-struct-major-and-no-whnf`
(lean4#15351 with lean4#15371): `andConst h` is
`And.rec (fun _ _ => 1) h`, applied to a proof of `True ∧ True` built
from Coquand's paradox (via `propext`), which has no weak head normal
form.  The `And` rescue on the major *as found* fabricates
`And.intro True True h.1 h.2` from the major's type (its type check
and the proof-irrelevance certificate read only types), and the rule
fires without reducing the proof: `1 = 1`.

Before task #342 R2 the major was head-normalized first: the loop never
returned and overflowed the native stack (exit 134).  Today: accept, as
the planned official kernel does (lean4#15371 eta-expands such majors,
lean4#15351 before reducing them).  Target: accept. -/
import Lean
open Lean Meta Elab Tactic


/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

theorem tautext {A B : Prop} (a : A) (b : B) : A = B := propext ⟨fun _ => b, fun _ => a⟩
def True' : Prop := ∀ A : Prop, A → A
def delta : True' → True' := fun z => z (True' → True') id z
def omega : True' := fun _ a => cast (tautext id a) delta
def Omega : True' := delta omega

noncomputable def andConst (h : True ∧ True) : Nat := And.rec (motive := fun _ => Nat) (fun _ _ => 1) h

set_option debug.skipKernelTC true in
theorem andMajorNoWhnf : andConst (Omega _ ⟨.intro, .intro⟩) = 1 := by unchecked_rfl
