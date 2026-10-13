--#export prodMajorNoWhnf
/- Task #342 R2, the arena's `corner-cases/eta-struct-major-no-whnf`
(lean4#15351, part of Lean's kernel logic renovation, lean4#14977): a
structure major whose head normalization does not terminate.
`prodConst loopPair` is `Prod.rec (fun _ _ => 1) loopPair`, and
`loopPair` is an `Acc.rec` whose major is a proof built from Coquand's
paradox (via `propext`), with no weak head normal form.  Expanding the
`Prod` major by structure η *as found* — before reducing it — lets the
recursor fire from the major's type alone: `1 = 1`.

Before task #342 R2 the major was head-normalized first (the official
kernel's order today): the δ loop never returned, and since the loop
grew the native stack per step, the checker aborted on a stack
overflow (exit 134) after about 1.8 s.  Today: accept, as the planned
official kernel (lean4#15351) does.  Target: accept. -/
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

def loopAcc : Acc (fun _ _ : Nat => False) 0 := Omega _ (Acc.intro 0 fun _ h => h.elim)
noncomputable def loopPair : Nat × Nat :=
  Acc.rec (motive := fun _ _ => Nat × Nat) (fun _ _ _ => (0, 0)) loopAcc
noncomputable def prodConst (p : Nat × Nat) : Nat := Prod.rec (motive := fun _ => Nat) (fun _ _ => 1) p

set_option debug.skipKernelTC true in
theorem prodMajorNoWhnf : prodConst loopPair = 1 := by unchecked_rfl
