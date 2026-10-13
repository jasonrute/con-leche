--#export loopFst
/- Task #342 R2: a head normalization that does not terminate, in a
position where nothing avoids it.  `loopPair.1 = 0` needs `loopPair`'s
head normal form: `loopPair` is an `Acc.rec` whose major — a proof
built from Coquand's paradox — must be reduced to a constructor
(`Acc` is not a structure, so no rescue applies), and its δ chain
(`Omega` → `delta omega` → … → `Omega`) never ends.  The official
kernel does not terminate here either.

Before task #342 R2 every step of the `whnf` loop grew the native
stack, and the checker aborted on a stack overflow (exit 134) after a
few seconds.  The loop now iterates in constant stack and memory, and
the run ends at the external timeout (exit 124 at this fixture's 5 s
budget, `tests/arena.sh`).  Target: the same — no verdict exists. -/
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

set_option debug.skipKernelTC true in
theorem loopFst : loopPair.1 = 0 := by unchecked_rfl
