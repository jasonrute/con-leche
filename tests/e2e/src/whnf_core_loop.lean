--#export loopRec
/- Task #342 R2: `whnf_delta_loop.lean` without δ — the non-terminating
head normalization runs entirely in the `whnfCore` loop (β and the
K-like `Eq.rec` ι only; `Ω`'s pieces are written inline, so no
definition is unfolded).  `accRecLoop` is an `Acc.rec` into `Nat`
whose major is that `Ω` applied to `Acc.intro`; the major must be
reduced to a constructor (`Acc` is not a structure), and the reduction
never ends.  The official kernel does not terminate here either.

Before task #342 R2 a fired ι or a β with arguments left over normalized
its reduct in a nested call, so the loop grew the native stack per step
and the checker aborted on a stack overflow (exit 134).  The loop's
steps now return their continuation to it (`WhnfStep`), the loop
iterates in constant stack and memory, and the run ends at the external
timeout (exit 124 at this fixture's 5 s budget, `tests/arena.sh`).
Target: the same — no verdict exists. -/
import Lean
open Lean Meta Elab Tactic


/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

theorem tautext {A B : Prop} (a : A) (b : B) : A = B := propext ⟨fun _ => b, fun _ => a⟩

def omegaAcc : Acc (fun _ _ : Nat => False) 0 :=
    ((fun z : (∀ A : Prop, A → A) => z ((∀ A : Prop, A → A) → (∀ A : Prop, A → A)) (fun x => x) z)
      (fun (A : Prop) (a : A) =>
        @Eq.rec Prop ((∀ A : Prop, A → A) → (∀ A : Prop, A → A)) (fun B _ => B)
          (fun z : (∀ A : Prop, A → A) => z ((∀ A : Prop, A → A) → (∀ A : Prop, A → A)) (fun x => x) z)
          A (tautext (fun x : (∀ A : Prop, A → A) => x) a))
      (Acc (fun _ _ : Nat => False) 0) (Acc.intro 0 fun _ h => h.elim))
noncomputable def accRecLoop : Nat :=
  @Acc.rec Nat (fun _ _ => False) (fun _ _ => Nat) (fun _ _ _ => 0) 0 omegaAcc

set_option debug.skipKernelTC true in
theorem loopRec : accRecLoop = 1 := by unchecked_rfl
