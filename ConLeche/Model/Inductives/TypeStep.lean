module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.Sound
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.InferLemmas

public section

/-!
# Walking types: the whnf step and the sort test, at the conditional claims

The positivity readers (`PosDerivMono`, `PosDerivNodes`, `PosDerivAcc`,
`NestPosRed`) walk the TYPES of constructor fields.  Under the conditional
claims (task #342, L9) a whnf step equates a subject with its reduct only
where the subject is not the point; a type never is ("not pt" source (1)),
so the readers carry the walked types' `IsTy` (`GradedTy`) and read their
steps through `red_sound_ty` (task #342, L12).

* `whnf_ty` — a checker whnf run on a graded type: `red_sound_ty` through
  the bridge;
* `gradedTy_of_sort` — a term whose inferred type whnf's to a sort (the
  checker's `ensureSort`) reads as a graded type: its type reads as a
  universe ("not pt" source (1) for the type's own step), whose members are
  types (`IsTy_of_mem_univ`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **A whnf run on a graded type** reads like its input, and its output is a
graded type (`red_sound_ty`). -/
theorem whnf_ty (hin : RulesInputs V m φ) {F d : Nat} {e w : Expr}
    (hw : ConLeche.whnf .verified env F d e = .ok w) (hf : Frame d e)
    {Δa : List AnnotTerm} {ea : AnnotTerm} (hC : CtxOk m φ d Δa e)
    (hea : denoteMeta m.acval env φ d e = some ea) (hg : GradedTy V Δa ea) :
    Frame d w ∧ LeavesSub w e ∧
      ∃ wa, denoteMeta m.acval env φ d w = some wa ∧ GradedTy V Δa wa ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ wa :=
  red_sound_ty hin (ConLeche.Rules.whnf_bridge hw) hf hC hea hg

/-- **A term whose type is a sort reads as a graded type**: the inference
claim puts its reading in its type's, the type is a type (so the sort
test's whnf step is an equation, "not pt" source (1)), and it reads as a
universe, whose members are types. -/
theorem gradedTy_of_sort (hin : RulesInputs V m φ) {F d : Nat} {e ty : Expr} {u : Level}
    (hty : ConLeche.inferTypeCore .verified env F d e = .ok ty)
    (hsort : ConLeche.ensureSortCore .verified env F d ty = .ok u) (hf : Frame d e)
    {Δa : List AnnotTerm} {ea : AnnotTerm} (hC : CtxOk m φ d Δa e)
    (hea : denoteMeta m.acval env φ d e = some ea) : GradedTy V Δa ea := by
  have hI : InferSemFull m φ d e ty := infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hty)
  obtain ⟨hft, hsub, ta, hta, hs⟩ := hI hf hC.toS hea
  obtain ⟨-, -, sa, hsa, hrs⟩ := red_sound hin
    (ConLeche.Rules.whnf_bridge (ConLeche.ensureSortCore_inv hsort)) hft
    (hC.toS.of_subset hsub) hta
  rw [denoteMeta_sort] at hsa
  obtain rfl := Option.some.inj hsa
  intro ρ hρ
  obtain ⟨hgE, hgT, hmem⟩ := hs ρ hρ (hC.leavesGr hρ)
  obtain ⟨-, heq⟩ := hrs ρ hρ ((hC.leavesGr hρ).of_subset hsub) hgT.1 hgT.2.ne_pt
  rw [heq, interp_sort] at hmem
  exact ⟨hgE, IsTy_of_mem_univ hmem⟩

end ConLeche.Model
