module

import ConLeche.Verify.Cached.BridgeC
public import ConLeche.Cached.Installed
public import ConLeche.Verify.Cached.SimC
public import ConLeche.Verify.EnvBound
import ConLeche.Verify.Cached.ParInstall
import ConLeche.Verify.Cached.KnotCongr
import ConLeche.Verify.CheckerSplit

public section

/-!
# Phase A's steps simulate the pure install and check halves

`FullyChecked μ ds` (`ConLeche/Cached/Installed.lean`) is what the
driver's two loops assemble: phase A's accepting run (`InstallRun`)
installs a separable value declaration by the install half and records
its datum, and every record was checked against the prefix view
`fe.restrictTo vis` from a fresh memo state (`GroupChecked`).  This
module holds the model-free half of the walk over that run:

* `installHeaderC_run` / `installValueGuardsC_run` / `installGuardsC_run` — phase
  A's install is the pure install halves
  (`installHeader`, `installValueGuards`, `ConLeche/Kernel/CheckerSplit.lean`).
* `checkPending_run` — the check at the prefix view simulates the pure
  check half `checkValueGroup` at the truncated environment.  The view
  and `mkFEnv` of the truncated environment have the same `find?`
  (`mkFEnv_find?_visibleBelow`, under the name uniqueness every driver
  step preserves — `PushChain`), so by `coreKnotI_congr` they run the
  SAME core, and the simulation stated at `mkFEnv env` covers the check
  at the view.

The walk itself — the model carried along the run, and the letters on
the fully checked environment — is `ConLeche/Model/InstallRun.lean`:
it needs the model's well-formedness at every step, so it stands above
the model lane (`tests/layering.sh`).
-/

namespace ConLeche.Cached

open ConLeche

variable {μ : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## The two-phase driver: phase A's install halves -/

/-- Phase A's header install is the pure install half: from an
invariant state at `mkFEnv env`, a successful run returns the header
as declared, its type well scoped, and `installHeader` succeeds on
it. -/
theorem installHeaderC_run {env : Env}
    {cv cvA : ConstantVal} {s₀ s' : CState} (hs : CSOK μ env s₀)
    (h : installHeaderC (mkFEnv env) cv s₀ = .ok (cvA, s')) :
    CSOK μ env s' ∧ cvA = cv ∧ Expr.WScoped 0 cv.type ∧
    installHeader (m := CheckM) env cv = .ok cv := by
  unfold installHeaderC at h
  simp only [mkFEnv_find?] at h
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [ite_eq_left h1] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_right h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [ite_eq_left h2] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_right h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [ite_eq_left h3] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_right h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [ite_eq_right h4] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_left h4] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [ite_eq_right h5] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_left h5] at h
  rw [hasFvar_spec' rfl] at h
  by_cases h6 : Expr.hasFvar cv.type = true
  · rw [ite_eq_left h6] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_right h6] at h
  try dsimp only at h
  rw [Expr.allLevelParamsDefinedC_spec] at h
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams cv.type = true
  case neg => rw [ite_eq_right h7] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_left h7] at h
  rw [constsResolveFC_spec, constsResolveF_eq] at h
  by_cases h8 : Expr.constsResolve env cv.type = true
  case neg => rw [ite_eq_right h8] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_left h8] at h
  obtain ⟨rfl, rfl⟩ := pureC_ok h
  refine ⟨hs, rfl, Expr.WScoped.of_not_hasFvar (by simpa using h6), ?_⟩
  exact installHeader_of_facts (Option.not_isSome_iff_eq_none.mp h1)
    (by simpa using h2) (by simpa using h3) h4 h5 (by simpa using h6) h7 h8

/-- Phase A's value install is the pure install half. -/
theorem installValueGuardsC_run {env : Env}
    {cvA : ConstantVal} {value jv : Expr} {s₀ s' : CState}
    (hs : CSOK μ env s₀)
    (h : installValueGuardsC (mkFEnv env) cvA value s₀ = .ok (jv, s')) :
    CSOK μ env s' ∧ jv = value ∧ Expr.WScoped 0 value ∧
    installValueGuards (m := CheckM) env cvA value = .ok value := by
  unfold installValueGuardsC at h
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => rw [ite_eq_right h1] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_left h1] at h
  rw [hasFvar_spec' rfl] at h
  by_cases h2 : Expr.hasFvar value = true
  · rw [ite_eq_left h2] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_right h2] at h
  try dsimp only at h
  rw [Expr.allLevelParamsDefinedC_spec] at h
  by_cases h3 : Expr.allLevelParamsDefined cvA.levelParams value = true
  case neg => rw [ite_eq_right h3] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_left h3] at h
  rw [constsResolveFC_spec, constsResolveF_eq] at h
  by_cases h4 : Expr.constsResolve env value = true
  case neg => rw [ite_eq_right h4] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_left h4] at h
  obtain ⟨rfl, rfl⟩ := pureC_ok h
  exact ⟨hs, rfl, Expr.WScoped.of_not_hasFvar (by simpa using h2),
    installValueGuards_of_facts h1 (by simpa using h2) h3 h4⟩

/-! ## The two-phase driver: phase B's check at the prefix view -/

/-- Phase B's check at the prefix view simulates the pure check half at
the environment the view names: the view and `mkFEnv env` have the same
`find?`, so by `coreKnotI_congr` the check runs the core the
simulation is stated about.  A theorem's value arrives unchecked and
its guards run here (`installValueGuardsC` at the view, `installValueGuardsC_congr`), so
the well-scopedness premise on the value is asked only of the other two
kinds. -/
theorem checkPending_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {feFinal : FEnv} {pc : PendingCheck}
    (hfind : ∀ n, (feFinal.restrictTo pc.vis).find? n = env.find? n)
    (hwty : Expr.WScoped 0 pc.vg.cvA.type)
    (hwv : pc.vg.kind ≠ .thm → Expr.WScoped 0 pc.vg.jv)
    {s₀ s' : CState} (hres : CSOKF s₀)
    (h : checkPending μ feFinal pc s₀ = .ok ((), s')) :
    CSOKF s' ∧ ∃ F, checkValueGroup (fueledOps μ F) env pc.vg = .ok () := by
  have hfe : (feFinal.restrictTo pc.vis).find? = (mkFEnv env).find? :=
    funext fun n => (hfind n).trans (mkFEnv_find? env n).symm
  unfold checkPending at h
  simp only [coreKnotI_congr hfe, opSIxC_congr hfe, installValueGuardsC_congr hfe] at h
  obtain ⟨u₀, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hcs : CSOK μ env s₀.flushed := flushC_csok hres
  obtain ⟨jsty, s₂, hst, h⟩ := bindC_ok h
  obtain ⟨hs₂, wsty, ⟨rfl, hwsty⟩, F₁, hF₁⟩ :=
    (ssimC hμ env henv checkFuel).infer hcs rfl hwty jsty s₂ hst
  obtain ⟨u, s₃, hsort, h⟩ := bindC_ok h
  obtain ⟨hs₃, u', rfl, F₂, hF₂⟩ := opSIxC_sim hμ henv hs₂ rfl hwsty u s₃ hsort
  -- the value's typing, after the theorem test (and a theorem's value
  -- install)
  have tail : ∀ {s₄ : CState} (jv : Expr), CSOK μ env s₄ → Expr.WScoped 0 jv →
      ((coreKnotI μ (mkFEnv env) checkFuel).infer 0 jv >>= fun jvt =>
        (coreKnotI μ (mkFEnv env) checkFuel).defeq 0 jvt pc.vg.cvA.type >>= fun b =>
          if b = true then pure () else
            throw (.invalid s!"type mismatch in {pc.vg.kind.word} {pc.vg.cvA.name}")) s₄
        = .ok ((), s') →
      CSOKF s' ∧ ∃ F jvt, inferTypeCore μ env F 0 jv = .ok jvt ∧
        isDefEqCore μ env F 0 jvt pc.vg.cvA.type = .ok true := by
    intro s₄ jv hs₄ hwjv h
    obtain ⟨jvt, s₅, hvt, h⟩ := bindC_ok h
    obtain ⟨hs₅, wvt, ⟨rfl, hwvt⟩, F₃, hF₃⟩ :=
      (ssimC hμ env henv checkFuel).infer hs₄ rfl hwjv jvt s₅ hvt
    obtain ⟨b, s₆, hde, h⟩ := bindC_ok h
    obtain ⟨hs₆, b', rfl, F₄, hF₄⟩ :=
      (ssimC hμ env henv checkFuel).defeq hs₅ rfl rfl hwvt hwty b s₆ hde
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact nomatch h
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨-, rfl⟩ := pureC_ok h
      exact ⟨hs₆.residue, max F₃ F₄, jvt, inferTypeCore_mono (Nat.le_max_left _ _) hF₃,
        isDefEqCore_mono (Nat.le_max_right _ _) hF₄⟩
  by_cases hk : pc.vg.kind = .thm
  · rw [ite_eq_left hk] at h
    obtain ⟨b, s₄, hlift, h⟩ := bindC_ok h
    obtain ⟨hs₄, b', rfl, F₀, hF₀⟩ := SimC.liftFueled _ _ hs₃ b s₄ hlift
    rw [liftFueled_atF] at hF₀
    cases heqv : Level.isEquiv u .zero with
    | none => rw [heqv] at hF₀; exact nomatch hF₀
    | some b₀ =>
    rw [heqv] at hF₀
    simp only [liftFueled, pure, Except.pure, Except.ok.injEq] at hF₀
    subst hF₀
    cases b₀ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h throwC_bind_ok
    | true =>
    simp only [↓reduceIte] at h
    obtain ⟨jv, s₅, hval, h⟩ := bindC_ok h
    obtain ⟨hs₅, rfl, hwjv, hV⟩ := installValueGuardsC_run hs₄ hval
    obtain ⟨hres', F₅, jvt, hvt, hde⟩ := tail _ hs₅ hwjv h
    refine ⟨hres', max (max F₁ F₂) F₅, ?_⟩
    exact checkValueGroup_of_facts (jv := pc.vg.jv)
      (inferTypeCore_mono (by omega) hF₁)
      (ensureSortCore_mono (by omega) hF₂)
      (fun _ => heqv) (fun _ => hV)
      (fun hk' => absurd hk hk')
      (inferTypeCore_mono (by omega) hvt)
      (isDefEqCore_mono (by omega) hde)
  · rw [ite_eq_right hk] at h
    obtain ⟨hres', F₅, jvt, hvt, hde⟩ := tail _ hs₃ (hwv hk) h
    refine ⟨hres', max (max F₁ F₂) F₅, ?_⟩
    exact checkValueGroup_of_facts (jv := pc.vg.jv)
      (inferTypeCore_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hF₁)
      (ensureSortCore_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hF₂)
      (fun hk' => absurd hk' hk) (fun hk' => absurd hk' hk) (fun _ => rfl)
      (inferTypeCore_mono (Nat.le_max_right _ _) hvt)
      (isDefEqCore_mono (Nat.le_max_right _ _) hde)

/-- Phase A's value install, run: the two install halves, the header
and the value as declared and well scoped, the residue kept. -/
theorem installGuardsC_run {env : Env}
    {cv cvA : ConstantVal} {value jv : Expr} {s₀ s' : CState}
    (hres : CSOKF s₀)
    (h : installGuardsC (mkFEnv env) cv value s₀ = .ok ((cvA, jv), s')) :
    CSOKF s' ∧ cvA = cv ∧ jv = value ∧
    Expr.WScoped 0 cv.type ∧ Expr.WScoped 0 value ∧
    installHeader (m := CheckM) env cv = .ok cv ∧
    installValueGuards (m := CheckM) env cv value = .ok value := by
  unfold installGuardsC at h
  obtain ⟨u₀, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  obtain ⟨cvA', s₂, hcv, h₂⟩ := bindC_ok h
  obtain ⟨hs₂, rfl, hwty, hI⟩ :=
    installHeaderC_run (μ := .verified) (env := env) (flushC_csok hres) hcv
  obtain ⟨jv', s₃, hv, h₃⟩ := bindC_ok h₂
  obtain ⟨hs₃, rfl, hwv, hV⟩ := installValueGuardsC_run (μ := .verified) hs₂ hv
  obtain ⟨hv', rfl⟩ := pureC_ok h₃
  simp only [Prod.mk.injEq] at hv'
  obtain ⟨rfl, rfl⟩ := hv'
  exact ⟨hs₃.residue, rfl, rfl, hwty, hwv, hI, hV⟩

/-- The lookup at the prefix view of a canonical, name-unique index whose
environment extends `env` by exactly the constants above `env`'s
length is `env`'s lookup. -/
theorem restrictTo_find?_of_extends {feFinal : FEnv} {env : Env}
    (hcanon : feFinal = mkFEnv feFinal.env) (hnd : NodupNames feFinal.env)
    {new : List ConstantInfo} (hext : feFinal.env.consts = new ++ env.consts) (n : Name) :
    (feFinal.restrictTo env.consts.length).find? n = env.find? n := by
  have h1 : (feFinal.restrictTo env.consts.length).find? n
      = ((mkFEnv feFinal.env).restrictTo env.consts.length).find? n := by
    rw [← hcanon]
  rw [h1, mkFEnv_find?_visibleBelow feFinal.env env.consts.length n hnd,
    Env.prefixTo_of_extends hext]

end ConLeche.Cached
