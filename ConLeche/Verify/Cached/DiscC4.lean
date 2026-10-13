module

public import ConLeche.Verify.Cached.BinderLoopC
import ConLeche.Verify.BetaSpine

public section

/-!
# Cached body walks, part 4: head normalization and the whnf loop

Simulation walks (task #163) for the cached `whnfAppI`/`betaPeelI`,
`whnfCoreStepI`/`whnfCoreLoopI`/`whnfCoreBodyI`,
`whnfStepI`/`whnfLoopI`/`whnfBodyI`, `inferSpineI` and `inferBodyI`
(`ConLeche/Cached/CoreC.lean`) against the pure fueled comparands, with
value relations `RelC`/`RelCL` and node inversion by `cases` on the
`Expr` constructor.

In `inferBodyI` the binder-telescope peel fuel is the constant
`peelFuelM`, opaque to the binder-loop tails, which quantify over the
fuel.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche.Expr

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

/-- The spine length the arity pre-check computes is the length of the
argument list the ι step builds. -/
private theorem iotaNumArgs_getAppArgsAcc (e : Expr) :
    ∀ acc : List Expr,
      iotaNumArgs e acc.length = (Expr.getAppArgsAccC e acc).length := by
  induction e with
  | app g a ihg _ =>
    intro acc
    rw [iotaNumArgs, Expr.getAppArgsAccC, ← ihg (a :: acc)]
    rfl
  | _ => intro acc; rfl

private theorem iotaNumArgs_zero (e : Expr) :
    iotaNumArgs e 0 = (Expr.getAppArgsC e).length :=
  iotaNumArgs_getAppArgsAcc e []

/-- Where the arity pre-check fails, the ι step has nothing to do: its
own guard returns `none` on exactly the same three grounds (the head is
not a constant, it is not a stored recursor, or the spine has the wrong
number of arguments or of levels). -/
private theorem iotaRecI_of_arityOk_false {mi : CheckMode} {r : CoreFnsI}
    {fe : FEnv} {d : Nat} {e : Expr} (h : iotaArityOk fe e = false) :
    iotaRecI mi r fe d e = pure none := by
  unfold iotaArityOk at h
  unfold iotaRecI
  cases hg : Expr.getAppFn e with
  | const c us =>
    rw [hg] at h
    dsimp only at h
    simp only [pure_bind]
    cases hf : fe.find? c with
    | none => rfl
    | some ci =>
      rw [hf] at h
      cases ci with
      | recInfo cv mI rP rules =>
        dsimp only at h ⊢
        rw [ite_eq_right]
        rintro ⟨hlen, hlvl, -⟩
        rw [iotaNumArgs_zero, hlen, hlvl] at h
        simp at h
      | _ => rfl
  | _ => rfl

/-- The pre-check in the spine loop changes no verdict. -/
private theorem iotaArityOk_guard {mi : CheckMode} {r : CoreFnsI}
    {fe : FEnv} {d : Nat} {e : Expr} :
    (if iotaArityOk fe e then iotaRecI mi r fe d e else pure none)
      = iotaRecI mi r fe d e := by
  by_cases h : iotaArityOk fe e = true
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, iotaRecI_of_arityOk_false (Bool.not_eq_true _ |>.mp h)]

/-- The projection rule simulates its specification. -/
theorem reduceProjCoreC_sim (ih : SSimC mode env f)
    {d : Nat} {sn : Name} {ip : Nat} {i : Expr} {ex : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelOC d)
      (reduceProjCoreI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d sn ip i)
      (reduceProjCore mode (fueledFns mode env) env d sn ip ex) := by
  unfold reduceProjCoreI reduceProjCore
  refine SimC.bind (projLitToCtorC_sim ih hs hden hw)
    (fun s₁ e' e'x hs₁ hP => ?_)
  obtain ⟨rfl, hwe'⟩ := hP
  refine SimC.bind_left (pureEq_eff hs₁ sn)
    (fun s₁' snw hs₁ hsnw => ?_)
  subst snw
  rw [mkFEnv_findProj?]
  cases hfp : env.findProj? sn ip with
  | none => exact SimC.pure hs₁ trivial
  | some entry =>
    dsimp only
    generalize hg : Expr.getAppFn e' = g
    cases g with
    | const c us =>
      dsimp only
      refine SimC.pureB ?_
      have hargs : RelCL (Expr.getAppArgsC e') ((Expr.getAppArgs e')) :=
        Expr.getAppArgsC_spec e'
      refine SimC.bind_left (pureEq_eff hs₁ (c == entry.ctor))
        (fun s₁b bq hs₁ hbq => ?_)
      subst bq
      rw [hargs.length]
      simp only [beq_iff_eq]
      have hwarg : Expr.WScoped d
          ((Expr.getAppArgs e').getD (entry.numParams + ip) (.bvar 0)) :=
        wscoped_getD hwe'.getAppArgs _
      split
      · rename_i hcond
        obtain ⟨rfl, -, -, -⟩ := hcond
        refine SimC.bind_left
          (pureBvar_eff hs₁ 0)
          (fun s₂ bvar0 hs₂ hQ0 => ?_)
        rw [projCertAtF_mkFEnv,
          show Expr.getAppArgsC e' = Expr.getAppArgs e' from hargs]
        split
        · exact SimC.pure hs₂
            (show RelEC d _ _ from
              ⟨RelCL.getD hQ0 (entry.numParams + ip) (show RelCL _ _ from rfl), hwarg⟩)
        · exact SimC.pure hs₂ trivial
      · exact SimC.pure hs₁ trivial
    | _ => exact SimC.pure hs₁ trivial

/-- The result relation of a loop step (task #342 R2): the same
outcome, with related and scoped terms. -/
@[expose] def RelWC (d : Nat) : WhnfStep → WhnfStep → Prop
  | .done a, .done b => RelEC d a b
  | .cont a, .cont b => RelEC d a b
  | _, _ => False

private theorem whnfAppI_ne_lam {r : CoreFnsI} {fe : FEnv} {d : Nat} {v : Expr}
    (hv : ∀ ty body, v ≠ .lam ty body) (a : Expr) (rest : List Expr) :
    whnfAppI mode r fe d v (a :: rest) =
      (pure (Expr.app v a) >>= fun fa =>
        (if iotaArityOk fe fa then iotaRecI mode r fe d fa else pure none) >>= fun o =>
        match o with
        | some e'' => mkAppNM e'' rest >>= fun e' => pure (WhnfStep.cont e')
        | none => whnfAppI mode r fe d fa rest) := by
  cases v with
  | lam ty body => exact absurd rfl (hv ty body)
  | _ => rw [whnfAppI.eq_def] <;> rfl

private theorem betaPeelI_ne_lam {r : CoreFnsI} {fe : FEnv} {d : Nat} {t : Expr}
    (ht : ∀ ty body, t ≠ .lam ty body) (acc : List Expr) (a : Expr) (rest : List Expr) :
    betaPeelI r fe d t acc (a :: rest) =
      (instListM t acc >>= fun e' =>
        mkAppNM e' (a :: rest) >>= fun e'' => pure (WhnfStep.cont e'')) := by
  cases t with
  | lam ty body => exact absurd rfl (ht ty body)
  | _ => rw [betaPeelI.eq_def] <;> rfl

mutual

/-- The bulk-beta argument loop simulates its pure mirror. -/
theorem whnfAppC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ {args : List Expr} {xs : List Expr} {v : Expr} {vx : Expr}
      {s₀ : CState}, CSOK mode env s₀ →
      RelC v vx → Expr.WScoped d vx →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelWC d)
        (whnfAppI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d v args)
        (whnfAppW mode (fueledFns mode env) env d vx xs)
  | [], xs, v, vx, s₀, hs, hv, hwv, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [whnfAppI.eq_def]
    dsimp only
    rw [whnfAppW_nil]
    exact SimC.pure (P := RelWC d) hs (show RelEC d v vx from ⟨hv, hwv⟩)
  | a :: rest, xs, v, vx, s₀, hs, hv, hwv, hargs, hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    obtain rfl := hv
    have hvr : RelC v v := rfl
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    by_cases hlam : ∃ ty body, v = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [whnfAppI.eq_def]
      dsimp only
      have hwtb : Expr.WScoped d ty ∧ Expr.WScoped d body := by
        have hw' : Expr.WScoped d
          (.lam ty body) := hwv
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
        rw [show (Expr.instantiateList body [xa])
            = (Expr.instantiate1 body xa) by
          rw [Expr.instantiateList_cons, Expr.instantiateList_nil]]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
      rw [whnfAppW_lam]
      exact betaPeelC_sim hμ ih henv hs rfl
        (RelCL.cons hax RelCL.nil) hwsub hrest hwrest
    · have hnl : ∀ ty body, v ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [whnfAppI_ne_lam hnl, whnfAppW_ne_lam _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hs hvr hwv hax hwxa hrest hwrest
  termination_by args _ => (args.length, 0)

/-- The iota arm of the loop simulates its mirror. -/
theorem whnfAppIotaC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat}
    {v a : Expr} {vx xa : Expr} {rest : List Expr} {xs : List Expr}
    {s₀ : CState} (hs : CSOK mode env s₀)
    (hv : RelC v vx) (hwv : Expr.WScoped d vx)
    (hax : RelC a xa) (hwxa : Expr.WScoped d xa)
    (hrest : RelCL rest xs) (hwrest : ∀ x ∈ xs, Expr.WScoped d x) :
    SimC mode env s₀ (RelWC d)
      (pure (Expr.app v a) >>= fun fa =>
        (if iotaArityOk (mkFEnv env) fa then
            iotaRecI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d fa
          else pure none) >>= fun o =>
        match o with
        | some e'' => mkAppNM e'' rest >>= fun e' => pure (WhnfStep.cont e')
        | none =>
          whnfAppI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d fa rest)
      (do
        match ← iotaRec mode (fueledFns mode env) env d (.app vx xa) with
        | some e'' => pure (.cont (Expr.mkAppN e'' xs))
        | none => whnfAppW mode (fueledFns mode env) env d (.app vx xa) xs) := by
    simp only [iotaArityOk_guard]
    have hwapp : Expr.WScoped d (.app vx xa) := by
      simp only [Expr.WScoped]
      exact ⟨hwv, hwxa⟩
    refine SimC.bind_left
      (pureC_eff hs (x := Expr.app v a))
      (fun s₁ fa hs₁ hQfa => ?_)
    have hQfa' : RelC fa (Expr.app vx xa) := by
      show _ = _
      have h := hQfa
      rw [hv, hax] at h
      exact h
    refine SimC.bind (iotaRecC_sim hμ ih henv hμ hs₁ hQfa' hwapp)
      (fun s₂ o ox hs₂ hPo => ?_)
    cases o with
    | some e'' =>
      cases ox with
      | none => exact absurd hPo (by simp [RelOC])
      | some e''x =>
        obtain ⟨hred, hwred⟩ := hPo
        dsimp only
        refine SimC.bind_left (mkAppNM_eff hs₂ hred hrest)
          (fun s₃ e' hs₃ hQ => ?_)
        exact SimC.pure (P := RelWC d) hs₃
          (show RelEC d e' (Expr.mkAppN e''x xs) from
            ⟨hQ, Expr.WScoped.mkAppN hwred hwrest⟩)
    | none =>
      cases ox with
      | some e''x => exact absurd hPo (by simp [RelOC])
      | none =>
        exact whnfAppC_sim hμ ih henv hs₂ hQfa' hwapp hrest hwrest
  termination_by (rest.length, 1)

/-- The peel loop simulates its pure mirror. -/
theorem betaPeelC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ {args : List Expr} {xs : List Expr} {t : Expr} {tx : Expr}
      {acc : List Expr} {ws : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC t tx → RelCL acc ws →
      Expr.WScoped d (tx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelWC d)
        (betaPeelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d t acc args)
        (betaPeelW mode (fueledFns mode env) env d tx ws xs)
  | [], xs, t, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [betaPeelI.eq_def]
    dsimp only
    rw [betaPeelW_nil]
    refine SimC.bind_left (instListM_eff (d := 0) hs ht hacc)
      (fun s₁ e' hs₁ hQ => ?_)
    exact SimC.pure (P := RelWC d) hs₁
      (show RelEC d e' (tx.instantiateList ws) from ⟨hQ, hwty⟩)
  | a :: rest, xs, t, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs,
      hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    obtain rfl := ht
    have htr : RelC t t := rfl
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [betaPeelI.eq_def]
      dsimp only
      rw [betaPeelW_lam]
      have hcomp : Expr.WScoped d ((Expr.instantiateList ty ws))
          ∧ Expr.WScoped d ((Expr.instantiateList body ws 1)) := by
        have hw' : Expr.WScoped d
            ((Expr.lam ty body).instantiateList ws) :=
          hwty
        rw [instList_lam] at hw'
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((Expr.instantiateList body (xa :: ws))) := by
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hcomp.2
      exact betaPeelC_sim hμ ih henv hs rfl
        (RelCL.cons hax hacc) hwsub hrest hwrest
    · have hnl : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [betaPeelI_ne_lam hnl, betaPeelW_ne_lam _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind_left (mkAppNM_eff hs₁ hQ (RelCL.cons hax hrest))
        (fun s₂ e'' hs₂ hQ₂ => ?_)
      exact SimC.pure (P := RelWC d) hs₂
        (show RelEC d e'' (Expr.mkAppN (t.instantiateList ws) (xa :: xs)) from
          ⟨hQ₂, Expr.WScoped.mkAppN hwty hwargs⟩)
  termination_by args _ => (args.length, 1)

end

private theorem whnfCoreStepW_unfold (env : Env) (cheap : Bool) (d : Nat) (e : Expr) :
    whnfCoreStepW mode (fueledFns mode env) env cheap d e =
    (match e with
    | .sort u => pure (.done (.sort u))
    | .fvar idx ty => pure (.done (.fvar idx ty))
    | .forallE ty body => pure (.done (.forallE ty body))
    | .lam ty body => pure (.done (.lam ty body))
    | .const n us => pure (.done (.const n us))
    | .lit l => pure (.done (.lit l))
    | .app g' a =>
      (fueledFns mode env).whnfCore cheap d (Expr.app g' a).getAppFn >>= fun v =>
        whnfAppW mode (fueledFns mode env) env d v (Expr.app g' a).getAppArgs
    | .proj sn i pe =>
      (if cheap then (fueledFns mode env).whnfCore true d pe
        else (fueledFns mode env).whnf d pe) >>= fun c =>
      reduceProjCore mode (fueledFns mode env) env d sn i c >>= fun o =>
      match o with
      | some m' => pure (.cont m')
      | none => pure (.done (.proj sn i pe))
    | .letE _ v b => pure (.cont (b.instantiate1 v))
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")) := by
  cases e <;> try rfl
  case proj sn i pe => cases cheap <;> rfl

theorem whnfCoreStepC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {c : Bool} {d : Nat}
    {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelWC d)
      (whnfCoreStepI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) c d i)
      (whnfCoreStepW mode (fueledFns mode env) env c d ex) := by
  unfold whnfCoreStepI
  rw [whnfCoreStepW_unfold]
  obtain rfl := hden
  have hden : RelC i i := rfl
  have hdone : RelWC d (.done i) (.done i) := ⟨hden, hw⟩
  cases i with
  | sort u => exact SimC.pure hs hdone
  | fvar idx t => exact SimC.pure hs hdone
  | forallE t b => exact SimC.pure hs hdone
  | lam t b => exact SimC.pure hs hdone
  | const nm us => exact SimC.pure hs hdone
  | lit l => exact SimC.pure hs hdone
  | bvar k => exact SimC.throw
  | letE t v b =>
    -- ζ: both sides substitute the value and continue the loop
    dsimp only
    have hw' : Expr.WScoped d t ∧ Expr.WScoped d v ∧ Expr.WScoped d b := by
      simpa only [Expr.WScoped] using hw
    refine SimC.bind_left (inst1M_eff hs (d := 0) rfl rfl)
      (fun s₁ e' hs₁ hQ => ?_)
    exact SimC.pure (P := RelWC d) hs₁
      (show RelEC d e' (b.instantiate1 v) from
        ⟨hQ, Expr.WScoped.instantiate1_gen hw'.2.1 0 hw'.2.2⟩)
  | app g' a =>
    dsimp only
    -- Bulk beta (task #50): the twin normalizes the spine head once and
    -- runs the argument loop against its mirror.
    refine SimC.pureB ?_
    refine SimC.pureB ?_
    have hhead : RelC (Expr.getAppFn (Expr.app g' a))
        ((Expr.app g' a).getAppFn) :=
      rfl
    have hargs : RelCL (Expr.getAppArgsC (Expr.app g' a))
        ((Expr.app g' a).getAppArgs) :=
      Expr.getAppArgsC_spec (Expr.app g' a)
    refine SimC.bind (ih.whnfCore hs hhead hw.getAppFn)
      (fun s₁ v vh hs₁ hP => ?_)
    exact whnfAppC_sim hμ ih henv hs₁ hP.1 hP.2 hargs hw.getAppArgs
  | proj sn ip pe =>
    dsimp only
    have hwpe : Expr.WScoped d pe := by
      have hw' : Expr.WScoped d (Expr.proj sn ip pe) := hw
      simpa only [Expr.WScoped] using hw'
    have hwproj : Expr.WScoped d (Expr.proj sn ip pe) := hw
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine SimC.bind (ih.whnf hs rfl hwpe)
        (fun s₀' e₀ e₀x hs₀' hP₀ => ?_)
      obtain ⟨he₀d, hwe₀⟩ := hP₀
      refine SimC.bind (reduceProjCoreC_sim ih hs₀' he₀d hwe₀)
        (fun s₁ o ox hs₁ hPo => ?_)
      cases o with
      | some m =>
        cases ox with
        | none => exact absurd hPo (by simp [RelOC])
        | some mx =>
          obtain ⟨hmd, hwm⟩ := hPo
          exact SimC.pure (P := RelWC d) hs₁ (show RelEC d m mx from ⟨hmd, hwm⟩)
      | none =>
        cases ox with
        | some mx => exact absurd hPo (by simp [RelOC])
        | none =>
          exact SimC.pure (P := RelWC d) hs₁
            (show RelEC d (Expr.proj sn ip pe) (Expr.proj sn ip pe) from ⟨rfl, hwproj⟩)
    | true =>
      simp only [↓reduceIte]
      refine SimC.bind (ih.whnfCore hs rfl hwpe)
        (fun s₀' e₀ e₀x hs₀' hP₀ => ?_)
      obtain ⟨he₀d, hwe₀⟩ := hP₀
      refine SimC.bind (reduceProjCoreC_sim ih hs₀' he₀d hwe₀)
        (fun s₁ o ox hs₁ hPo => ?_)
      cases o with
      | some m =>
        cases ox with
        | none => exact absurd hPo (by simp [RelOC])
        | some mx =>
          obtain ⟨hmd, hwm⟩ := hPo
          exact SimC.pure (P := RelWC d) hs₁ (show RelEC d m mx from ⟨hmd, hwm⟩)
      | none =>
        cases ox with
        | some mx => exact absurd hPo (by simp [RelOC])
        | none =>
          exact SimC.pure (P := RelWC d) hs₁
            (show RelEC d (Expr.proj sn ip pe) (Expr.proj sn ip pe) from ⟨rfl, hwproj⟩)

/-- The head-normalization *loop* simulates its mirror, by induction on
the shared step budget (task #106); a step's outcome is the same on
both sides, and a continuation re-enters the loop (task #342 R2). -/
theorem whnfCoreLoopC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {c : Bool} {d : Nat} :
    ∀ (n : Nat) {i : Expr} {ex : Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s₀ (RelEC d)
        (whnfCoreLoopI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) c d n i)
        (whnfCoreLoopM mode (fueledFns mode env) env c d n ex)
  | 0, _, _, _, _, _, _ => SimC.throw
  | n + 1, _, _, _, hs, hden, hw => by
    simp only [whnfCoreLoopI, whnfCoreLoopM]
    refine SimC.bind (whnfCoreStepC_sim hμ ih henv hs hden hw)
      (fun s₁ st stx hs₁ hP => ?_)
    cases st with
    | done v =>
      cases stx with
      | done vx => exact SimC.pure hs₁ hP
      | cont ex' => exact absurd hP (by simp [RelWC])
    | cont e' =>
      cases stx with
      | done vx => exact absurd hP (by simp [RelWC])
      | cont ex' => exact whnfCoreLoopC_sim hμ ih henv n hs₁ hP.1 hP.2

/-- The cached head-normalization body simulates the chained
specification body: the loop run is reproduced by `whnfCoreBody` at
some knot fuel (`whnfCoreLoop_sound_body`). -/
theorem whnfCoreBodyC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {c : Bool} {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfCoreBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) c d i)
      (whnfCoreBody mode (fueledFns mode env) env c d ex) := by
  unfold whnfCoreBodyI
  exact SimC.wr (whnfCoreLoopC_sim hμ ih henv whnfCoreLoopFuel hs hden hw)
    (fun v F hF => whnfCoreLoop_sound_body (c := c) d ex v whnfCoreLoopFuel F hF)

end Walks

section Walks2

variable {env : Env} {f : Nat}

private theorem whnfStep_unfold (env : Env) (d : Nat)
    (kM : Expr → FueledM Expr) (e : Expr) :
    whnfStep (fueledFns mode env) env d kM e =
    ((fueledFns mode env).whnfCore false d e >>= fun e₁ =>
      reduceNat (fueledFns mode env) env d e₁ >>= fun o =>
      match o with
      | some e₂ => kM e₂
      | none =>
        match unfoldDefinition env e₁ with
        | some e₂ => kM e₂
        | none => pure e₁) := rfl

/-- One iteration of the reduction loop simulates its specification
(task #106; the continuation is abstract, as in the body). -/
theorem whnfStepC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {kI : Expr → CheckCM Expr} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {j : Expr} {ey : Expr}, CSOK mode env s →
      RelC j ey → Expr.WScoped d ey →
      SimC mode env s (RelEC d) (kI j) (kM ey))
    {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfStepI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI i)
      (whnfStep (fueledFns mode env) env d kM ex) := by
  unfold whnfStepI
  rw [whnfStep_unfold]
  refine SimC.bind (ih.whnfCore hs hden hw)
    (fun s₁ e₁ e₁x hs₁ hP => ?_)
  obtain ⟨he₁d, hwe₁⟩ := hP
  refine SimC.bind (reduceNatC_sim ih hs₁ he₁d hwe₁)
    (fun s₂ o ox hs₂ hPo => ?_)
  cases o with
  | some e₂ =>
    cases ox with
    | none => exact absurd hPo (by simp [RelOC])
    | some e₂x =>
      obtain ⟨he₂d, hwe₂⟩ := hPo
      exact hk hs₂ he₂d hwe₂
  | none =>
    cases ox with
    | some e₂x => exact absurd hPo (by simp [RelOC])
    | none =>
      refine SimC.bind_left (unfoldDefinitionC_eff hs₂ he₁d)
        (fun s₃ o₂ hs₃ hQ => ?_)
      cases hu : unfoldDefinition env e₁x with
      | some e₂x =>
        rw [hu] at hQ
        cases o₂ with
        | none => exact absurd hQ (by simp [OptEr])
        | some e₂ =>
          exact hk hs₃ hQ (unfoldDefinition_WScoped henv hu hwe₁)
      | none =>
        rw [hu] at hQ
        cases o₂ with
        | some e₂ => exact absurd hQ (by simp [OptEr])
        | none => exact SimC.pure hs₃ ⟨he₁d, hwe₁⟩

/-- The reduction loop simulates its specification, by induction on the
shared step budget (task #106). -/
theorem whnfLoopC_sim (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ (n : Nat) {i : Expr} {ex : Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s₀ (RelEC d)
        (whnfLoopI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n i)
        (whnfLoop (fueledFns mode env) env d n ex)
  | 0, _, _, _, _, _, _ => SimC.throw
  | n + 1, _, _, _, hs, hden, hw => by
    simp only [whnfLoopI, whnfLoop]
    exact whnfStepC_sim ih henv
      (fun h1 h2 h3 => whnfLoopC_sim ih henv n h1 h2 h3) hs hden hw

theorem whnfBodyC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (whnfBody (fueledFns mode env) env d ex) :=
  whnfLoopC_sim ih henv whnfLoopFuel hs hden hw

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-- The application-inference spine loop simulates its pure mirror. -/
theorem inferSpineC_sim (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ {args : List Expr} {xs : List Expr} {ty : Expr} {tx : Expr}
      {acc : Array Expr} {ws : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC ty tx →
      RelCL acc.toList.reverse ws →
      Expr.WScoped d (tx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelEC d)
        (inferSpineI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty acc args)
        (inferSpine (fueledFns mode env) d tx ws xs)
  | [], xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [inferSpineI.eq_def]
    dsimp only
    rw [inferSpine_nil]
    exact SimC.of_eff (instListRevM_eff (d := 0) hs ht hacc) _
      (fun r hQ => ⟨hQ, hwty⟩)
  | a :: rest, xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs,
      hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    rw [inferSpineI.eq_def]
    dsimp only
    obtain rfl := ht
    have htr : RelC ty ty := rfl
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases ty with
    | forallE dom body =>
      dsimp only
      rw [show (Expr.forallE dom body)
        = Expr.forallE dom body from rfl, inferSpine_pi]
      unfold inferSpinePi
      have hcomp : Expr.WScoped d ((Expr.instantiateList dom ws))
          ∧ Expr.WScoped d ((Expr.instantiateList body ws 1)) := by
        have hw' : Expr.WScoped d
          ((Expr.forallE dom body).instantiateList ws) :=
          hwty
        rw [instList_forallE] at hw'
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((Expr.instantiateList body (xa :: ws))) := by
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hcomp.2
      dsimp only
      refine SimC.bind_left (instListRevM_eff (d := 0) hs rfl hacc)
        (fun s₁ dom' hs₁ hQdom => ?_)
      refine SimC.bind (ih.infer hs₁ hax hwxa)
        (fun s₂ ta tax hs₂ hP => ?_)
      obtain ⟨htad, hwta⟩ := hP
      refine SimC.bind (ih.defeq hs₂ htad hQdom hwta hcomp.1)
        (fun s₃ b b' hs₃ hPb => ?_)
      obtain rfl : b = b' := hPb
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.throw_bind
      | true =>
        simp only [↓reduceIte]
        exact inferSpineC_sim ih henv hs₃ rfl
          (by rw [toListRev_push]; exact RelCL.cons hax hacc) hwsub
          hrest hwrest
    | bvar k =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.bvar k) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | sort u =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.sort u) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | const nm us =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.const nm us) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | lit l =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.lit l) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | fvar idx tt =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.fvar idx tt) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | app f₂ a₂ =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.app f₂ a₂) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | lam tt b =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.lam tt b) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | letE tt vv b =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.letE tt vv b) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | proj sn j pe =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.proj sn j pe) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw

theorem inferSpineIOC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ {args : List Expr} {xs : List Expr} {ty : Expr} {tx : Expr}
      {acc : Array Expr} {ws : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC ty tx →
      RelCL acc.toList.reverse ws →
      Expr.WScoped d (tx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelEC d)
        (inferSpineIOI
          (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)) (mkFEnv env)
          d ty acc args)
        (inferSpineIO (fueledFns mode env) d tx ws xs)
  | [], xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [inferSpineIOI.eq_def]
    dsimp only
    rw [inferSpineIO_nil]
    exact SimC.of_eff (instListRevM_eff (d := 0) hs ht hacc) _
      (fun r hQ => ⟨hQ, hwty⟩)
  | a :: rest, xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs,
      hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    rw [inferSpineIOI.eq_def]
    dsimp only
    obtain rfl := ht
    have htr : RelC ty ty := rfl
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases ty with
    | forallE dom body =>
      dsimp only
      rw [show (Expr.forallE dom body)
        = Expr.forallE dom body from rfl, inferSpineIO_pi]
      unfold inferSpineIOPi
      have hcomp : Expr.WScoped d ((Expr.instantiateList dom ws))
          ∧ Expr.WScoped d ((Expr.instantiateList body ws 1)) := by
        have hw' : Expr.WScoped d
          ((Expr.forallE dom body).instantiateList ws) :=
          hwty
        rw [instList_forallE] at hw'
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((Expr.instantiateList body (xa :: ws))) := by
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hcomp.2
      try dsimp only
      exact inferSpineIOC_sim hμ ih henv hs rfl
        (by rw [toListRev_push]; exact RelCL.cons hax hacc) hwsub
        hrest hwrest
    | bvar k =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.bvar k) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        exact inferSpineIOC_sim hμ ih henv hs₂ rfl
          (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
          hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | sort u =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.sort u) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        exact inferSpineIOC_sim hμ ih henv hs₂ rfl
          (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
          hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | const nm us =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.const nm us) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        exact inferSpineIOC_sim hμ ih henv hs₂ rfl
          (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
          hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | lit l =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.lit l) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        exact inferSpineIOC_sim hμ ih henv hs₂ rfl
          (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
          hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | fvar idx tt =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.fvar idx tt) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        exact inferSpineIOC_sim hμ ih henv hs₂ rfl
          (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
          hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | app f₂ a₂ =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.app f₂ a₂) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        exact inferSpineIOC_sim hμ ih henv hs₂ rfl
          (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
          hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | lam tt b =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.lam tt b) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        exact inferSpineIOC_sim hμ ih henv hs₂ rfl
          (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
          hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | letE tt vv b =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.letE tt vv b) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        exact inferSpineIOC_sim hμ ih henv hs₂ rfl
          (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
          hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | proj sn j pe =>
      dsimp only
      have hnl : ∀ dom' body',
          (Expr.proj sn j pe) ≠ Expr.forallE dom' body' :=
        fun _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        exact inferSpineIOC_sim hμ ih henv hs₂ rfl
          (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
          hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw

theorem inferBodyC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (inferBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (inferBody (fueledFns mode env) env d ex) := by
  unfold inferBodyI
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | sort u =>
    dsimp only
    unfold inferBody
    dsimp only
    try dsimp only
    refine SimC.bind_left (pureEq_eff hs (Level.succ u))
      (fun s₁ su hs₁ hsu => ?_)
    subst su
    exact SimC.of_eff
      (pureC_eff hs₁ (x := Expr.sort (Level.succ u))) _
      (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
  | bvar k =>
    dsimp only
    unfold inferBody
    dsimp only
    try dsimp only
    exact SimC.throw
  | letE t v b =>
    -- official `infer_let`: the annotation's sort, the value against
    -- it, then the body at the value
    dsimp only
    have hw' : Expr.WScoped d t ∧ Expr.WScoped d v ∧ Expr.WScoped d b := by
      simpa only [Expr.WScoped] using hw
    unfold inferBody
    dsimp only
    refine SimC.bind (ih.infer hs rfl hw'.1)
      (fun s₁ tty ttyx hs₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimC.bind (ensureSortC_sim ih hs₁ httyd hwtty)
      (fun s₂ _ _ hs₂ _ => ?_)
    refine SimC.bind (ih.infer hs₂ rfl hw'.2.1)
      (fun s₃ tv tvx hs₃ hP₃ => ?_)
    obtain ⟨htvd, hwtv⟩ := hP₃
    refine SimC.bind (ih.defeq hs₃ htvd rfl hwtv hw'.1)
      (fun s₄ bb bb' hs₄ hPb => ?_)
    obtain rfl : bb = bb' := hPb
    cases bb with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte, Bool.not_true]
      refine SimC.bind_left (inst1M_eff hs₄ (d := 0) rfl rfl)
        (fun s₅ ob hs₅ hQ => ?_)
      exact ih.infer hs₅ hQ (Expr.WScoped.instantiate1_gen hw'.2.1 0 hw'.2.2)
  | fvar idx t =>
    simp only [inferBodyI, inferBody]
    have h' : idx < d ∧ Expr.WScoped idx t := by
      have hw' : Expr.WScoped d (Expr.fvar idx t) := hw
      simpa only [Expr.WScoped] using hw'
    by_cases hidx : idx < d
    · rw [ite_eq_left hidx, ite_eq_left hidx]
      exact SimC.pure hs
        ⟨rfl, Expr.WScoped.mono (Nat.le_of_lt h'.1) h'.2⟩
    · rw [ite_eq_right hidx, ite_eq_right hidx]
      exact SimC.throw
  | lit l =>
    dsimp only
    unfold inferBody
    dsimp only
    refine SimC.bind_pure_right ?_
    try dsimp only
    cases l with
    | natVal k =>
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [ite_eq_left hg, ite_eq_left hg]
        refine SimC.bind_left (pureEq_eff hs natName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.const natName [])) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [ite_eq_right hg, ite_eq_right hg]
        exact SimC.throw
    | strVal str =>
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [ite_eq_left hg, ite_eq_left hg]
        refine SimC.bind_left (pureEq_eff hs stringName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.const stringName [])) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [ite_eq_right hg, ite_eq_right hg]
        exact SimC.throw
  | const nm us =>
    dsimp only
    unfold inferBody
    dsimp only
    refine SimC.bind_pure_right ?_
    try dsimp only
    refine SimC.bind_left (pureEq_eff hs nm)
      (fun s₀' nw hs hnw => ?_)
    subst nw
    rw [mkFEnv_find?]
    cases hfn : env.find? nm with
    | none => exact SimC.throw
    | some ci =>
      dsimp only
      by_cases htw : (!ci.isTowerEntry) = true
      · rw [ite_eq_left htw, ite_eq_left htw]
        by_cases hlen : us.length = ci.toConstantVal.levelParams.length
        · rw [ite_eq_left hlen, ite_eq_left hlen]
          refine SimC.of_eff (constTyAtM_eff hs hfn) _ (fun r hQ => ?_)
          refine ⟨hQ, ?_⟩
          obtain ⟨htf, -⟩ := henv _ (Env.find?_mem hfn)
          exact wscoped_instLevels_of_not_hasFvar htf _ _
        · rw [ite_eq_right hlen, ite_eq_right hlen]
          exact SimC.throw_bind
      · rw [ite_eq_right htw, ite_eq_right htw]
        exact SimC.throw_bind
  | forallE t b =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.forallE t b) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBody
    dsimp only
    try dsimp only
    refine SimC.bind (ih.infer hs rfl hwtb.1)
      (fun s₁ tty ttyx hs₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimC.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hP₂ => ?_)
    obtain ⟨rfl, hww⟩ := hP₂
    cases w with
    | sort u =>
      dsimp only
      refine SimC.bind_left
        (pureC_eff hs₂ (x := Expr.fvar d t))
        (fun s₃ fv hs₃ hQfv => ?_)
      refine SimC.bind_left (peelFuelM_eff hs₃)
        (fun s₃f fuel hs₃f _hQfuel => ?_)
      exact inferPisC_tail_sim ih hs₃f rfl rfl hQfv hwtb.1 hwtb.2
    | bvar k' => exact SimC.throw
    | const nm' us' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' => exact SimC.throw
    | forallE t' b' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw
  | lam t b =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.lam t b) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBody
    dsimp only
    try dsimp only
    refine SimC.bind (ih.infer hs rfl hwtb.1)
      (fun s₁ tty ttyx hs₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimC.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hP₂ => ?_)
    obtain ⟨rfl, hww⟩ := hP₂
    cases w with
    | sort u =>
      dsimp only
      refine SimC.bind_left
        (pureC_eff hs₂ (x := Expr.fvar d t))
        (fun s₃ fv hs₃ hQfv => ?_)
      refine SimC.bind_left (peelFuelM_eff hs₃)
        (fun s₃f fuel hs₃f _hQfuel => ?_)
      exact inferLamsC_tail_sim ih henv hs₃f rfl rfl hQfv
        hwtb.1 hwtb.2
    | bvar k' => exact SimC.throw
    | const nm' us' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' => exact SimC.throw
    | forallE t' b' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw
  | app g' a =>
    dsimp only
    -- Bulk telescope consumption (task #50): the twin infers the spine
    -- head once and walks the Π-telescope; `inferSpine_sound_body`
    -- reproduces the loop's verdict in the chained body.
    refine SimC.wr ?_
      (fun v F hF => inferSpine_sound_body d g' a v F hF)
    refine SimC.pureB ?_
    refine SimC.pureB ?_
    have hhead : RelC (Expr.getAppFn (Expr.app g' a))
        ((Expr.app g' a).getAppFn) :=
      rfl
    have hargsSpec : RelCL (Expr.getAppArgsC (Expr.app g' a))
        ((Expr.app g' a).getAppArgs) :=
      Expr.getAppArgsC_spec (Expr.app g' a)
    refine SimC.bind (ih.infer hs hhead hw.getAppFn)
      (fun s₁ tf tfx hs₁ hP => ?_)
    refine inferSpineC_sim ih henv hs₁ hP.1
      (by rw [toListRev_empty]; exact RelCL.nil) ?_
      hargsSpec hw.getAppArgs
    rw [Expr.instantiateList_nil]
    exact hP.2
  | proj sn ip pe =>
    dsimp only
    have hwpe : Expr.WScoped d pe := by
      have hw' : Expr.WScoped d (Expr.proj sn ip pe) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBody
    dsimp only
    try dsimp only
    refine SimC.bind (ih.infer hs rfl hwpe)
      (fun s₁ tpe tpex hs₁ hP => ?_)
    obtain ⟨htped, hwtpe⟩ := hP
    refine SimC.bind (ih.whnf hs₁ htped hwtpe)
      (fun s₂ te tex hs₂ hP₂ => ?_)
    obtain ⟨rfl, hwte⟩ := hP₂
    refine SimC.pureB ?_
    generalize hg : Expr.getAppFn te = g
    cases g with
    | const T us =>
      dsimp only
      refine SimC.bind_left (pureEq_eff hs₂ T)
        (fun s₂' Tw hs₂ hTw => ?_)
      subst Tw
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? T ip with
      | none => exact SimC.throw
      | some entry =>
        dsimp only
        refine SimC.pureB ?_
        have htargs : RelCL (Expr.getAppArgsC te) ((Expr.getAppArgs te)) :=
          Expr.getAppArgsC_spec te
        rw [htargs.length]
        -- the cached core's three node guards (until task #342 the
        -- annotate pass's, now inference's) throw where the spec's joint guard
        -- throws; a cached throw simulates anything
        by_cases hT : T = sn
        case neg =>
          simp only [hT, false_and, ↓reduceIte]
          exact SimC.throw_bind
        by_cases hnp : (Expr.getAppArgs te).length = entry.numParams
        case neg =>
          simp only [hT, hnp, false_and, and_false, ↓reduceIte]
          exact SimC.throw_bind
        by_cases hlp : us.length = entry.levelParams.length
        case neg =>
          simp only [hT, hnp, hlp, and_false, ↓reduceIte, pure_bind]
          exact SimC.throw
        simp only [hT, hnp, hlp, and_self, ↓reduceIte, pure_bind]
        -- task #175 S1: the body at the spine and the subject —
        -- `Expr = Expr` (the identity world), so the two results
        -- coincide once `RelCL` rewrites the spine
        rw [htargs]
        have hres : SimC mode env s₂' (RelEC d)
            (pure (entry.typeAtI us (Expr.getAppArgs te) pe))
            (pure (entry.typeAt us (Expr.getAppArgs te) pe) : FueledM Expr) :=
          SimC.pure hs₂ ⟨ProjEntry.typeAtI_eq entry us _ pe,
            projEntry_typeAt_WScoped henv hfp us
            hnp
            (fun a ha => hwte.getAppArgs a ha) hwpe⟩
        -- the Prop guard (task #175 W4c) runs no walk of its own
        split
        · split
          · exact hres
          · exact SimC.throw
        · exact hres
    | bvar k' => exact SimC.throw
    | sort u' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' => exact SimC.throw
    | forallE t' b' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw

/-- The io inference body's walk (task #172 B4), at the verified mode.
The leaf, `letE` and `proj` arms are `inferBodyC_sim`'s with the
recursion at the io slot; the two binder arms are the io lane's own
**chained** clauses; the application arm is the io spine walk
(`inferSpineIOI`, no argument check) with `inferSpineIO_sound_body`. -/
theorem inferBodyIOC_sim (hμ : mode.verifiedChecks = true)
    (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (inferBodyIOI
        (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)) (mkFEnv env) d i)
      (inferBodyIO (CoreFns.ioView (fueledFns mode env)) env d ex) := by
  unfold inferBodyIOI
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | sort u =>
    dsimp only
    unfold inferBodyI inferBodyIO
    dsimp only
    try dsimp only
    refine SimC.bind_left (pureEq_eff hs (Level.succ u))
      (fun s₁ su hs₁ hsu => ?_)
    subst su
    exact SimC.of_eff
      (pureC_eff hs₁ (x := Expr.sort (Level.succ u))) _
      (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
  | bvar k =>
    dsimp only
    unfold inferBodyI inferBodyIO
    dsimp only
    try dsimp only
    exact SimC.throw
  | letE t v b =>
    -- official `infer_let` at `infer_only`: the body at the value
    dsimp only
    have hw' : Expr.WScoped d t ∧ Expr.WScoped d v ∧ Expr.WScoped d b := by
      simpa only [Expr.WScoped] using hw
    unfold inferBodyIO
    dsimp only
    refine SimC.bind_left (inst1M_eff hs (d := 0) rfl rfl)
      (fun s₁ ob hs₁ hQ => ?_)
    exact ih.inferIO hs₁ hQ (Expr.WScoped.instantiate1_gen hw'.2.1 0 hw'.2.2)
  | fvar idx t =>
    simp only [inferBodyI, inferBodyIO]
    have h' : idx < d ∧ Expr.WScoped idx t := by
      have hw' : Expr.WScoped d (Expr.fvar idx t) := hw
      simpa only [Expr.WScoped] using hw'
    by_cases hidx : idx < d
    · rw [ite_eq_left hidx, ite_eq_left hidx]
      exact SimC.pure hs
        ⟨rfl, Expr.WScoped.mono (Nat.le_of_lt h'.1) h'.2⟩
    · rw [ite_eq_right hidx, ite_eq_right hidx]
      exact SimC.throw
  | lit l =>
    dsimp only
    unfold inferBodyI inferBodyIO
    dsimp only
    refine SimC.bind_pure_right ?_
    try dsimp only
    cases l with
    | natVal k =>
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [ite_eq_left hg, ite_eq_left hg]
        refine SimC.bind_left (pureEq_eff hs natName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.const natName [])) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [ite_eq_right hg, ite_eq_right hg]
        exact SimC.throw
    | strVal str =>
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [ite_eq_left hg, ite_eq_left hg]
        refine SimC.bind_left (pureEq_eff hs stringName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.const stringName [])) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [ite_eq_right hg, ite_eq_right hg]
        exact SimC.throw
  | const nm us =>
    dsimp only
    unfold inferBodyI inferBodyIO
    dsimp only
    refine SimC.bind_pure_right ?_
    try dsimp only
    refine SimC.bind_left (pureEq_eff hs nm)
      (fun s₀' nw hs hnw => ?_)
    subst nw
    rw [mkFEnv_find?]
    cases hfn : env.find? nm with
    | none => exact SimC.throw
    | some ci =>
      dsimp only
      by_cases htw : (!ci.isTowerEntry) = true
      · rw [ite_eq_left htw, ite_eq_left htw]
        by_cases hlen : us.length = ci.toConstantVal.levelParams.length
        · rw [ite_eq_left hlen, ite_eq_left hlen]
          refine SimC.of_eff (constTyAtM_eff hs hfn) _ (fun r hQ => ?_)
          refine ⟨hQ, ?_⟩
          obtain ⟨htf, -⟩ := henv _ (Env.find?_mem hfn)
          exact wscoped_instLevels_of_not_hasFvar htf _ _
        · rw [ite_eq_right hlen, ite_eq_right hlen]
          exact SimC.throw_bind
      · rw [ite_eq_right htw, ite_eq_right htw]
        exact SimC.throw_bind
  | forallE t b =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.forallE t b) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBodyIO
    dsimp only
    try dsimp only
    refine SimC.bind (ih.inferIO hs rfl hwtb.1)
      (fun s₁ tty ttyx hs₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimC.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hP₂ => ?_)
    obtain ⟨rfl, hww⟩ := hP₂
    cases w with
    | sort u =>
      dsimp only
      refine SimC.bind_left
        (pureC_eff hs₂ (x := Expr.fvar d t))
        (fun s₃ fv hs₃ hQfv => ?_)
      subst hQfv
      refine SimC.bind_left (inst1M_eff hs₃ rfl rfl)
        (fun s₄ ob hs₄ hQob => ?_)
      have hwopen : Expr.WScoped (d + 1)
          (b.instantiate1 (Expr.fvar d t)) :=
        Expr.WScoped.instantiate1 hwtb.1 0 hwtb.2
      refine SimC.bind (ih.inferIO hs₄ hQob hwopen)
        (fun s₅ bt btx hs₅ hP₅ => ?_)
      obtain ⟨hbtd, hwbt⟩ := hP₅
      refine SimC.bind (ensureSortC_sim ih hs₅ hbtd hwbt)
        (fun s₆ v lv hs₆ hPv => ?_)
      obtain rfl := hPv
      refine SimC.bind_left (pureEq_eff hs₆ (Level.imax u v))
        (fun s₇ iu hs₇ hQiu => ?_)
      subst hQiu
      exact SimC.of_eff
        (pureC_eff hs₇ (x := Expr.sort (Level.imax u v))) _
        (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
    | bvar k' => exact SimC.throw
    | const nm' us' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' => exact SimC.throw
    | forallE t' b' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw
  | lam t b =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.lam t b) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBodyIO
    dsimp only
    try dsimp only
    -- task #168 stage 2: no domain-sort run at the io λ clause
    refine SimC.bind_left
      (pureC_eff hs (x := Expr.fvar d t))
      (fun s₃ fv hs₃ hQfv => ?_)
    subst hQfv
    refine SimC.bind_left (inst1M_eff hs₃ rfl rfl)
      (fun s₄ ob hs₄ hQob => ?_)
    have hwopen : Expr.WScoped (d + 1)
        (b.instantiate1 (Expr.fvar d t)) :=
      Expr.WScoped.instantiate1 hwtb.1 0 hwtb.2
    refine SimC.bind (ih.inferIO hs₄ hQob hwopen)
      (fun s₅ bt btx hs₅ hP₅ => ?_)
    obtain ⟨hbtd, hwbt⟩ := hP₅
    obtain rfl := hbtd
    have hres : ∀ {s₆ : CState}, CSOK mode env s₆ →
        SimC mode env s₆ (RelEC d)
          ((do
            let bAbs ← abstract1M bt d
            pure (Expr.forallE t bAbs)) : CheckCM Expr)
          ((pure (Expr.forallE t (Expr.abstract1 bt d)) :
            FueledM Expr)) := by
      intro s₆ hs₆
      refine SimC.bind_left (abstract1M_eff hs₆ rfl)
        (fun s₇ bAbs hs₇ hQ => ?_)
      subst hQ
      exact SimC.of_eff
        (pureC_eff hs₇
          (x := Expr.forallE t (Expr.abstract1 bt d))) _
        (fun r hQ => ⟨hQ, by
          simp only [Expr.WScoped]
          exact ⟨hwtb.1, ConLeche.WScoped.abstract1 0 hwbt⟩⟩)
    exact hres hs₅
  | app g' a =>
    dsimp only
    -- the io spine walk; `inferSpineIO_sound_body`
    -- reproduces the loop's verdict in the chained io body over the
    -- io-grade view
    refine SimC.wr ?_
      (fun v F hF => inferSpineIO_sound_body d g' a v F hF)
    refine SimC.pureB ?_
    refine SimC.pureB ?_
    have hhead : RelC (Expr.getAppFn (Expr.app g' a))
        ((Expr.app g' a).getAppFn) :=
      rfl
    have hargsSpec : RelCL (Expr.getAppArgsC (Expr.app g' a))
        ((Expr.app g' a).getAppArgs) :=
      Expr.getAppArgsC_spec (Expr.app g' a)
    refine SimC.bind (ih.inferIO hs hhead hw.getAppFn)
      (fun s₁ tf tfx hs₁ hP => ?_)
    refine inferSpineIOC_sim hμ ih henv hs₁ hP.1
      (by rw [toListRev_empty]; exact RelCL.nil) ?_
      hargsSpec hw.getAppArgs
    rw [Expr.instantiateList_nil]
    exact hP.2
  | proj sn ip pe =>
    dsimp only
    have hwpe : Expr.WScoped d pe := by
      have hw' : Expr.WScoped d (Expr.proj sn ip pe) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBodyI inferBodyIO
    dsimp only
    try dsimp only
    refine SimC.bind (ih.inferIO hs rfl hwpe)
      (fun s₁ tpe tpex hs₁ hP => ?_)
    obtain ⟨htped, hwtpe⟩ := hP
    refine SimC.bind (ih.whnf hs₁ htped hwtpe)
      (fun s₂ te tex hs₂ hP₂ => ?_)
    obtain ⟨rfl, hwte⟩ := hP₂
    refine SimC.pureB ?_
    generalize hg : Expr.getAppFn te = g
    cases g with
    | const T us =>
      dsimp only
      refine SimC.bind_left (pureEq_eff hs₂ T)
        (fun s₂' Tw hs₂ hTw => ?_)
      subst Tw
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? T ip with
      | none => exact SimC.throw
      | some entry =>
        dsimp only
        refine SimC.pureB ?_
        have htargs : RelCL (Expr.getAppArgsC te) ((Expr.getAppArgs te)) :=
          Expr.getAppArgsC_spec te
        rw [htargs.length]
        -- the cached node guards, as in `inferBodyC_sim`
        by_cases hT : T = sn
        case neg =>
          simp only [hT, false_and, ↓reduceIte]
          exact SimC.throw_bind
        by_cases hnp : (Expr.getAppArgs te).length = entry.numParams
        case neg =>
          simp only [hT, hnp, false_and, and_false, ↓reduceIte]
          exact SimC.throw_bind
        by_cases hlp : us.length = entry.levelParams.length
        case neg =>
          simp only [hT, hnp, hlp, and_false, ↓reduceIte, pure_bind]
          exact SimC.throw
        simp only [hT, hnp, hlp, and_self, ↓reduceIte, pure_bind]
        rw [htargs]
        have hres : SimC mode env s₂' (RelEC d)
            (pure (entry.typeAtI us (Expr.getAppArgs te) pe))
            (pure (entry.typeAt us (Expr.getAppArgs te) pe) : FueledM Expr) :=
          SimC.pure hs₂ ⟨ProjEntry.typeAtI_eq entry us _ pe,
            projEntry_typeAt_WScoped henv hfp us
            hnp
            (fun a ha => hwte.getAppArgs a ha) hwpe⟩
        split
        · split
          · exact hres
          · exact SimC.throw
        · exact hres
    | bvar k' => exact SimC.throw
    | sort u' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' => exact SimC.throw
    | forallE t' b' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw


end Walks3

end ConLeche.Cached
