module

public import ConLeche.Verify.Cached.DiscC3
public import ConLeche.Verify.BinderLoop

public section

/-!
# Cached binder-loop walks (task #163)

Simulation walks relating the cached binder-telescope loops
(`inferLamsI`/`inferPisI`, `ConLeche/Cached/CoreC.lean`) to the pure
mirrors (`ConLeche/Verify/BinderLoop.lean`) at the fueled record, plus
the two *tail compositions* against `inferBody`'s own λ/∀ tails.  The
relations are `SimC` and `RelC`; binder metas and levels are trees, so
the stack relations' meta and level legs are equations.

**The peel fuel is not a parameter of these walks.**  Every loop
theorem quantifies over the fuel, so the constant `peelFuel` is an
instance, and no proof below reads a property of the fuel value.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr

variable {mode : CheckMode}

variable {env : Env} {f : Nat}

/-- Erasure-only result relation for the loop walks. -/
abbrev RelDC : Expr → Expr → Prop := RelC

/-- Pushing on the accumulator array conses on its reversed read
(task #97: the loops keep the opened fvars innermost-**last**; the
mirrors' lists stay innermost-first). -/
theorem toListRev_push {α} (a : Array α) (x : α) :
    (a.push x).toList.reverse = x :: a.toList.reverse := by
  simp

theorem toListRev_singleton {α} (x : α) :
    (#[x] : Array α).toList.reverse = [x] := by
  simp

theorem toListRev_empty {α} :
    (#[] : Array α).toList.reverse = ([] : List α) := by
  simp

/-! ## Stack relations -/

/-- Pointwise relation of `inferLamsI` stack entries (binder metas
are trees, so their leg is an equation). -/
def RelILE : InferLamEntry → InferLamEntryX → Prop
  | (tyo, mb), (tyox, mbx) =>
    RelC tyo tyox ∧ mb = mbx

def RelILStk : List InferLamEntry → List InferLamEntryX → Prop
  | [], [] => True
  | e :: r, ex :: rx => RelILE e ex ∧ RelILStk r rx
  | _, _ => False

/-! ## The infer-λ loop walks -/

theorem inferLamsOutC_sim {d : Nat} :
    ∀ {stk : List InferLamEntry} {stkx : List InferLamEntryX} {j : Nat}
      {cur : Expr} {curx : Expr} {s₀ : CState},
      CSOK mode env s₀ → RelILStk stk stkx → RelC cur curx →
      SimC mode env s₀ RelDC (inferLamsOutI d stk j cur)
        (inferLamsOut (m := FueledM) d stkx j curx) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx j cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact SimC.pure hs hcur
    | cons ex rx => exact absurd hstk (by simp [RelILStk])
  | cons e rest ihOut =>
    obtain ⟨tyo, mb⟩ := e
    intro stkx j cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact absurd hstk (by simp [RelILStk])
    | cons ex rx =>
      obtain ⟨tyox, mbx⟩ := ex
      obtain ⟨⟨htyo, hmb⟩, hrest⟩ := hstk
      subst hmb
      show SimC mode env s₀ RelDC
        (do
          let tyAbs ← abstractRangeM tyo d j
          let node ← pure (Expr.forallE tyAbs cur mb)
          inferLamsOutI d rest (j - 1) node)
        (inferLamsOut (m := FueledM) d rx (j - 1)
            (Expr.forallE (tyox.abstractRange d j) curx mb))
      refine SimC.bind_left (abstractRangeM_eff hs htyo)
        (fun s₃ tyAbs hs₃ hQab => ?_)
      refine SimC.bind_left
        (pureC_eff hs₃ (x := Expr.forallE tyAbs cur mb))
        (fun s₄ node hs₄ hQnode => ?_)
      have hQnode' : RelC node
          (Expr.forallE (tyox.abstractRange d j) curx mb) := by
        show _ = _
        rw [show node
            = .forallE tyAbs cur mb from hQnode,
          hQab, hcur]
      exact ihOut hs₄ hrest hQnode'

theorem inferLamsLeafC_sim (ih : SSimC mode env f) {d : Nat}
    {t : Expr} {tx : Expr} {k : Nat} {fvs : Array Expr} {ws : List Expr}
    {stk : List InferLamEntry} {stkx : List InferLamEntryX} {s₀ : CState}
    (hs : CSOK mode env s₀) (ht : RelC t tx)
    (hfvs : RelCL fvs.toList.reverse ws) (hstk : RelILStk stk stkx)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    SimC mode env s₀ RelDC
      (inferLamsLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (inferLamsLeaf (fueledFns mode env) d tx k ws stkx) := by
  unfold inferLamsLeafI inferLamsLeaf
  refine SimC.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hQob => ?_)
  refine SimC.bind (ih.infer hs₁ hQob hw)
    (fun s₂ bt btx hs₂ hPbt => ?_)
  obtain ⟨hbtd, hwbt⟩ := hPbt
  refine SimC.bind_left (abstractRangeM_eff hs₂ hbtd)
    (fun s₅ cur hs₅ hQcur => ?_)
  exact inferLamsOutC_sim hs₅ hstk hQcur

theorem inferLamsC_sim (ih : SSimC mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : Expr} {tx : Expr} {k : Nat}
      {fvs : Array Expr} {ws : List Expr}
      {stk : List InferLamEntry} {stkx : List InferLamEntryX}
      {s₀ : CState},
      CSOK mode env s₀ → RelC t tx →
      RelCL fvs.toList.reverse ws → RelILStk stk stkx →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      SimC mode env s₀ RelDC
        (inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (inferLams (fueledFns mode env) d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact inferLamsLeafC_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimC mode env s₀ RelDC
      (do
        match t with
        | .lam ty body mb => do
          let tyo ← instListRevM ty fvs
          let tty ← (coreKnotI mode (mkFEnv env) f).infer (d + k) tyo
          let wtty ← (coreKnotI mode (mkFEnv env) f).whnf (d + k) tty
          match wtty with
          | .sort _ => do
            let fv ← pure (Expr.fvar (d + k) tyo)
            inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel body (k + 1)
              (fvs.push fv) ((tyo, mb) :: stk)
          | _ => throw (.invalid "expected a sort")
        | _ => inferLamsLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      _
    have ht' := ht
    obtain rfl := ht
    cases t
    case lam ty body mb =>
      dsimp only at hw ⊢
      rw [inferLams_succ_lam]
      have hlamL : (Expr.lam ty body mb).instantiateList
          ws = Expr.lam ((Expr.instantiateList ty ws))
            ((Expr.instantiateList body ws 1)) mb := by
        simp [Expr.instantiateList]
      have hwcomp : Expr.WScoped (d + k) ((Expr.instantiateList ty ws))
          ∧ Expr.WScoped (d + k) ((Expr.instantiateList body ws 1)) := by
        rw [hlamL] at hw
        simpa only [Expr.WScoped] using hw
      refine SimC.bind_left
        (instListRevM_eff (d := 0) hs rfl hfvs)
        (fun s₁ tyo hs₁ hQtyo => ?_)
      refine SimC.bind (ih.infer hs₁ hQtyo hwcomp.1)
        (fun s₂ tty ttyx hs₂ hPtty => ?_)
      obtain ⟨httyd, hwtty⟩ := hPtty
      refine SimC.bind (ih.whnf hs₂ httyd hwtty)
        (fun s₃ wtty wx hs₃ hPw => ?_)
      obtain ⟨hwd, hww⟩ := hPw
      obtain rfl := hwd
      cases wtty
      case sort u =>
        dsimp only
        refine SimC.bind_left
          (pureC_eff hs₃ (x := Expr.fvar (d + k) tyo))
          (fun s₄ fv hs₄ hQfv => ?_)
        have hQfv' : RelC fv
            (Expr.fvar (d + k) ((Expr.instantiateList ty ws))) := by
          show _ = _
          rw [show fv = .fvar (d + k) tyo from hQfv,
            hQtyo]
        have hwopen : Expr.WScoped (d + (k + 1))
            ((Expr.instantiateList body
              (Expr.fvar (d + k) (ty.instantiateList ws) :: ws))) := by
          rw [Expr.instantiateList_cons]
          have := Expr.WScoped.instantiate1 hwcomp.1 0 hwcomp.2
          simpa [Nat.add_assoc] using this
        refine inferLamsC_sim ih fuel hs₄ rfl
          (by rw [toListRev_push]
              exact RelCL.cons hQfv' hfvs)
          ⟨⟨hQtyo, rfl⟩, hstk⟩ hwopen
      all_goals exact SimC.throw
    all_goals
      dsimp only
      rw [inferLams_succ_ne_lam _ (fun _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafC_sim ih hs ht' hfvs hstk hw

/-! ## The infer-∀ loop walks (task #100 stage 6: the ∀-rule infers
its codomain sort, so the cached side runs a telescope loop) -/

theorem inferPisOutC_sim :
    ∀ {stk : List Level} {v : Level} {s₀ : CState},
      CSOK mode env s₀ →
      SimC mode env s₀ (fun (iv : Level) (ivx : Level) => iv = ivx)
        (inferPisOutI stk v)
        (inferPisOut (m := FueledM) stk v) := by
  intro stk
  induction stk with
  | nil => intro v s₀ hs; exact SimC.pure hs rfl
  | cons u rest ih =>
    intro v s₀ hs
    show SimC mode env s₀ _
        (pure (.imax u v) >>= fun v' => inferPisOutI rest v')
        (inferPisOut (m := FueledM) rest (.imax u v))
    refine SimC.bind_left (pureEq_eff hs (Level.imax u v))
      (fun s₁ v' hs₁ hv' => ?_)
    subst hv'
    exact ih hs₁

theorem inferPisLeafC_sim (ih : SSimC mode env f) {d : Nat}
    {t : Expr} {tx : Expr} {k : Nat} {fvs : Array Expr} {ws : List Expr}
    {stk : List Level} {s₀ : CState}
    (hs : CSOK mode env s₀) (ht : RelC t tx)
    (hfvs : RelCL fvs.toList.reverse ws)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    SimC mode env s₀ RelDC
      (inferPisLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (inferPisLeaf (fueledFns mode env) d tx k ws stk) := by
  unfold inferPisLeafI inferPisLeaf
  refine SimC.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hQob => ?_)
  refine SimC.bind (ih.infer hs₁ hQob hw)
    (fun s₂ bt btx hs₂ hPbt => ?_)
  obtain ⟨hbtd, hwbt⟩ := hPbt
  refine SimC.bind (ih.whnf hs₂ hbtd hwbt)
    (fun s₃ wbt wx hs₃ hPw => ?_)
  obtain ⟨hwd, hww⟩ := hPw
  obtain rfl := hwd
  cases wbt
  case sort v =>
    dsimp only
    refine SimC.bind (inferPisOutC_sim hs₃)
      (fun s₄ iv ivx hs₄ hiv => ?_)
    exact SimC.of_eff (pureC_eff hs₄ (x := Expr.sort iv))
      _ (fun s hQ => by
        show _ = _
        rw [show s = Expr.sort iv from hQ, hiv])
  all_goals exact SimC.throw

theorem inferPisC_sim (ih : SSimC mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : Expr} {tx : Expr} {k : Nat}
      {fvs : Array Expr} {ws : List Expr}
      {stk : List Level} {s₀ : CState},
      CSOK mode env s₀ → RelC t tx →
      RelCL fvs.toList.reverse ws →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      SimC mode env s₀ RelDC
        (inferPisI (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (inferPis (fueledFns mode env) d fuel tx k ws stk)
  | 0, t, tx, k, fvs, ws, stk, s₀ => by
    intro hs ht hfvs hw
    exact inferPisLeafC_sim ih hs ht hfvs hw
  | fuel + 1, t, tx, k, fvs, ws, stk, s₀ => by
    intro hs ht hfvs hw
    show SimC mode env s₀ RelDC
      (do
        match t with
        | .forallE ty body _ => do
          let tyo ← instListRevM ty fvs
          let tty ← (coreKnotI mode (mkFEnv env) f).infer (d + k) tyo
          let wtty ← (coreKnotI mode (mkFEnv env) f).whnf (d + k) tty
          match wtty with
          | .sort u => do
            let fv ← pure (Expr.fvar (d + k) tyo)
            inferPisI (coreKnotI mode (mkFEnv env) f) d fuel body
              (k + 1) (fvs.push fv) (u :: stk)
          | _ => throw (.invalid "expected a sort")
        | _ =>
          inferPisLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      _
    have ht' := ht
    obtain rfl := ht
    cases t
    case forallE ty body mb =>
      dsimp only at hw ⊢
      rw [inferPis_succ_pi]
      have hpiL : (Expr.forallE ty body mb).instantiateList
          ws = Expr.forallE ((Expr.instantiateList ty ws))
            ((Expr.instantiateList body ws 1)) mb := by
        simp [Expr.instantiateList]
      have hwcomp : Expr.WScoped (d + k) ((Expr.instantiateList ty ws))
          ∧ Expr.WScoped (d + k) ((Expr.instantiateList body ws 1)) := by
        rw [hpiL] at hw
        simpa only [Expr.WScoped] using hw
      refine SimC.bind_left
        (instListRevM_eff (d := 0) hs rfl hfvs)
        (fun s₁ tyo hs₁ hQtyo => ?_)
      refine SimC.bind (ih.infer hs₁ hQtyo hwcomp.1)
        (fun s₂ tty ttyx hs₂ hPtty => ?_)
      obtain ⟨httyd, hwtty⟩ := hPtty
      refine SimC.bind (ih.whnf hs₂ httyd hwtty)
        (fun s₃ wtty wx hs₃ hPw => ?_)
      obtain ⟨hwd, hww⟩ := hPw
      obtain rfl := hwd
      cases wtty
      case sort u =>
        dsimp only
        refine SimC.bind_left
          (pureC_eff hs₃ (x := Expr.fvar (d + k) tyo))
          (fun s₄ fv hs₄ hQfv => ?_)
        have hQfv' : RelC fv
            (Expr.fvar (d + k) ((Expr.instantiateList ty ws))) := by
          show _ = _
          rw [show fv = .fvar (d + k) tyo from hQfv,
            hQtyo]
        have hwopen : Expr.WScoped (d + (k + 1))
            ((Expr.instantiateList body
              (Expr.fvar (d + k) (ty.instantiateList ws) :: ws))) := by
          rw [Expr.instantiateList_cons]
          have := Expr.WScoped.instantiate1 hwcomp.1 0 hwcomp.2
          simpa [Nat.add_assoc] using this
        exact inferPisC_sim ih fuel hs₄ rfl
          (by rw [toListRev_push]
              exact RelCL.cons hQfv' hfvs)
          hwopen
      all_goals exact SimC.throw
    all_goals
      dsimp only
      rw [inferPis_succ_ne_pi _ (fun _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafC_sim ih hs ht' hfvs hw

/-! ## Tail compositions: the infer loops against the chained bodies'
own tails, with the result scoping recovered from the chained run -/

private theorem inferLamTail_atF {env : Env} (d : Nat)
    (tyx bodyx : Expr) (mbx : BinderMeta) (F : Nat) :
    ((do
      let bt ← (fueledFns mode env).infer (d + 1)
        (bodyx.instantiate1 (.fvar d tyx))
      pure (Expr.forallE tyx (bt.abstract1 d) mbx)) : FueledM Expr).val F
    = (inferTypeCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d tyx))
        >>= fun bt => pure (Expr.forallE tyx (bt.abstract1 d) mbx)) := by
  rw [FueledM.atF_bind]
  rfl

/-- The λ-inference loop against `inferBody`'s own λ-tail (a pure
rebuild). -/
theorem inferLamsC_tail_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d fuel : Nat} {b t fv : Expr} {bodyx tyx : Expr}
    {mb : BinderMeta} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hbody : RelC b bodyx)
    (hty : RelC t tyx)
    (hfv : RelC fv (.fvar d tyx))
    (hwty : Expr.WScoped d tyx) (hwbody : Expr.WScoped d bodyx) :
    SimC mode env s₀ (RelEC d)
      (inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(t, mb)])
      (do
        let bt ← (fueledFns mode env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d tyx))
        pure (Expr.forallE tyx (bt.abstract1 d) mb)) := by
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d tyx]) := by
    rw [instList_single]
    exact Expr.WScoped.instantiate1 hwty 0 hwbody
  have hcore : SimC mode env s₀ RelDC
      (inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(t, mb)])
      (inferLams (fueledFns mode env) d fuel bodyx 1 [Expr.fvar d tyx]
        [(tyx, mb)]) := by
    refine inferLamsC_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact RelCL.cons hfv RelCL.nil)
      ⟨⟨hty, rfl⟩, trivial⟩ hwopen
  refine SimC.wp (SimC.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferLams_atF] at hF
    obtain ⟨F', hchain⟩ := inferLams_sound fuel bodyx 1
      [Expr.fvar d tyx] [(tyx, mb)] F res rfl hF
    refine ⟨F', ?_⟩
    rw [inferLamTail_atF]
    obtain ⟨bt, hbt, htail⟩ := bind_okB hchain
    have hbt' : inferTypeCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d tyx)]
      exact hbt
    rw [hbt', okB_bind]
    exact htail
  case hsc =>
    intro v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferLamTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    have hwbt : Expr.WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv F hbt
        (Expr.WScoped.instantiate1 hwty 0 hwbody)
    have hres : vv = Expr.forallE tyx (bt.abstract1 d) mb := by
      injection hF with hres
      exact hres.symm
    subst hres
    exact (by
      simp only [Expr.WScoped]
      exact ⟨hwty, ConLeche.WScoped.abstract1 0 hwbt⟩ :
      Expr.WScoped d (Expr.forallE tyx (bt.abstract1 d) mb))

private theorem inferPiTail_atF {env : Env} (d : Nat)
    (tyx bodyx : Expr) (lu : Level) (F : Nat) :
    ((do
      let v ← ensureSort (fueledFns mode env) env (d + 1)
        (← (fueledFns mode env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d tyx)))
      pure (Expr.sort (.imax lu v))) : FueledM Expr).val F
    = (inferTypeCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d tyx))
        >>= fun bt => ensureSortCore mode env F (d + 1) bt >>= fun v =>
        pure (Expr.sort (.imax lu v))) := by
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind, ensureSort_atF]
  rfl

/-- The ∀-inference loop against `inferBody`'s own ∀-tail (the codomain
sort is inferred). -/
theorem inferPisC_tail_sim (ih : SSimC mode env f)
    {d fuel : Nat} {b fv : Expr} {bodyx tyx : Expr}
    {u : Level} {lu : Level} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hbody : RelC b bodyx)
    (hlu : u = lu)
    (hfv : RelC fv (.fvar d tyx))
    (hwty : Expr.WScoped d tyx) (hwbody : Expr.WScoped d bodyx) :
    SimC mode env s₀ (RelEC d)
      (inferPisI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv] [u])
      (do
        let v ← ensureSort (fueledFns mode env) env (d + 1)
          (← (fueledFns mode env).infer (d + 1)
            (bodyx.instantiate1 (.fvar d tyx)))
        pure (Expr.sort (.imax lu v))) := by
  subst hlu
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d tyx]) := by
    rw [instList_single]
    exact Expr.WScoped.instantiate1 hwty 0 hwbody
  have hcore : SimC mode env s₀ RelDC
      (inferPisI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv] [u])
      (inferPis (fueledFns mode env) d fuel bodyx 1
        [Expr.fvar d tyx] [u]) := by
    refine inferPisC_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact RelCL.cons hfv RelCL.nil)
      hwopen
  refine SimC.wp (SimC.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferPis_atF] at hF
    obtain ⟨F', hchain⟩ := inferPis_sound fuel bodyx 1
      [Expr.fvar d tyx] [u] F res rfl (Nat.le_refl 1) hF
    refine ⟨F', ?_⟩
    rw [inferPiTail_atF]
    obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
    have hbt' : inferTypeCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d tyx)]
      exact hbt
    rw [hbt', okB_bind]
    unfold inferPisWrap at hwrap
    obtain ⟨v, hv, hwrap⟩ := bind_okB hwrap
    rw [ensureSort_def] at hv
    have hv' : ensureSortCore mode env F' (d + 1) bt = .ok v := hv
    rw [hv', okB_bind]
    unfold inferPisWrap at hwrap
    exact hwrap
  case hsc =>
    intro v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferPiTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    obtain ⟨v, hv, hF⟩ := bind_okB hF
    injection hF with hres
    subst hres
    simp [Expr.WScoped]

end ConLeche.Cached
