module

public import ConLeche.Verify.Cached.DiscC1

public section

/-!
# Cached body walks, part 2: the stuck-term certificates (task #163)

`SimC` walks (value relations `RelC`/`RelCL`, node inversion by `cases`
on the `Expr` constructor, the identity name/level wrapper effects of
`SimCEff.lean`).
-/

namespace ConLeche.Cached

open ConLeche.Expr

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

/-- The hoisted `Prop`-branch test (task #168): the fast arm is the
same pure read on both sides (`mkFEnv_find?_fun`); the slow branch is
`proofIrrelC_sim`'s `Prop` branch. -/
theorem propIrrelC_sim (ih : SSimC mode env f) {d : Nat} {i j : Expr}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (propIrrelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (propIrrel (fueledFns mode env) env d a b) := by
  obtain rfl : a = i := hdena.symm
  obtain rfl : b = j := hdenb.symm
  show SimC mode env s₀ RelVC
    (if notProofFast (mkFEnv env).find? a || notProofFast (mkFEnv env).find? b
      then pure false
      else if
        isProofFast (mkFEnv env).find? a && isProofFast (mkFEnv env).find? b
      then pure true else
      (coreKnotI mode (mkFEnv env) f).inferIO d a >>= fun ta =>
      (coreKnotI mode (mkFEnv env) f).inferIO d ta >>= fun tta =>
      (coreKnotI mode (mkFEnv env) f).whnf d tta >>= fun wtta =>
      
      match wtta with
      | .sort uT =>
        pure .zero >>= fun zA =>
        isEquivLM uT zA >>= fun oA =>
        liftFueled "level comparison" oA >>= fun okA =>
        (coreKnotI mode (mkFEnv env) f).inferIO d b >>= fun tb =>
        (coreKnotI mode (mkFEnv env) f).inferIO d tb >>= fun ttb =>
        (coreKnotI mode (mkFEnv env) f).whnf d ttb >>= fun wttb =>
        
        match wttb with
        | .sort vT =>
          pure .zero >>= fun zB =>
          isEquivLM vT zB >>= fun oB =>
          liftFueled "level comparison" oB >>= fun okB =>
          pure (okA && okB)
        | _ => pure false
      | _ => pure false)
    (propIrrel (fueledFns mode env) env d a b)
  rw [show (mkFEnv env).find? = env.find? from funext (mkFEnv_find? env)]
  unfold propIrrel
  by_cases hc :
      (notProofFast env.find? a || notProofFast env.find? b) = true
  · rw [ite_eq_left hc, ite_eq_left hc]
    exact SimC.pure hs rfl
  · rw [ite_eq_right hc, ite_eq_right hc]
    by_cases hy :
        (isProofFast env.find? a && isProofFast env.find? b) = true
    · rw [ite_eq_left hy, ite_eq_left hy]
      exact SimC.pure hs rfl
    rw [ite_eq_right hy, ite_eq_right hy]
    refine SimC.bind (ih.inferIO hs rfl hwa) (fun s₁ ta tax hs₁ hP => ?_)
    obtain ⟨htad, hwta⟩ := hP
    refine SimC.bind (ih.inferIO hs₁ htad hwta) (fun s₃ tta ttax hs₃ hP₃ => ?_)
    obtain ⟨httad, hwtta⟩ := hP₃
    refine SimC.bind (ih.whnf hs₃ httad hwtta) (fun s₄ wtta wttax hs₄ hP₄ => ?_)
    obtain ⟨hwttad, hwwtta⟩ := hP₄
    obtain rfl := hwttad
    cases wtta with
    | sort uT =>
      refine SimC.bind_left (pureEq_eff hs₄ Level.zero)
        (fun s₄z zA hs₄z hzA => ?_)
      subst hzA
      refine SimC.bind_left (isEquivLM_eff hs₄z uT .zero)
        (fun s₄o oA hs₄o hoA => ?_)
      subst hoA
      refine SimC.bind (SimC.liftFueled _ _ hs₄o)
        (fun s₅ okA okA' hs₅ hPok => ?_)
      obtain rfl : okA = okA' := hPok
      refine SimC.bind (ih.inferIO hs₅ rfl hwb) (fun s₆ tb tbx hs₆ hP₆ => ?_)
      obtain ⟨htbd, hwtb⟩ := hP₆
      refine SimC.bind (ih.inferIO hs₆ htbd hwtb) (fun s₇ ttb ttbx hs₇ hP₇ => ?_)
      obtain ⟨httbd, hwttb⟩ := hP₇
      refine SimC.bind (ih.whnf hs₇ httbd hwttb)
        (fun s₈ wttb wttbx hs₈ hP₈ => ?_)
      obtain ⟨hwttbd, hwwttb⟩ := hP₈
      obtain ⟨hwc', rfl⟩ := hwttbd
      cases wttb with
      | sort vT =>
        refine SimC.bind_left (pureEq_eff hs₈ Level.zero)
          (fun s₈z zB hs₈z hzB => ?_)
        subst hzB
        refine SimC.bind_left (isEquivLM_eff hs₈z vT .zero)
          (fun s₈o oB hs₈o hoB => ?_)
        subst hoB
        refine SimC.bind (SimC.liftFueled _ _ hs₈o)
          (fun s₉ okB okB' hs₉ hPok' => ?_)
        obtain rfl : okB = okB' := hPok'
        exact SimC.pure hs₉ rfl
      | bvar k => exact SimC.pure hs₈ rfl
      | const nm us => exact SimC.pure hs₈ rfl
      | lit l => exact SimC.pure hs₈ rfl
      | fvar idx t => exact SimC.pure hs₈ rfl
      | app f' a' => exact SimC.pure hs₈ rfl
      | lam t b' m => exact SimC.pure hs₈ rfl
      | forallE t b' m => exact SimC.pure hs₈ rfl
      | letE t v b' => exact SimC.pure hs₈ rfl
      | proj s i e => exact SimC.pure hs₈ rfl
    | bvar k => exact SimC.pure hs₄ rfl
    | const nm us => exact SimC.pure hs₄ rfl
    | lit l => exact SimC.pure hs₄ rfl
    | fvar idx t => exact SimC.pure hs₄ rfl
    | app f' a' => exact SimC.pure hs₄ rfl
    | lam t b' m => exact SimC.pure hs₄ rfl
    | forallE t b' m => exact SimC.pure hs₄ rfl
    | letE t v b' => exact SimC.pure hs₄ rfl
    | proj s i e => exact SimC.pure hs₄ rfl

/-- `Expr.isBoolTrue` transported along the value equation. -/
theorem isBoolTrue_spec' {e : Expr} {ex : Expr}
    (h : e = ex) : Expr.isBoolTrue e = ex.isBoolTrue := by
  rw [h]

/-- The eq-true shortcut (the audit's E2) simulates its specification:
one `whnf`, then the store read of the head test. -/
theorem boolTrueShortcutC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {a : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i a) (hw : Expr.WScoped d a) :
    SimC mode env s₀ RelVC
      (boolTrueShortcutI (coreKnotI mode (mkFEnv env) f) d i)
      (boolTrueShortcut (fueledFns mode env) d a) := by
  unfold boolTrueShortcutI boolTrueShortcut
  refine SimC.bind (ih.whnf hs hden hw) (fun s₁ w wx hs₁ hP => ?_)
  obtain ⟨hwden, _⟩ := hP
  rw [RelC.erase hwden]
  exact SimC.pure hs₁ rfl

/-- `boolTrueShortcutC_sim` under its guard. -/
theorem boolTrueShortcutIfC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {a : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i a) (hw : Expr.WScoped d a) (g : Bool) :
    SimC mode env s₀ RelVC
      (if g then boolTrueShortcutI (coreKnotI mode (mkFEnv env) f) d i
        else pure false)
      (if g then boolTrueShortcut (fueledFns mode env) d a else pure false) := by
  cases g
  · exact SimC.pure hs rfl
  · exact boolTrueShortcutC_sim ih hs hden hw

/-- `propIrrelC_sim` under the once-per-entry gate (the audit's D3):
the pruned branch is `pure false` twinned. -/
theorem propIrrelIfC_sim (ih : SSimC mode env f) {d : Nat} {i j : Expr}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) (g : Bool) :
    SimC mode env s₀ RelVC
      (if g then propIrrelI (coreKnotI mode (mkFEnv env) f)
        (mkFEnv env) d i j else pure false)
      (if g then propIrrel (fueledFns mode env) env d a b
        else pure false) := by
  cases g
  · exact SimC.pure hs rfl
  · exact propIrrelC_sim ih hs hdena hdenb hwa hwb

/-- `proofIrrelI` simulates its fueled original. -/
theorem proofIrrelC_sim (ih : SSimC mode env f) {d : Nat} {i j : Expr}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (proofIrrelI (coreKnotI mode (mkFEnv env) f) d i j)
      (proofIrrel (fueledFns mode env) d a b) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).inferIO d i >>= fun ta =>
      (coreKnotI mode (mkFEnv env) f).inferIO d ta >>= fun tta =>
      (coreKnotI mode (mkFEnv env) f).whnf d tta >>= fun wtta =>
      
      match wtta with
      | .sort uT =>
        pure .zero >>= fun zA =>
        isEquivLM uT zA >>= fun oA =>
        liftFueled "level comparison" oA >>= fun okA =>
        (coreKnotI mode (mkFEnv env) f).inferIO d j >>= fun tb =>
        (coreKnotI mode (mkFEnv env) f).inferIO d tb >>= fun ttb =>
        (coreKnotI mode (mkFEnv env) f).whnf d ttb >>= fun wttb =>
        
        match wttb with
        | .sort vT =>
          pure .zero >>= fun zB =>
          isEquivLM vT zB >>= fun oB =>
          liftFueled "level comparison" oB >>= fun okB =>
          pure (okA && okB)
        | _ => pure false
      | _ => pure false)
    (proofIrrel (fueledFns mode env) d a b)
  refine SimC.bind (ih.inferIO hs hdena hwa) (fun s₁ ta tax hs₁ hP => ?_)
  obtain ⟨htad, hwta⟩ := hP
  refine SimC.bind (ih.inferIO hs₁ htad hwta) (fun s₃ tta ttax hs₃ hP₃ => ?_)
  obtain ⟨httad, hwtta⟩ := hP₃
  refine SimC.bind (ih.whnf hs₃ httad hwtta) (fun s₄ wtta wttax hs₄ hP₄ => ?_)
  obtain ⟨hwttad, hwwtta⟩ := hP₄
  obtain rfl := hwttad
  cases wtta with
  | sort uT =>
    refine SimC.bind_left (pureEq_eff hs₄ Level.zero)
      (fun s₄z zA hs₄z hzA => ?_)
    subst hzA
    refine SimC.bind_left (isEquivLM_eff hs₄z uT .zero)
      (fun s₄o oA hs₄o hoA => ?_)
    subst hoA
    refine SimC.bind (SimC.liftFueled _ _ hs₄o)
      (fun s₅ okA okA' hs₅ hPok => ?_)
    obtain rfl : okA = okA' := hPok
    refine SimC.bind (ih.inferIO hs₅ hdenb hwb) (fun s₆ tb tbx hs₆ hP₆ => ?_)
    obtain ⟨htbd, hwtb⟩ := hP₆
    refine SimC.bind (ih.inferIO hs₆ htbd hwtb) (fun s₇ ttb ttbx hs₇ hP₇ => ?_)
    obtain ⟨httbd, hwttb⟩ := hP₇
    refine SimC.bind (ih.whnf hs₇ httbd hwttb)
      (fun s₈ wttb wttbx hs₈ hP₈ => ?_)
    obtain ⟨hwttbd, hwwttb⟩ := hP₈
    obtain ⟨hwc', rfl⟩ := hwttbd
    cases wttb with
    | sort vT =>
      refine SimC.bind_left (pureEq_eff hs₈ Level.zero)
        (fun s₈z zB hs₈z hzB => ?_)
      subst hzB
      refine SimC.bind_left (isEquivLM_eff hs₈z vT .zero)
        (fun s₈o oB hs₈o hoB => ?_)
      subst hoB
      refine SimC.bind (SimC.liftFueled _ _ hs₈o)
        (fun s₉ okB okB' hs₉ hPok' => ?_)
      obtain rfl : okB = okB' := hPok'
      exact SimC.pure hs₉ rfl
    | bvar k => exact SimC.pure hs₈ rfl
    | const nm us => exact SimC.pure hs₈ rfl
    | lit l => exact SimC.pure hs₈ rfl
    | fvar idx t => exact SimC.pure hs₈ rfl
    | app f' a' => exact SimC.pure hs₈ rfl
    | lam t b' m => exact SimC.pure hs₈ rfl
    | forallE t b' m => exact SimC.pure hs₈ rfl
    | letE t v b' => exact SimC.pure hs₈ rfl
    | proj sn j' e' => exact SimC.pure hs₈ rfl
  | bvar k => exact SimC.pure hs₄ rfl
  | const nm us => exact SimC.pure hs₄ rfl
  | lit l => exact SimC.pure hs₄ rfl
  | fvar idx t => exact SimC.pure hs₄ rfl
  | app f' a' => exact SimC.pure hs₄ rfl
  | lam t b' m => exact SimC.pure hs₄ rfl
  | forallE t b' m => exact SimC.pure hs₄ rfl
  | letE t v b' => exact SimC.pure hs₄ rfl
  | proj sn j' e' => exact SimC.pure hs₄ rfl

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- `etaCertI` simulates its fueled original. -/
theorem etaCertC_sim (ih : SSimC mode env f) {d : Nat}
    {ty₁ body₁ b : Expr} {ty₁x body₁x bx : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀)
    (hty : RelC ty₁ ty₁x) (hbody : RelC body₁ body₁x) (hb : RelC b bx)
    (hwty : Expr.WScoped d ty₁x) (hwbody : Expr.WScoped d body₁x)
    (hwb : Expr.WScoped d bx) :
    SimC mode env s₀ RelVC
      (etaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
        ty₁ body₁ b)
      (etaCert mode (fueledFns mode env) env d ty₁x body₁x bx) := by
  unfold etaCertI etaCert
  obtain rfl := hty
  obtain rfl := hbody
  obtain rfl := hb
  have hty : RelC ty₁ (ty₁) := rfl
  have hbody : RelC body₁ (body₁) := rfl
  have hb : RelC b b := rfl
  cases hneu : b.ioNeutral with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact SimC.pure hs rfl
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine SimC.bind (ih.inferIO hs hb hwb) (fun s₁ tb tbx hs₁ hP => ?_)
  obtain ⟨htbd, hwtb⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htbd hwtb) (fun s₂ wtb wtbx hs₂ hP₂ => ?_)
  obtain ⟨hwtbd, hwwtb⟩ := hP₂
  obtain rfl := hwtbd
  cases wtb with
  | forallE ty₂ b₂ m₂ =>
    simp only [Expr.WScoped] at hwwtb
    refine SimC.bind (ih.defeq hs₂ rfl hty hwwtb.1 hwty)
      (fun s₄ r r' hs₄ hPr => ?_)
    obtain rfl : r = r' := hPr
    cases r with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.pure hs₄ rfl
    | true =>
      simp only [↓reduceIte]
      refine SimC.bind_left
        (pureC_eff hs₄ (x := Expr.fvar d ty₁))
        (fun s₅ fv hs₅ hQfv => ?_)
      have hQfv' : RelC fv (.fvar d (ty₁)) := hQfv
      refine SimC.bind_left (inst1M_eff hs₅ hbody hQfv')
        (fun s₆ b₁ hs₆ hQb₁ => ?_)
      refine SimC.bind_left
        (pureC_eff hs₆ (x := Expr.app b fv))
        (fun s₇ ba hs₇ hQba => ?_)
      have hQba' : RelC ba (.app b (.fvar d (ty₁))) := by
        show _ = _
        rw [show ba = .app b fv from hQba,
          hQfv']
      have hwapp : Expr.WScoped (d + 1)
          (.app b (.fvar d (ty₁))) := by
        simp only [Expr.WScoped]
        exact ⟨Expr.WScoped.mono (Nat.le_succ d) hwb, Nat.lt_succ_self d,
          hwty⟩
      have hwb₁ : Expr.WScoped (d + 1) (body₁.instantiate1 (.fvar d ty₁)) :=
        Expr.WScoped.instantiate1 hwty 0 hwbody
      refine SimC.bind (ih.defeq hs₇ hQb₁ hQba' hwb₁ hwapp)
        (fun s₈ r₂ r₂x hs₈ hPr₂ => ?_)
      obtain rfl : r₂ = r₂x := hPr₂
      cases r₂ with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.pure hs₈ rfl
      | true =>
        simp only [↓reduceIte]
        split
        · refine SimC.bind (ih.infer hs₈ hQb₁ hwb₁) (fun s₉ t₁ t₁x hs₉ hP₉ => ?_)
          obtain ⟨ht₁, hwt₁⟩ := hP₉
          refine SimC.bind_left (inst1M_eff hs₉ (rfl : RelC b₂ b₂) hQfv')
            (fun s₁₀ t₂ hs₁₀ hQt₂ => ?_)
          refine SimC.bind (ih.defeq hs₁₀ ht₁ hQt₂ hwt₁
            (Expr.WScoped.instantiate1 hwty 0 hwwtb.2))
            (fun s₁₁ r₃ r₃x hs₁₁ hP₃ => ?_)
          obtain rfl : r₃ = r₃x := hP₃
          cases r₃ with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.pure hs₁₁ rfl
          | true =>
            simp only [↓reduceIte]
            exact SimC.pure hs₁₁ rfl
        · exact SimC.pure hs₈ rfl
  | bvar k => exact SimC.pure hs₂ rfl
  | sort u => exact SimC.pure hs₂ rfl
  | const nm us => exact SimC.pure hs₂ rfl
  | lit l => exact SimC.pure hs₂ rfl
  | fvar idx t => exact SimC.pure hs₂ rfl
  | app f' a' => exact SimC.pure hs₂ rfl
  | lam t b' m => exact SimC.pure hs₂ rfl
  | letE t v b' => exact SimC.pure hs₂ rfl
  | proj sn j' e' => exact SimC.pure hs₂ rfl

/-- Indexed readout of a related list (the erasure is a `List.map`,
so the default travels with it). -/
theorem RelCL.getD {dflt : Expr} {dfltx : Expr} (hd : RelC dflt dfltx) :
    ∀ (n : Nat) {l : List Expr} {xs : List Expr}, RelCL l xs →
      RelC (l.getD n dflt) (xs.getD n dfltx)
  | _, [], xs, h => by rw [h.nil_inv]; exact hd
  | 0, a :: as, xs, h => by
    obtain ⟨x, xs', rfl, hax, -⟩ := h.cons_inv
    exact hax
  | n + 1, a :: as, xs, h => by
    obtain ⟨x, xs', rfl, -, has⟩ := h.cons_inv
    exact RelCL.getD hd n has

/-- The cached projection-fire check is the spec's (`mkFEnv`). -/
theorem projCertAtF_mkFEnv (env : Env) (v : Bool) (c : Name) (args : List Expr) :
    projCertAtF (mkFEnv env) v c args = projCertAt env v c args := by
  unfold projCertAtF projCertAt projCertF projCert
  rw [mkFEnv_find?]
  split <;> rfl

/-- `structUnitCertI` simulates its fueled original. -/
theorem structUnitCertC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (_henv : EnvWF env)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (structUnitCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (structUnitCert (fueledFns mode env) env d a b) := by
  obtain rfl := CheckMode.eq_verified hμ
  show SimC .verified env s₀ RelVC
    ((coreKnotI .verified (mkFEnv env) f).inferIO d i >>= fun ta =>
      (coreKnotI .verified (mkFEnv env) f).whnf d ta >>= fun wta =>
      
      match (Expr.getAppFn wta) with
      | .const T us' =>
        pure T >>= fun Tn =>
        match (mkFEnv env).find? Tn with
        | some (.indInfo cvT caps) =>
          pure (Expr.getAppArgsC wta) >>= fun targs =>
          if caps.unitlike = true ∧
              reservedBasisNames.contains Tn = false ∧
              targs.length = caps.unitParams ∧
              us'.length = cvT.levelParams.length then
            (coreKnotI .verified (mkFEnv env) f).inferIO d j >>= fun tb =>
            (coreKnotI .verified (mkFEnv env) f).whnf d tb >>= fun wtb =>
            if wtb.isForallE then pure false else
            (coreKnotI .verified (mkFEnv env) f).defeq d wta wtb
          else pure false
        | _ => pure false
      | _ => pure false)
    ((fueledFns .verified env).inferIO d a >>= fun ta =>
      (fueledFns .verified env).whnf d ta >>= fun wta =>
      match wta.getAppFn with
      | .const T us' =>
        match env.find? T with
        | some (.indInfo cvT caps) =>
          if caps.unitlike = true ∧
              reservedBasisNames.contains T = false ∧
              wta.getAppArgs.length = caps.unitParams ∧
              us'.length = cvT.levelParams.length then
            (fueledFns .verified env).inferIO d b >>= fun tb =>
            (fueledFns .verified env).whnf d tb >>= fun wtb =>
            if wtb.isForallE then pure false else
            (fueledFns .verified env).defeq d wta wtb
          else pure false
        | _ => pure false
      | _ => pure false)
  refine SimC.bind (ih.inferIO hs hdena hwa) (fun s₁ ta tax hs₁ hP => ?_)
  obtain ⟨htad, hwta⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htad hwta) (fun s₂ wta wtax hs₂ hP₂ => ?_)
  obtain ⟨hwtad, hwwta⟩ := hP₂
  refine SimC.pureB ?_
  obtain rfl := hwtad
  have hargs := Expr.getAppArgsC_spec wta
  have hlena : (Expr.getAppArgsC wta).length
      = (Expr.getAppArgs wta).length := RelCL.length hargs
  generalize hg : Expr.getAppFn wta = g
  cases g with
  | const T us' =>
    dsimp only
    refine SimC.bind_left (pureEq_eff hs₂ T)
      (fun s₂' Tv hs₂ hTv => ?_)
    subst hTv
    rw [mkFEnv_find?]
    cases hfT : env.find? Tv with
    | none => exact SimC.pure hs₂ rfl
    | some ci =>
      cases ci with
      | indInfo cvT caps =>
        dsimp only
        refine SimC.pureB ?_
        simp only [hlena]
        split
        · refine SimC.bind (ih.inferIO hs₂ hdenb hwb)
            (fun s₃ tb tbx hs₃ hP₃ => ?_)
          obtain ⟨htbd, hwtb⟩ := hP₃
          refine SimC.bind (ih.whnf hs₃ htbd hwtb)
            (fun s₄ wtb wtbx hs₄ hP₄ => ?_)
          obtain ⟨hwtbd, hwwtb⟩ := hP₄
          obtain rfl := hwtbd
          split
          · exact SimC.pure hs₄ rfl
          · exact ih.defeq hs₄ rfl rfl hwwta hwwtb
        · exact SimC.pure hs₂ rfl
      | axiomInfo cv => exact SimC.pure hs₂ rfl
      | defnInfo cv v h => exact SimC.pure hs₂ rfl
      | thmInfo cv => exact SimC.pure hs₂ rfl
      | ctorInfo cv nP nF => exact SimC.pure hs₂ rfl
      | recInfo cv mI rP rules => exact SimC.pure hs₂ rfl
      | projInfo entry => exact SimC.pure hs₂ rfl
  | bvar k =>
    exact SimC.pure hs₂ rfl
  | sort u =>
    exact SimC.pure hs₂ rfl
  | lit l =>
    exact SimC.pure hs₂ rfl
  | fvar idx t =>
    exact SimC.pure hs₂ rfl
  | app f' a' =>
    exact SimC.pure hs₂ rfl
  | lam t b' m =>
    exact SimC.pure hs₂ rfl
  | forallE t b' m =>
    exact SimC.pure hs₂ rfl
  | letE t v b' =>
    exact SimC.pure hs₂ rfl
  | proj sn j' e' =>
    exact SimC.pure hs₂ rfl

end Walks2

section Walks3

variable {env : Env} {f : Nat}

end Walks3

section Walks4

variable {env : Env} {f : Nat}

/-- The cached `.proj` spine (the tower spelling, task #175 W4c). -/
theorem projNodesC_eff (T : Name) :
    ∀ (l : List Nat) {s₀ : CState}, CSOK mode env s₀ →
      ∀ {b : Expr} {xb : Expr}, RelC b xb →
      CEff mode env s₀ (fun rs => RelCL rs (l.map fun i => Expr.proj T i xb))
        (projNodesI T b l)
  | [], s₀, hs, b, xb, hb => by
    exact CEff.pure hs RelCL.nil
  | i :: rest, s₀, hs, b, xb, hb => by
    obtain rfl := hb
    show CEff mode env s₀ _
      (pure (Expr.proj T i b) >>= fun r =>
        projNodesI T b rest >>= fun rs =>
        pure (r :: rs))
    refine CEff.bind (pureC_eff hs (x := Expr.proj T i b))
      (fun s₁ r hs₁ hQr => ?_)
    refine CEff.bind (projNodesC_eff T rest hs₁ rfl)
      (fun s₂ rs hs₂ hQrs => ?_)
    exact CEff.pure hs₂ (RelCL.cons hQr hQrs)

/-- The index's slot tests are the spec's (`mkFEnv`). -/
theorem towerSlotsAllF_mkFEnv (env : Env) (T : Name) (n : Nat) :
    (mkFEnv env).towerSlotsAllF T n = towerSlotsAll env T n := by
  simp only [FEnv.towerSlotsAllF, towerSlotsAll, mkFEnv_findProj?]
  all_goals rfl

/-- The cached fabricated-projection spine denotes `etaProjs`. -/
theorem etaProjsC_eff (T : Name) (nF : Nat)
    {s₀ : CState} (hs : CSOK mode env s₀) {b : Expr} {xb : Expr} (hb : RelC b xb) :
    CEff mode env s₀ (fun rs => RelCL rs (etaProjs T xb nF))
      (projNodesI T b (List.range nF)) :=
  projNodesC_eff T (List.range nF) hs hb

/-- Prefix of a related list. -/
theorem RelCL.take {l : List Expr} {xs : List Expr} (h : RelCL l xs)
    (k : Nat) : RelCL (l.take k) (xs.take k) := by
  show _ = _
  rw [show l = xs from h]

/-- Suffix of a related list. -/
theorem RelCL.drop {l : List Expr} {xs : List Expr} (h : RelCL l xs)
    (k : Nat) : RelCL (l.drop k) (xs.drop k) := by
  show _ = _
  rw [show l = xs from h]

private theorem structEtaCertWithC_unfold (env : Env) (d : Nat)
    (a b wtb : Expr) :
    structEtaCertWith (fueledFns mode env) env d a b wtb =
    (match a.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.ctorInfo cvc cnP cnF) =>
        if a.getAppArgs.length = cnP + cnF then
          match wtb.getAppFn with
          | .const T us' =>
            match env.find? T with
            | some (.indInfo cvT caps) =>
              if caps.eta = true ∧ caps.etaCtor = c ∧
                  reservedBasisNames.contains T = false ∧
                  reservedBasisNames.contains c = false ∧
                  wtb.getAppArgs.length = caps.etaParams ∧
                  us'.length = cvT.levelParams.length ∧
                  cvc.levelParams = cvT.levelParams ∧
                  towerSlotsAll env T caps.etaFields = true then
                liftFueled "level comparison"
                  (Level.isEquivList us us') >>= fun ok =>
                if ok then
                  defEqList (fueledFns mode env) env d
                      (a.getAppArgs.take caps.etaParams) wtb.getAppArgs >>=
                    fun r₃ =>
                  if r₃ then
                    defEqList (fueledFns mode env) env d
                      (a.getAppArgs.drop caps.etaParams)
                      (etaProjs T b caps.etaFields)
                  else pure false
                else pure false
              else pure false
            | _ => pure false
          | _ => pure false
        else pure false
      | _ => pure false
    | _ => pure false) := rfl

/-- `structEtaCertWithI` simulates its fueled original. -/
theorem structEtaCertWithC_sim (ih : SSimC mode env f)
    {d : Nat} {i j w : Expr} {a b wtb : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b) (hdenw : RelC w wtb)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (hwwtb : Expr.WScoped d wtb) :
    SimC mode env s₀ RelVC
      (structEtaCertWithI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
        i j w)
      (structEtaCertWith (fueledFns mode env) env d a b wtb) := by
  show SimC mode env s₀ RelVC
    (
      match (Expr.getAppFn i) with
      | .const c us =>
        pure c >>= fun cn =>
        match (mkFEnv env).find? cn with
        | some (.ctorInfo cvc cnP cnF) =>
          pure (Expr.getAppArgsC i) >>= fun aargs =>
          if aargs.length = cnP + cnF then
            
            match (Expr.getAppFn w) with
            | .const T us' =>
              pure T >>= fun Tn =>
              match (mkFEnv env).find? Tn with
              | some (.indInfo cvT caps) =>
                pure (Expr.getAppArgsC w) >>= fun targs =>
                if caps.eta = true ∧ caps.etaCtor = cn ∧
                    reservedBasisNames.contains Tn = false ∧
                    reservedBasisNames.contains cn = false ∧
                    targs.length = caps.etaParams ∧
                    us'.length = cvT.levelParams.length ∧
                    cvc.levelParams = cvT.levelParams ∧
                    (mkFEnv env).towerSlotsAllF Tn caps.etaFields = true then
                  isEquivListLM us us' >>= fun o =>
                  liftFueled "level comparison" o >>= fun ok =>
                  if ok then
                    defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env)
                        d (aargs.take caps.etaParams) targs >>= fun r₃ =>
                    if r₃ then
                      projNodesI T j (List.range caps.etaFields) >>=
                        fun projs =>
                      defEqListI (coreKnotI mode (mkFEnv env) f)
                        (mkFEnv env) d (aargs.drop caps.etaParams) projs
                    else pure false
                  else pure false
                else pure false
              | _ => pure false
            | _ => pure false
          else pure false
        | _ => pure false
      | _ => pure false)
    (structEtaCertWith (fueledFns mode env) env d a b wtb)
  obtain rfl := hdena
  obtain rfl := hdenb
  obtain rfl := hdenw
  have hdenb : RelC j j := rfl
  rw [structEtaCertWithC_unfold]
  refine SimC.pureB ?_
  have haargs : RelCL (Expr.getAppArgsC i) (Expr.getAppArgs i) :=
    Expr.getAppArgsC_spec i
  have hlena : (Expr.getAppArgsC i).length
      = (Expr.getAppArgs i).length := RelCL.length haargs
  have htargs : RelCL (Expr.getAppArgsC w) (Expr.getAppArgs w) :=
    Expr.getAppArgsC_spec w
  have hlenw : (Expr.getAppArgsC w).length
      = (Expr.getAppArgs w).length := RelCL.length htargs
  generalize hga : Expr.getAppFn i = ga
  cases ga with
  | const c us =>
    dsimp only
    refine SimC.bind_left (pureEq_eff hs c) (fun s₀c cw hs hcw => ?_)
    subst cw
    rw [mkFEnv_find?]
    cases hfc : env.find? c with
    | none => exact SimC.pure hs rfl
    | some ci =>
      cases ci with
      | ctorInfo cvc cnP cnF =>
        dsimp only
        refine SimC.pureB ?_
        simp only [hlena]
        split
        · refine SimC.pureB ?_
          generalize hgw : Expr.getAppFn w = gw
          cases gw with
          | const T us' =>
            dsimp only
            refine SimC.bind_left (pureEq_eff hs T)
              (fun s₀T Tw hs hTw => ?_)
            subst Tw
            rw [mkFEnv_find?]
            cases hfT : env.find? T with
            | none => exact SimC.pure hs rfl
            | some ciT =>
              cases ciT with
              | indInfo cvT caps =>
                dsimp only
                refine SimC.pureB ?_
                simp only [hlenw]
                rw [towerSlotsAllF_mkFEnv]
                split
                · refine SimC.bind_left (isEquivListLM_eff hs)
                    (fun s₀o o hs₀o ho => ?_)
                  subst ho
                  refine SimC.bind (SimC.liftFueled _ _ hs₀o)
                    (fun s₁ ok ok' hs₁ hPok => ?_)
                  obtain rfl : ok = ok' := hPok
                  cases ok with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    exact SimC.pure hs₁ rfl
                  | true =>
                    simp only [↓reduceIte]
                    refine SimC.bind (defEqListC_sim ih hs₁
                      (haargs.take caps.etaParams) htargs
                      (fun x hx => hwa.getAppArgs x
                        (List.mem_of_mem_take hx))
                      hwwtb.getAppArgs)
                      (fun s₅ r₃ r₃' hs₅ hPr₃ => ?_)
                    obtain rfl : r₃ = r₃' := hPr₃
                    cases r₃ with
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      exact SimC.pure hs₅ rfl
                    | true =>
                      simp only [↓reduceIte]
                      refine SimC.bind_left (etaProjsC_eff T caps.etaFields hs₅ hdenb)
                        (fun s₆ projs hs₆ hQp => ?_)
                      have hwprojs : ∀ x ∈ etaProjs T j caps.etaFields,
                          Expr.WScoped d x := by
                        intro x hx
                        unfold etaProjs at hx
                        obtain ⟨i', -, rfl⟩ := List.mem_map.mp hx
                        simpa [Expr.WScoped] using hwb
                      exact defEqListC_sim ih hs₆
                        (haargs.drop caps.etaParams) hQp
                        (fun x hx => hwa.getAppArgs x
                          (List.mem_of_mem_drop hx)) hwprojs
                · exact SimC.pure hs rfl
              | axiomInfo cv => exact SimC.pure hs rfl
              | defnInfo cv v h => exact SimC.pure hs rfl
              | thmInfo cv => exact SimC.pure hs rfl
              | ctorInfo cv nP' nF' => exact SimC.pure hs rfl
              | recInfo cv mI rP rules => exact SimC.pure hs rfl
              | projInfo entry => exact SimC.pure hs rfl
          | bvar k =>
            exact SimC.pure hs rfl
          | sort u =>
            exact SimC.pure hs rfl
          | lit l =>
            exact SimC.pure hs rfl
          | fvar ix t =>
            exact SimC.pure hs rfl
          | app f' a' =>
            exact SimC.pure hs rfl
          | lam t b' m =>
            exact SimC.pure hs rfl
          | forallE t b' m =>
            exact SimC.pure hs rfl
          | letE t v b' =>
            exact SimC.pure hs rfl
          | proj sn jx e' =>
            exact SimC.pure hs rfl
        · exact SimC.pure hs rfl
      | axiomInfo cv => exact SimC.pure hs rfl
      | defnInfo cv v h => exact SimC.pure hs rfl
      | thmInfo cv => exact SimC.pure hs rfl
      | indInfo cv caps => exact SimC.pure hs rfl
      | recInfo cv mI rP rules => exact SimC.pure hs rfl
      | projInfo entry => exact SimC.pure hs rfl
  | bvar k =>
    exact SimC.pure hs rfl
  | sort u =>
    exact SimC.pure hs rfl
  | lit l =>
    exact SimC.pure hs rfl
  | fvar ix t =>
    exact SimC.pure hs rfl
  | app f' a' =>
    exact SimC.pure hs rfl
  | lam t b' m =>
    exact SimC.pure hs rfl
  | forallE t b' m =>
    exact SimC.pure hs rfl
  | letE t v b' =>
    exact SimC.pure hs rfl
  | proj sn jx e' =>
    exact SimC.pure hs rfl

/-- `structEtaCertI` simulates its fueled original. -/
theorem structEtaCertC_sim (ih : SSimC mode env f)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (structEtaCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (structEtaCert (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    (pure (etaCtorShapeC (mkFEnv env) i) >>=
      fun sh =>
      if sh = true then
        (coreKnotI mode (mkFEnv env) f).inferIO d j >>= fun tb =>
        (coreKnotI mode (mkFEnv env) f).whnf d tb >>= fun wtb =>
        structEtaCertWithI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
          i j wtb
      else pure false)
    (if etaCtorShape env a = true then
      (fueledFns mode env).inferIO d b >>= fun tb =>
      (fueledFns mode env).whnf d tb >>= fun wtb =>
      structEtaCertWith (fueledFns mode env) env d a b wtb
    else pure false)
  -- the constructor-shape gate (D13): one store read, the same `Bool`
  refine SimC.pureB ?_
  rw [etaCtorShapeC_spec' hdena]
  by_cases hsh : etaCtorShape env a = true
  case neg =>
    rw [ite_eq_right hsh, ite_eq_right hsh]
    exact SimC.pure hs rfl
  rw [ite_eq_left hsh, ite_eq_left hsh]
  refine SimC.bind (ih.inferIO hs hdenb hwb) (fun s₁ tb tbx hs₁ hP => ?_)
  obtain ⟨htbd, hwtb⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htbd hwtb) (fun s₂ wtb wtbx hs₂ hP₂ => ?_)
  obtain ⟨hwtbd, hwwtb⟩ := hP₂
  exact structEtaCertWithC_sim ih hs₂ hdena hdenb hwtbd hwa hwb hwwtb

/-- `stuckIrrelI` simulates its fueled original. -/
theorem stuckIrrelC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (stuckIrrelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (stuckIrrel (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    (structEtaCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j >>=
        fun r₃ =>
      if r₃ then pure true else
      structEtaCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d j i >>=
        fun r₄ =>
      if r₄ then pure true else
      structUnitCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j >>=
        fun r₅ =>
      if r₅ then pure true else
      proofIrrelI (coreKnotI mode (mkFEnv env) f) d i j)
    (structEtaCert (fueledFns mode env) env d a b >>= fun r₃ =>
      if r₃ then pure true else
      structEtaCert (fueledFns mode env) env d b a >>= fun r₄ =>
      if r₄ then pure true else
      structUnitCert (fueledFns mode env) env d a b >>= fun r₅ =>
      if r₅ then pure true else
      proofIrrel (fueledFns mode env) d a b)
  refine SimC.bind (structEtaCertC_sim ih hs hdena hdenb hwa hwb)
    (fun s₃ r₃ r₃' hs₃ hP₃ => ?_)
  obtain rfl : r₃ = r₃' := hP₃
  cases r₃ with
  | true => simp only [↓reduceIte]; exact SimC.pure hs₃ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimC.bind (structEtaCertC_sim ih hs₃ hdenb hdena hwb hwa)
      (fun s₄ r₄ r₄' hs₄ hP₄ => ?_)
    obtain rfl : r₄ = r₄' := hP₄
    cases r₄ with
    | true => simp only [↓reduceIte]; exact SimC.pure hs₄ rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine SimC.bind (structUnitCertC_sim hμ ih henv hs₄ hdena hdenb
        hwa hwb) (fun s₅ r₅ r₅' hs₅ hP₅ => ?_)
      obtain rfl : r₅ = r₅' := hP₅
      cases r₅ with
      | true => simp only [↓reduceIte]; exact SimC.pure hs₅ rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact proofIrrelC_sim ih hs₅ hdena hdenb hwa hwb

end Walks4

end ConLeche.Cached
