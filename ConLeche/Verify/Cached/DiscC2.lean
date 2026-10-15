module

public import ConLeche.Verify.Cached.DiscC1

public section

/-!
# Cached body walks, part 2: the stuck-term certificates (task #163)

Each walk is a `Std.WP` triple whose post names the cached value as the
fueled answer (`Runs`), proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`; the triple forms of the knot's
entry points and the vocabulary these walks add are in `DiscC1.lean`).
A `…_sim`/`…_eff` corollary restates a walk for the callers that are
still stated as `SimC`/`CEff`.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

/-- The hoisted `Prop`-branch test (task #168): the fast arms are the
same pure reads on both sides (`mkFEnv_find?_eq`). -/
theorem propIrrelC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ propIrrelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs (propIrrel (fueledFns mode env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, propIrrel, mkFEnv_find?_eq] =>
    vcgen [propIrrelI, ih.inferIO_spec, ih.whnf_spec, isEquivLM_spec (mode := mode) (env := env),
      liftFueled_spec (mode := mode) (env := env)] <;>
      -- the pure side is nine binds deep, one `Runs.bind_eq` generation each
      finish (gen := 12)

/-- `propIrrelC_spec` as a simulation, for the unconverted callers. -/
theorem propIrrelC_sim (ih : SSimC mode env f) {d : Nat} {i j : Expr}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (propIrrelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (propIrrel (fueledFns mode env) env d a b) := by
  subst hdena hdenb; exact SimC.of_triple_eq (propIrrelC_spec ih hs hwa hwb)

/-- `Expr.isBoolTrue` transported along the value equation. -/
theorem isBoolTrue_spec' {e : Expr} {ex : Expr}
    (h : e = ex) : Expr.isBoolTrue e = ex.isBoolTrue := by
  rw [h]

/-- The eq-true shortcut (the audit's E2) simulates its specification:
one `whnf`, then the store read of the head test. -/
theorem boolTrueShortcutC_spec (ih : SSimC mode env f) {d : Nat} {a : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d a) :
    ⦃fun s => s = s₀⦄ boolTrueShortcutI (coreKnotI mode (mkFEnv env) f) d a
    ⦃fun v s' => CSOK mode env s' ∧ Runs (boolTrueShortcut (fueledFns mode env) d a) v; ⊤⦄ := by
  sym only [conleche_grind, boolTrueShortcut] =>
    vcgen [boolTrueShortcutI, ih.whnf_spec] <;> finish

/-- `boolTrueShortcutC_spec` under its guard. -/
theorem boolTrueShortcutIfC_spec (ih : SSimC mode env f) {d : Nat} {a : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d a) (g : Bool) :
    ⦃fun s => s = s₀⦄
      (if g then boolTrueShortcutI (coreKnotI mode (mkFEnv env) f) d a else pure false)
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (if g then boolTrueShortcut (fueledFns mode env) d a else pure false) v; ⊤⦄ := by
  sym only [conleche_grind] =>
    vcgen [boolTrueShortcutC_spec ih hs hw] <;> finish

/-- `boolTrueShortcutIfC_spec` as a simulation, for the unconverted callers. -/
theorem boolTrueShortcutIfC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {a : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i a) (hw : Expr.WScoped d a) (g : Bool) :
    SimC mode env s₀ RelVC
      (if g then boolTrueShortcutI (coreKnotI mode (mkFEnv env) f) d i
        else pure false)
      (if g then boolTrueShortcut (fueledFns mode env) d a else pure false) := by
  subst hden; exact SimC.of_triple_eq (boolTrueShortcutIfC_spec ih hs hw g)

/-- `proofIrrelI` simulates its fueled original. -/
theorem proofIrrelC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ proofIrrelI (coreKnotI mode (mkFEnv env) f) d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs (proofIrrel (fueledFns mode env) d a b) v; ⊤⦄ := by
  sym only [conleche_grind, proofIrrel] =>
    vcgen [proofIrrelI, ih.inferIO_spec, ih.whnf_spec, isEquivLM_spec (mode := mode) (env := env),
      liftFueled_spec (mode := mode) (env := env)] <;>
      -- the pure side is nine binds deep, one `Runs.bind_eq` generation each
      finish (gen := 12)

/-- `proofIrrelC_spec` as a simulation, for the unconverted callers. -/
theorem proofIrrelC_sim (ih : SSimC mode env f) {d : Nat} {i j : Expr}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (proofIrrelI (coreKnotI mode (mkFEnv env) f) d i j)
      (proofIrrel (fueledFns mode env) d a b) := by
  subst hdena hdenb; exact SimC.of_triple_eq (proofIrrelC_spec ih hs hwa hwb)

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- `etaCertI` simulates its fueled original. -/
theorem etaCertC_spec (ih : SSimC mode env f) {d : Nat} {ty₁ body₁ b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwty : Expr.WScoped d ty₁) (hwbody : Expr.WScoped d body₁)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ etaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty₁ body₁ b
    ⦃fun v s' => CSOK mode env s' ∧
        Runs (etaCert mode (fueledFns mode env) env d ty₁ body₁ b) v; ⊤⦄ := by
  sym only [conleche_grind, etaCert] =>
    vcgen [etaCertI, ih.inferIO_spec, ih.whnf_spec, ih.defeq_spec, ih.infer_spec,
      inst1M_spec (mode := mode) (env := env)] <;>
      -- the verified arm is seven binds deep, one `Runs.bind_eq` generation each
      finish (gen := 10)

/-- `etaCertC_spec` as a simulation, for the unconverted callers. -/
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
  subst hty hbody hb; exact SimC.of_triple_eq (etaCertC_spec ih hs hwty hwbody hwb)

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
theorem structUnitCertC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structUnitCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧
        Runs (structUnitCert (fueledFns mode env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structUnitCert, mkFEnv_find?, Expr.getAppArgsC_spec] =>
    vcgen [structUnitCertI, ih.inferIO_spec, ih.whnf_spec, ih.defeq_spec] <;> finish

end Walks2

section Walks4

variable {env : Env} {f : Nat}

/-- The cached `.proj` spine (the tower spelling, task #175 W4c). -/
theorem projNodesC_spec (T : Name) (b : Expr) :
    ∀ (l : List Nat) {s₀ : CState}, CSOK mode env s₀ →
      ⦃fun s => s = s₀⦄ projNodesI T b l
      ⦃fun rs s' => CSOK mode env s' ∧ rs = projsOf T b l; ⊤⦄
  | [], _, _ => by
    sym only [conleche_grind] =>
      vcgen [projNodesI] <;> finish
  | _ :: rest, _, _ => by
    sym only [conleche_grind] =>
      vcgen [projNodesI, projNodesC_spec T b rest] <;> finish

/-- `projNodesC_spec` as an effect, for the unconverted callers. -/
theorem projNodesC_eff (T : Name) (l : List Nat) {s₀ : CState} (hs : CSOK mode env s₀)
    {b : Expr} {xb : Expr} (hb : RelC b xb) :
    CEff mode env s₀ (fun rs => RelCL rs (l.map fun i => Expr.proj T i xb))
      (projNodesI T b l) := by
  subst hb; exact triple_iff_run.mp (projNodesC_spec T b l hs)

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

/-- `structEtaCertWithI` simulates its fueled original. -/
theorem structEtaCertWithC_spec (ih : SSimC mode env f) {d : Nat} {a b wtb : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (hwwtb : Expr.WScoped d wtb) :
    ⦃fun s => s = s₀⦄
      structEtaCertWithI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b wtb
    ⦃fun v s' => CSOK mode env s' ∧
        Runs (structEtaCertWith (fueledFns mode env) env d a b wtb) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaCertWith, mkFEnv_find?, Expr.getAppArgsC_spec,
      towerSlotsAllF_mkFEnv] =>
    vcgen [structEtaCertWithI, isEquivListLM_spec (mode := mode) (env := env),
      liftFueled_spec (mode := mode) (env := env), defEqListC_spec ih,
      projNodesC_spec (mode := mode) (env := env)] <;> finish

/-- `structEtaCertI` simulates its fueled original. -/
theorem structEtaCertC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structEtaCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧
        Runs (structEtaCert (fueledFns mode env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaCert] =>
    vcgen [structEtaCertI, ih.inferIO_spec, ih.whnf_spec, structEtaCertWithC_spec ih] <;>
      finish

/-- `stuckIrrelI` simulates its fueled original. -/
theorem stuckIrrelC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ stuckIrrelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧
        Runs (stuckIrrel (fueledFns mode env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, stuckIrrel] =>
    vcgen [stuckIrrelI, structEtaCertC_spec ih, structUnitCertC_spec ih,
      proofIrrelC_spec ih] <;> finish

/-- `stuckIrrelC_spec` as a simulation, for the unconverted callers. -/
theorem stuckIrrelC_sim (ih : SSimC mode env f) (_henv : EnvWF env)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (stuckIrrelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (stuckIrrel (fueledFns mode env) env d a b) := by
  subst hdena hdenb; exact SimC.of_triple_eq (stuckIrrelC_spec ih hs hwa hwb)

end Walks4

end ConLeche.Cached
