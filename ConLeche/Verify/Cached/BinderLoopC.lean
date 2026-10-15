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
relations are `SimC` and `RelC`; a stack entry is an opened domain, related
by `RelC`.

**The peel fuel is not a parameter of these walks.**  Every loop
theorem quantifies over the fuel, so the constant `peelFuel` is an
instance, and no proof below reads a property of the fuel value.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr
open Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

variable {env : Env} {f : Nat}

/-! ## Vocabulary candidates (for Grind.lean)

The triple form of a `SimC` at plain equality, the core knot's
entry points and the pure cached operations as triples, and the
scoping of one opened binder. -/

/-- A simulation at plain equality is a triple whose post names the
cached value as the pure answer. -/
theorem SimC.tripleVC {β : Type} {s₀ : CState} {c : CheckCM β} {p : FueledM β}
    (h : SimC mode env s₀ RelVC c p) :
    ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode env s' ∧ Runs p v; ⊤⦄ := by
  refine triple_iff_run.mpr fun v' s' hr => ?_
  obtain ⟨hs', v, rfl, F, hF⟩ := h v' s' hr
  exact ⟨hs', ⟨F, hF⟩⟩

/-- The converse of `SimC.tripleVC`. -/
theorem SimC.of_tripleVC {β : Type} {s₀ : CState} {c : CheckCM β} {p : FueledM β}
    (h : ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode env s' ∧ Runs p v; ⊤⦄) :
    SimC mode env s₀ RelVC c p := by
  intro v' s' hr
  obtain ⟨hs', ⟨F, hF⟩⟩ := triple_iff_run.mp h v' s' hr
  exact ⟨hs', v', rfl, F, hF⟩

/-- Past a first step that is a `pure`, a bind answers what its
continuation answers (`Runs.bind_eq` needs a `Runs` term of the first
step, which no callee spec supplies when the step is operation-free). -/
@[conleche_grind =] theorem Runs.pure_bind_eq {α β : Type} (a : α) (f : α → FueledM β) (b : β) :
    Runs (Pure.pure a >>= f) b = Runs (f a) b :=
  Runs.bind_eq b (Runs.pure a)

/-- `instListRevM_eff` as a triple. -/
theorem instListRevM_spec {s₀ : CState} (hs : CSOK mode env s₀) (e : Expr) (vs : Array Expr)
    (d : Nat) :
    ⦃fun s => s = s₀⦄ instListRevM e vs d
    ⦃fun r s' => CSOK mode env s' ∧ r = e.instantiateList vs.toList.reverse d; ⊤⦄ :=
  (instListRevM_eff hs (RelC.refl e) (show RelCL vs.toList.reverse _ from rfl) :
    CEff mode env s₀ (fun i => i = e.instantiateList vs.toList.reverse d) _).triple

/-- `abstractRangeM_eff` as a triple. -/
theorem abstractRangeM_spec {s₀ : CState} (hs : CSOK mode env s₀) (e : Expr) (d k : Nat) :
    ⦃fun s => s = s₀⦄ abstractRangeM e d k
    ⦃fun r s' => CSOK mode env s' ∧ r = e.abstractRange d k; ⊤⦄ :=
  (abstractRangeM_eff hs (RelC.refl e) :
    CEff mode env s₀ (fun i => i = e.abstractRange d k) _).triple

theorem instList_lam_eq (ty body : Expr) (ws : List Expr) :
    (Expr.lam ty body).instantiateList ws
      = .lam (ty.instantiateList ws) (body.instantiateList ws 1) := by
  simp [Expr.instantiateList]
grind_pattern [conleche_grind] instList_lam_eq => (Expr.lam ty body).instantiateList ws

theorem instList_forallE_eq (ty body : Expr) (ws : List Expr) :
    (Expr.forallE ty body).instantiateList ws
      = .forallE (ty.instantiateList ws) (body.instantiateList ws 1) := by
  simp [Expr.instantiateList]
grind_pattern [conleche_grind] instList_forallE_eq => (Expr.forallE ty body).instantiateList ws

/-- One binder opened at the next free variable: the body, instantiated
with it in front of the accumulator, is scoped one deeper. -/
theorem wscoped_open_binder {D D' : Nat} {ty body : Expr} {ws : List Expr}
    (hty : Expr.WScoped D ty) (hb : Expr.WScoped D (body.instantiateList ws 1))
    (hD : D' = D + 1) :
    Expr.WScoped D' (body.instantiateList (Expr.fvar D ty :: ws)) := by
  subst hD
  rw [Expr.instantiateList_cons]
  exact Expr.WScoped.instantiate1 hty 0 hb
grind_pattern [conleche_grind] wscoped_open_binder =>
  Expr.WScoped D' (body.instantiateList (Expr.fvar D ty :: ws))

/-- Pushing on the accumulator array conses on its reversed read
(task #97: the loops keep the opened fvars innermost-**last**; the
mirrors' lists stay innermost-first). -/
@[conleche_grind =] theorem toListRev_push {α} (a : Array α) (x : α) :
    (a.push x).toList.reverse = x :: a.toList.reverse := by
  simp

theorem toListRev_singleton {α} (x : α) :
    (#[x] : Array α).toList.reverse = [x] := by
  simp

theorem toListRev_empty {α} :
    (#[] : Array α).toList.reverse = ([] : List α) := by
  simp

/-! ## The infer-λ loop walks

The cached loops match their term on `.lam`/`.forallE`; the equation
compiler states their successor step as one equation per arm, the
fall-through one conditional, so each loop gets one unconditional
equation for `vcgen` (`inferLamsI_succ`, `inferPisI_succ`), and the pure
mirrors' own equation lemmas go into the `sym` list. -/

theorem inferLamsI_succ (r : CoreFnsI) (d fuel : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Expr) :
    inferLamsI r d (fuel + 1) t k fvs stk =
      match t with
      | .lam ty body => do
        let tyo ← instListRevM ty fvs
        let tty ← r.infer (d + k) tyo
        let wtty ← r.whnf (d + k) tty
        match wtty with
        | .sort _ => do
          let fv ← pure (Expr.fvar (d + k) tyo)
          inferLamsI r d fuel body (k + 1) (fvs.push fv) (tyo :: stk)
        | _ => throw (.invalid "expected a sort")
      | t => inferLamsLeafI r d t k fvs stk := by
  cases t <;> (simp only [inferLamsI]; try rfl)

theorem inferLamsOutC_spec {d : Nat} :
    ∀ {stk : List Expr} {j : Nat} {cur : Expr} {s₀ : CState}, CSOK mode env s₀ →
      ⦃fun s => s = s₀⦄ inferLamsOutI d stk j cur
      ⦃fun v s' => CSOK mode env s' ∧ Runs (inferLamsOut (m := FueledM) d stk j cur) v; ⊤⦄
  | [], _, _, _, _ => by
    sym only [conleche_grind, inferLamsOut.eq_1] => vcgen [inferLamsOutI] <;> finish
  | _ :: rest, _, _, _, _ => by
    sym only [conleche_grind, inferLamsOut.eq_2] =>
      vcgen [inferLamsOutI, abstractRangeM_spec (mode := mode) (env := env),
        inferLamsOutC_spec (stk := rest)] <;> finish

theorem inferLamsLeafC_spec (ih : SSimC mode env f) {d : Nat} {t : Expr} {k : Nat}
    {fvs : Array Expr} {stk : List Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hw : Expr.WScoped (d + k) (t.instantiateList fvs.toList.reverse)) :
    ⦃fun s => s = s₀⦄ inferLamsLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (inferLamsLeaf (fueledFns mode env) d t k fvs.toList.reverse stk) v; ⊤⦄ := by
  sym only [conleche_grind, inferLamsLeaf.eq_1] =>
    vcgen [inferLamsLeafI, instListRevM_spec hs, ih.infer_spec,
      abstractRangeM_spec (mode := mode) (env := env),
      inferLamsOutC_spec (mode := mode) (env := env)] <;> finish

theorem inferLamsC_spec (ih : SSimC mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : Expr} {k : Nat} {fvs : Array Expr} {stk : List Expr} {s₀ : CState},
      CSOK mode env s₀ → Expr.WScoped (d + k) (t.instantiateList fvs.toList.reverse) →
      ⦃fun s => s = s₀⦄ inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (inferLams (fueledFns mode env) d fuel t k fvs.toList.reverse stk) v; ⊤⦄
  | 0, _, _, _, _, _, hs, hw => by
    sym only [conleche_grind, inferLams.eq_3] =>
      vcgen [inferLamsI, inferLamsLeafC_spec ih] <;> finish
  | fuel + 1, _, _, _, _, _, hs, hw => by
    sym only [conleche_grind, inferLams.eq_1, inferLams.eq_2] =>
      vcgen [inferLamsI_succ, instListRevM_spec hs, ih.infer_spec, ih.whnf_spec,
        inferLamsC_spec ih fuel, inferLamsLeafC_spec ih] <;> finish

/-! ## The infer-∀ loop walks (task #100 stage 6: the ∀-rule infers
its codomain sort, so the cached side runs a telescope loop) -/

theorem inferPisI_succ (r : CoreFnsI) (d fuel : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Level) :
    inferPisI r d (fuel + 1) t k fvs stk =
      match t with
      | .forallE ty body => do
        let tyo ← instListRevM ty fvs
        let tty ← r.infer (d + k) tyo
        let wtty ← r.whnf (d + k) tty
        match wtty with
        | .sort u => do
          let fv ← pure (Expr.fvar (d + k) tyo)
          inferPisI r d fuel body (k + 1) (fvs.push fv) (u :: stk)
        | _ => throw (.invalid "expected a sort")
      | t => inferPisLeafI r d t k fvs stk := by
  cases t <;> (simp only [inferPisI]; try rfl)

theorem inferPisOutC_spec :
    ∀ {stk : List Level} {v : Level} {s₀ : CState}, CSOK mode env s₀ →
      ⦃fun s => s = s₀⦄ inferPisOutI stk v
      ⦃fun r s' => CSOK mode env s' ∧ Runs (inferPisOut (m := FueledM) stk v) r; ⊤⦄
  | [], _, _, _ => by
    sym only [conleche_grind, inferPisOut.eq_1] => vcgen [inferPisOutI] <;> finish
  | _ :: rest, _, _, _ => by
    sym only [conleche_grind, inferPisOut.eq_2] =>
      vcgen [inferPisOutI, inferPisOutC_spec (stk := rest)] <;> finish

theorem inferPisLeafC_spec (ih : SSimC mode env f) {d : Nat} {t : Expr} {k : Nat}
    {fvs : Array Expr} {stk : List Level} {s₀ : CState} (hs : CSOK mode env s₀)
    (hw : Expr.WScoped (d + k) (t.instantiateList fvs.toList.reverse)) :
    ⦃fun s => s = s₀⦄ inferPisLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (inferPisLeaf (fueledFns mode env) d t k fvs.toList.reverse stk) v; ⊤⦄ := by
  sym only [conleche_grind, inferPisLeaf.eq_1] =>
    vcgen [inferPisLeafI, instListRevM_spec hs, ih.infer_spec, ih.whnf_spec,
      inferPisOutC_spec (mode := mode) (env := env)] <;> finish

theorem inferPisC_spec (ih : SSimC mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : Expr} {k : Nat} {fvs : Array Expr} {stk : List Level} {s₀ : CState},
      CSOK mode env s₀ → Expr.WScoped (d + k) (t.instantiateList fvs.toList.reverse) →
      ⦃fun s => s = s₀⦄ inferPisI (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (inferPis (fueledFns mode env) d fuel t k fvs.toList.reverse stk) v; ⊤⦄
  | 0, _, _, _, _, _, hs, hw => by
    sym only [conleche_grind, inferPis.eq_3] =>
      vcgen [inferPisI, inferPisLeafC_spec ih] <;> finish
  | fuel + 1, _, _, _, _, _, hs, hw => by
    sym only [conleche_grind, inferPis.eq_1, inferPis.eq_2] =>
      vcgen [inferPisI_succ, instListRevM_spec hs, ih.infer_spec, ih.whnf_spec,
        inferPisC_spec ih fuel, inferPisLeafC_spec ih] <;> finish

/-! ## Tail compositions: the infer loops against the chained bodies'
own tails, with the result scoping recovered from the chained run -/

private theorem inferLamTail_atF {env : Env} (d : Nat)
    (tyx bodyx : Expr) (F : Nat) :
    ((do
      let bt ← (fueledFns mode env).infer (d + 1)
        (bodyx.instantiate1 (.fvar d tyx))
      pure (Expr.forallE tyx (bt.abstract1 d))) : FueledM Expr).val F
    = (inferTypeCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d tyx))
        >>= fun bt => pure (Expr.forallE tyx (bt.abstract1 d))) := by
  rw [FueledM.atF_bind]
  rfl

/-- The λ-inference loop against `inferBody`'s own λ-tail (a pure
rebuild). -/
theorem inferLamsC_tail_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d fuel : Nat} {b t fv : Expr} {bodyx tyx : Expr}
    {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hbody : RelC b bodyx)
    (hty : RelC t tyx)
    (hfv : RelC fv (.fvar d tyx))
    (hwty : Expr.WScoped d tyx) (hwbody : Expr.WScoped d bodyx) :
    SimC mode env s₀ (RelEC d)
      (inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [t])
      (do
        let bt ← (fueledFns mode env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d tyx))
        pure (Expr.forallE tyx (bt.abstract1 d))) := by
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d tyx]) := by
    rw [instList_single]
    exact Expr.WScoped.instantiate1 hwty 0 hwbody
  have hb : bodyx = b := hbody.symm
  have ht : tyx = t := hty.symm
  subst hb ht
  have hf : .fvar d tyx = fv := hfv.symm
  subst hf
  have hcore : SimC mode env s₀ RelVC
      (inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel bodyx 1 #[.fvar d tyx] [tyx])
      (inferLams (fueledFns mode env) d fuel bodyx 1 [Expr.fvar d tyx] [tyx]) :=
    SimC.of_tripleVC (inferLamsC_spec ih fuel hs hwopen)
  refine SimC.wp (SimC.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferLams_atF] at hF
    obtain ⟨F', hchain⟩ := inferLams_sound fuel bodyx 1
      [Expr.fvar d tyx] [tyx] F res rfl hF
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
    have hres : vv = Expr.forallE tyx (bt.abstract1 d) := by
      injection hF with hres
      exact hres.symm
    subst hres
    exact (by
      simp only [Expr.WScoped]
      exact ⟨hwty, ConLeche.WScoped.abstract1 0 hwbt⟩ :
      Expr.WScoped d (Expr.forallE tyx (bt.abstract1 d)))

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
  have hb : bodyx = b := hbody.symm
  have hf : .fvar d tyx = fv := hfv.symm
  subst hb hf
  have hcore : SimC mode env s₀ RelVC
      (inferPisI (coreKnotI mode (mkFEnv env) f) d fuel bodyx 1 #[.fvar d tyx] [u])
      (inferPis (fueledFns mode env) d fuel bodyx 1 [Expr.fvar d tyx] [u]) :=
    SimC.of_tripleVC (inferPisC_spec ih fuel hs hwopen)
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
