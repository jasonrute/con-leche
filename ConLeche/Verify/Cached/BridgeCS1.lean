module

public import ConLeche.Verify.Cached.SimCS
public import ConLeche.Verify.BridgeWfImp

public section

/-!
# Cached shared-state walks, part 1: the single-environment checker
functions

Each lemma relates a generic declaration-checker function instantiated at the
cached shared operations (`sharedOpsC mode (mkFEnv env)`, state shared
across all operation calls) to the same function at the fueled families
(`(fueledOpsM mode)`) — the invariant `CSOK mode env` is threaded through
every call, so cache entries created by one call are consumed by later
ones soundly.  The per-site well-scopedness facts mirror the `_wfimp`
walks (`ConLeche/Verify/BridgeWfImp.lean`).

The walks are `Std.WP` triples (`…S_spec`) proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`): the cached and the fueled side are
the same generic function, so its own equation lemmas unfold the fueled
side and the shared operations' triples (§ vocabulary) are the callee
specs.  The `…S_sim` forms the unconverted callers use are one-line
`SimC.of_triple`s.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr
open Std.WP
open scoped Lean.Order

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## Vocabulary candidates (for Grind.lean)

The shared operations' triples, stated at the `sharedOpsC` projections a
generic checker function calls (a triple about `opB …` is not found for
`(sharedOpsC …).isDefEq …`; `SimC.tripleVC` is `BinderLoopC.lean`'s). -/

section Vocabulary

variable {env : Env}

theorem inferS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC mode (mkFEnv env)).inferType env d e
    ⦃fun v s' => CSOK mode env s' ∧ Runs ((fueledOpsM mode).inferType env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  (opE_infer_sim hμ henv hs hw).triple (fun _ _ h => h)

theorem whnfS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC mode (mkFEnv env)).whnf env d e
    ⦃fun v s' => CSOK mode env s' ∧ Runs ((fueledOpsM mode).whnf env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  (opE_whnf_sim hμ henv hs hw).triple (fun _ _ h => h)

theorem defeqS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ (sharedOpsC mode (mkFEnv env)).isDefEq env d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs ((fueledOpsM mode).isDefEq env d a b) v; ⊤⦄ :=
  (opB_sim hμ henv hs hwa hwb).tripleVC

theorem sortS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC mode (mkFEnv env)).ensureSort env d e
    ⦃fun v s' => CSOK mode env s' ∧ Runs ((fueledOpsM mode).ensureSort env d e) v; ⊤⦄ :=
  (opS_sim hμ henv hs hw).tripleVC

/-- A closed term is scoped at every depth. -/
theorem wscoped_of_hasFvar_false {d : Nat} {e : Expr} (h : e.hasFvar = false) :
    Expr.WScoped d e :=
  Expr.WScoped.of_not_hasFvar h
grind_pattern [conleche_grind] wscoped_of_hasFvar_false => Expr.WScoped d e

end Vocabulary

section Walks1

variable {env : Env} {s₀ : CState}

/-- `checkConstantVal` at the cached shared operations simulates the
fueled instantiation; the checked constant's type is well-scoped. -/
theorem checkConstantValS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {cv : ConstantVal} (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ checkConstantVal (sharedOpsC mode (mkFEnv env)) env cv
    ⦃fun v s' => CSOK mode env s' ∧ Runs (checkConstantVal (fueledOpsM mode) env cv) v ∧
      Expr.WScoped 0 cv.type; ⊤⦄ := by
  sym only [conleche_grind, checkConstantVal.eq_1] =>
    vcgen [checkConstantVal, inferS_spec hμ henv hs, sortS_spec hμ henv] <;> finish

theorem checkConstantValS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {cv : ConstantVal}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun _ _ => Expr.WScoped 0 cv.type)
      (checkConstantVal (sharedOpsC mode (mkFEnv env)) env cv)
      (checkConstantVal (fueledOpsM mode) env cv) :=
  SimC.of_triple (fun _ h => h) (checkConstantValS_spec hμ henv hs)

/-- The identity certificate's variable is scoped at its frame. -/
theorem wscoped_reduceCertVar (c : Name) : Expr.WScoped 1 (reduceCertVar c) := by
  unfold reduceCertVar
  simp only [Expr.WScoped]
  refine ⟨Nat.zero_lt_one, ?_⟩
  unfold reduceElemTy
  split <;> simp only [Expr.WScoped]

/-- `checkReducePin` at the cached shared operations. -/
theorem checkReducePinS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env2 : Env}
    {c : Name} {value : Expr} (hvf : value.hasFvar = false) (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ checkReducePin (sharedOpsC mode (mkFEnv env)) env env2 c value
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (checkReducePin (fueledOpsM mode) env env2 c value) v; ⊤⦄ := by
  sym only [conleche_grind, checkReducePin.eq_1, reducePinGuard,
      wscoped_reduceCertVar c] =>
    vcgen [checkReducePin, defeqS_spec hμ henv] <;> finish

theorem checkReducePinS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env2 : Env}
    {c : Name} {value : Expr} (hvf : value.hasFvar = false) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkReducePin (sharedOpsC mode (mkFEnv env)) env env2 c value)
      (checkReducePin (fueledOpsM mode) env env2 c value) :=
  SimC.of_tripleVC (checkReducePinS_spec hμ henv hvf hs)

/-- `certifyNatEqs` at the cached shared operations. -/
theorem certifyNatEqsS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) :
    ∀ {eqs : List (Expr × Expr)},
      (∀ eq ∈ eqs, (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true)) →
      ∀ {s₀ : CState}, CSOK mode env s₀ →
      ⦃fun s => s = s₀⦄ certifyNatEqs (sharedOpsC mode (mkFEnv env)) env eqs
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (certifyNatEqs (fueledOpsM mode) env eqs) v; ⊤⦄
  | [], _, _, _ => by
    sym only [conleche_grind, certifyNatEqs.eq_1] => vcgen [certifyNatEqs] <;> finish
  | eq :: _, hsc, _, hs => by
    sym only [conleche_grind, certifyNatEqs.eq_2,
        Expr.WScoped.of_wscopedB (hsc eq List.mem_cons_self).1,
        Expr.WScoped.of_wscopedB (hsc eq List.mem_cons_self).2] =>
      vcgen [certifyNatEqs, defeqS_spec hμ henv hs,
        certifyNatEqsS_spec hμ henv (fun e he => hsc e (List.mem_cons_of_mem _ he))] <;>
        finish

theorem certifyNatEqsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {eqs : List (Expr × Expr)}
    (hsc : ∀ eq ∈ eqs, (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true))
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (certifyNatEqs (sharedOpsC mode (mkFEnv env)) env eqs)
      (certifyNatEqs (fueledOpsM mode) env eqs) :=
  SimC.of_tripleVC (certifyNatEqsS_spec hμ henv hsc hs)

/-- A certificate's applied proof is scoped at the certificate frame
once its guard holds. -/
theorem divModCertApplied_wscoped {env : Env} {c : Name} {annVal : Expr}
    (hvf : annVal.hasFvar = false) {hyps : List Expr} {eqE proof : Expr}
    (hhyps : ∀ hyp ∈ hyps, hyp.wscopedB 2 = true)
    (hg : divModCertGuard env c annVal hyps eqE proof = true) :
    Expr.WScoped 4 (divModCertApplied (Expr.substConstAll c annVal proof)
      (hyps.map (Expr.substConst0 c annVal))) := by
  unfold divModCertGuard at hg
  simp only [Bool.and_eq_true] at hg
  refine Expr.WScoped.of_wscopedB (divModCertApplied_wscopedB (by simpa using hg.1.1.1.1.2) ?_)
  intro hyp hh
  obtain ⟨h₀, hh₀, rfl⟩ := List.mem_map.mp hh
  exact wscopedB_substConst0 hvf _ (hhyps h₀ hh₀)

/-- `checkDivModCerts` at the cached shared operations. -/
theorem checkDivModCertsS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {c : Name}
    {annVal : Expr} (hvf : annVal.hasFvar = false) :
    ∀ {stmts : List (List Expr × Expr)} {proofs : List Expr},
      (∀ st ∈ stmts, (∀ hyp ∈ st.1, hyp.wscopedB 2 = true) ∧
        st.2.wscopedB 4 = true) →
      ∀ {s₀ : CState}, CSOK mode env s₀ →
      ⦃fun s => s = s₀⦄
        checkDivModCerts (sharedOpsC mode (mkFEnv env)) env c annVal stmts proofs
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (checkDivModCerts (fueledOpsM mode) env c annVal stmts proofs) v; ⊤⦄
  | [], [], _, _, _ => by
    sym only [conleche_grind, checkDivModCerts.eq_1] => vcgen [checkDivModCerts] <;> finish
  | [], _ :: _, _, _, _ | _ :: _, [], _, _, _ => by
    -- the catch-all arm's equation is conditional (`vcgen` finds no spec)
    simp only [checkDivModCerts]
    sym only [conleche_grind] => vcgen <;> finish
  | (hyps, eqE) :: _, _ :: _, hsc, _, hs => by
    sym only [conleche_grind, checkDivModCerts.eq_2,
        divModCertApplied_wscoped hvf (hsc (hyps, eqE) List.mem_cons_self).1,
        Expr.WScoped.of_wscopedB
          (wscopedB_substConst0 hvf _ (hsc (hyps, eqE) List.mem_cons_self).2)] =>
      vcgen [checkDivModCerts, inferS_spec hμ henv hs, defeqS_spec hμ henv,
        checkDivModCertsS_spec hμ henv hvf
          (fun st hst => hsc st (List.mem_cons_of_mem _ hst))] <;> finish

/-- **The variant-fallback combinator simulates** (task #273).  The
cached attempt's success is reproduced by the fueled attempt (`hx`);
every other outcome runs the continuation — on the state the attempt
left, well-formed by `hx`, or after an error on the pre-attempt state
— and the fueled loop reproduces that with its own `none`
continuation (`hk`, for whatever outcome the cached lane delivered).
The common fuel is the larger of the attempt's and the
continuation's.  A statement about the runs: the cached combinator
recovers from an error, which a partial-correctness triple's `⊤`
exception post does not describe. -/
theorem SimC.orElse {s₀ : CState} (hs : CSOK mode env s₀)
    {x : CheckCM Bool} {x' : FueledM Bool}
    {k : Option CheckError → CheckCM Unit}
    {k' : Option CheckError → FueledM Unit}
    (hx : SimC mode env s₀ RelVC x x')
    (hk : ∀ r (s₁ : CState), CSOK mode env s₁ →
      SimC mode env s₁ RelVC (k r) (k' none)) :
    SimC mode env s₀ RelVC ((sharedOpsC mode (mkFEnv env)).orElse x k)
      ((fueledOpsM mode).orElse x' k') := by
  intro v' s' h
  dsimp only [sharedOpsC] at h
  revert h
  cases hxs : x s₀ with
  | ok p =>
    obtain ⟨b, s₁⟩ := p
    obtain ⟨hs₁, v, hv, F₁, hF₁⟩ := hx b s₁ hxs
    subst hv
    cases b with
    | true =>
      intro h
      cases h
      exact ⟨hs₁, (), rfl, F₁, by simp only [fueledOpsM_orElse_atF, hF₁]; rfl⟩
    | false =>
      intro h
      obtain ⟨hs', v₂, hv₂, F₂, hF₂⟩ := hk none s₁ hs₁ v' s' h
      refine ⟨hs', v₂, hv₂, max F₁ F₂, ?_⟩
      simp only [fueledOpsM_orElse_atF]
      rw [x'.property (Nat.le_max_left _ _) hF₁]
      exact (k' none).property (Nat.le_max_right _ _) hF₂
  | error e =>
    intro h
    obtain ⟨hs', v₂, hv₂, F₂, hF₂⟩ := hk (some e) s₀ hs v' s' h
    refine ⟨hs', v₂, hv₂, F₂, ?_⟩
    simp only [fueledOpsM_orElse_atF]
    cases hx' : x'.val F₂ with
    | ok b =>
      cases b with
      | true => cases v₂; rfl
      | false => exact hF₂
    | error e' => exact hF₂

/-- `SimC.orElse` as a triple. -/
theorem orElseS_spec {s₀ : CState} (hs : CSOK mode env s₀)
    {x : CheckCM Bool} {x' : FueledM Bool}
    {k : Option CheckError → CheckCM Unit} {k' : Option CheckError → FueledM Unit}
    (hx : ⦃fun s => s = s₀⦄ x ⦃fun v s' => CSOK mode env s' ∧ Runs x' v; ⊤⦄)
    (hk : ∀ r (s₁ : CState), CSOK mode env s₁ →
      ⦃fun s => s = s₁⦄ k r ⦃fun v s' => CSOK mode env s' ∧ Runs (k' none) v; ⊤⦄) :
    ⦃fun s => s = s₀⦄ (sharedOpsC mode (mkFEnv env)).orElse x k
    ⦃fun v s' => CSOK mode env s' ∧ Runs ((fueledOpsM mode).orElse x' k') v; ⊤⦄ :=
  (SimC.orElse hs (SimC.of_tripleVC hx)
    (fun r s₁ hs₁ => SimC.of_tripleVC (hk r s₁ hs₁))).tripleVC

/-- A variant's pin is closed once its guard holds. -/
theorem divModDeclPin_hasFvar {ps : NatOpPinSet} {env : Env} {c : Name} {value' : Expr}
    (h : (divModPinGuard ps env c && divModCertsGuard ps env c value') = true) :
    (divModDeclPin ps c).hasFvar = false := by
  simp only [divModPinGuard, Bool.and_eq_true] at h
  simpa using h.1.1.1.2

/-- One pin variant's attempt. -/
theorem checkDivModPinAtS_spec (hμ : mode.verifiedChecks = true)
    (henv : EnvWF env) {c : Name} (hc : c ∈ natDivModNames)
    {value' : Expr} (hvf : value'.hasFvar = false) {ps : NatOpPinSet}
    (hping : (divModPinGuard ps env c && divModCertsGuard ps env c value') = true)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ checkDivModPinAt (sharedOpsC mode (mkFEnv env)) env c value' ps
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (checkDivModPinAt (fueledOpsM mode) env c value' ps) v; ⊤⦄ := by
  sym only [conleche_grind, checkDivModPinAt.eq_1, divModDeclPin_hasFvar hping] =>
    vcgen [checkDivModPinAt, defeqS_spec hμ henv hs,
      checkDivModCertsS_spec hμ henv hvf (divModCertStmts_wscopedB hc)] <;> finish

/-- The variant loop, for any two reason accumulators (the cached
lane's carry the outcomes, the fueled lane's the `none` text; neither
affects success). -/
theorem checkDivModPinLoopS_spec (hμ : mode.verifiedChecks = true)
    (henv : EnvWF env) {c : Name} (hc : c ∈ natDivModNames) {value' : Expr} :
    ∀ (pss : List NatOpPinSet) (tried tried' : List String) {s₀ : CState},
      CSOK mode env s₀ → value'.hasFvar = false →
      ⦃fun s => s = s₀⦄
        checkDivModPinLoop (sharedOpsC mode (mkFEnv env)) env c value' pss tried
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (checkDivModPinLoop (fueledOpsM mode) env c value' pss tried') v; ⊤⦄
  | [], _, _, _, _, _ => by
    sym only [conleche_grind, checkDivModPinLoop.eq_1] =>
      vcgen [checkDivModPinLoop] <;> finish
  | ps :: rest, _, tried', _, hs, hvf => by
    by_cases hping : (divModPinGuard ps env c && divModCertsGuard ps env c value') = true
    · sym only [conleche_grind, checkDivModPinLoop.eq_2] =>
        vcgen [checkDivModPinLoop, orElseS_spec hs
          (k' := fun r => checkDivModPinLoop (fueledOpsM mode) env c value' rest
            (tried' ++ [divModAttemptReason ps r]))
          (checkDivModPinAtS_spec hμ henv hc hvf hping hs)
          (fun _ _ hs₁ => checkDivModPinLoopS_spec hμ henv hc rest _ _ hs₁ hvf)] <;> finish
    · sym only [conleche_grind, checkDivModPinLoop.eq_2] =>
        vcgen [checkDivModPinLoop, checkDivModPinLoopS_spec hμ henv hc rest _
          (tried' ++ [s!"{ps.toolchain}: pin or certificate ground constants absent"]) hs hvf] <;>
          finish

/-- `checkDivModPin` at the cached shared operations. -/
theorem checkDivModPinS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env2 : Env}
    {c : Name} (hc : c ∈ natDivModNames)
    (hv'f : ∀ cv' v' h', env2.find? c = some (.defnInfo cv' v' h') →
      v'.hasFvar = false)
    (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ checkDivModPin (sharedOpsC mode (mkFEnv env)) pins env env2 c
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (checkDivModPin (fueledOpsM mode) pins env env2 c) v; ⊤⦄ := by
  sym only [conleche_grind, checkDivModPin.eq_1] =>
    vcgen [checkDivModPin, checkDivModPinLoopS_spec hμ henv hc pins [] []] <;> finish

theorem checkDivModPinS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env2 : Env}
    {c : Name} (hc : c ∈ natDivModNames)
    (hv'f : ∀ cv' v' h', env2.find? c = some (.defnInfo cv' v' h') →
      v'.hasFvar = false)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkDivModPin (sharedOpsC mode (mkFEnv env)) pins env env2 c)
      (checkDivModPin (fueledOpsM mode) pins env env2 c) :=
  SimC.of_tripleVC (checkDivModPinS_spec hμ henv hc hv'f hs)

/-- The basis-install fold (operation-free). -/
theorem installBasisFoldS_spec :
    ∀ (cis : List ConstantInfo) (env' : Env) {s₀ : CState},
      CSOK mode env s₀ →
      ⦃fun s => s = s₀⦄ (cis.foldlM installBasisDecl env' : CheckCM Env)
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (cis.foldlM installBasisDecl env' : FueledM Env) v; ⊤⦄
  | [], _, _, _ => by
    sym only [conleche_grind, List.foldlM_nil] => vcgen [List.foldlM_nil] <;> finish
  | _ :: cis, _, _, _ => by
    sym only [conleche_grind, List.foldlM_cons, installBasisDecl.eq_1] =>
      vcgen [List.foldlM_cons, installBasisDecl, installBasisFoldS_spec cis] <;> finish

theorem installBasisFoldS_sim (cis : List ConstantInfo) (env' : Env) {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (cis.foldlM installBasisDecl env' : CheckCM Env)
      (cis.foldlM installBasisDecl env' : FueledM Env) :=
  SimC.of_tripleVC (installBasisFoldS_spec cis env' hs)

end Walks1

end ConLeche.Cached
