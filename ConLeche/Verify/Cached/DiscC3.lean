module

public import ConLeche.Verify.Cached.DiscC2
public import ConLeche.Verify.Cached.Grind

public section

/-!
# Cached body walks, part 3: the stuck-major rescue and iota

Simulation walks for the cached `majorToCtorI`/`pinArgsI`/`iotaRecI`
(`ConLeche/Cached/CoreC.lean`) against `majorToCtor`/`iotaRec`
(`ConLeche/Kernel/Core.lean`).

The ι step (`iotaRecC_spec`) and its certificate block (`iotaCertC_spec`)
are `Std.WP` triples proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`).  The pure side is never unfolded
into its `match` tree: grind splits such a tree on every discriminant and
compares the alternatives' lambdas.  Each arm the cached walk can reach is
instead one equation whose hypotheses are the cached match's own arm
hypotheses (`iotaRec_rec`, `iotaRecK_ctor`, …, registered with guarded
patterns), and the pieces between the arms are named functions
(`iotaRecK`, `iotaCertGate`, `iotaCertP`, `iotaRecFire`; the cached
certificate block `iotaCertI`), so no `fun` reaches grind.  The environment
reads are named (`findRule`, `ctorVal?`, `constTyOf`, `ruleRhsOf`), with
one guarded equation each at the arm that reads them.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## Vocabulary candidates (for Grind.lean) -/

section Vocabulary

variable {env : Env}

@[conleche_grind =] theorem getAppArgsC_eq (e : Expr) :
    Expr.getAppArgsC e = Expr.getAppArgs e :=
  Expr.getAppArgsC_spec e

@[conleche_grind =] theorem mkFEnv_find_eq (env : Env) (n : Name) :
    (mkFEnv env).find? n = env.find? n :=
  mkFEnv_find? env n

/-- The index as a function (`iotaCase3` takes the lookup itself). -/
@[conleche_grind =] theorem mkFEnv_find_fun (env : Env) :
    (mkFEnv env).find? = env.find? :=
  funext (mkFEnv_find? env)

@[conleche_grind =] theorem mkBvar_eq' (i : Nat) : Expr.mkBvar i = .bvar i :=
  Expr.mkBvar_eq i

@[conleche_grind =] theorem instSpineC_eq (args : List Expr) (t : Nat) (e : Expr) :
    Expr.instSpineC args t e = Expr.instSpine args t e :=
  instSpineC_spec

@[conleche_grind =] theorem instLevelParams_eq (ks : List Name) (us : List Level) (e : Expr) :
    Expr.instLevelParams ks us e = e.instantiateLevelParams ks us :=
  instLevelParams_spec

@[conleche_grind =] theorem OptWS.none_eq (d : Nat) : OptWS d none = True := rfl

/-- A `liftFueled` of a present answer is that answer. -/
@[conleche_grind =] theorem liftFueled_some_bind {α β : Type} (w : String) (a : α)
    (g : α → FueledM β) : (liftFueled w (some a) >>= g : FueledM β) = g a := rfl

theorem allWS_getAppArgs {d : Nat} {e : Expr} (h : Expr.WScoped d e) :
    AllWS d e.getAppArgs :=
  h.getAppArgs
grind_pattern [conleche_grind] allWS_getAppArgs => Expr.WScoped d e, e.getAppArgs

theorem allWS_drop {d : Nat} {xs : List Expr} (n : Nat) (h : AllWS d xs) :
    AllWS d (xs.drop n) :=
  fun x hx => h x (List.mem_of_mem_drop hx)
grind_pattern [conleche_grind] allWS_drop => AllWS d (xs.drop n)

theorem allWS_take {d : Nat} {xs : List Expr} (n : Nat) (h : AllWS d xs) :
    AllWS d (xs.take n) :=
  fun x hx => h x (List.mem_of_mem_take hx)
grind_pattern [conleche_grind] allWS_take => AllWS d (xs.take n)

theorem allWS_append {d : Nat} {xs ys : List Expr} (h : AllWS d xs) (h' : AllWS d ys) :
    AllWS d (xs ++ ys) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · exact h' x hx
grind_pattern [conleche_grind] allWS_append => AllWS d (xs ++ ys)

theorem allWS_getD {d : Nat} {xs : List Expr} (h : AllWS d xs) (n : Nat) :
    Expr.WScoped d (xs.getD n (.bvar 0)) :=
  wscoped_getD h n
grind_pattern [conleche_grind] allWS_getD => AllWS d xs, xs.getD n (.bvar 0)

theorem wscoped_piResidual {d : Nat} {t : Expr} {ys : List Expr} (ht : Expr.WScoped d t)
    (hys : AllWS d ys) : OptWS d (piResidual t ys) := by
  cases h : piResidual t ys with
  | none => trivial
  | some r => exact piResidual_WScoped h ht hys
grind_pattern [conleche_grind] wscoped_piResidual => Expr.WScoped d t, piResidual t ys

/-- A level instantiation of an `fvar`-free term (a stored type or rule
right-hand side) is well scoped. -/
theorem wscoped_instLevels {d : Nat} {e : Expr} (h : e.hasFvar = false) (ps : List Name)
    (us : List Level) : Expr.WScoped d (e.instantiateLevelParams ps us) :=
  wscoped_instLevels_of_not_hasFvar h ps us
grind_pattern [conleche_grind] wscoped_instLevels =>
  Expr.WScoped d (e.instantiateLevelParams ps us)

/-- `wscoped_mkAppN` keyed by its goal (the head is a term the walk
computed, whose scope is derived on demand). -/
theorem wscoped_mkAppN_bwd {d : Nat} {g : Expr} {xs : List Expr} (hg : Expr.WScoped d g)
    (hxs : AllWS d xs) : Expr.WScoped d (Expr.mkAppN g xs) :=
  Expr.WScoped.mkAppN hg hxs
grind_pattern [conleche_grind] wscoped_mkAppN_bwd => Expr.WScoped d (Expr.mkAppN g xs)

/-- The stored type of a constant at levels `us` (a dummy where there is
no constant). -/
@[expose] def constTyOf (env : Env) (n : Name) (us : List Level) : Expr :=
  match env.find? n with
  | some ci => ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us
  | none => .bvar 0

/-! Effect and simulation triples of the callees, stated over the
program's own arguments (a spec argument the program does not determine
would stay a metavariable in `vcgen`'s instantiation). -/

theorem piResidualM_spec {s₀ : CState} (hs : CSOK mode env s₀) (e : Expr) (args : List Expr) :
    ⦃fun s => s = s₀⦄ piResidualM e args
    ⦃fun o s' => CSOK mode env s' ∧ o = piResidual e args; ⊤⦄ := by
  refine triple_iff_run.mpr fun o s' hr => ?_
  obtain ⟨hs', h⟩ := piResidualM_eff hs (RelC.refl e) (show RelCL args args from rfl) o s' hr
  refine ⟨hs', ?_⟩
  revert h
  cases o <;> cases piResidual e args <;> simp [OptEr]

theorem isEquivListLM_spec {s₀ : CState} (hs : CSOK mode env s₀) (ls rs : List Level) :
    ⦃fun s => s = s₀⦄ isEquivListLM ls rs
    ⦃fun o s' => CSOK mode env s' ∧ o = Level.isEquivList ls rs; ⊤⦄ :=
  CEff.triple (isEquivListLM_eff hs)

theorem constTyAtM_spec {s₀ : CState} (hs : CSOK mode env s₀) (nI n : Name) (us : List Level)
    (hfind : (env.find? n).isSome = true) :
    ⦃fun s => s = s₀⦄ constTyAtM (mkFEnv env) nI n us
    ⦃fun t s' => CSOK mode env s' ∧ t = constTyOf env n us; ⊤⦄ := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hfind
  refine triple_iff_run.mpr fun t s' hr => ?_
  obtain ⟨hs', h⟩ := constTyAtM_eff hs hci t s' hr
  exact ⟨hs', by rw [constTyOf, hci]; exact h⟩

variable {f : Nat}

theorem defEqListC_spec (ih : SSimC mode env f) {d : Nat} {s₀ : CState}
    (hs : CSOK mode env s₀) {xs ys : List Expr} (hxs : AllWS d xs) (hys : AllWS d ys) :
    ⦃fun s => s = s₀⦄ defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d xs ys
    ⦃fun b s' => CSOK mode env s' ∧
      Runs (defEqList (fueledFns mode env) env d xs ys) b; ⊤⦄ := by
  refine triple_iff_run.mpr fun b s' hr => ?_
  obtain ⟨hs', _, (rfl : b = _), h⟩ :=
    defEqListC_sim ih hs (show RelCL xs xs from rfl) (show RelCL ys ys from rfl) hxs hys b s' hr
  exact ⟨hs', h⟩

theorem iotaCertsFullC_spec (ih : SSimC mode env f) {d : Nat} {s₀ : CState}
    (hs : CSOK mode env s₀) {ty : Expr} {xs : List Expr} (hty : Expr.WScoped d ty)
    (hxs : AllWS d xs) :
    ⦃fun s => s = s₀⦄ iotaCertsFullI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty xs
    ⦃fun b s' => CSOK mode env s' ∧
      Runs (iotaCertsFull (fueledFns mode env) env d ty xs) b; ⊤⦄ := by
  refine triple_iff_run.mpr fun b s' hr => ?_
  obtain ⟨hs', _, (rfl : b = _), h⟩ :=
    iotaCertsFullC_sim ih hs (RelC.refl ty) hty (show RelCL xs xs from rfl) hxs b s' hr
  exact ⟨hs', h⟩

end Vocabulary

section Walks

variable {env : Env} {f : Nat}

private theorem majorToCtor_unfold (env : Env) (d : Nat) (recName : Name)
    (rules : List RecRule) (major : Expr) :
    majorToCtor mode (fueledFns mode env) env d recName rules major =
    (if isCtorApp env major then pure major else
    match rules with
    | [rl] =>
      match env.find? rl.ctor with
      | some (.ctorInfo cvj cnP _cnF) =>
        match (cvj.type.piResult).getAppFn with
        | .const T _ =>
          match env.find? T with
          | some (.indInfo cvT caps) =>
            if rl.k = true then
              (fueledFns mode env).inferIO d major >>= fun tm =>
              (fueledFns mode env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ cvj.levelParams.length = ust.length then
                  if cnP ≤ tmaj.getAppArgs.length then
                    let fab := Expr.mkAppN (.const rl.ctor ust)
                      (tmaj.getAppArgs.take cnP)
                    if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                        fab.fvarLeaves.all
                          (fun l => major.fvarLeaves.contains l) then
                      (fueledFns mode env).inferIO d fab >>= fun tfab =>
                      (fueledFns mode env).defeq d tmaj tfab >>= fun rd =>
                      if rd then
                        (if mode.verifiedChecks then
                          proofIrrel (fueledFns mode env) d fab major
                        else pure true) >>=
                          fun r =>
                        if r then pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else if rl.eta = true then
              (fueledFns mode env).inferIO d major >>= fun tm =>
              (fueledFns mode env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
                    ust.length = cvT.levelParams.length ∧
                    capsNeverZero cvT.levelParams ust caps = true ∧
                    reservedBasisNames.contains T = false ∧
                    reservedBasisNames.contains caps.etaCtor = false ∧
                    towerSlotsAll env T caps.etaFields = true then
                  let fab := Expr.mkAppN (.const caps.etaCtor ust)
                    (etaFabArgsE T tmaj.getAppArgs major caps.etaFields)
                  if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    pure fab
                  else pure major
                else pure major
              | _ => pure major
            else if T = andName then
              (fueledFns mode env).inferIO d major >>= fun tm =>
              (fueledFns mode env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
                    cvj.levelParams.length = ust.length ∧
                    andRescueSlots env rl.ctor cnP ust = true then
                  let fab := Expr.mkAppN (.const rl.ctor ust)
                    (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])
                  if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    (fueledFns mode env).inferIO d fab >>= fun tfab =>
                    (fueledFns mode env).defeq d tmaj tfab >>= fun rd =>
                    if rd then
                      (if mode.verifiedChecks then
                        proofIrrel (fueledFns mode env) d fab major
                      else pure true) >>=
                        fun r =>
                      if r then pure fab
                      else pure major
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else pure major
          | _ => pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major) := rfl

/-- `majorToCtorI` simulates its fueled original. -/
theorem majorToCtorC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    {d : Nat} {recName : Name} {rules : List RecRule} {i : Expr}
    {major : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i major) (hmaj : Expr.WScoped d major) :
    SimC mode env s₀ (RelEC d)
      (majorToCtorI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d recName
        rules i)
      (majorToCtor mode (fueledFns mode env) env d recName rules major) := by
  -- `.verified` or its eager tower (task #353): the same walk at either
  -- literal mode
  rcases CheckMode.verified_cases hμ with rfl | rfl
  all_goals
    show SimC _ env s₀ (RelEC d)
      (pure (isCtorAppC (mkFEnv env) i) >>=
        fun ctor =>
        if ctor then pure i else
        match rules with
        | [rl] =>
          match (mkFEnv env).find? rl.ctor with
          | some (.ctorInfo cvj cnP cnF) =>
            match (cvj.type.piResult).getAppFn with
            | .const T _ =>
              match (mkFEnv env).find? T with
              | some (.indInfo cvT caps) =>
                if rl.k = true then
                  (coreKnotI _ (mkFEnv env) f).inferIO d i >>= fun tm =>
                  (coreKnotI _ (mkFEnv env) f).whnf d tm >>= fun tmaj =>
                
                  match (Expr.getAppFn tmaj) with
                  | .const T' ust =>
                    pure (T' == T) >>= fun bq =>
                    if bq ∧ cvj.levelParams.length = ust.length then
                      pure (Expr.getAppArgsC tmaj) >>= fun margs =>
                      if cnP ≤ margs.length then
                        pure rl.ctor >>= fun ctorI =>
                        pure (Expr.const ctorI ust) >>= fun h =>
                        mkAppNM h (margs.take cnP) >>= fun fab =>
                        pure (Expr.wscopedBC d fab &&
                          Expr.looseBVarsBounded 0 fab &&
                          Expr.leafGuard fab i) >>=
                          fun g =>
                        if g then
                          (coreKnotI _ (mkFEnv env) f).inferIO d fab >>=
                            fun tfab =>
                          (coreKnotI _ (mkFEnv env) f).defeq d tmaj
                              tfab >>= fun rd =>
                          if rd then
                            proofIrrelI (coreKnotI _ (mkFEnv env) f)
                                d fab i >>= fun r =>
                            if r then pure fab
                            else pure i
                          else pure i
                        else pure i
                      else pure i
                    else pure i
                  | _ => pure i
                else if rl.eta = true then
                  (coreKnotI _ (mkFEnv env) f).inferIO d i >>= fun tm =>
                  (coreKnotI _ (mkFEnv env) f).whnf d tm >>= fun tmaj =>
                
                  match (Expr.getAppFn tmaj) with
                  | .const T' ust =>
                    pure (Expr.getAppArgsC tmaj) >>= fun margs =>
                    pure ust >>= fun ustL =>
                    pure (T' == T) >>= fun bq =>
                    if bq ∧ margs.length = caps.etaParams ∧
                        ust.length = cvT.levelParams.length ∧
                        capsNeverZero cvT.levelParams ustL caps
                          = true ∧
                        reservedBasisNames.contains T = false ∧
                        reservedBasisNames.contains caps.etaCtor = false ∧
                        (mkFEnv env).towerSlotsAllF T caps.etaFields = true then
                      pure T >>= fun TI =>
                      projNodesI TI i (List.range caps.etaFields) >>= fun projs =>
                      pure caps.etaCtor >>= fun ctorI =>
                      pure (Expr.const ctorI ust) >>= fun h =>
                      mkAppNM h (margs ++ projs) >>= fun fab =>
                      pure (Expr.wscopedBC d fab &&
                        Expr.looseBVarsBounded 0 fab &&
                        Expr.leafGuard fab i) >>=
                        fun g =>
                      if g then pure fab
                      else pure i
                    else pure i
                  | _ => pure i
                else if T = andName then
                  (coreKnotI _ (mkFEnv env) f).inferIO d i >>= fun tm =>
                  (coreKnotI _ (mkFEnv env) f).whnf d tm >>= fun tmaj =>

                  match (Expr.getAppFn tmaj) with
                  | .const T' ust =>
                    pure (Expr.getAppArgsC tmaj) >>= fun margs =>
                    pure (T' == T) >>= fun bq =>
                    if bq ∧ margs.length = cnP ∧
                        cvj.levelParams.length = ust.length ∧
                        (mkFEnv env).andRescueSlotsF rl.ctor cnP ust = true then
                      pure T >>= fun TI =>
                      projNodesI TI i [0, 1] >>= fun projs =>
                      pure rl.ctor >>= fun ctorI =>
                      pure (Expr.const ctorI ust) >>= fun h =>
                      mkAppNM h (margs ++ projs) >>= fun fab =>
                      pure (Expr.wscopedBC d fab &&
                        Expr.looseBVarsBounded 0 fab &&
                        Expr.leafGuard fab i) >>=
                        fun g =>
                      if g then
                        (coreKnotI _ (mkFEnv env) f).inferIO d fab >>=
                          fun tfab =>
                        (coreKnotI _ (mkFEnv env) f).defeq d tmaj
                            tfab >>= fun rd =>
                        if rd then
                          proofIrrelI (coreKnotI _ (mkFEnv env) f)
                              d fab i >>= fun r =>
                          if r then pure fab
                          else pure i
                        else pure i
                      else pure i
                    else pure i
                  | _ => pure i
                else pure i
              | _ => pure i
            | _ => pure i
          | _ => pure i
        | _ => pure i)
      (majorToCtor _ (fueledFns _ env) env d recName rules major)
    rw [majorToCtor_unfold]
    refine SimC.pureB ?_
    obtain rfl := hden
    have hden : RelC i i := rfl
    rw [isCtorAppC_spec' rfl]
    by_cases hctor : isCtorApp env i
    · rw [ite_eq_left hctor, ite_eq_left hctor]
      exact SimC.pure hs ⟨hden, hmaj⟩
    · rw [ite_eq_right hctor, ite_eq_right hctor]
      match rules with
      | [] => exact SimC.pure hs ⟨hden, hmaj⟩
      | _ :: _ :: _ => exact SimC.pure hs ⟨hden, hmaj⟩
      | [rl] =>
        dsimp only
        rw [show (mkFEnv env).find? rl.ctor = env.find? rl.ctor from
          mkFEnv_find? env rl.ctor]
        cases hfj : env.find? rl.ctor with
        | none => exact SimC.pure hs ⟨hden, hmaj⟩
        | some ci =>
          cases ci with
          | ctorInfo cvj cnP cnF =>
            dsimp only
            cases hpr : (cvj.type.piResult).getAppFn with
            | const T lus =>
              dsimp only
              rw [show (mkFEnv env).find? T = env.find? T from
                mkFEnv_find? env T]
              cases hfT : env.find? T with
              | none => exact SimC.pure hs ⟨hden, hmaj⟩
              | some ciT =>
                cases ciT with
                | indInfo cvT caps =>
                  dsimp only
                  by_cases hK : rl.k = true
                  · rw [ite_eq_left hK, ite_eq_left hK]
                    refine SimC.bind (ih.inferIO hs hden hmaj)
                      (fun s₁ tm tmx hs₁ hP => ?_)
                    obtain ⟨htmd, hwtm⟩ := hP
                    refine SimC.bind (ih.whnf hs₁ htmd hwtm)
                      (fun s₂ tmaj tmajx hs₂ hP₂ => ?_)
                    obtain ⟨rfl, hwtmaj⟩ := hP₂
                    have hmargs : RelCL (Expr.getAppArgsC tmaj)
                        (Expr.getAppArgs tmaj) :=
                      Expr.getAppArgsC_spec _
                    refine SimC.pureB ?_
                    generalize hg : Expr.getAppFn tmaj = g
                    cases g with
                    | const T' ust =>
                      dsimp only
                      refine SimC.bind_left (pureEq_eff hs₂ (T' == T))
                        (fun s₂b bq hs₂ hbq => ?_)
                      subst bq
                      simp only [beq_iff_eq]
                      split
                      · refine SimC.pureB ?_
                        simp only [hmargs.length]
                        split
                        rotate_left
                        · exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        refine SimC.bind_left (pureEq_eff hs₂ rl.ctor)
                          (fun s₂n ctorI hs₂ hQctorI => ?_)
                        subst hQctorI
                        refine SimC.bind_left (pureC_eff hs₂
                          (x := Expr.const rl.ctor ust))
                          (fun s₃ hd hs₃ hQh => ?_)
                        refine SimC.bind_left (mkAppNM_eff hs₃ hQh
                          (hmargs.take cnP))
                          (fun s₄ fab hs₄ hQfab => ?_)
                        have hQfab' : RelC fab
                            (Expr.mkAppN (.const rl.ctor ust)
                              ((Expr.getAppArgs tmaj).take cnP)) := hQfab
                        refine SimC.pureB ?_
                        rw [wscopedB_spec' hQfab',
                          looseBVarsBounded_spec' hQfab',
                          leafGuard_spec' hQfab' rfl]
                        split
                        · rename_i hguard
                          have hwfab := Expr.WScoped.of_wscopedB
                            (by simp only [Bool.and_eq_true] at hguard
                                exact hguard.1.1)
                          -- the official `to_cnstr_when_K` type check
                          refine SimC.bind (ih.inferIO hs₄ hQfab' hwfab)
                            (fun s₄e tfab tfabx hs₄e hPtf => ?_)
                          obtain ⟨htfd, hwtf⟩ := hPtf
                          refine SimC.bind (ih.defeq hs₄e rfl
                            htfd hwtmaj hwtf)
                            (fun s₄f rd rd' hs₄f hPrd => ?_)
                          obtain rfl : rd = rd' := hPrd
                          cases rd with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₄f ⟨hden, hmaj⟩
                          | true =>
                            simp only [↓reduceIte]
                            refine SimC.bind (proofIrrelC_sim ih hs₄f
                              hQfab' hden hwfab hmaj)
                              (fun s₅ r r' hs₅ hPr => ?_)
                            obtain rfl : r = r' := hPr
                            cases r with
                            | true =>
                              simp only [↓reduceIte]
                              exact SimC.pure hs₅ ⟨hQfab', hwfab⟩
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact SimC.pure hs₅ ⟨hden, hmaj⟩
                        · exact SimC.pure hs₄ ⟨hden, hmaj⟩
                      · exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | bvar k =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | sort u =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | lit l =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | fvar ix t =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | app f' a' =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | lam t b' =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | forallE t b' =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | letE t v b' =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | proj sn jx e' =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  · rw [ite_eq_right hK, ite_eq_right hK]
                    by_cases hEta : rl.eta = true
                    · rw [ite_eq_left hEta, ite_eq_left hEta]
                      refine SimC.bind (ih.inferIO hs hden hmaj)
                        (fun s₁ tm tmx hs₁ hP => ?_)
                      obtain ⟨htmd, hwtm⟩ := hP
                      refine SimC.bind (ih.whnf hs₁ htmd hwtm)
                        (fun s₂ tmaj tmajx hs₂ hP₂ => ?_)
                      obtain ⟨rfl, hwtmaj⟩ := hP₂
                      have hmargs : RelCL (Expr.getAppArgsC tmaj)
                          (Expr.getAppArgs tmaj) :=
                        Expr.getAppArgsC_spec _
                      refine SimC.pureB ?_
                      generalize hg : Expr.getAppFn tmaj = g
                      cases g with
                      | const T' ust =>
                        dsimp only
                        refine SimC.pureB ?_
                        refine SimC.bind_left (pureEq_eff hs₂ ust)
                          (fun s₂r ustL hs₂r hustL => ?_)
                        subst ustL
                        refine SimC.bind_left (pureEq_eff hs₂r (T' == T))
                          (fun s₂rb bq hs₂r hbq => ?_)
                        subst bq
                        simp only [hmargs.length,
                          beq_iff_eq]
                        rw [towerSlotsAllF_mkFEnv]
                        split
                        · refine SimC.bind_left (pureEq_eff hs₂r T)
                            (fun s₂t TI hs₂r hQTI => ?_)
                          subst TI
                          refine SimC.bind_left (etaProjsC_eff T caps.etaFields hs₂r hden)
                            (fun s₃ projs hs₃ hQp => ?_)
                          refine SimC.bind_left (pureEq_eff hs₃
                            caps.etaCtor)
                            (fun s₃n ctorI hs₃ hQctorI => ?_)
                          subst hQctorI
                          refine SimC.bind_left (pureC_eff hs₃
                            (x := Expr.const caps.etaCtor ust))
                            (fun s₄ hd hs₄ hQh => ?_)
                          refine SimC.bind_left (mkAppNM_eff hs₄ hQh
                            (hmargs.append hQp))
                            (fun s₅ fab hs₅ hQfab => ?_)
                          have hQfab' : RelC fab
                              (Expr.mkAppN (.const caps.etaCtor ust)
                                (etaFabArgsE T (Expr.getAppArgs tmaj) i
                                  caps.etaFields)) := hQfab
                          refine SimC.pureB ?_
                          rw [wscopedB_spec' hQfab',
                            looseBVarsBounded_spec' hQfab',
                            leafGuard_spec' hQfab' rfl]
                          split
                          · rename_i hguard
                            have hwfab := Expr.WScoped.of_wscopedB
                              (by simp only [Bool.and_eq_true] at hguard
                                  exact hguard.1.1)
                            exact SimC.pure hs₅ ⟨hQfab', hwfab⟩
                          · exact SimC.pure hs₅ ⟨hden, hmaj⟩
                        · exact SimC.pure hs₂r ⟨hden, hmaj⟩
                      | bvar k =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | sort u =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | lit l =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | fvar ix t =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | app f' a' =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | lam t b' =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | forallE t b' =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | letE t v b' =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | proj sn jx e' =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    · rw [ite_eq_right hEta, ite_eq_right hEta]
                      by_cases hAnd : T = andName
                      · rw [ite_eq_left hAnd, ite_eq_left hAnd]
                        refine SimC.bind (ih.inferIO hs hden hmaj)
                          (fun s₁ tm tmx hs₁ hP => ?_)
                        obtain ⟨htmd, hwtm⟩ := hP
                        refine SimC.bind (ih.whnf hs₁ htmd hwtm)
                          (fun s₂ tmaj tmajx hs₂ hP₂ => ?_)
                        obtain ⟨rfl, hwtmaj⟩ := hP₂
                        have hmargs : RelCL (Expr.getAppArgsC tmaj)
                            (Expr.getAppArgs tmaj) :=
                          Expr.getAppArgsC_spec _
                        refine SimC.pureB ?_
                        generalize hg : Expr.getAppFn tmaj = g
                        cases g with
                        | const T' ust =>
                          dsimp only
                          refine SimC.pureB ?_
                          refine SimC.bind_left (pureEq_eff hs₂ (T' == T))
                            (fun s₂b bq hs₂ hbq => ?_)
                          subst bq
                          rw [andRescueSlotsF_spec]
                          simp only [hmargs.length, beq_iff_eq]
                          split
                          · refine SimC.bind_left (pureEq_eff hs₂ T)
                              (fun s₂t TI hs₂ hQTI => ?_)
                            subst TI
                            refine SimC.bind_left
                              (projNodesC_eff T [0, 1] hs₂ hden)
                              (fun s₃ projs hs₃ hQp => ?_)
                            have hQp' : RelCL projs
                                [Expr.proj T 0 i, Expr.proj T 1 i] := hQp
                            refine SimC.bind_left (pureEq_eff hs₃ rl.ctor)
                              (fun s₃n ctorI hs₃ hQctorI => ?_)
                            subst hQctorI
                            refine SimC.bind_left (pureC_eff hs₃
                              (x := Expr.const rl.ctor ust))
                              (fun s₄ hd hs₄ hQh => ?_)
                            refine SimC.bind_left (mkAppNM_eff hs₄ hQh
                              (hmargs.append hQp'))
                              (fun s₅ fab hs₅ hQfab => ?_)
                            have hQfab' : RelC fab
                                (Expr.mkAppN (.const rl.ctor ust)
                                  (Expr.getAppArgs tmaj ++
                                    [Expr.proj T 0 i, Expr.proj T 1 i])) := hQfab
                            refine SimC.pureB ?_
                            rw [wscopedB_spec' hQfab',
                              looseBVarsBounded_spec' hQfab',
                              leafGuard_spec' hQfab' rfl]
                            split
                            · rename_i hguard
                              have hwfab := Expr.WScoped.of_wscopedB
                                (by simp only [Bool.and_eq_true] at hguard
                                    exact hguard.1.1)
                              -- the fabrication's type against the major's
                              refine SimC.bind (ih.inferIO hs₅ hQfab' hwfab)
                                (fun s₅e tfab tfabx hs₅e hPtf => ?_)
                              obtain ⟨htfd, hwtf⟩ := hPtf
                              refine SimC.bind (ih.defeq hs₅e rfl
                                htfd hwtmaj hwtf)
                                (fun s₅f rd rd' hs₅f hPrd => ?_)
                              obtain rfl : rd = rd' := hPrd
                              cases rd with
                              | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte]
                                exact SimC.pure hs₅f ⟨hden, hmaj⟩
                              | true =>
                                simp only [↓reduceIte]
                                refine SimC.bind (proofIrrelC_sim ih hs₅f
                                  hQfab' hden hwfab hmaj)
                                  (fun s₆ r r' hs₆ hPr => ?_)
                                obtain rfl : r = r' := hPr
                                cases r with
                                | true =>
                                  simp only [↓reduceIte]
                                  exact SimC.pure hs₆ ⟨hQfab', hwfab⟩
                                | false =>
                                  simp only [Bool.false_eq_true, ↓reduceIte]
                                  exact SimC.pure hs₆ ⟨hden, hmaj⟩
                            · exact SimC.pure hs₅ ⟨hden, hmaj⟩
                          · exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        | bvar k =>
                          exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        | sort u =>
                          exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        | lit l =>
                          exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        | fvar ix t =>
                          exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        | app f' a' =>
                          exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        | lam t b' =>
                          exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        | forallE t b' =>
                          exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        | letE t v b' =>
                          exact SimC.pure hs₂ ⟨hden, hmaj⟩
                        | proj sn jx e' =>
                          exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      · rw [ite_eq_right hAnd, ite_eq_right hAnd]
                        exact SimC.pure hs ⟨hden, hmaj⟩
                | axiomInfo cv => exact SimC.pure hs ⟨hden, hmaj⟩
                | defnInfo cv v h => exact SimC.pure hs ⟨hden, hmaj⟩
                | thmInfo cv => exact SimC.pure hs ⟨hden, hmaj⟩
                | ctorInfo cv nP' nF' => exact SimC.pure hs ⟨hden, hmaj⟩
                | recInfo cv mI rP rules' => exact SimC.pure hs ⟨hden, hmaj⟩
                | projInfo entry => exact SimC.pure hs ⟨hden, hmaj⟩
            | bvar k => exact SimC.pure hs ⟨hden, hmaj⟩
            | fvar ix t => exact SimC.pure hs ⟨hden, hmaj⟩
            | sort u => exact SimC.pure hs ⟨hden, hmaj⟩
            | app f' a' => exact SimC.pure hs ⟨hden, hmaj⟩
            | lam t b' => exact SimC.pure hs ⟨hden, hmaj⟩
            | forallE t b' => exact SimC.pure hs ⟨hden, hmaj⟩
            | letE t v b' => exact SimC.pure hs ⟨hden, hmaj⟩
            | lit l => exact SimC.pure hs ⟨hden, hmaj⟩
            | proj s'ᵢ j' e' => exact SimC.pure hs ⟨hden, hmaj⟩
          | axiomInfo cv => exact SimC.pure hs ⟨hden, hmaj⟩
          | defnInfo cv v h => exact SimC.pure hs ⟨hden, hmaj⟩
          | thmInfo cv => exact SimC.pure hs ⟨hden, hmaj⟩
          | indInfo cv caps => exact SimC.pure hs ⟨hden, hmaj⟩
          | recInfo cv mI rP rules' => exact SimC.pure hs ⟨hden, hmaj⟩
          | projInfo entry => exact SimC.pure hs ⟨hden, hmaj⟩

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- Simulation of the major chain, in either order (the K flag is the
single rule's stored bit, read identically on both sides; off K, the
rescue on the raw major, then, failing a constructor, the whnf chain). -/
theorem prepareMajorC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    {d : Nat} {recName : Name} {rules : List RecRule} {i : Expr}
    {major : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i major) (hmaj : Expr.WScoped d major) :
    SimC mode env s₀ (RelEC d)
      (prepareMajorI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d recName
        rules i)
      (prepareMajor mode (fueledFns mode env) env d recName rules major) := by
  unfold prepareMajorI prepareMajor
  by_cases hk : recRuleK rules = true
  · rw [ite_eq_left hk, ite_eq_left hk]
    refine SimC.bind (majorToCtorC_sim hμ ih hs hden hmaj)
      (fun s₁ m₁ m₁x hs₁ hP₁ => ?_)
    obtain ⟨hd₁, hw₁⟩ := hP₁
    rw [isCtorAppC_spec' hd₁]
    by_cases hca : isCtorApp env m₁x
    · rw [ite_eq_left hca, ite_eq_left hca]
      exact litMajorToCtorC_sim ih hs₁ hd₁ hw₁
    · rw [ite_eq_right hca, ite_eq_right hca]
      exact SimC.pure hs₁ ⟨hd₁, hw₁⟩
  · -- the structure rescues on the raw major first (task #342 R2)
    rw [ite_eq_right hk, ite_eq_right hk]
    obtain rfl := hden
    by_cases hsl : i.isStrLit = true
    · rw [ite_eq_left hsl, ite_eq_left hsl]
      refine SimC.bind (SimC.pure (P := RelEC d) hs (show RelEC d i i from ⟨rfl, hmaj⟩))
        (fun s₁ m₁ m₁x hs₁ hP₁ => ?_)
      obtain ⟨hd₁, hw₁⟩ := hP₁
      dsimp only
      rw [isCtorAppC_spec' hd₁]
      by_cases hca : isCtorApp env m₁x
      · rw [ite_eq_left hca, ite_eq_left hca]
        exact SimC.pure hs₁ ⟨hd₁, hw₁⟩
      · rw [ite_eq_right hca, ite_eq_right hca]
        refine SimC.bind (ih.whnf hs₁ hd₁ hw₁) (fun s₂ m₂ m₂x hs₂ hP₂ => ?_)
        obtain ⟨hd₂, hw₂⟩ := hP₂
        refine SimC.bind (litMajorToCtorC_sim ih hs₂ hd₂ hw₂)
          (fun s₃ m₃ m₃x hs₃ hP₃ => ?_)
        obtain ⟨hd₃, hw₃⟩ := hP₃
        exact majorToCtorC_sim hμ ih hs₃ hd₃ hw₃
    · rw [ite_eq_right hsl, ite_eq_right hsl]
      refine SimC.bind (majorToCtorC_sim hμ ih hs rfl hmaj)
        (fun s₁ m₁ m₁x hs₁ hP₁ => ?_)
      obtain ⟨hd₁, hw₁⟩ := hP₁
      dsimp only
      rw [isCtorAppC_spec' hd₁]
      by_cases hca : isCtorApp env m₁x
      · rw [ite_eq_left hca, ite_eq_left hca]
        exact SimC.pure hs₁ ⟨hd₁, hw₁⟩
      · rw [ite_eq_right hca, ite_eq_right hca]
        refine SimC.bind (ih.whnf hs₁ hd₁ hw₁) (fun s₂ m₂ m₂x hs₂ hP₂ => ?_)
        obtain ⟨hd₂, hw₂⟩ := hP₂
        refine SimC.bind (litMajorToCtorC_sim ih hs₂ hd₂ hw₂)
          (fun s₃ m₃ m₃x hs₃ hP₃ => ?_)
        obtain ⟨hd₃, hw₃⟩ := hP₃
        exact majorToCtorC_sim hμ ih hs₃ hd₃ hw₃

theorem prepareMajorC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    {d : Nat} {recName : Name} {rules : List RecRule} {i : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      prepareMajorI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d recName rules i
    ⦃fun m s' => CSOK mode env s' ∧
      Runs (prepareMajor mode (fueledFns mode env) env d recName rules i) m ∧
      Expr.WScoped d m; ⊤⦄ :=
  (prepareMajorC_sim hμ ih hs (RelC.refl i) hw).triple relEC_inv

/-! ### The ι step's named pieces -/

/-- A nested rule's pin at the recursor's levels and leading arguments. -/
@[expose] def pinInst (lps : List Name) (us : List Level) (args : List Expr) (t : Nat)
    (p : Expr) : Expr :=
  Expr.instSpine args t (p.instantiateLevelParams lps us)

/-- `recFireComparands` with the firing mode as an argument. -/
@[expose] def fireCmp (fire : RecRuleFire) (ctorParams : Nat) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    List Level × List Expr :=
  match fire with
  | .nested lvls pins =>
    (lvls.map (Level.subst lps us), pins.map (pinInst lps us (args.take rP) (rP - 1)))
  | .plain => ((cvjLps.map Level.param).map (Level.subst lps us), args.take ctorParams)

@[conleche_grind =] theorem recFireComparands_eq (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    recFireComparands rl lps us cvjLps args rP =
      fireCmp rl.fire rl.ctorParams lps us cvjLps args rP := by
  unfold recFireComparands fireCmp pinInst
  cases rl.fire <;> simp

@[conleche_grind =] theorem fireCmp_nested (lvls : List Level) (pins : List Expr) (n : Nat)
    (lps : List Name) (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    fireCmp (.nested lvls pins) n lps us cvjLps args rP =
      (lvls.map (Level.subst lps us), pins.map (pinInst lps us (args.take rP) (rP - 1))) := rfl

@[conleche_grind =] theorem fireCmp_plain (n : Nat)
    (lps : List Name) (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    fireCmp .plain n lps us cvjLps args rP =
      ((cvjLps.map Level.param).map (Level.subst lps us), args.take n) := rfl

/-- Every element of the list is free of free variables. -/
@[expose] def AllClosed (xs : List Expr) : Prop := ∀ x ∈ xs, x.hasFvar = false

theorem allWS_pinInst {d : Nat} {pins args : List Expr} (lps : List Name) (us : List Level)
    (t : Nat) (hp : AllClosed pins) (ha : AllWS d args) :
    AllWS d (pins.map (pinInst lps us args t)) := by
  intro x hx
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
  exact instSpine_WScoped t (WScoped.of_not_hasFvar (by
    rw [hasFvar_instantiateLevelParams]; exact hp p hp')) ha
grind_pattern [conleche_grind] allWS_pinInst => AllWS d (pins.map (pinInst lps us args t))

/-- A nested rule's stored pins are closed. -/
@[expose] def FireClosed : RecRuleFire → Prop
  | .plain => True
  | .nested _ pins => AllClosed pins

@[conleche_grind =] theorem FireClosed.nested_eq (lvls : List Level) (pins : List Expr) :
    FireClosed (.nested lvls pins) = AllClosed pins := rfl

/-- A found rule's stored data is closed. -/
@[expose] def OptRuleOK : Option RecRule → Prop
  | none => True
  | some rl => rl.rhs.hasFvar = false ∧ FireClosed rl.fire

@[conleche_grind =] theorem OptRuleOK.some_eq (rl : RecRule) :
    OptRuleOK (some rl) = (rl.rhs.hasFvar = false ∧ FireClosed rl.fire) := rfl

/-- Every rule's stored data is closed. -/
@[expose] def AllRulesOK (rules : List RecRule) : Prop := ∀ rl ∈ rules, OptRuleOK (some rl)

/-- The rule a recursor stores for constructor `cj` (the lookup's `fun`
named, so that two lookups at equal names are congruent). -/
@[expose] def findRule (rules : List RecRule) (cj : Name) : Option RecRule :=
  rules.find? (fun r' => r'.ctor == cj)

theorem allRulesOK_find {rules : List RecRule} (h : AllRulesOK rules) (cj : Name) :
    OptRuleOK (findRule rules cj) := by
  cases hf : findRule rules cj with
  | none => trivial
  | some rl => exact h rl (List.mem_of_find?_eq_some hf)
grind_pattern [conleche_grind] allRulesOK_find => AllRulesOK rules, findRule rules cj

theorem EnvWF.ctorTy_closed (henv : EnvWF env) {cj : Name} {cvj : ConstantVal} {nP nF : Nat}
    (hfj : env.find? cj = some (.ctorInfo cvj nP nF)) : cvj.type.hasFvar = false :=
  (henv _ (Env.find?_mem hfj)).1

theorem EnvWF.rules_ok (henv : EnvWF env) {c : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hfc : env.find? c = some (.recInfo cv mI rP rules)) :
    AllRulesOK rules := by
  obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (Env.find?_mem hfc)
  intro rl hrl
  obtain ⟨hrf, -, -, -, g5⟩ := hrules cv mI rP rules rfl rl hrl
  refine ⟨hrf, ?_⟩
  cases hf : rl.fire with
  | plain => trivial
  | nested lvls pins => exact fun pin hpin => ((g5 lvls pins hf).2.2.1 pin hpin).1

/-- The constructor record stored under `n`. -/
@[expose] def ctorVal? (env : Env) (n : Name) : Option ConstantVal :=
  match env.find? n with
  | some (.ctorInfo cv _ _) => some cv
  | _ => none

theorem ctorVal?_some {n : Name} {cv : ConstantVal} (h : ctorVal? env n = some cv) :
    ∃ nP nF, env.find? n = some (.ctorInfo cv nP nF) := by
  unfold ctorVal? at h
  split at h
  · cases h; exact ⟨_, _, by assumption⟩
  · cases h

theorem ctorVal?_of {n : Name} {cv : ConstantVal} {nP nF : Nat}
    (h : env.find? n = some (.ctorInfo cv nP nF)) : ctorVal? env n = some cv := by
  simp only [ctorVal?, h]
grind_pattern [conleche_grind] ctorVal?_of => ctorVal? env n, ConstantInfo.ctorInfo cv nP nF where
  guard env.find? n = some (.ctorInfo cv nP nF)

/-- A recursor's rule right-hand side for constructor `j` at levels `us`. -/
@[expose] def ruleRhsOf (env : Env) (c j : Name) (us : List Level) : Option Expr :=
  match env.find? c with
  | some (.recInfo cv _ _ rules) =>
    match findRule rules j with
    | some rl => some (rl.rhs.instantiateLevelParams cv.levelParams us)
    | none => none
  | _ => none

theorem ruleRhsOf_some {c j : Name} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {rl : RecRule} (h2 : env.find? c = some (.recInfo cv mI rP rules))
    (h3 : findRule rules j = some rl) (us : List Level) :
    ruleRhsOf env c j us = some (rl.rhs.instantiateLevelParams cv.levelParams us) := by
  simp only [ruleRhsOf, h2, h3]
grind_pattern [conleche_grind] ruleRhsOf_some =>
    ruleRhsOf env c j us, ConstantInfo.recInfo cv mI rP rules, some rl where
  guard env.find? c = some (.recInfo cv mI rP rules)
  guard findRule rules j = some rl

theorem ruleRhsAtM_spec {s₀ : CState} (hs : CSOK mode env s₀) (cI jI c j : Name)
    (us : List Level) (hfind : (ruleRhsOf env c j us).isSome = true) :
    ⦃fun s => s = s₀⦄ ruleRhsAtM (mkFEnv env) cI jI c j us
    ⦃fun t s' => CSOK mode env s' ∧ some t = ruleRhsOf env c j us; ⊤⦄ := by
  refine triple_iff_run.mpr fun t s' hr => ?_
  unfold ruleRhsOf at hfind ⊢
  split at hfind
  · rename_i cv mI rP rules hc
    split at hfind
    · rename_i rl hrl
      obtain ⟨hs', h⟩ := ruleRhsAtM_eff hs hc hrl t s' hr
      exact ⟨hs', congrArg some h⟩
    · exact nomatch hfind
  · exact nomatch hfind

/-- The cached ι certificate block (the argument of `certAtI` in
`iotaRecI`). -/
@[expose] def iotaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (cv : ConstantVal)
    (mI rP : Nat) (us : List Level) (args : List Expr) (cj cjn : Name) (usj : List Level)
    (cvj : ConstantVal) (rl : RecRule) (margs : List Expr) : CheckCM Bool := do
  let cmpLvls : List Level ←
    match rl.fire with
    | .nested lvls _ => substLevelTreesM cv.levelParams us lvls
    | .plain =>
      substLevelTreesM cv.levelParams us
        (cvj.levelParams.map Level.param)
  if iotaCase3 fe.find? rl cvj cmpLvls then do
    let oL ← isEquivListLM usj cmpLvls
    if ← liftFueled "level comparison" oL then do
      let cmpArgs : List Expr ←
        match rl.fire with
        | .nested _ pins =>
          pinArgsI cv.levelParams us (args.take rP) (rP - 1) pins
        | .plain => pure (args.take rl.ctorParams)
      if ← defEqListI r fe depth (margs.take rl.ctorParams) cmpArgs then do
        let tyCtor ← constTyAtM fe cj cjn usj
        if ← iotaCertsFullI r fe depth tyCtor margs then
          iotaIndexOkI r fe depth mI rP rl.ctorParams tyCtor
            margs ((args.take mI).drop rP)
        else pure false
      else pure false
    else pure false
  else pure true

/-- The pure ι certificate block (case 3 of the ι case split). -/
@[expose] def iotaCertP {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) (env : Env) (depth : Nat) (cv : ConstantVal) (mI rP : Nat)
    (us : List Level) (args : List Expr) (usj : List Level) (cvj : ConstantVal)
    (rl : RecRule) (margs : List Expr) : m Bool := do
  let cmp := recFireComparands rl cv.levelParams us cvj.levelParams args rP
  if iotaCase3 env.find? rl cvj cmp.1 then do
    if ← liftFueled "level comparison" (Level.isEquivList usj cmp.1) then
      if ← defEqList r env depth (margs.take rl.ctorParams) cmp.2 then
        if ← iotaCertsFull r env depth
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            margs then
          iotaIndexOk r env depth mI rP rl.ctorParams
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            margs ((args.take mI).drop rP)
        else pure false
      else pure false
    else pure false
  else pure true

/-- The pure ι certificate block behind its mode gate. -/
@[expose] def iotaCertGate {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat) (cv : ConstantVal)
    (mI rP : Nat) (us : List Level) (args : List Expr) (usj : List Level) (cvj : ConstantVal)
    (rl : RecRule) (margs : List Expr) : m Bool :=
  if mode.verifiedChecks then iotaCertP r env depth cv mI rP us args usj cvj rl margs
  else pure true

/-- The firing tail of the pure ι step. -/
@[expose] def iotaRecFire {m : Type → Type} [Monad m] (cv : ConstantVal) (us : List Level)
    (args : List Expr) (rP : Nat) (rl : RecRule) (margs : List Expr) (ok : Bool) :
    m (Option Expr) :=
  if ok then
    pure (some (Expr.mkAppN
      (rl.rhs.instantiateLevelParams cv.levelParams us)
      (args.take rP ++ margs.drop rl.ctorParams)))
  else pure none

/-- The pure ι step past the major's preparation. -/
@[expose] def iotaRecK {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) (env : Env) (depth : Nat) (args : List Expr) (us : List Level)
    (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule) (major : Expr) :
    m (Option Expr) :=
  match major.getAppFn with
  | .const cj usj =>
    match env.find? cj with
    | some (.ctorInfo cvj _ _) =>
      match findRule rules cj with
      | some rl =>
        if major.getAppArgs.length = rl.ctorParams + rl.nfields then
          iotaCertGate mode r env depth cv mI rP us args usj cvj rl major.getAppArgs >>=
            iotaRecFire cv us args rP rl major.getAppArgs
        else pure none
      | none => pure none
    | _ => pure none
  | _ => pure none

/-- `iotaRecI` with its certificate block named. -/
theorem iotaRecI_eq (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    iotaRecI mode r fe depth e =
    (match Expr.getAppFn e with
    | .const c us => do
      let cn ← pure c
      match fe.find? cn with
      | some (.recInfo cv mI rP rules) => do
        let args ← pure (Expr.getAppArgsC e)
        if args.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
            (Expr.peelPis (mI + 1) cv.type).isSome = true then do
          let bvar0 ← pure (Expr.mkBvar 0)
          let major ← prepareMajorI mode r fe depth cn rules (args.getD mI bvar0)
          match Expr.getAppFn major with
          | .const cj usj => do
            let cjn ← pure cj
            match fe.find? cjn with
            | some (.ctorInfo cvj _ _) =>
              match findRule rules cjn with
              | some rl => do
                let margs ← pure (Expr.getAppArgsC major)
                if margs.length = rl.ctorParams + rl.nfields then do
                  if ← certAtI mode
                      (iotaCertI r fe depth cv mI rP us args cj cjn usj cvj rl margs) then do
                    let rhs ← ruleRhsAtM fe c cj cn cjn us
                    let red ← mkAppNM rhs
                      (args.take rP ++ margs.drop rl.ctorParams)
                    pure (some red)
                  else pure none
                else pure none
              | none => pure none
            | _ => pure none
          | _ => pure none
        else pure none
      | _ => pure none
    | _ => pure none) := rfl

/-- `iotaRec` with its continuation past the major named. -/
theorem iotaRec_eq {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    iotaRec mode r env depth e =
    (match e.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.recInfo cv mI rP rules) =>
        if e.getAppArgs.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
            (Expr.peelPis (mI + 1) cv.type).isSome = true then
          prepareMajor mode r env depth c rules (e.getAppArgs.getD mI (.bvar 0)) >>=
            iotaRecK (mode := mode) r env depth e.getAppArgs us cv mI rP rules
        else pure none
      | _ => pure none
    | _ => pure none) := rfl

/-! ### The pure ι step's arms, one equation each -/

section PureArms

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m] {r : CoreFns m} {d : Nat}

theorem iotaRec_rec {e : Expr} {c : Name} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (h1 : e.getAppFn = .const c us)
    (h2 : env.find? c = some (.recInfo cv mI rP rules)) :
    iotaRec mode r env d e =
      if e.getAppArgs.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
          (Expr.peelPis (mI + 1) cv.type).isSome = true then
        prepareMajor mode r env d c rules (e.getAppArgs.getD mI (.bvar 0)) >>=
          iotaRecK (mode := mode) r env d e.getAppArgs us cv mI rP rules
      else pure none := by
  rw [iotaRec_eq]; simp only [h1, h2]
grind_pattern [conleche_grind] iotaRec_rec =>
    iotaRec mode r env d e, Expr.const c us, ConstantInfo.recInfo cv mI rP rules where
  guard e.getAppFn = .const c us
  guard env.find? c = some (.recInfo cv mI rP rules)

theorem iotaRec_notconst {e : Expr} (h : ∀ c us, e.getAppFn = .const c us → False) :
    iotaRec mode r env d e = pure none := by
  rw [iotaRec_eq]; split
  · next h' => exact (h _ _ h').elim
  · rfl

theorem iotaRec_notrec {e : Expr} {c : Name} {us : List Level} (h1 : e.getAppFn = .const c us)
    (h2 : ∀ cv mI rP rules, env.find? c = some (.recInfo cv mI rP rules) → False) :
    iotaRec mode r env d e = pure none := by
  rw [iotaRec_eq]; simp only [h1]
grind_pattern [conleche_grind] iotaRec_notrec => iotaRec mode r env d e, Expr.const c us where
  guard e.getAppFn = .const c us

theorem iotaRecK_ctor {args : List Expr} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {major : Expr} {cj : Name} {usj : List Level} {cvj : ConstantVal}
    {nP nF : Nat} {rl : RecRule} (h1 : major.getAppFn = .const cj usj)
    (h2 : env.find? cj = some (.ctorInfo cvj nP nF)) (h3 : findRule rules cj = some rl) :
    iotaRecK (mode := mode) r env d args us cv mI rP rules major =
      if major.getAppArgs.length = rl.ctorParams + rl.nfields then
        iotaCertGate mode r env d cv mI rP us args usj cvj rl major.getAppArgs >>=
          iotaRecFire cv us args rP rl major.getAppArgs
      else pure none := by
  rw [iotaRecK]; simp only [h1, h2, h3]
grind_pattern [conleche_grind] iotaRecK_ctor =>
    iotaRecK (mode := mode) r env d args us cv mI rP rules major, Expr.const cj usj,
      ConstantInfo.ctorInfo cvj nP nF, some rl where
  guard major.getAppFn = .const cj usj
  guard env.find? cj = some (.ctorInfo cvj nP nF)
  guard findRule rules cj = some rl

theorem iotaRecK_notconst {args : List Expr} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {major : Expr} (h : ∀ c us, major.getAppFn = .const c us → False) :
    iotaRecK (mode := mode) r env d args us cv mI rP rules major = pure none := by
  rw [iotaRecK]; split
  · next h' => exact (h _ _ h').elim
  · rfl

theorem iotaRecK_notctor {args : List Expr} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {major : Expr} {cj : Name} {usj : List Level}
    (h1 : major.getAppFn = .const cj usj)
    (h2 : ∀ cvj nP nF, env.find? cj = some (.ctorInfo cvj nP nF) → False) :
    iotaRecK (mode := mode) r env d args us cv mI rP rules major = pure none := by
  rw [iotaRecK]; simp only [h1]
grind_pattern [conleche_grind] iotaRecK_notctor =>
    iotaRecK (mode := mode) r env d args us cv mI rP rules major, Expr.const cj usj where
  guard major.getAppFn = .const cj usj

theorem iotaRecK_norule {args : List Expr} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {major : Expr} {cj : Name} {usj : List Level} {cvj : ConstantVal}
    {nP nF : Nat} (h1 : major.getAppFn = .const cj usj)
    (h2 : env.find? cj = some (.ctorInfo cvj nP nF)) (h3 : findRule rules cj = none) :
    iotaRecK (mode := mode) r env d args us cv mI rP rules major = pure none := by
  rw [iotaRecK]; simp only [h1, h2, h3]
grind_pattern [conleche_grind] iotaRecK_norule =>
    iotaRecK (mode := mode) r env d args us cv mI rP rules major, Expr.const cj usj,
      ConstantInfo.ctorInfo cvj nP nF where
  guard major.getAppFn = .const cj usj
  guard env.find? cj = some (.ctorInfo cvj nP nF)
  guard findRule rules cj = none

theorem iotaCertGate_of (hμ : mode.verifiedChecks = true) (r : CoreFns m) (env : Env)
    (depth : Nat) (cv : ConstantVal) (mI rP : Nat) (us : List Level) (args : List Expr)
    (usj : List Level) (cvj : ConstantVal) (rl : RecRule) (margs : List Expr) :
    iotaCertGate mode r env depth cv mI rP us args usj cvj rl margs =
      iotaCertP r env depth cv mI rP us args usj cvj rl margs := by
  simp [iotaCertGate, hμ]

omit [MonadExceptOf CheckError m] in
@[conleche_grind =] theorem iotaRecFire_true (cv : ConstantVal) (us : List Level)
    (args : List Expr) (rP : Nat) (rl : RecRule) (margs : List Expr) :
    (iotaRecFire cv us args rP rl margs true : m (Option Expr)) =
      pure (some (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
        (args.take rP ++ margs.drop rl.ctorParams))) := rfl

omit [MonadExceptOf CheckError m] in
@[conleche_grind =] theorem iotaRecFire_false (cv : ConstantVal) (us : List Level)
    (args : List Expr) (rP : Nat) (rl : RecRule) (margs : List Expr) :
    (iotaRecFire cv us args rP rl margs false : m (Option Expr)) = pure none := rfl

end PureArms

/-! ### The ι walks -/

/-- The cached pin instantiations are the nested comparand's mapped
list. -/
theorem pinArgsC_spec (lps : List Name) (us : List Level) :
    ∀ (ps : List Expr) {s₀ : CState}, CSOK mode env s₀ → ∀ (args : List Expr) (t : Nat),
      ⦃fun s => s = s₀⦄ pinArgsI lps us args t ps
      ⦃fun rs s' => CSOK mode env s' ∧ rs = ps.map (pinInst lps us args t); ⊤⦄
  | [], _, _, _, _ => by
    sym only [conleche_grind, List.map_nil] => vcgen [pinArgsI] <;> finish
  | _ :: ps, _, _, _, _ => by
    sym only [conleche_grind, List.map_cons, pinInst] =>
      vcgen [pinArgsI, instLevelParamsM, instSpineM, pinArgsC_spec lps us ps] <;> finish

/-- The canonical-index comparison (the ι batch) simulates its fueled
original. -/
theorem iotaIndexOkC_spec (ih : SSimC mode env f) {d : Nat} {mI rP cnP : Nat}
    {ty : Expr} {margs idx : List Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hwty : Expr.WScoped d ty) (hwm : AllWS d margs) (hwi : AllWS d idx) :
    ⦃fun s => s = s₀⦄
      iotaIndexOkI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d mI rP cnP ty margs idx
    ⦃fun b s' => CSOK mode env s' ∧
      Runs (iotaIndexOk (fueledFns mode env) env d mI rP cnP ty margs idx) b; ⊤⦄ := by
  sym only [conleche_grind, iotaIndexOk] =>
    vcgen [iotaIndexOkI, piResidualM_spec hs, defEqListC_spec ih] <;> finish

/-- The case-3 certificate block simulates its fueled original. -/
theorem iotaCertC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {s₀ : CState}
    (hs : CSOK mode env s₀) (cv : ConstantVal) (mI rP : Nat) (us : List Level)
    {args : List Expr} (hargs : AllWS d args) (cj cjn : Name) (usj : List Level)
    {cvj : ConstantVal} (hfj : ctorVal? env cjn = some cvj) {rl : RecRule}
    (hrl : OptRuleOK (some rl)) {margs : List Expr} (hm : AllWS d margs) :
    ⦃fun s => s = s₀⦄
      iotaCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d cv mI rP us args cj cjn usj cvj
        rl margs
    ⦃fun b s' => CSOK mode env s' ∧
      Runs (iotaCertP (fueledFns mode env) env d cv mI rP us args usj cvj rl margs) b; ⊤⦄ := by
  obtain ⟨nP, nF, hfj⟩ := ctorVal?_some hfj
  sym only [conleche_grind, iotaCertP, constTyOf, ConstantInfo.toConstantVal,
      Option.isSome_some, EnvWF.ctorTy_closed henv hfj] =>
    vcgen [iotaCertI, liftFueled, substLevelTreesM, isEquivListLM_spec hs,
      pinArgsC_spec (mode := mode) (env := env),
      defEqListC_spec ih, constTyAtM_spec (mode := mode) (env := env),
      iotaCertsFullC_spec ih, iotaIndexOkC_spec ih] <;> finish

/-- The ι step simulates its fueled original. -/
theorem iotaRecC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) {d : Nat} {i : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ iotaRecI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i
    ⦃fun o s' => CSOK mode env s' ∧ Runs (iotaRec mode (fueledFns mode env) env d i) o ∧
      OptWS d o; ⊤⦄ := by
  sym only [conleche_grind, iotaRec_notconst, iotaRecK_notconst, Option.isSome_some,
      iotaCertGate_of hμ, → EnvWF.rules_ok henv] =>
    vcgen [iotaRecI_eq, certAtI, mkAppNM, prepareMajorC_spec hμ ih,
      iotaCertC_spec ih henv (mode := mode) (env := env),
      ruleRhsAtM_spec (mode := mode) (env := env)] <;> finish

end Walks2

end ConLeche.Cached
