module

import ConLeche.Cached.CoreC
public import ConLeche.Verify.Cached.GuardsC
public import ConLeche.Verify.Cached.SimCEff
public import ConLeche.Verify.Cached.Grind
import ConLeche.Verify.InstSpine

public section

/-!
# Cached body walks, part 1: list helpers and small twins (task #163)

Per-helper simulation walks: each cached twin
(`ConLeche/Cached/CoreC.lean`) simulates its `Expr` original at the
fueled record on well-scoped inputs, stated as a `Std.WP` triple whose
post names the cached value as the fueled answer (`Runs`) and proved by
`vcgen` and `grind` (`ConLeche/Verify/Cached/Grind.lean`).  The list
loops (`defEqListC_spec`, `iotaCertsFullCAux_spec`) recurse one
`sym … => vcgen … <;> finish` per list arm, the induction hypothesis a
term in `vcgen`'s list.  A `…_sim`/`…_eff` corollary restates a walk for
the callers that are still stated as `SimC`/`CEff`.

The module also declares the knot's hypothesis `SSimC` and, after it,
the triple forms of its fields and of the small effects, with the
`grind` vocabulary the walks of this module and `DiscC2.lean` add.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-- The cached conditional simulation at fuel `f`: every cached entry point simulates the corresponding fueled family on
well-scoped inputs.  Declared here so the per-body walks can
take it as their induction hypothesis; the knot batch proves it at
every fuel. -/
structure SSimC (mode : CheckMode) (env : Env) (f : Nat) : Prop where
  whnfCore : ∀ {c : Bool} {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).whnfCore c d i)
      ((fueledFns mode env).whnfCore c d e)
  whnf : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).whnf d i)
      ((fueledFns mode env).whnf d e)
  infer : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).infer d i)
      ((fueledFns mode env).infer d e)
  defeq : ∀ {s₀ : CState} {d : Nat} {i j : Expr} {a b : Expr},
    CSOK mode env s₀ → RelC i a → RelC j b →
    Expr.WScoped d a → Expr.WScoped d b →
    SimC mode env s₀ RelVC
      ((coreKnotI mode (mkFEnv env) f).defeq d i j)
      ((fueledFns mode env).defeq d a b)
  /-- the eager slot (task #353): the eager tower's comparison, under
  its own memos, simulates the fueled eager slot -/
  defeqE : ∀ {s₀ : CState} {d : Nat} {i j : Expr} {a b : Expr},
    CSOK mode env s₀ → RelC i a → RelC j b →
    Expr.WScoped d a → Expr.WScoped d b →
    SimC mode env s₀ RelVC
      ((coreKnotI mode (mkFEnv env) f).defeqE d i j)
      ((fueledFns mode env).defeqE d a b)
  /-- the io slot (task #172 B4): the memoized knot's `inferIO` entry
  simulates the fueled io-slot family -/
  inferIO : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).inferIO d i)
      ((fueledFns mode env).inferIO d e)

/-- The base case: fuel `0` throws everywhere. -/
theorem ssimC_zero (env : Env) : SSimC mode env 0 :=
  { whnfCore := fun _ _ _ => SimC.throw
    whnf := fun _ _ _ => SimC.throw
    infer := fun _ _ _ => SimC.throw
    defeq := fun _ _ _ _ _ => SimC.throw
    defeqE := fun _ _ _ _ _ => SimC.throw
    inferIO := fun _ _ _ => SimC.throw }

/-! ## Vocabulary candidates (for Grind.lean)

The triple forms of a data-valued simulation (`RelVC`: the cached value
IS the pure answer, no side condition) and of the knot's entry points
(`SSimC`'s fields), for `vcgen`'s list. -/

/-- A simulation at `RelVC` is a triple whose post names the cached
value as the pure side's answer. -/
theorem SimC.triple_eq {env : Env} {β : Type} {s₀ : CState} {c : CheckCM β} {p : FueledM β}
    (h : SimC mode env s₀ RelVC c p) :
    ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode env s' ∧ Runs p v; ⊤⦄ := by
  refine triple_iff_run.mpr fun v' s' hr => ?_
  obtain ⟨hs', v, rfl, F, hF⟩ := h v' s' hr
  exact ⟨hs', F, hF⟩

/-- The converse of `SimC.triple_eq`. -/
theorem SimC.of_triple_eq {env : Env} {β : Type} {s₀ : CState} {c : CheckCM β}
    {p : FueledM β}
    (h : ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode env s' ∧ Runs p v; ⊤⦄) :
    SimC mode env s₀ RelVC c p := by
  intro v' s' hr
  obtain ⟨hs', F, hF⟩ := triple_iff_run.mp h v' s' hr
  exact ⟨hs', v', rfl, F, hF⟩

section SSimCSpecs

variable {env : Env} {f : Nat}

theorem SSimC.whnfCore_spec (ih : SSimC mode env f) {c : Bool} {s₀ : CState} {d : Nat}
    {i : Expr} (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) f).whnfCore c d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).whnfCore c d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  (ih.whnfCore hs rfl hw).triple relEC_inv

theorem SSimC.whnf_spec (ih : SSimC mode env f) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) f).whnf d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).whnf d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  (ih.whnf hs rfl hw).triple relEC_inv

theorem SSimC.infer_spec (ih : SSimC mode env f) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) f).infer d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).infer d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  (ih.infer hs rfl hw).triple relEC_inv

theorem SSimC.inferIO_spec (ih : SSimC mode env f) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) f).inferIO d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).inferIO d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  (ih.inferIO hs rfl hw).triple relEC_inv

theorem SSimC.defeq_spec (ih : SSimC mode env f) {s₀ : CState} {d : Nat} {i j : Expr}
    (hs : CSOK mode env s₀) (hwi : Expr.WScoped d i) (hwj : Expr.WScoped d j) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) f).defeq d i j
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).defeq d i j) r; ⊤⦄ :=
  (ih.defeq hs rfl rfl hwi hwj).triple_eq

theorem SSimC.defeqE_spec (ih : SSimC mode env f) {s₀ : CState} {d : Nat} {i j : Expr}
    (hs : CSOK mode env s₀) (hwi : Expr.WScoped d i) (hwj : Expr.WScoped d j) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) f).defeqE d i j
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).defeqE d i j) r; ⊤⦄ :=
  (ih.defeqE hs rfl rfl hwi hwj).triple_eq

end SSimCSpecs

/-- `instListM_eff` as a triple. -/
theorem instListM_spec {env : Env} {s₀ : CState} (hs : CSOK mode env s₀) (e : Expr)
    (vs : List Expr) (d : Nat) :
    ⦃fun s => s = s₀⦄ instListM e vs d
    ⦃fun r s' => CSOK mode env s' ∧ r = e.instantiateList vs d; ⊤⦄ :=
  (instListM_eff hs (RelC.refl e) (show RelCL vs vs from rfl) :
    CEff mode env s₀ (fun i => i = e.instantiateList vs d) _).triple

/-- The level-instantiated value of the stored definition `n`, where
there is one: what `constValAtM` answers. -/
@[expose] def constValAt? (env : Env) (n : Name) (us : List Level) : Option Expr :=
  match env.find? n with
  | some (.defnInfo cv v _) => some (v.instantiateLevelParams cv.levelParams us)
  | _ => none

/-- `constValAtM` answers the stored definition's instantiated value
(a run succeeds only at a stored definition: a hit is backed by the
invariant, a miss elsewhere throws). -/
theorem constValAtM_spec {env : Env} {s₀ : CState} (hs : CSOK mode env s₀) (nI n : Name)
    (us : List Level) :
    ⦃fun s => s = s₀⦄ constValAtM (mkFEnv env) nI n us
    ⦃fun r s' => CSOK mode env s' ∧ constValAt? env n us = some r; ⊤⦄ := by
  refine triple_iff_run.mpr fun r s' hr => ?_
  have hdef : ∃ cv v h, env.find? n = some (.defnInfo cv v h) := by
    cases hl : s₀.constValAt[(n, us)]? with
    | some i =>
      obtain ⟨cv, v, h, hf, -⟩ := hs.constVal n us i hl
      exact ⟨cv, v, h, hf⟩
    | none =>
      -- a miss: off a stored definition the run throws
      cases hf : env.find? n with
      | some ci =>
        cases ci <;> first | exact ⟨_, _, _, rfl⟩ | (exfalso; revert hr; simp [constValAtM,
          bind, StateT.bind, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind,
          pure, Except.pure, hl, mkFEnv_find?, hf] <;> exact fun h => nomatch h)
      | none =>
        exfalso; revert hr; simp [constValAtM, bind, StateT.bind, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, pure, Except.pure, hl,
          mkFEnv_find?, hf] <;> exact fun h => nomatch h
  obtain ⟨cv, v, h, hf⟩ := hdef
  obtain ⟨hs', hrel⟩ := constValAtM_eff hs hf r s' hr
  exact ⟨hs', by rw [constValAt?, hf, show r = _ from hrel]⟩

/-- `isEquivListLM_eff` as a triple. -/
theorem isEquivListLM_spec {env : Env} {s₀ : CState} (hs : CSOK mode env s₀)
    (ls rs : List Level) :
    ⦃fun s => s = s₀⦄ isEquivListLM ls rs
    ⦃fun ob s' => CSOK mode env s' ∧ ob = Level.isEquivList ls rs; ⊤⦄ :=
  (isEquivListLM_eff hs).triple

/-- `isEquivLM_eff` as a triple. -/
theorem isEquivLM_spec {env : Env} {s₀ : CState} (hs : CSOK mode env s₀) (l r : Level) :
    ⦃fun s => s = s₀⦄ isEquivLM l r
    ⦃fun ob s' => CSOK mode env s' ∧ ob = Level.isEquiv l r; ⊤⦄ :=
  (isEquivLM_eff hs l r).triple

/-- The fuel-exhaustion lift is the same on both sides. -/
theorem liftFueled_spec {env : Env} {α : Type} {s₀ : CState} (hs : CSOK mode env s₀)
    (what : String) (o : Option α) :
    ⦃fun s => s = s₀⦄ (liftFueled what o : CheckCM α)
    ⦃fun a s' => CSOK mode env s' ∧ Runs (liftFueled what o) a; ⊤⦄ :=
  (SimC.liftFueled what o hs).triple_eq

/-- The cached index's lookup function is the environment's (unapplied,
for the head-symbol readers that take it as an argument). -/
theorem mkFEnv_find?_eq (env : Env) : FEnv.find? (mkFEnv env) = env.find? :=
  funext (mkFEnv_find? env)

/-- `inst1M_eff` as a triple. -/
theorem inst1M_spec {env : Env} {s₀ : CState} (hs : CSOK mode env s₀) (e v : Expr) (d : Nat) :
    ⦃fun s => s = s₀⦄ inst1M e v d
    ⦃fun r s' => CSOK mode env s' ∧ r = e.instantiate1 v d; ⊤⦄ :=
  (inst1M_eff hs (RelC.refl e) (RelC.refl v) :
    CEff mode env s₀ (fun i => i = e.instantiate1 v d) _).triple

@[conleche_grind =] theorem wscoped_fvar_eq (k i : Nat) (ty : Expr) :
    Expr.WScoped k (.fvar i ty) = (i < k ∧ Expr.WScoped i ty) := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_forallE_eq (d : Nat) (ty body : Expr) :
    Expr.WScoped d (.forallE ty body) = (Expr.WScoped d ty ∧ Expr.WScoped d body) := by
  rw [Expr.WScoped]

/-- One more binder in scope keeps a term well scoped. -/
theorem wscoped_succ {d : Nat} {e : Expr} (h : Expr.WScoped d e) : Expr.WScoped (d + 1) e :=
  h.mono (Nat.le_succ d)
grind_pattern [conleche_grind] wscoped_succ => Expr.WScoped d e, Expr.WScoped (d + 1) e

/-- Opening a binder at the next free variable. -/
theorem wscoped_open {d : Nat} {ty e : Expr} (k : Nat) (hty : Expr.WScoped d ty)
    (he : Expr.WScoped d e) : Expr.WScoped (d + 1) (e.instantiate1 (.fvar d ty) k) :=
  Expr.WScoped.instantiate1 hty k he
grind_pattern [conleche_grind] wscoped_open =>
  Expr.WScoped d e, e.instantiate1 (.fvar d ty) k

/-- A prefix of well-scoped terms is well scoped. -/
theorem AllWS.take {d : Nat} {xs : List Expr} (h : AllWS d xs) (k : Nat) :
    AllWS d (xs.take k) :=
  fun x hx => h x (List.mem_of_mem_take hx)
grind_pattern [conleche_grind] AllWS.take => AllWS d xs, xs.take k

/-- A suffix of well-scoped terms is well scoped. -/
theorem AllWS.drop {d : Nat} {xs : List Expr} (h : AllWS d xs) (k : Nat) :
    AllWS d (xs.drop k) :=
  fun x hx => h x (List.mem_of_mem_drop hx)
grind_pattern [conleche_grind] AllWS.drop => AllWS d xs, xs.drop k

/-- The `.proj T i b` nodes over the indices `l` (a named function, so
that its scope fact has a pattern: a `List.map` pattern loses its
lambda). -/
@[expose] def projsOf (T : Name) (b : Expr) (l : List Nat) : List Expr :=
  l.map fun i => Expr.proj T i b

@[conleche_grind =] theorem projsOf_nil (T : Name) (b : Expr) : projsOf T b [] = [] := rfl

@[conleche_grind =] theorem projsOf_cons (T : Name) (b : Expr) (i : Nat) (l : List Nat) :
    projsOf T b (i :: l) = Expr.proj T i b :: projsOf T b l := rfl

@[conleche_grind =] theorem etaProjs_eq (T : Name) (b : Expr) (n : Nat) :
    etaProjs T b n = projsOf T b (List.range n) := rfl

/-- The projections of a well-scoped term are well scoped. -/
theorem allWS_projsOf {d : Nat} {b : Expr} (T : Name) (l : List Nat) (h : Expr.WScoped d b) :
    AllWS d (projsOf T b l) := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  rw [Expr.WScoped]; exact h
grind_pattern [conleche_grind] allWS_projsOf => Expr.WScoped d b, projsOf T b l

/-- The constructor-shape gate reads the same store on both sides. -/
@[conleche_grind =] theorem etaCtorShapeC_eq (env : Env) (e : Expr) :
    etaCtorShapeC (mkFEnv env) e = etaCtorShape env e :=
  etaCtorShapeC_spec' rfl

/-- A well-scoped spine's arguments are well scoped. -/
theorem allWS_getAppArgs {d : Nat} {e : Expr} (h : Expr.WScoped d e) :
    AllWS d e.getAppArgs :=
  h.getAppArgs
grind_pattern [conleche_grind] allWS_getAppArgs => Expr.WScoped d e, e.getAppArgs

@[conleche_grind =] theorem AllWS.reverse_eq (d : Nat) (xs : List Expr) :
    AllWS d xs.reverse = AllWS d xs := by
  simp [AllWS]

theorem relOC_diag {d : Nat} : ∀ o : Option Expr, OptWS d o → RelOC d o o
  | none, _ => trivial
  | some _, h => ⟨rfl, h⟩

@[conleche_grind =] theorem OptWS.none_eq (d : Nat) : OptWS d none = True := rfl

@[conleche_grind =] theorem wscoped_lit_eq (d : Nat) (l : Literal) :
    Expr.WScoped d (.lit l) = True := by
  rw [Expr.WScoped]

/-- A native `Nat` operation's answer is closed. -/
@[conleche_grind .] theorem optWS_natOpResult (d : Nat) (c : Name) (a b : Nat) :
    OptWS d (natOpResult c a b) := by
  cases h : natOpResult c a b with
  | none => trivial
  | some e =>
    rcases natOpResult_shape h with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> simp [OptWS, Expr.WScoped]

/-- The domain of a well-scoped instantiated `∀` is well scoped. -/
theorem wscoped_piDom {d : Nat} {dom body : Expr} {acc : List Expr}
    (hw : Expr.WScoped d ((Expr.forallE dom body).instantiateList acc)) :
    Expr.WScoped d (dom.instantiateList acc) := by
  rw [Expr.instantiateList, Expr.WScoped] at hw
  exact hw.1
grind_pattern [conleche_grind] wscoped_piDom =>
  Expr.WScoped d ((Expr.forallE dom body).instantiateList acc), dom.instantiateList acc

/-- The peel step's scope under a `∀` (`wscoped_peel`'s twin). -/
theorem wscoped_piPeel {d : Nat} {dom body a : Expr} {acc : List Expr}
    (hw : Expr.WScoped d ((Expr.forallE dom body).instantiateList acc))
    (ha : Expr.WScoped d a) :
    Expr.WScoped d (body.instantiateList (a :: acc)) := by
  rw [Expr.instantiateList, Expr.WScoped] at hw
  rw [Expr.instantiateList_cons]
  exact Expr.WScoped.instantiate1_gen ha 0 hw.2
grind_pattern [conleche_grind] wscoped_piPeel =>
  Expr.WScoped d ((Expr.forallE dom body).instantiateList acc),
  body.instantiateList (a :: acc)

section Walks

variable {env : Env} {f : Nat}

/-- The full-grade argument check simulates its fueled original: the
same argument, so the same tower (task #353). -/
theorem defeqArgC_spec (ih : SSimC mode env f) {s₀ : CState} {d : Nat} {a ta ty : Expr}
    (hs : CSOK mode env s₀) (hwta : Expr.WScoped d ta) (hwty : Expr.WScoped d ty) :
    ⦃fun s => s = s₀⦄ defeqArgI (coreKnotI mode (mkFEnv env) f) d a ta ty
    ⦃fun v s' => CSOK mode env s' ∧ Runs (defeqArg (fueledFns mode env) d a ta ty) v; ⊤⦄ := by
  sym only [conleche_grind, defeqArg] =>
    vcgen [defeqArgI, ih.defeq_spec hs, ih.defeqE_spec hs] <;> finish

/-- `defeqArgC_spec` as a simulation, for the unconverted callers. -/
theorem defeqArgC_sim (ih : SSimC mode env f) {s₀ : CState} {d : Nat}
    {a ta ty : Expr} {xa xta xty : Expr} (hs : CSOK mode env s₀)
    (ha : RelC a xa) (hta : RelC ta xta) (hty : RelC ty xty)
    (hwta : Expr.WScoped d xta) (hwty : Expr.WScoped d xty) :
    SimC mode env s₀ RelVC
      (defeqArgI (coreKnotI mode (mkFEnv env) f) d a ta ty)
      (defeqArg (fueledFns mode env) d xa xta xty) := by
  subst ha hta hty; exact SimC.of_triple_eq (defeqArgC_spec ih hs hwta hwty)

/-- `defEqListI`'s fall-through arms as unconditional equations
(`vcgen` cannot use the conditional `defEqListI.eq_3`). -/
theorem defEqListI_nil_cons (r : CoreFnsI) (fe : FEnv) (d : Nat) (b : Expr) (bs : List Expr) :
    defEqListI r fe d [] (b :: bs) = pure false := rfl

theorem defEqListI_cons_nil (r : CoreFnsI) (fe : FEnv) (d : Nat) (a : Expr) (as : List Expr) :
    defEqListI r fe d (a :: as) [] = pure false := rfl

/-- The pure side's fall-through arms likewise: `grind` does not
discharge the premise `∀ a as b bs, True` that `defEqList.eq_3` reduces
to. -/
theorem defEqList_nil_cons (env : Env) (d : Nat) (b : Expr) (bs : List Expr) :
    defEqList (fueledFns mode env) env d [] (b :: bs) = pure false := rfl

theorem defEqList_cons_nil (env : Env) (d : Nat) (a : Expr) (as : List Expr) :
    defEqList (fueledFns mode env) env d (a :: as) [] = pure false := rfl

/-- The pairwise definitional-equality helper simulates its fueled
original on well-scoped lists. -/
theorem defEqListC_spec (ih : SSimC mode env f) {d : Nat} :
    ∀ {args brgs : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      AllWS d args → AllWS d brgs →
      ⦃fun s => s = s₀⦄ defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d args brgs
      ⦃fun v s' => CSOK mode env s' ∧
          Runs (defEqList (fueledFns mode env) env d args brgs) v; ⊤⦄
  | [], [], _, _, _, _ => by
    sym only [conleche_grind, defEqList.eq_1] =>
      vcgen [defEqListI] <;> finish
  | _ :: as, _ :: _, _, _, _, _ => by
    sym only [conleche_grind, defEqList.eq_2] =>
      vcgen [defEqListI, ih.defeq_spec, defEqListC_spec ih (args := as)] <;> finish
  | [], _ :: _, _, _, _, _ => by
    sym only [conleche_grind, defEqList_nil_cons] =>
      vcgen [defEqListI_nil_cons] <;> finish
  | _ :: _, [], _, _, _, _ => by
    sym only [conleche_grind, defEqList_cons_nil] =>
      vcgen [defEqListI_cons_nil] <;> finish

/-- `defEqListC_spec` as a simulation, for the unconverted callers. -/
theorem defEqListC_sim (ih : SSimC mode env f) {d : Nat} {args xs brgs ys : List Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hargs : RelCL args xs) (hbrgs : RelCL brgs ys)
    (hwx : ∀ x ∈ xs, Expr.WScoped d x) (hwy : ∀ y ∈ ys, Expr.WScoped d y) :
    SimC mode env s₀ RelVC
      (defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d args brgs)
      (defEqList (fueledFns mode env) env d xs ys) :=
  by subst hargs hbrgs; exact SimC.of_triple_eq (defEqListC_spec ih hs hwx hwy)

/-- `iotaCertsFullIAux`'s step as one unconditional equation (the
equation compiler's fall-through arm is conditional). -/
theorem iotaCertsFullIAux_cons (r : CoreFnsI) (fe : FEnv) (d : Nat) (ty : Expr)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    iotaCertsFullIAux r fe d ty acc (a :: rest) =
      match ty, acc with
      | .forallE dom body, acc => instListM dom acc >>= fun dom' =>
          r.infer d a >>= fun ta => r.defeq d ta dom' >>= fun c =>
          if c then iotaCertsFullIAux r fe d body (a :: acc) rest else pure false
      | .bvar _, [] => pure false
      | .bvar k, acc@(_ :: _) => instListM (.bvar k) acc >>= fun ty' =>
          iotaCertsFullIAux r fe d ty' [] (a :: rest)
      | _, _ => pure false := by
  cases ty <;> cases acc <;> rw [iotaCertsFullIAux] <;> (try rfl) <;> (intros; contradiction)

/-- The pure certificate loop at a bulk-instantiated telescope, stepped
in the cached loop's shape. -/
theorem iotaCertsFull_instList_cons {m : Type → Type} [Monad m] (r : CoreFns m) (env : Env)
    (d : Nat) (ty : Expr) (acc : List Expr) (a : Expr) (rest : List Expr) :
    iotaCertsFull r env d (ty.instantiateList acc) (a :: rest) =
      match ty, acc with
      | .forallE dom body, acc =>
          r.infer d a >>= fun ta => r.defeq d ta (dom.instantiateList acc) >>= fun c =>
          if c then iotaCertsFull r env d (body.instantiateList (a :: acc)) rest
          else pure false
      | .bvar _, [] => pure false
      | .bvar k, acc@(_ :: _) =>
          iotaCertsFull r env d ((Expr.bvar k).instantiateList acc) (a :: rest)
      | _, _ => pure false := by
  cases ty with
  | forallE dom body =>
    rw [Expr.instantiateList, iotaCertsFull.eq_2]; dsimp only; rw [Expr.instantiateList_cons]
  | bvar k => cases acc with
    | nil => rw [Expr.instantiateList_nil]; rfl
    | cons => rfl
  | _ => rw [Expr.instantiateList]; cases acc <;> rfl

/-- The bulk-accumulating full-grade certificate loop (task #342 L10)
simulates its fueled original. -/
theorem iotaCertsFullCAux_spec (ih : SSimC mode env f) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {acc : List Expr} {s₀ : CState},
      CSOK mode env s₀ → Expr.WScoped d (ty.instantiateList acc) → AllWS d args →
      ⦃fun s => s = s₀⦄
        iotaCertsFullIAux (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty acc args
      ⦃fun v s' => CSOK mode env s' ∧
          Runs (iotaCertsFull (fueledFns mode env) env d (ty.instantiateList acc) args) v; ⊤⦄
  | [], _, _, _, _, _, _ => by
    sym only [conleche_grind, iotaCertsFull.eq_1] =>
      vcgen [iotaCertsFullIAux.eq_1] <;> finish
  | _ :: as, _, [], _, hs, _, _ => by
    sym only [conleche_grind, iotaCertsFull_instList_cons] =>
      vcgen [iotaCertsFullIAux_cons, instListM_spec hs, ih.infer_spec, ih.defeq_spec,
        iotaCertsFullCAux_spec ih (args := as)] <;> finish
  | a :: as, _, _ :: _, _, hs, _, _ => by
    sym only [conleche_grind, iotaCertsFull_instList_cons, Expr.instantiateList_nil] =>
      vcgen [iotaCertsFullIAux_cons, instListM_spec hs, ih.infer_spec, ih.defeq_spec,
        iotaCertsFullCAux_spec ih (args := as),
        iotaCertsFullCAux_spec ih (args := a :: as) (acc := [])] <;> finish
termination_by args _ acc => (args.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- `iotaCertsFullI` simulates its fueled original. -/
theorem iotaCertsFullC_spec (ih : SSimC mode env f) {d : Nat} {args : List Expr} {ty : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hw : Expr.WScoped d ty) (hargs : AllWS d args) :
    ⦃fun s => s = s₀⦄ iotaCertsFullI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty args
    ⦃fun v s' => CSOK mode env s' ∧
        Runs (iotaCertsFull (fueledFns mode env) env d ty args) v; ⊤⦄ := by
  sym only [conleche_grind, Expr.instantiateList_nil] =>
    vcgen [iotaCertsFullI, iotaCertsFullCAux_spec ih] <;> finish

/-- `iotaCertsFullC_spec` as a simulation, for the unconverted callers. -/
theorem iotaCertsFullC_sim (ih : SSimC mode env f) {d : Nat} {args xs : List Expr}
    {ty tyx : Expr} {s₀ : CState} (hs : CSOK mode env s₀) (hty : RelC ty tyx)
    (hwty : Expr.WScoped d tyx) (hargs : RelCL args xs) (hwargs : ∀ x ∈ xs, Expr.WScoped d x) :
    SimC mode env s₀ RelVC
      (iotaCertsFullI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty args)
      (iotaCertsFull (fueledFns mode env) env d tyx xs) := by
  subst hty hargs; exact SimC.of_triple_eq (iotaCertsFullC_spec ih hs hwty hwargs)

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- `ensureSortI` simulates its fueled original. -/
theorem ensureSortC_spec (ih : SSimC mode env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ ensureSortI (coreKnotI mode (mkFEnv env) f) d i
    ⦃fun v s' => CSOK mode env s' ∧ Runs (ensureSort (fueledFns mode env) env d i) v; ⊤⦄ := by
  sym only [conleche_grind, ensureSort] =>
    vcgen [ensureSortI, ih.whnf_spec] <;> finish

/-- `ensureSortC_spec` as a simulation, for the unconverted callers. -/
theorem ensureSortC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ RelVC (ensureSortI (coreKnotI mode (mkFEnv env) f) d i)
      (ensureSort (fueledFns mode env) env d e) := by
  subst hden; exact SimC.of_triple_eq (ensureSortC_spec ih hs hw)

/-- The cached twin computes the spec's `litToCtorIfNat`. -/
theorem litToCtorIfNatC_spec {s₀ : CState} (hs : CSOK mode env s₀) (i : Expr) :
    ⦃fun s => s = s₀⦄ litToCtorIfNatI (mkFEnv env) i
    ⦃fun r s' => CSOK mode env s' ∧ r = litToCtorIfNat env i; ⊤⦄ := by
  sym only [conleche_grind, litToCtorIfNat, natLitSupportedF_eq] =>
    vcgen [litToCtorIfNatI] <;> finish

/-- The cached twin computes the spec's pure `unfoldDefinition`. -/
theorem unfoldDefinitionC_spec {s₀ : CState} (hs : CSOK mode env s₀) (i : Expr) :
    ⦃fun s => s = s₀⦄ unfoldDefinitionI (mkFEnv env) i
    ⦃fun o s' => CSOK mode env s' ∧ o = unfoldDefinition env i; ⊤⦄ := by
  sym only [conleche_grind, unfoldDefinition, constValAt?, mkFEnv_find?, Expr.getAppArgsC_spec] =>
    vcgen [unfoldDefinitionI, mkAppNM, constValAtM_spec hs] <;> finish

/-- `unfoldDefinitionC_spec` as an effect, for the unconverted callers. -/
theorem unfoldDefinitionC_eff {s₀ : CState} (hs : CSOK mode env s₀)
    {i : Expr} {e : Expr} (hden : RelC i e) :
    CEff mode env s₀ (fun o => OptEr o (unfoldDefinition env e))
      (unfoldDefinitionI (mkFEnv env) i) := by
  subst hden
  intro v s' hr
  obtain ⟨hs', rfl⟩ := triple_iff_run.mp (unfoldDefinitionC_spec hs i) v s' hr
  exact ⟨hs', by cases unfoldDefinition env i <;> trivial⟩

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-- A twin-only effect against a pure fueled value. -/
theorem SimC.of_eff {s₀ : CState} {β α : Type} {Q : β → Prop}
    {P : β → α → Prop} {c : CheckCM β}
    (h : CEff mode env s₀ Q c) (a : α) (hPa : ∀ b, Q b → P b a) :
    SimC mode env s₀ P c (pure a) := by
  intro v' s' hr
  obtain ⟨hs', hQ⟩ := h v' s' hr
  exact ⟨hs', a, hPa v' hQ, 0, rfl⟩

/-- `litMajorToCtorI` simulates its fueled original. -/
theorem litMajorToCtorC_spec (ih : SSimC mode env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ litMajorToCtorI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs (litMajorToCtor (fueledFns mode env) env d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, litMajorToCtor, strLitSupportedF_eq, strLitToConstructor_WScoped,
      litToCtorIfNat_WScoped] =>
    vcgen [litMajorToCtorI, litToCtorIfNatC_spec hs, ih.whnf_spec] <;> finish

/-- `litMajorToCtorC_spec` as a simulation, for the unconverted callers. -/
theorem litMajorToCtorC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d)
      (litMajorToCtorI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (litMajorToCtor (fueledFns mode env) env d e) := by
  subst hden; exact SimC.of_triple relEC_diag (litMajorToCtorC_spec ih hs hw)

/-- `projLitToCtorI` simulates its fueled original. -/
theorem projLitToCtorC_spec (ih : SSimC mode env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ projLitToCtorI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs (projLitToCtor (fueledFns mode env) env d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, projLitToCtor, strLitSupportedF_eq, strLitToConstructor_WScoped] =>
    vcgen [projLitToCtorI, ih.whnf_spec] <;> finish

/-- `projLitToCtorC_spec` as a simulation, for the unconverted callers. -/
theorem projLitToCtorC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d)
      (projLitToCtorI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (projLitToCtor (fueledFns mode env) env d e) := by
  subst hden; exact SimC.of_triple relEC_diag (projLitToCtorC_spec ih hs hw)

/-- `defeqSpineI` simulates its fueled original. -/
theorem defeqSpineC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ defeqSpineI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs (defeqSpine (fueledFns mode env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, defeqSpine, Expr.getAppArgsC_spec] =>
    vcgen [defeqSpineI, isEquivListLM_spec hs, defEqListC_spec ih] <;> finish

/-- `defeqSpineC_spec` as a simulation, for the unconverted callers. -/
theorem defeqSpineC_sim (ih : SSimC mode env f) {d : Nat} {i j : Expr}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (defeqSpineI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (defeqSpine (fueledFns mode env) env d a b) := by
  subst hdena hdenb; exact SimC.of_triple_eq (defeqSpineC_spec ih hs hwa hwb)

end Walks3

section Walks4

variable {env : Env} {f : Nat}

/-- `reduceNat`'s dispatch in the cached twin's nested shape, one
constructor per level (the definition's overlapping wildcard gives a
conditional equation whose premise `grind` cannot discharge from the
nested arms' hypotheses). -/
theorem reduceNat_nested {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) (env : Env) (d : Nat) (e : Expr) :
    reduceNat r env d e =
      match e with
      | .app f₁ b =>
        match f₁ with
        | .const c us =>
          match us with
          | [] => reduceNat r env d (.app (.const c []) b)
          | _ :: _ => pure none
        | .app f₂ a =>
          match f₂ with
          | .const c us =>
            match us with
            | [] => reduceNat r env d (.app (.app (.const c []) a) b)
            | _ :: _ => pure none
          | _ => pure none
        | _ => pure none
      | _ => pure none := by
  cases e with
  | app f₁ b =>
    cases f₁ with
    | const c us => cases us <;> rfl
    | app f₂ a => cases f₂ with
      | const c us => cases us <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- `reduceNatI` simulates its fueled original. -/
theorem reduceNatC_spec (ih : SSimC mode env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ reduceNatI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i
    ⦃fun o s' => CSOK mode env s' ∧ Runs (reduceNat (fueledFns mode env) env d i) o ∧
      OptWS d o; ⊤⦄ := by
  sym only [conleche_grind, reduceNat_nested, reduceNat.eq_1, reduceNat.eq_2,
      natLitSupportedF_eq, natOpStoredF_eq, rawNatLitC?_spec] =>
    vcgen [reduceNatI, ih.whnf_spec] <;> finish

/-- `reduceNatC_spec` as a simulation, for the unconverted callers. -/
theorem reduceNatC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelOC d)
      (reduceNatI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (reduceNat (fueledFns mode env) env d e) := by
  subst hden; exact SimC.of_triple relOC_diag (reduceNatC_spec ih hs hw)

/-- `reduceNatC_spec` under the defeq-side fvar guard (the same `Bool`
on both sides). -/
theorem reduceNatIfC_spec (ih : SSimC mode env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) (g : Bool) :
    ⦃fun s => s = s₀⦄
      (if g then reduceNatI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i else pure none)
    ⦃fun o s' => CSOK mode env s' ∧
      Runs (if g then reduceNat (fueledFns mode env) env d i else pure none) o ∧
      OptWS d o; ⊤⦄ := by
  sym only [conleche_grind] =>
    vcgen [reduceNatC_spec ih hs hw] <;> finish

/-- `reduceNatIfC_spec` as a simulation, for the unconverted callers. -/
theorem reduceNatIfC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) (g : Bool) :
    SimC mode env s₀ (RelOC d)
      (if g then reduceNatI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i
        else pure none)
      (if g then reduceNat (fueledFns mode env) env d e else pure none) := by
  subst hden; exact SimC.of_triple relOC_diag (reduceNatIfC_spec ih hs hw g)

end Walks4

end ConLeche.Cached
