module

public import Fragment.Sound

public section

/-!
# Uniform β is unsound in the fragment's model (task #338)

`Red.betaGate` fires at a `never` binder and `Red.beta` with a
certificate; a β that fires at *every* binder — "uniform β",
certificate-free and datum-blind — is not sound for the fragment's
claims in the fragment's model.  The obstruction is the forced
collapse of task #337 (`research/nopw/Nopw/Collapse.lean`): the point
`pt` that a proof-λ denotes does not remember its domain, so the
invariant of a redex `(λ x : A. b) a` whose λ is the point says nothing
about `a ∈ A`.

The counterexample, at every valuation, in every model whose point
inhabits `Sort 1` and is not the universe of truth values — which holds
whatever the point is chosen to be, in any well-founded model with
transitive universes: `pt ∈ {pt} ∈ univ 0 ∈ univ 1`, and
`pt = univ 0` would be a membership cycle.  Moving the point out of
every function space changes nothing: the redex below sits in a
*propositional* product, which holds the point because every proof of a
∀-proposition is the point.

* `falseE := ∀ P : Prop, P`, a proposition (the false one);
* `idProof := λ (h : falseE). h`, annotated "always a proposition" —
  well-typed: `falseE → falseE`;
* `badRedex := idProof Prop`, *ill-typed* (`Prop` is not a proof of
  `falseE`), but well-denoted — the point is a member of the
  propositional product `Sort 1 → {pt}` — and denoting the point;
* `c : Sort 1 := badRedex` is a model of the environment: its value
  denotes the point, a member of `Sort 1` (`badModel`).

The constant `c` is typed — `Sort 1`, whose sort is `Sort 2` — so it is
not a proof at any valuation, and no case split on the proof regime
excuses its reduction.  δ takes `c` to `badRedex`, and uniform β takes that
to `Prop`, which denotes the universe of truth values, not the point
(`uniform_beta_unsound`).  The checker never stores such a `c` (its
value does not type-check), but the soundness proof does not know
that: the environment invariant is semantic — the value denotes a
member of the type — and in *this* model the point is a member of
`Sort 1`.  The obstruction is that model choice, not the rules: with
restricted universes, where `Sort (n+1)` holds no set that is the point
or contains it, `c` has no model (`Uniform.badEnv_no_model`), and β at
every binder is sound with no datum and no certificate
(`Uniform/Sound.lean`, `Uniform.soundnessU`).
-/

namespace Fragment

open SetLib Expr

/-- `∀ P : Prop, P`. -/
@[expose] def falseE : Expr := .pi (.sort .zero) PropWhen.always (.bvar 0)

/-- `λ (h : ∀ P : Prop, P). h`, annotated "always a proposition". -/
@[expose] def idProof : Expr := .lam falseE PropWhen.always (.bvar 0)

/-- `idProof Prop`: ill-typed, well-denoted, the point. -/
@[expose] def badRedex : Expr := .app idProof (.sort .zero)

/-- The constant `c : Sort 1 := idProof Prop`. -/
@[expose] def cName : Name := "c"

@[expose] def cInfo : ConstInfo :=
  { lparams := [], type := .sort (.succ .zero), kind := .defn badRedex }

@[expose] def badEnv : Env := Env.empty.add cName cInfo

universe w

variable {V : Type w} [SetLib V]

theorem badEnv_find {n : Name} {ci : ConstInfo} (h : badEnv.find? n = some ci) :
    n = cName ∧ ci = cInfo := by
  unfold badEnv Env.add Env.find? at h
  simp only [List.lookup] at h
  split at h
  · next hn => exact ⟨(beq_iff_eq.mp hn), (Option.some.inj h).symm⟩
  · exact nomatch h

theorem interp_falseE (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) :
    interp M φ ρ falseE = truthVal (∀ x, x ∈ˢ (univ 0 : V) → x = one) := by
  simp [falseE, interp, piR_true]

/-- `∀ P : Prop, P` is empty: the false truth value is a truth value
other than `{pt}`. -/
theorem not_mem_falseE (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) {x : V} :
    ¬ x ∈ˢ interp M φ ρ falseE := by
  intro hx
  rw [interp_falseE] at hx
  have he : (truthVal False : V) = one := of_mem_truthVal hx _ (truthVal_mem_univ_zero False)
  have hpt : (pt : V) ∈ˢ truthVal False := by rw [he]; exact mem_one.mpr rfl
  exact of_mem_truthVal hpt

/-- The redex is well-denoted (through the propositional product
`Sort 1 → {pt}`) and denotes the point. -/
theorem badRedex_wellDenoted (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) :
    WellDenoted M φ ρ badRedex ∧ interp M φ ρ badRedex = pt := by
  have hlam : interp M φ ρ idProof = pt := by simp [idProof, interp, lamR_true]
  refine ⟨?_, by simp [badRedex, hlam, app_pt]⟩
  rw [badRedex, WellDenoted_app]
  refine ⟨?_, by simp, true, univ 1, fun _ => one, ?_, ?_, fun _ _ _ => one_mem_univ_zero⟩
  · rw [idProof, WellDenoted_lam]
    refine ⟨?_, fun x hx => absurd hx (not_mem_falseE M φ ρ),
      fun x => interp M φ (cons x ρ) falseE, fun x hx => absurd hx (not_mem_falseE M φ ρ),
      fun _ x hx => absurd hx (not_mem_falseE M φ ρ)⟩
    rw [falseE, WellDenoted_pi]
    exact ⟨by simp, fun _ _ => by simp, fun _ x hx => by simpa using hx⟩
  · rw [hlam, piR_true]
    exact pt_mem_truthVal (fun _ _ => rfl)
  · simpa using univ_mem_succ 0

/-- **The environment `c : Sort 1 := idProof Prop` has a model**
wherever the point inhabits `Sort 1`. -/
def badModel (hpt : (pt : V) ∈ˢ univ 1) : EnvModel V badEnv where
  M := fun _ _ => pt
  type_ok := fun n ci h φ ρ ls hls => by
    obtain ⟨rfl, rfl⟩ := badEnv_find h
    simp only [cInfo, List.length_nil, List.length_eq_zero_iff] at hls
    subst hls
    rw [show instL cInfo.lparams [] cInfo.type = .sort (.succ .zero) by rfl]
    exact ⟨by simp, by simpa [Level.eval] using hpt⟩
  unfold := fun n ci v h hv φ ρ ls hls => by
    obtain ⟨rfl, rfl⟩ := badEnv_find h
    simp only [cInfo, List.length_nil, List.length_eq_zero_iff] at hls
    subst hls
    simp only [cInfo, ConstInfo.value?, ConstKind.value?, Option.some.injEq] at hv
    subst hv
    rw [show instL cInfo.lparams [] badRedex = badRedex by rfl]
    exact badRedex_wellDenoted _ φ ρ
  rec_rules := fun n ci _ _ _ _ _ h hk => by
    obtain ⟨rfl, rfl⟩ := badEnv_find h
    simp [cInfo] at hk
  rec_rules_nested := fun n ci _ _ _ _ _ h hk => by
    obtain ⟨rfl, rfl⟩ := badEnv_find h
    simp [cInfo] at hk

/-- **Uniform β is unsound.**  In a model whose point inhabits `Sort 1`
and is not the universe of truth values: the constant `c` is typed
`Sort 1`, of sort `Sort 2` — never a proof — and reduces by δ to the
redex `idProof Prop`; the uniform β step from that redex to `Prop`
violates the reduction claim at every valuation. -/
theorem uniform_beta_unsound [LevelOracle] (hpt : (pt : V) ∈ˢ univ 1)
    (hne : (pt : V) ≠ univ 0) (φ : Name → Nat) :
    Infer badEnv [] (.const cName []) (.sort (.succ .zero)) ∧
    Infer badEnv [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) ∧
    Red badEnv [] (.const cName []) badRedex ∧
    ¬ RedSem (badModel hpt) φ [] badRedex ((Expr.bvar 0).inst (.sort .zero)) := by
  have hfind : badEnv.find? cName = some cInfo := by
    simp [badEnv, Env.add, Env.find?]
  have hbad : ¬ RedSem (badModel hpt) φ [] badRedex ((Expr.bvar 0).inst (.sort .zero)) := by
    intro h
    obtain ⟨hw, hv⟩ := badRedex_wellDenoted (badModel hpt).M φ (fun _ => pt)
    obtain ⟨-, he⟩ := h (fun _ => pt) (Sat_nil _ φ _) hw
    rw [hv] at he
    exact hne (by simpa [interp, Level.eval] using he)
  exact ⟨.const hfind rfl, .sort, .delta hfind rfl rfl, hbad⟩

end Fragment
