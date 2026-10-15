module

public import ConLeche.Verify.Cached.SimC
public import ConLeche.Verify.Cached.GrindAttr
public import Std.WP

public section

/-!
# The cached simulation as `Std.WP` triples, and its `grind` vocabulary

A converted walk proof is

```lean
  sym only [conleche_grind] =>
    vcgen [f, callee specs…] <;> finish
```

`vcgen` runs in `grind`'s symbolic mode (`SymM`), generates the
verification conditions of the cached program `f` and internalizes
each one's hypotheses into the E-graph as it introduces them; `finish`
closes every condition in that same E-graph.  `only`: the project's set
(`@[conleche_grind]`, `GrindAttr.lean`) and nothing else.

1. **The triple forms** (§1, §3).  A simulation `SimC mode env s₀ P c p`
   whose value relation `P` is equality up to a side condition `W` is the
   `Std.WP` triple `⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode env s' ∧
   Runs p v ∧ W v; ⊤⦄` (`SimC.triple`, `SimC.of_triple`); an effect
   `CEff mode env s₀ Q c` is `⦃…⦄ c ⦃fun v s' => CSOK mode env s' ∧ Q v; ⊤⦄`
   (`CEff.triple`).  Partial correctness: the exception postcondition is
   `⊤`.  `SimC`/`CEff` keep their run-based definitions (`triple_iff_run`
   is the bridge), so the unconverted walks are unchanged.
2. **The pure side's answer as a named predicate** (§2).  `Runs p v`: the
   fuelled computation `p` succeeds with `v` at some fuel.  Fuel is the
   one witness that is not a function of anything a walk names, so it
   stays inside `Runs`; `Runs.pure_eq` and `Runs.bind_eq` are equations
   whose proofs merge it by `FueledM`'s monotonicity.  A walk's post
   states the cached value AS the pure answer (`Runs p v`), never
   `∃ w, v = w ∧ Runs p w`.
3. **Scope side conditions as named predicates** (§4: `AllWS`, `StepWS`,
   `OptWS`), each with one equation per constructor, so that no `∀` or
   `match` reaches `grind`, and `Expr.WScoped` opened one constructor at a
   time and carried through bulk instantiation and spine building.
4. **The value relations as answers** (§5): `RelEC`/`RelOC` split into
   the equation and the side condition, for `SimC.triple`/`SimC.of_triple`.
5. **The knot's unary slots** (§6): `BodySpec`, a body's simulation as a
   named predicate, so that a memo wrapper's hypothesis is an atom and
   its triple enters `vcgen`'s list as a term.
-/

namespace ConLeche.Cached

open ConLeche Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env}

/-! ## 1. A `CheckCM` triple is a statement about the successful runs -/

/-- A partial-correctness triple from a fixed initial state is a
statement about the successful runs. -/
theorem triple_iff_run {β : Type} {s₀ : CState} {c : CheckCM β}
    {Q : β → CState → Prop} :
    (⦃fun s => s = s₀⦄ c ⦃fun v s' => Q v s'; ⊤⦄) ↔
      ∀ v' s', c s₀ = .ok (v', s') → Q v' s' := by
  constructor
  · intro ⟨h⟩ v' s' hr
    have := h s₀ rfl
    rw [StateT.wp_apply_eq, StateT.run, hr] at this
    exact this
  · intro h
    refine ⟨fun s hs => ?_⟩
    obtain rfl : s = s₀ := hs
    rw [StateT.wp_apply_eq, StateT.run]
    cases hc : c s with
    | ok r => obtain ⟨v, s'⟩ := r; exact h v s' hc
    | error e =>
      show (⊤ : CheckError → Prop) e
      rw [Lean.Order.top_apply, Lean.Order.top_prop_eq]; trivial

/-! ## 2. The pure side's answer -/

/-- The fuelled computation `p` succeeds with `v` at some fuel. -/
@[expose] def Runs {α : Type} (p : FueledM α) (v : α) : Prop :=
  ∃ F, p.val F = .ok v

theorem Runs.pure {α : Type} (a : α) : Runs (pure a : FueledM α) a := ⟨0, rfl⟩

theorem Runs.bind {α β : Type} {x : FueledM α} {f : α → FueledM β} {a : α} {b : β}
    (hx : Runs x a) (hf : Runs (f a) b) : Runs (x >>= f) b := by
  obtain ⟨F₁, h₁⟩ := hx
  obtain ⟨F₂, h₂⟩ := hf
  refine ⟨max F₁ F₂, ?_⟩
  rw [FueledM.atF_bind]
  simp only [Bind.bind]
  rw [x.property (Nat.le_max_left F₁ F₂) h₁]
  exact (f a).property (Nat.le_max_right F₁ F₂) h₂

/-- A `pure` answers its value and nothing else. -/
@[conleche_grind =] theorem Runs.pure_eq {α : Type} (a b : α) :
    Runs (Pure.pure a : FueledM α) b = (a = b) := by
  apply propext; constructor
  · intro ⟨F, h⟩; exact Except.ok.inj h
  · rintro rfl; exact Runs.pure a

/-- Past a first step that answers `a`, a bind answers what its
continuation at `a` answers.  The equation (rather than `Runs.bind`'s
implication) is what lets `grind` push a goal `Runs (x >>= f) b` into
the continuation: it fires on the step's answer and the bind, both of
which are terms of the verification condition. -/
theorem Runs.bind_eq {α β : Type} {x : FueledM α} {f : α → FueledM β} {a : α} (b : β)
    (hx : Runs x a) : Runs (x >>= f) b = Runs (f a) b := by
  apply propext; constructor
  · intro ⟨F, h⟩
    obtain ⟨F₁, h₁⟩ := hx
    refine ⟨max F F₁, ?_⟩
    have h' := (x >>= f).property (Nat.le_max_left F F₁) h
    rw [FueledM.atF_bind] at h'
    simp only [Bind.bind] at h'
    rw [x.property (Nat.le_max_right F F₁) h₁] at h'
    exact h'
  · intro hf; exact Runs.bind hx hf
grind_pattern [conleche_grind] Runs.bind_eq => Runs x a, Runs (x >>= f) b

/-! ## 3. The triple forms of `SimC` and `CEff` -/

/-- A simulation whose value relation is equality up to `W` is a triple
whose post names the cached value as the pure side's answer. -/
theorem SimC.triple {β : Type} {P : β → β → Prop} {W : β → Prop} {s₀ : CState}
    {c : CheckCM β} {p : FueledM β} (hP : ∀ v' v, P v' v → v' = v ∧ W v')
    (h : SimC mode env s₀ P c p) :
    ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode env s' ∧ Runs p v ∧ W v; ⊤⦄ := by
  refine triple_iff_run.mpr fun v' s' hr => ?_
  obtain ⟨hs', v, hP', F, hF⟩ := h v' s' hr
  obtain ⟨rfl, hW⟩ := hP v' v hP'
  exact ⟨hs', ⟨F, hF⟩, hW⟩

/-- The converse of `SimC.triple`: an answer-shaped triple is a
simulation for any value relation that holds on the diagonal under `W`. -/
theorem SimC.of_triple {β : Type} {P : β → β → Prop} {W : β → Prop} {s₀ : CState}
    {c : CheckCM β} {p : FueledM β} (hP : ∀ v, W v → P v v)
    (h : ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode env s' ∧ Runs p v ∧ W v; ⊤⦄) :
    SimC mode env s₀ P c p := by
  intro v' s' hr
  obtain ⟨hs', ⟨F, hF⟩, hW⟩ := triple_iff_run.mp h v' s' hr
  exact ⟨hs', v', hP v' hW, F, hF⟩

theorem CEff.triple {β : Type} {Q : β → Prop} {s₀ : CState} {c : CheckCM β}
    (h : CEff mode env s₀ Q c) :
    ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode env s' ∧ Q v; ⊤⦄ :=
  triple_iff_run.mpr h


/-! ## 4. Scope side conditions

Each a named predicate with one equation per constructor, so that no
`∀` or `match` reaches `grind`; `Expr.WScoped` itself is opened one
constructor at a time (`wscoped_app_eq`, `wscoped_lam_eq`) and carried
through the substitutions the walks perform. -/

/-- Every element of the list is well scoped at `d`. -/
@[expose] def AllWS (d : Nat) (xs : List Expr) : Prop := ∀ x ∈ xs, Expr.WScoped d x

@[conleche_grind =] theorem AllWS.nil_eq (d : Nat) : AllWS d [] = True := by
  simp [AllWS]

@[conleche_grind =] theorem AllWS.cons_eq (d : Nat) (x : Expr) (xs : List Expr) :
    AllWS d (x :: xs) = (Expr.WScoped d x ∧ AllWS d xs) := by
  simp [AllWS]

/-- A loop step's term is well scoped at `d`. -/
@[expose] def StepWS (d : Nat) : WhnfStep → Prop
  | .done e => Expr.WScoped d e
  | .cont e => Expr.WScoped d e

@[conleche_grind =] theorem StepWS.done_eq (d : Nat) (e : Expr) :
    StepWS d (.done e) = Expr.WScoped d e := rfl

@[conleche_grind =] theorem StepWS.cont_eq (d : Nat) (e : Expr) :
    StepWS d (.cont e) = Expr.WScoped d e := rfl

/-- An optional answer is well scoped at `d` where present. -/
@[expose] def OptWS (d : Nat) : Option Expr → Prop
  | none => True
  | some e => Expr.WScoped d e

@[conleche_grind =] theorem OptWS.some_eq (d : Nat) (e : Expr) :
    OptWS d (some e) = Expr.WScoped d e := rfl

@[conleche_grind =] theorem wscoped_app_eq (d : Nat) (g a : Expr) :
    Expr.WScoped d (.app g a) = (Expr.WScoped d g ∧ Expr.WScoped d a) := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_lam_eq (d : Nat) (ty body : Expr) :
    Expr.WScoped d (.lam ty body) = (Expr.WScoped d ty ∧ Expr.WScoped d body) := by
  rw [Expr.WScoped]

/-- Bulk instantiation with well-scoped values keeps a well-scoped term
well scoped. -/
theorem wscoped_instantiateList {d : Nat} {e : Expr} (he : Expr.WScoped d e) :
    ∀ {vs : List Expr} {k : Nat}, AllWS d vs → Expr.WScoped d (e.instantiateList vs k)
  | [], _, _ => by rw [Expr.instantiateList_nil]; exact he
  | v :: vs, k, hvs => by
    rw [Expr.instantiateList_cons]
    rw [AllWS.cons_eq] at hvs
    exact Expr.WScoped.instantiate1_gen hvs.1 k (wscoped_instantiateList he hvs.2)
grind_pattern [conleche_grind] wscoped_instantiateList =>
  Expr.WScoped d e, e.instantiateList vs k

theorem wscoped_mkAppN {d : Nat} {g : Expr} {xs : List Expr} (hg : Expr.WScoped d g)
    (hxs : AllWS d xs) : Expr.WScoped d (Expr.mkAppN g xs) :=
  Expr.WScoped.mkAppN hg hxs
grind_pattern [conleche_grind] wscoped_mkAppN => Expr.WScoped d g, Expr.mkAppN g xs

/-! ## 5. The value relations as answers -/

theorem relEC_inv {d : Nat} (v' v : Expr) (h : RelEC d v' v) : v' = v ∧ Expr.WScoped d v' :=
  ⟨h.1, h.1 ▸ h.2⟩

theorem relEC_diag {d : Nat} (v : Expr) (h : Expr.WScoped d v) : RelEC d v v := ⟨rfl, h⟩

/-! ## 6. The knot's unary slots

A memo wrapper's body is specified as a named predicate (`BodySpec`), not
as a `∀`-triple hypothesis: a `∀` fact in the context is an E-matching
theorem `grind` instantiates at every state and input in sight, while the
named predicate is an atom, and its triple enters `vcgen`'s list as the
term `hbody.triple`. -/

/-- A unary entry point's body simulates its fueled body on well-scoped
inputs, with a well-scoped answer. -/
@[expose] def BodySpec (mode : CheckMode) (env : Env) (body : Nat → Expr → CheckCM Expr)
    (spec : Nat → Expr → FueledM Expr) : Prop :=
  ∀ {s₀ : CState} {d : Nat} {i : Expr}, CSOK mode env s₀ → Expr.WScoped d i →
    ⦃fun s => s = s₀⦄ body d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs (spec d i) r ∧ Expr.WScoped d r; ⊤⦄

theorem BodySpec.triple {body : Nat → Expr → CheckCM Expr} {spec : Nat → Expr → FueledM Expr}
    (h : BodySpec mode env body spec) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ body d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs (spec d i) r ∧ Expr.WScoped d r; ⊤⦄ := h hs hw

end ConLeche.Cached
