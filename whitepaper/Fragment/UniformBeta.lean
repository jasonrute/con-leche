module

public import Fragment.Sound

public section

/-!
# Why the universes are restricted (tasks #338, #340)

Under the model con-leche's `Semantics` uses — `Sort n` denotes the
universe `univ n` itself — a β that fires at *every* binder, with no
certificate and no comparison of the binder's datum, is unsound.
The fragment's earlier model was that one, and its β was certified
where the body may be a proposition; this file keeps the witness, and
shows that the restricted universes (`typeU`, `Lib.lean`) exclude it.

The witness: `falseE := ∀ P : Prop, P`; `idProof := λ (h : falseE). h`
(the point: its domain is empty); `badRedex := idProof Prop`, which is
*ill-typed* (`Prop` is not a proof of `falseE`) but well-denoted under
the old invariant — the point is a member of the propositional product
`Sort 1 → {pt}` — and denotes the point; and the environment
`c : Sort 1 := badRedex`.  Where `Sort 1` is `univ 1`, the point is a
member of it in any well-founded model with transitive universes
(`pt ∈ {pt} ∈ univ 0 ∈ univ 1`), so that environment has a model; δ
takes `c` to `badRedex` and uniform β takes that to `Prop`, which does
not denote the point — the reduction claim fails at every valuation
(task #338's `uniform_beta_unsound`, on `agent/339-uniform-ind`).
Excluding `c` syntactically would need subject reduction for stored
values.

With restricted universes the environment has **no model**
(`badEnv_no_model`): the value denotes the point, and `Sort 1`'s
members are types, which the point is not.  That is the whole change of model: β is then
sound at every binder (`Sound.lean`, `Red.beta_sound`).
-/

namespace Fragment

open SetLib Expr

/-- `∀ P : Prop, P`. -/
@[expose] def falseE : Expr := .pi (.sort .zero) (.bvar 0)

/-- `λ (h : ∀ P : Prop, P). h`. -/
@[expose] def idProof : Expr := .lam falseE (.bvar 0)

/-- `idProof Prop`: ill-typed, well-denoted, the point. -/
@[expose] def badRedex : Expr := .app idProof (.sort .zero)

/-- The constant `c : Sort 1 := idProof Prop`. -/
@[expose] def cName : Name := "c"

@[expose] def cInfo : ConstInfo :=
  { lparams := [], type := .sort (.succ .zero), kind := .defn badRedex }

@[expose] def badEnv : Env := Env.empty.add cName cInfo

universe w

variable {V : Type w} [SetLib V]

/-- `∀ P : Prop, P` has no member, under every model, valuation and
environment: the product is propositional, and `False` is a fibre. -/
theorem not_mem_falseE (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) (z : V) :
    ¬ z ∈ˢ interp M φ ρ falseE := by
  intro hz
  have hp : propB (typeU 0 : V) (fun x => x) = true :=
    propB_eq_true.mpr fun x hx => mem_typeU_zero.mp hx
  simp only [falseE, interp_pi, interp_sort, interp_bvar, cons_zero, Level.eval_zero] at hz
  unfold piV at hz
  rw [hp, piR_true] at hz
  have h := of_mem_truthVal hz (truthVal False)
    (mem_typeU_zero.mpr (truthVal_mem_univ_zero False))
  exact one_ne_truthVal_false h.symm

/-- **The witness has no model**: the environment
`c : Sort 1 := (λ (h : ∀ P : Prop, P). h) Prop` — its value denotes the
point (an abstraction over an empty domain), and `Sort 1`'s members are
types. -/
theorem badEnv_no_model (m : EnvModel V badEnv) : False := by
  have hfind : badEnv.find? cName = some cInfo := by
    simp [badEnv, Env.add, Env.find?, cName]
  have φ : Name → Nat := fun _ => 0
  obtain ⟨-, hv⟩ := m.unfold cName cInfo badRedex hfind rfl φ (fun _ => pt) [] (by simp [cInfo])
  obtain ⟨-, -, hmem⟩ := m.type_ok cName cInfo hfind φ (fun _ => pt) [] (by simp [cInfo])
  have hpt : interp m.M φ (fun _ => pt) (badRedex.instL cInfo.lparams []) = pt := by
    show interp m.M φ (fun _ => pt) badRedex = pt
    rw [badRedex, idProof, interp_app, interp_lam,
      lamV_of_empty (not_mem_falseE m.M φ (fun _ => pt)), app_pt]
  rw [hpt] at hv
  rw [← hv] at hmem
  have hmem' : (pt : V) ∈ˢ typeU 1 := by
    simpa [cInfo, Expr.instL, Level.subst, Level.eval] using hmem
  exact ((mem_typeU_pos (by omega)).mp hmem').2.ne_pt rfl

end Fragment
