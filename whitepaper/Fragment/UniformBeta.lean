module

public import Fragment.Sound

public section

/-!
# Why the universes are restricted (tasks #338, #340)

Under the model con-leche's `Semantics` uses — `Sort n` denotes the
universe `univ n` itself — a β that fires at *every* binder, with no
certificate and no comparison of the binder's annotation, is unsound.
The fragment's earlier model was that one, and its β was certified
where the body may be a proposition; this file keeps the witness, and
shows that the restricted universes (`typeU`, `Lib.lean`) exclude it.

The witness: `falseE := ∀ P : Prop, P`; `idProof := λ (h : falseE). h`,
annotated "always a proposition"; `badRedex := idProof Prop`, which is
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
members are strict.  That is the whole change of model: β is then
sound at every binder (`Sound.lean`, `Red.beta_sound`).
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

/-- **The witness has no model**: the environment
`c : Sort 1 := (λ (h : ∀ P : Prop, P). h) Prop` — its value denotes the
point, and `Sort 1`'s members are strict. -/
theorem badEnv_no_model (m : EnvModel V badEnv) : False := by
  have hfind : badEnv.find? cName = some cInfo := by
    simp [badEnv, Env.add, Env.find?, cName]
  have φ : Name → Nat := fun _ => 0
  obtain ⟨-, hv⟩ := m.unfold cName cInfo badRedex hfind rfl φ (fun _ => pt) [] (by simp [cInfo])
  obtain ⟨-, -, hmem⟩ := m.type_ok cName cInfo hfind φ (fun _ => pt) [] (by simp [cInfo])
  have hpt : interp m.M φ (fun _ => pt) (badRedex.instL cInfo.lparams []) = pt := by
    show interp m.M φ (fun _ => pt) badRedex = pt
    simp [badRedex, idProof, interp, PropWhen.holds_always, lamR_true, app_pt]
  rw [hpt] at hv
  rw [← hv] at hmem
  have hmem' : (pt : V) ∈ˢ typeU 1 := by
    simpa [cInfo, Expr.instL, Level.subst, Level.eval] using hmem
  exact ((mem_typeU_pos (by omega)).mp hmem').2.1 rfl

end Fragment
