module

@[expose] public section

/-!
# First-order formulas of the language `L = {∈}`

`Form n` is the type of first-order formulas of the pure set-theoretic
language `L = {∈}` (one binary relation symbol, no function symbols, so
terms are just variables) in de Bruijn representation: `n` is the number
of free variables, and free variable `i : Fin n` is the `i`-th entry of
the realizing assignment.  The constructors mirror Mathlib's
`FirstOrder.Language.BoundedFormula` for this language exactly
(`falsum`/`equal`/`rel`/`imp`/`all`), which is what lets the bridge
package `bridge/lean4lean-model` embed `Form n` into
`LSet.BoundedFormula Empty n` (`ConLecheBridge.toBF`) and read Mathlib's
`repSchema` instances off as realizations of `Form`s
(`ConLecheBridge.replF_of_ZFC_model`).

`Realize mem v φ` is the meaning of `φ` in a membership relation `mem`
under the assignment `v : Fin n → V`.  The quantifiers bind the *last*
variable (`Form.snoc`), matching `BoundedFormula.realize_all`.

This is the formula universe for the *definable* (first-order)
replacement scheme: the bridge proves that every `M ⊨ ZFC` satisfies
replacement for all `Form`s (`replF_of_ZFC_model`), while the meta-level
scheme over all `p : V → V → Prop` (`SetTheory.repl`) is strictly stronger
for arbitrary models and is the content of the bridge axiom
`replScheme_of_ZFC_model`.
-/

namespace ConLeche

/-- First-order formulas of `L = {∈}` in de Bruijn representation. -/
inductive Form : Nat → Type
  | falsum {n : Nat} : Form n
  | equal {n : Nat} (i j : Fin n) : Form n
  | mem {n : Nat} (i j : Fin n) : Form n
  | imp {n : Nat} (a b : Form n) : Form n
  | all {n : Nat} (a : Form (n + 1)) : Form n

namespace Form

variable {n : Nat}

/-- Append `x` at the last position of an assignment (Mathlib's
`Fin.snoc`, which is unavailable here without Mathlib). -/
def snoc {V : Type u} {n : Nat} (v : Fin n → V) (x : V) : Fin (n + 1) → V :=
  fun i => if h : i.val < n then v ⟨i.val, h⟩ else x

/-- Assignment binding the first two variables to `x` and `y` and the
remaining `n` variables to the parameters `p` (variable `0` ↦ `x`,
variable `1` ↦ `y`, variable `i + 2` ↦ `p i`) — the parameter convention
of the (first-order) replacement schema. -/
def cons2 {V : Type u} {n : Nat} (x y : V) (p : Fin n → V) : Fin (n + 2) → V :=
  fun i => if h0 : i.val = 0 then x else if h1 : i.val = 1 then y else p ⟨i.val - 2, by omega⟩

/-- Lift a variable map `f : Fin m → Fin n` to `Fin (m + 1) → Fin (n + 1)`,
sending the bound (last) variable to the last variable — the bound-variable
step of `relabel`. -/
def liftRelabel {m n : Nat} (f : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  fun i => if h : i.val < m then Fin.castSucc (f ⟨i.val, h⟩) else Fin.last n

/-- Relabel the free variables of a formula along `f : Fin m → Fin n`
(Mathlib's `BoundedFormula.relabel`, which is unavailable here without
Mathlib). -/
def relabel {m n : Nat} (f : Fin m → Fin n) : Form m → Form n
  | .falsum => .falsum
  | .equal i j => .equal (f i) (f j)
  | .mem i j => .mem (f i) (f j)
  | .imp a b => .imp (relabel f a) (relabel f b)
  | .all a => .all (relabel (liftRelabel f) a)

/-- Realization of a formula in a membership relation `mem` under the
assignment `v` of its `n` free variables. -/
def Realize {V : Type u} (mem : V → V → Prop) {n : Nat} (v : Fin n → V) : Form n → Prop
  | .falsum => False
  | .equal i j => v i = v j
  | .mem i j => mem (v i) (v j)
  | .imp a b => Realize mem v a → Realize mem v b
  | .all a => ∀ x, Realize mem (snoc v x) a

/-- Negation. -/
def not (φ : Form n) : Form n := φ.imp .falsum

/-- Conjunction. -/
def and (φ ψ : Form n) : Form n := (φ.imp ψ.not).not

/-- Disjunction. -/
def or (φ ψ : Form n) : Form n := φ.not.imp ψ

/-- Bi-implication. -/
def iff (φ ψ : Form n) : Form n := (φ.imp ψ).and (ψ.imp φ)

/-- Existential quantifier (binds the last variable). -/
def ex (φ : Form (n + 1)) : Form n := φ.not.all.not

@[simp] theorem realize_falsum {V : Type u} {mem : V → V → Prop} {v : Fin n → V} :
    Realize mem v .falsum ↔ False := Iff.rfl

@[simp] theorem realize_equal {V : Type u} {mem : V → V → Prop} {v : Fin n → V} {i j : Fin n} :
    Realize mem v (.equal i j) ↔ v i = v j := Iff.rfl

@[simp] theorem realize_mem {V : Type u} {mem : V → V → Prop} {v : Fin n → V} {i j : Fin n} :
    Realize mem v (.mem i j) ↔ mem (v i) (v j) := Iff.rfl

@[simp] theorem realize_imp {V : Type u} {mem : V → V → Prop} {v : Fin n → V} {a b : Form n} :
    Realize mem v (.imp a b) ↔ (Realize mem v a → Realize mem v b) := Iff.rfl

@[simp] theorem realize_all {V : Type u} {mem : V → V → Prop} {v : Fin n → V} {a : Form (n + 1)} :
    Realize mem v (.all a) ↔ ∀ x, Realize mem (snoc v x) a := Iff.rfl

@[simp] theorem realize_not {V : Type u} {mem : V → V → Prop} {v : Fin n → V} {φ : Form n} :
    Realize mem v (not φ) ↔ ¬ Realize mem v φ := by
  rw [show not φ = φ.imp .falsum from rfl, realize_imp, realize_falsum]

@[simp] theorem realize_and {V : Type u} {mem : V → V → Prop} {v : Fin n → V} {φ ψ : Form n} :
    Realize mem v (and φ ψ) ↔ (Realize mem v φ ∧ Realize mem v ψ) := by
  rw [show and φ ψ = (φ.imp ψ.not).not from rfl, realize_not, realize_imp, realize_not,
    not_imp, Classical.not_not]

@[simp] theorem realize_or {V : Type u} {mem : V → V → Prop} {v : Fin n → V} {φ ψ : Form n} :
    Realize mem v (or φ ψ) ↔ (Realize mem v φ ∨ Realize mem v ψ) := by
  rw [show or φ ψ = φ.not.imp ψ from rfl, realize_imp, realize_not]
  constructor
  · intro h
    by_cases hφ : Realize mem v φ
    · exact Or.inl hφ
    · exact Or.inr (h hφ)
  · rintro (hφ | hψ) hn
    · exact absurd hφ hn
    · exact hψ

@[simp] theorem realize_iff {V : Type u} {mem : V → V → Prop} {v : Fin n → V} {φ ψ : Form n} :
    Realize mem v (iff φ ψ) ↔ (Realize mem v φ ↔ Realize mem v ψ) := by
  rw [show iff φ ψ = (φ.imp ψ).and (ψ.imp φ) from rfl, realize_and, realize_imp, realize_imp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩

@[simp] theorem realize_ex {V : Type u} {mem : V → V → Prop} {v : Fin n → V} {φ : Form (n + 1)} :
    Realize mem v (ex φ) ↔ ∃ x, Realize mem (snoc v x) φ := by
  rw [show ex φ = φ.not.all.not from rfl, realize_not, realize_all]
  simp only [realize_not]
  constructor
  · intro h
    refine Classical.byContradiction fun hn => h ?_
    intro x hx
    exact hn ⟨x, hx⟩
  · rintro ⟨x, hx⟩ h
    exact h x hx

theorem snoc_comp_liftRelabel {V : Type u} {m n : Nat} (v : Fin n → V) (f : Fin m → Fin n) (x : V) :
    (snoc v x) ∘ liftRelabel f = snoc (v ∘ f) x := by
  funext i
  by_cases h : i.val < m
  · simp [snoc, liftRelabel, h, Fin.castSucc]
  · have him : i.val = m := by omega
    simp [snoc, liftRelabel, Fin.last, him]

/-- Relabeling the free variables commutes with realization
(Mathlib's `BoundedFormula.realize_relabel`). -/
theorem realize_relabel {V : Type u} {mem : V → V → Prop} {m : Nat} (φ : Form m) :
    ∀ {n : Nat} (f : Fin m → Fin n) (v : Fin n → V),
      Realize mem v (relabel f φ) ↔ Realize mem (v ∘ f) φ := by
  induction φ with
  | falsum => intro n f v; exact Iff.rfl
  | equal i j => intro n f v; simp [relabel, realize_equal]
  | mem i j => intro n f v; simp [relabel, realize_mem]
  | imp a b iha ihb => intro n f v; simp [relabel, realize_imp, iha, ihb]
  | all a iha =>
    intro n f v
    simp only [relabel, realize_all]
    exact forall_congr' fun x => by
      rw [iha (liftRelabel f) (snoc v x), snoc_comp_liftRelabel]

/-- The empty parameter assignment. -/
def nil {V : Type u} : Fin 0 → V := fun i => i.elim0

@[simp] theorem snoc_nil {V : Type u} (x : V) :
    snoc (nil : Fin 0 → V) x = fun _ => x := by
  funext i
  simp [snoc]

@[simp] theorem snoc_castSucc {V : Type u} {n : Nat} (v : Fin n → V) (x : V) (i : Fin n) :
    snoc v x (Fin.castSucc i) = v i := by
  show (if h : i.val < n then v ⟨i.val, h⟩ else x) = v i
  rw [dite_eq_left i.isLt]

@[simp] theorem snoc_last {V : Type u} {n : Nat} (v : Fin n → V) (x : V) :
    snoc v x (Fin.last n) = x := by
  show (if h : n < n then v ⟨n, h⟩ else x) = x
  rw [dite_eq_right (Nat.lt_irrefl n)]

/-- Evaluation of `snoc` at a literal index (this is `rfl`; stated as a
simp lemma so that `Realize` proofs reduce ground de Bruijn indices). -/
@[simp] theorem snoc_mk {V : Type u} {n : Nat} (v : Fin n → V) (x : V) {k : Nat}
    {hk : k < n + 1} :
    snoc v x ⟨k, hk⟩ = if h : k < n then v ⟨k, h⟩ else x := rfl

end Form

end ConLeche
