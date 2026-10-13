module

public import Fragment.Lib
public import Fragment.Env

@[expose] public section

/-!
# The interpretation

`interp M φ ρ e` maps a term to a set: **total** (every term, well-typed
or not), **term-directed** (structural recursion on the term; no
derivation, no environment lookup, no `Option`), and **annotation-free**:
at a binder the regime is read off the values (`piV`/`lamV`,
`Lib.lean`), not off a datum.  The parameters:

* `M : Name → List Nat → V`, the model's assignment of a set to every
  constant at every list of concrete levels (what the environment
  invariant `EnvModel.lean` constrains);
* `φ : Name → Nat`, the valuation of the level parameters;
* `ρ : Nat → V`, the values of the bound variables.

| term | value |
|---|---|
| `bvar i` | `ρ i` |
| `sort u` | `typeU (eval φ u)` |
| `const c ls` | `M c (ls.map (eval φ))` |
| `app f a` | `app ⟦f⟧ ⟦a⟧` |
| `lam A b` | `lamV ⟦A⟧ (fun x => ⟦b⟧ (x :: ρ))` |
| `pi A B` | `piV ⟦A⟧ (fun x => ⟦B⟧ (x :: ρ))` |
| `letE T v b` | `⟦b⟧ (⟦v⟧ :: ρ)` |

A `let` reads its body at the value's value; its type is not read,
as no type is read anywhere (the counterpart of con-leche's `Denotes`
`let` rule: `Denotes ρ v Y → Denotes (Y :: ρ) b X → Denotes ρ (let x :
T := v; b) X`, `interp_letE_of`).  The checker's ζ step substitutes
the value (`Red.zeta`), which the β-substitution lemma makes an
identity on every environment (`interp_zeta`), the point included.

`app` is uniform — `app pt a = pt` is the proposition regime's β and
`app_graph` the graph regime's — so the whole regime dispatch lives in
the two binder cases, and there it is a property of the values: a
product is propositional when every fibre is a truth value, an
abstraction is the point when every body value is.  Over an empty
domain both are read as propositional (task #344).

A sort denotes its **restricted universe** `typeU` (`Lib.lean`): the
truth values at `0`, the strict members of `univ n` above — the sets
that are not the point and do not contain it.  That is the one place
the model departs from con-leche's `ConLeche/Semantics/Interp.lean`,
which interprets a sort by the universe itself (and whose checker
therefore keeps the certified β, until its port); its binder numeral
is the concrete sort of the body, where here no datum exists and the
values decide, and constants read the model's assignment directly
rather than a stored annotated term.
-/

namespace Fragment
open SetLib

universe u

/-! ## Variable environments -/

section Env

variable {V : Type u}

/-- Extend an environment with a new innermost binding. -/
def cons (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

@[simp] theorem cons_zero (x : V) (ρ : Nat → V) : cons x ρ 0 = x := rfl
@[simp] theorem cons_succ (x : V) (ρ : Nat → V) (i : Nat) : cons x ρ (i + 1) = ρ i := rfl

/-- The environment transformation matching `Expr.liftN n · k`. -/
def shiftE (n k : Nat) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else ρ (i + n)

/-- The environment transformation matching `Expr.inst · a k`. -/
def instE (k : Nat) (x : V) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else if i = k then x else ρ (i - 1)

theorem shiftE_zero (n : Nat) (ρ : Nat → V) : shiftE n 0 ρ = fun i => ρ (i + n) := by
  funext i; simp [shiftE]

theorem shiftE_zero_zero (ρ : Nat → V) : shiftE 0 0 ρ = ρ := by
  funext i; simp [shiftE]

theorem instE_zero (x : V) (ρ : Nat → V) : instE 0 x ρ = cons x ρ := by
  funext i; cases i <;> simp [instE, cons]

theorem cons_shiftE (x : V) (n k : Nat) (ρ : Nat → V) :
    cons x (shiftE n k ρ) = shiftE n (k + 1) (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [shiftE]
  | succ j =>
    show shiftE n k ρ j = shiftE n (k + 1) (cons x ρ) (j + 1)
    simp only [shiftE]
    by_cases h : j < k
    · rw [ite_eq_left h, ite_eq_left (show j + 1 < k + 1 by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (show ¬ (j + 1 < k + 1) by omega)]
      show ρ (j + n) = cons x ρ (j + 1 + n)
      rw [show j + 1 + n = (j + n) + 1 by omega]; rfl

theorem cons_instE (x : V) (k : Nat) (y : V) (ρ : Nat → V) :
    cons x (instE k y ρ) = instE (k + 1) y (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [instE]
  | succ j =>
    show instE k y ρ j = instE (k + 1) y (cons x ρ) (j + 1)
    simp only [instE]
    by_cases h : j < k
    · rw [ite_eq_left h, ite_eq_left (show j + 1 < k + 1 by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (show ¬ (j + 1 < k + 1) by omega)]
      by_cases h2 : j = k
      · rw [ite_eq_left h2, ite_eq_left (show j + 1 = k + 1 by omega)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (j + 1 = k + 1) by omega)]
        show ρ (j - 1) = cons x ρ (j + 1 - 1)
        rw [show j + 1 - 1 = (j - 1) + 1 by omega]; rfl

theorem shiftE_succ_cons (x : V) (k : Nat) (ρ : Nat → V) :
    shiftE (k + 1) 0 (cons x ρ) = shiftE k 0 ρ := by
  rw [shiftE_zero, shiftE_zero]
  funext i
  show cons x ρ (i + (k + 1)) = ρ (i + k)
  rw [show i + (k + 1) = (i + k) + 1 by omega]; rfl

end Env

/-! ## The interpretation -/

variable {V : Type u} [SetLib V]

/-- **The interpretation**: total, term-directed, reading no type. -/
noncomputable def interp (M : Name → List Nat → V) (φ : Name → Nat) : (Nat → V) → Expr → V
  | ρ, .bvar i => ρ i
  | _, .sort u => typeU (u.eval φ)
  | _, .const c ls => M c (ls.map (Level.eval φ))
  | ρ, .app f a => app (interp M φ ρ f) (interp M φ ρ a)
  | ρ, .lam A b => lamV (interp M φ ρ A) fun x => interp M φ (cons x ρ) b
  | ρ, .pi A B => piV (interp M φ ρ A) fun x => interp M φ (cons x ρ) B
  | ρ, .letE _ v b => interp M φ (cons (interp M φ ρ v) ρ) b

variable (M : Name → List Nat → V) (φ : Name → Nat)

@[simp] theorem interp_bvar (ρ : Nat → V) (i : Nat) : interp M φ ρ (.bvar i) = ρ i := rfl
@[simp] theorem interp_sort (ρ : Nat → V) (u : Level) :
    interp M φ ρ (.sort u) = typeU (u.eval φ) := rfl
@[simp] theorem interp_const (ρ : Nat → V) (c : Name) (ls : List Level) :
    interp M φ ρ (.const c ls) = M c (ls.map (Level.eval φ)) := rfl
@[simp] theorem interp_app (ρ : Nat → V) (f a : Expr) :
    interp M φ ρ (.app f a) = app (interp M φ ρ f) (interp M φ ρ a) := rfl
@[simp] theorem interp_lam (ρ : Nat → V) (A : Expr) (b : Expr) :
    interp M φ ρ (.lam A b) =
      lamV (interp M φ ρ A) fun x => interp M φ (cons x ρ) b := rfl
@[simp] theorem interp_pi (ρ : Nat → V) (A : Expr) (B : Expr) :
    interp M φ ρ (.pi A B) =
      piV (interp M φ ρ A) fun x => interp M φ (cons x ρ) B := rfl
@[simp] theorem interp_letE (ρ : Nat → V) (T v b : Expr) :
    interp M φ ρ (.letE T v b) = interp M φ (cons (interp M φ ρ v) ρ) b := rfl

/-- **The `let` clause, in `Denotes`' shape**: a `let` whose value
denotes `Y` and whose body denotes `X` at `Y` pushed denotes `X`.  The
type is not read. -/
theorem interp_letE_of {ρ : Nat → V} {T v b : Expr} {Y X : V}
    (hv : interp M φ ρ v = Y) (hb : interp M φ (cons Y ρ) b = X) :
    interp M φ ρ (.letE T v b) = X := by
  rw [interp_letE, hv, hb]

/-! ## The substitution lemmas -/

/-- Lifting is an environment shift. -/
theorem interp_liftN (n : Nat) :
    ∀ (e : Expr) (k : Nat) (ρ : Nat → V),
      interp M φ ρ (e.liftN n k) = interp M φ (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [Expr.liftN_bvar, interp_bvar, shiftE]
    split <;> rfl
  | sort u => intro k ρ; rfl
  | const c ls => intro k ρ; rfl
  | app f a ihf iha => intro k ρ; simp [ihf, iha]
  | lam A b ihA ihb =>
    intro k ρ
    simp only [Expr.liftN_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, cons_shiftE]
  | pi A B ihA ihB =>
    intro k ρ
    simp only [Expr.liftN_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, cons_shiftE]
  | letE T v b _ ihv ihb =>
    intro k ρ
    simp only [Expr.liftN_letE, interp_letE, ihv]
    rw [ihb, cons_shiftE]

/-- Instantiation is an environment update. -/
theorem interp_inst :
    ∀ (e a : Expr) (k : Nat) (ρ : Nat → V),
      interp M φ ρ (e.inst a k) =
        interp M φ (instE k (interp M φ (shiftE k 0 ρ) a) ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ
    simp only [Expr.inst_bvar, interp_bvar, instE]
    by_cases h : i < k
    · simp [h]
    · by_cases h2 : i = k
      · simp only [ite_eq_right h, ite_eq_left h2]
        rw [interp_liftN]
      · simp [h, h2]
  | sort u => intro a k ρ; rfl
  | const c ls => intro a k ρ; rfl
  | app f b ihf ihb => intro a k ρ; simp [ihf, ihb]
  | lam A b ihA ihb =>
    intro a k ρ
    simp only [Expr.inst_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, shiftE_succ_cons, cons_instE]
  | pi A B ihA ihB =>
    intro a k ρ
    simp only [Expr.inst_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, shiftE_succ_cons, cons_instE]
  | letE T v b _ ihv ihb =>
    intro a k ρ
    simp only [Expr.inst_letE, interp_letE, ihv]
    rw [ihb, shiftE_succ_cons, cons_instE]

/-- **The β-substitution lemma**: substituting for the innermost
variable is consing its value. -/
theorem interp_inst0 (e a : Expr) (ρ : Nat → V) :
    interp M φ ρ (e.inst a) = interp M φ (cons (interp M φ ρ a) ρ) e := by
  rw [interp_inst, shiftE_zero_zero, instE_zero]

/-- **ζ is an identity**: a `let` denotes what its body with the value
substituted denotes — at every environment, the point included (as β
is at a λ that is a graph; ζ has no λ that could be the point). -/
theorem interp_zeta (T v b : Expr) (ρ : Nat → V) :
    interp M φ ρ (.letE T v b) = interp M φ ρ (b.inst v) := by
  rw [interp_letE, interp_inst0]

/-- Level instantiation is a change of valuation. -/
theorem interp_instL (ps : List Name) (ls : List Level) :
    ∀ (e : Expr) (ρ : Nat → V),
      interp M φ ρ (e.instL ps ls) = interp M (Level.substVal φ ps ls) ρ e := by
  intro e
  induction e with
  | bvar i => intro ρ; rfl
  | sort u => intro ρ; simp [Level.eval_subst]
  | const c us =>
    intro ρ
    simp only [Expr.instL_const, interp_const, List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    exact Level.eval_subst φ ps ls l
  | app f a ihf iha => intro ρ; simp [ihf, iha]
  | lam A b ihA ihb =>
    intro ρ
    simp only [Expr.instL_lam, interp_lam, ihA]
    congr 1
    funext x
    exact ihb _
  | pi A B ihA ihB =>
    intro ρ
    simp only [Expr.instL_pi, interp_pi, ihA]
    congr 1
    funext x
    exact ihB _
  | letE T v b _ ihv ihb =>
    intro ρ
    simp only [Expr.instL_letE, interp_letE, ihv]
    exact ihb _

/-- The interpretation of a spine. -/
theorem interp_mkAppN (ρ : Nat → V) :
    ∀ (f : Expr) (args : List Expr),
      interp M φ ρ (Expr.mkAppN f args) =
        args.foldl (fun v a => app v (interp M φ ρ a)) (interp M φ ρ f)
  | _, [] => rfl
  | f, a :: args => by
    rw [Expr.mkAppN_cons, interp_mkAppN ρ (.app f a) args]
    rfl

end Fragment
