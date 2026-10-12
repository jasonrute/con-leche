module

import ConLeche.Verify.Denote.VClosed
public import ConLeche.Semantics.Tower.TowerKit

@[expose] public section

/-!
# Parallel substitution of annotated terms

`ITerm.substAV τ e k` replaces every bound variable `k + j` (at or
above the cut `k`) by `τ j`, lifted over the `k` binders passed.  It is
the reading-side twin of the Expr operation `Expr.substFvars`
(`Verify/SubstFvars.lean`): a container frame's constructor type is the
recorded member-abstracted constructor type with its parameter and hole
variables replaced ALL AT ONCE — by the key's parameters and by the
frame's holes or the other members' formers — and its reading is the
recorded reading so substituted (`denoteMeta_substFvars`,
`Model/Reading/SubstFvars.lean`).  The one semantic lemma
(`interp_substAV`) reads it at the valuation holding `τ`'s values; for
`τ` of length one it is `interp_inst`'s content.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term
open ConLeche.SetTheory

universe w

namespace ITerm

/-- **Parallel substitution** at the cut `k`: `bvar (k + j) ↦ (τ j).liftN k`. -/
def substAV (τ : Nat → ITerm) : ITerm → (k : Nat) → ITerm
  | .bvar i, k => if i < k then .bvar i else (τ (i - k)).liftN k
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, k => .app (substAV τ f k) (substAV τ a k)
  | .lam A b, k => .lam (substAV τ A k) (substAV τ b (k + 1))
  | .pi A B, k => .pi (substAV τ A k) (substAV τ B (k + 1))
  | .letE v b, k => .letE (substAV τ v k) (substAV τ b (k + 1))
  | .eqE a b, k => .eqE (substAV τ a k) (substAV τ b k)
  | .fst e, k => .fst (substAV τ e k)
  | .snd e, k => .snd (substAV τ e k)
  | .prf, _ => .prf

@[simp] theorem substAV_app (τ : Nat → ITerm) (f a : ITerm) (k : Nat) :
    substAV τ (.app f a) k = .app (substAV τ f k) (substAV τ a k) := rfl
@[simp] theorem substAV_pi (τ : Nat → ITerm) (A B : ITerm) (k : Nat) :
    substAV τ (.pi A B) k = .pi (substAV τ A k) (substAV τ B (k + 1)) := rfl
@[simp] theorem substAV_lam (τ : Nat → ITerm) (A b : ITerm) (k : Nat) :
    substAV τ (.lam A b) k = .lam (substAV τ A k) (substAV τ b (k + 1)) := rfl
@[simp] theorem substAV_letE (τ : Nat → ITerm) (v b : ITerm) (k : Nat) :
    substAV τ (.letE v b) k = .letE (substAV τ v k) (substAV τ b (k + 1)) := rfl
@[simp] theorem substAV_fst (τ : Nat → ITerm) (e : ITerm) (k : Nat) :
    substAV τ (.fst e) k = .fst (substAV τ e k) := rfl
@[simp] theorem substAV_snd (τ : Nat → ITerm) (e : ITerm) (k : Nat) :
    substAV τ (.snd e) k = .snd (substAV τ e k) := rfl

theorem substAV_bvar_lt (τ : Nat → ITerm) {i k : Nat} (h : i < k) :
    substAV τ (.bvar i) k = .bvar i := by
  simp [substAV, h]

theorem substAV_bvar_ge (τ : Nat → ITerm) {i k : Nat} (h : k ≤ i) :
    substAV τ (.bvar i) k = (τ (i - k)).liftN k := by
  simp [substAV, show ¬ i < k by omega]

/-- **A term closed below the cut is fixed.** -/
theorem substAV_eq_self (τ : Nat → ITerm) : ∀ (e : ITerm) {k : Nat},
    Term.bvarsBelow k e.erase → substAV τ e k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    have h' : i < k := h
    simp [substAV, h']
  | sort u => intro _ _; rfl
  | const c us => intro _ _; rfl
  | prf => intro _ _; rfl
  | app f a ihf iha => intro k h; rw [substAV_app, ihf h.1, iha h.2]
  | lam A b ihA ihb => intro k h; rw [substAV_lam, ihA h.1, ihb h.2]
  | pi A B ihA ihB => intro k h; rw [substAV_pi, ihA h.1, ihB h.2]
  | letE v b ihv ihb => intro k h; rw [substAV_letE, ihv h.1, ihb h.2]
  | eqE a b iha ihb => intro k h; show ITerm.eqE _ _ = _; rw [iha h.1, ihb h.2]
  | fst e ihe => intro k h; rw [substAV_fst, ihe h]
  | snd e ihe => intro k h; rw [substAV_snd, ihe h]

theorem substAV_mkAppN (τ : Nat → ITerm) (k : Nat) :
    ∀ (as : List ITerm) (f : ITerm),
      substAV τ (mkAppN f as) k = mkAppN (substAV τ f k) (as.map (substAV τ · k))
  | [], _ => rfl
  | a :: as, f => by
    rw [mkAppN_cons, substAV_mkAppN τ k as, substAV_app]; rfl

theorem substAV_projAV (τ : Nat → ITerm) (k : Nat) :
    ∀ (i : Nat) (e : ITerm), substAV τ (projAV i e) k = projAV i (substAV τ e k)
  | 0, _ => rfl
  | i + 1, e => by
    show substAV τ (projAV i (.snd e)) k = projAV i (.snd (substAV τ e k))
    rw [substAV_projAV τ k i]; rfl

end ITerm

variable (V : Type w) [SetTheory V]

/-- The valuation `substAV τ · k` reads its subject at: the `k` innermost
positions kept, position `k + j` holding `τ j`'s value (read below the
`k` binders). -/
noncomputable def substE (τ : Nat → ITerm) (k : Nat) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else interp V (shiftE k 0 ρ) (τ (i - k))

theorem cons_substE (τ : Nat → ITerm) (k : Nat) (x : V) (ρ : Nat → V) :
    cons x (substE V τ k ρ) = substE V τ (k + 1) (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [substE]
  | succ j =>
    show substE V τ k ρ j = substE V τ (k + 1) (cons x ρ) (j + 1)
    simp only [substE]
    by_cases h : j < k
    · rw [ite_eq_left h, ite_eq_left (show j + 1 < k + 1 by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (show ¬ (j + 1 < k + 1) by omega), shiftE_succ_cons,
        show j + 1 - (k + 1) = j - k by omega]

/-- **The substitution lemma** for parallel substitution. -/
theorem interp_substAV (τ : Nat → ITerm) :
    ∀ (e : ITerm) (k : Nat) (ρ : Nat → V),
      interp V ρ (ITerm.substAV τ e k) = interp V (substE V τ k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    by_cases h : i < k
    · rw [ITerm.substAV_bvar_lt τ h, interp_bvar, interp_bvar]
      simp [substE, h]
    · rw [ITerm.substAV_bvar_ge τ (by omega), interp_liftN, interp_bvar]
      simp only [substE, ite_eq_right h]
  | sort u => intro k ρ; rfl
  | const c us => intro k ρ; rfl
  | prf => intro k ρ; rfl
  | app f a ihf iha =>
    intro k ρ; rw [ITerm.substAV_app, interp_app, interp_app, ihf, iha]
  | lam A b ihA ihb =>
    intro k ρ
    rw [ITerm.substAV_lam, interp_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, ← cons_substE]
  | pi A B ihA ihB =>
    intro k ρ
    rw [ITerm.substAV_pi, interp_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, ← cons_substE]
  | letE v b ihv ihb =>
    intro k ρ
    rw [ITerm.substAV_letE, interp_letE, interp_letE, ihv, ihb, ← cons_substE]
  | eqE a b iha ihb =>
    intro k ρ
    show interp V ρ (.eqE _ _) = _
    rw [interp_eqE, interp_eqE, iha, ihb]
  | fst e ihe => intro k ρ; rw [ITerm.substAV_fst, interp_fst, interp_fst, ihe]
  | snd e ihe => intro k ρ; rw [ITerm.substAV_snd, interp_snd, interp_snd, ihe]

/-- Below a spine of values, the cut moves up by the spine's length. -/
theorem substE_consList (τ : Nat → ITerm) :
    ∀ (fs : List V) (k : Nat) (ρ : Nat → V),
      substE V τ (fs.length + k) (consList fs ρ) = consList fs (substE V τ k ρ)
  | [], k, ρ => by simp [consList]
  | f :: fs, k, ρ => by
    rw [List.length_cons, show fs.length + 1 + k = fs.length + (k + 1) by omega, consList_cons,
      substE_consList τ fs (k + 1) (cons f ρ), ← cons_substE, consList_cons]


/-! ## Π-towers -/

namespace ITerm

/-- A Π-tower's binder data, substituted at increasing cuts. -/
def substTele (τ : Nat → ITerm) : Nat → List ITerm → List ITerm
  | _, [] => []
  | k, d :: ds => substAV τ d k :: substTele τ (k + 1) ds

theorem substAV_mkPisAV (τ : Nat → ITerm) (B : ITerm) :
    ∀ (ab : List ITerm) (k : Nat),
      substAV τ (mkPisAV ab B) k = mkPisAV (substTele τ k ab) (substAV τ B (k + ab.length))
  | [], k => rfl
  | d :: ab, k => by
    show ITerm.pi _ (substAV τ (mkPisAV ab B) (k + 1)) = ITerm.pi _ _
    rw [substAV_mkPisAV τ B ab (k + 1), List.length_cons, show k + 1 + ab.length = k + (ab.length + 1)
      by omega]


end ITerm

/-- **A spine fits a substituted telescope exactly when it fits the
telescope at the substituted valuation.** -/
theorem spineFit_substTele (τ : Nat → ITerm) :
    ∀ (ab : List ITerm) (k : Nat) (ρ : Nat → V) (fs : List V),
      SpineFit ρ (ITerm.substTele τ k ab) fs ↔
        SpineFit (substE V τ k ρ) ab fs
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | d :: ab, k, ρ, f :: fs => by
    show (f ∈ˢ interp V ρ (ITerm.substAV τ d k) ∧ _) ↔ (f ∈ˢ interp V _ d ∧ _)
    rw [interp_substAV, spineFit_substTele τ ab (k + 1) (cons f ρ) fs, ← cons_substE]

end ConLeche.Semantics
